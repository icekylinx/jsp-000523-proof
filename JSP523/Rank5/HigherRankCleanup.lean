import JSP523.Rank5.HigherRankInheritance

/-!
# Finite cleanup for higher-rank center inheritance

The cleanup deletes an edge exactly when it contains a witness to a failed
noncenter deletion at the base rank. This derives the occurrence-local
inheritance law needed by the higher-rank center tower.
-/

namespace JSP523.Rank5

section HigherRankCleanup

variable {α : Type*} [DecidableEq α]

/-- A base-rank face inside `E` violates noncenter deletion inheritance. -/
def HasBadRankDeletion (n : ℕ) (z : Edge α → α) (E : Edge α) : Prop :=
  ∃ T : Edge α, T ⊆ E ∧ T.card = n ∧
    ∃ a ∈ T, a ≠ z T ∧ z (T.erase a) ≠ z T

/-- Retain exactly the edges with no bad base-rank deletion. -/
noncomputable def repairRankInheritance
    (F : Family α) (n : ℕ) (z : Edge α → α) : Family α := by
  classical
  exact F.filter (fun E => ¬ HasBadRankDeletion n z E)

theorem repair_rank_inheritance_subset
    (F : Family α) (n : ℕ) (z : Edge α → α) :
    repairRankInheritance F n z ⊆ F := by
  classical
  exact Finset.filter_subset _ _

/-- An actual base-rank label lies in its face before cleanup. -/
def ActualRankLabels (F : Family α) (n : ℕ) (z : Edge α → α) : Prop :=
  ∀ T : Edge α, (∃ E ∈ F, T ⊆ E) → T.card = n → z T ∈ T

/-- Filtering all parent edges incident with a bad deletion forces exact
    noncenter inheritance on every base-rank face that still occurs. -/
theorem repaired_family_rank_center_inheritance
    {F : Family α} {n : ℕ} {z : Edge α → α}
    (hLabels : ActualRankLabels F n z) :
    FamilyRankCenterInheritance (repairRankInheritance F n z) n z := by
  intro T hOcc hT
  obtain ⟨E, hE, hTE⟩ := hOcc
  have hEparts : E ∈ F ∧ ¬ HasBadRankDeletion n z E := by
    simpa only [repairRankInheritance, Finset.mem_filter] using hE
  refine ⟨hLabels T ⟨E, hEparts.1, hTE⟩ hT, ?_⟩
  intro a ha hna
  by_contra hneq
  exact hEparts.2 ⟨T, hTE, hT, a, ha, hna, hneq⟩

/-- Explicit `(face, deleted vertex)` witnesses within one parent edge. -/
def badRankDeletionWitnesses (n : ℕ) (z : Edge α → α) (E : Edge α) :
    Finset (Edge α × α) :=
  ((E.powersetCard n).product E).filter (fun p =>
    p.2 ∈ p.1 ∧ p.2 ≠ z p.1 ∧ z (p.1.erase p.2) ≠ z p.1)

theorem bad_rank_deletion_witnesses_nonempty_of_bad
    {n : ℕ} {z : Edge α → α} {E : Edge α}
    (hBad : HasBadRankDeletion n z E) :
    (badRankDeletionWitnesses n z E).Nonempty := by
  obtain ⟨T, hTE, hT, a, ha, hna, hneq⟩ := hBad
  have haE := hTE ha
  refine ⟨(T, a), Finset.mem_filter.mpr ⟨?_, ⟨ha, hna, hneq⟩⟩⟩
  exact Finset.mem_product.mpr
    ⟨Finset.mem_powersetCard.mpr ⟨hTE, hT⟩, haE⟩

/-- Preserve the parent edge in each bad-deletion incidence. -/
def badRankDeletionIncidences (F : Family α) (n : ℕ)
    (z : Edge α → α) : Finset ((_E : Edge α) × Edge α × α) :=
  F.sigma (fun E => badRankDeletionWitnesses n z E)

/-- Exact finite loss charge to actual bad-deletion incidences. -/
theorem repair_rank_inheritance_loss_le_bad_incidences
    (F : Family α) (n : ℕ) (z : Edge α → α) [Nonempty α] :
    F.card - (repairRankInheritance F n z).card ≤
      (badRankDeletionIncidences F n z).card := by
  classical
  let bad := F.filter (HasBadRankDeletion n z)
  have hPartition : bad.card + (repairRankInheritance F n z).card = F.card := by
    simpa [bad, repairRankInheritance] using
      (Finset.card_filter_add_card_filter_not
        (s := F) (HasBadRankDeletion n z))
  let pick : Edge α → (_E : Edge α) × Edge α × α := fun E =>
    ⟨E, if h : HasBadRankDeletion n z E then
      Classical.choose (bad_rank_deletion_witnesses_nonempty_of_bad h)
      else (∅, Classical.choice inferInstance)⟩
  have hInject : bad.card ≤ (badRankDeletionIncidences F n z).card := by
    apply Finset.card_le_card_of_injOn pick
    · intro E hE
      have hParts : E ∈ F ∧ HasBadRankDeletion n z E := by
        simpa [bad] using hE
      have hW := Classical.choose_spec
        (bad_rank_deletion_witnesses_nonempty_of_bad hParts.2)
      change pick E ∈ F.sigma (fun E => badRankDeletionWitnesses n z E)
      rw [Finset.mem_sigma]
      refine ⟨hParts.1, ?_⟩
      simpa [pick, hParts.2] using hW
    · intro E _ G _ hEq
      exact congrArg Sigma.fst hEq
  omega

/-- A finite inherited-prefix assignment on the repaired family, derived
    solely from actual base-rank labels and the explicit bad deletion filter. -/
theorem repaired_higher_rank_assigned_prefix_center_exists
    {r : ℕ} (hr : 6 ≤ r) {F : Family α} {V : Edge α}
    (hUniform : Uniform r F) {z : Edge α → α}
    (hLabels : ActualRankLabels F (r - 2) z) :
    ∃ chosen : Edge α → Edge α,
      (∀ E ∈ repairRankInheritance F (r - 2) z, chosen E ⊆ E) ∧
      (∀ E ∈ repairRankInheritance F (r - 2) z,
        (chosen E).card = r - 3) ∧
      (∀ P : Edge α,
        ∀ Y ∈ JSP523.Counting.chosenPrefixesAt
          (repairRankInheritance F (r - 2) z) V (r - 3) chosen P,
        ∀ x ∈ P, z (Y ∪ {x}) ∈ Y) := by
  classical
  have hUniformRepair : Uniform r (repairRankInheritance F (r - 2) z) := by
    intro E hE
    exact hUniform (Finset.mem_filter.mp hE).1
  exact higher_rank_assigned_prefix_center_exists hr hUniformRepair
    (repaired_family_rank_center_inheritance hLabels)

end HigherRankCleanup

end JSP523.Rank5
