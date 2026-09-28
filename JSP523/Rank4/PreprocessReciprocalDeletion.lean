import JSP523.Rank4.GraphCompletionData

/-!
# Deleting edges with distinct reciprocal witnesses

For a fixed pair-link root, the bad deletion set consists of the target
four-edges that carry a reciprocal pair with two distinct witnesses.  The
remaining-family statement is separated from the quantitative estimate for
the size of this set.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Edges to delete at `P`: a target edge `abP` is included when the parent
pair-link contains `ab`, has witnesses `br` and `as`, and their labels make
them reciprocal with distinct witnesses. -/
noncomputable def reciprocalDifferentWitnessDeletionSet
    (D : FiniteCompletionCliqueData α) (P : Edge α) : Family α := by
  classical
  exact D.K.filter fun E => ∃ a b r s : α,
    E = insert a (insert b P) ∧
    (completionPairLinkGraph D P).Adj a b ∧
    (completionPairLinkGraph D P).Adj b r ∧
    (completionPairLinkGraph D P).Adj a s ∧
    D.label a r = b ∧ D.label b s = a ∧
    a ≠ r ∧ b ≠ s ∧ r ≠ s

/-- Delete bad reciprocal edges over every two-element root in the ground
set. -/
noncomputable def reciprocalDifferentWitnessDeletionSetAll
    (D : FiniteCompletionCliqueData α) : Family α := by
  classical
  exact D.ground.powersetCard 2 |>.biUnion
    (fun P => reciprocalDifferentWitnessDeletionSet D P)

/-- Label fiber at a fixed ordered pair of center and label. -/
def reciprocalLabelFiber
    (D : FiniteCompletionCliqueData α) (a b : α) : Finset α :=
  D.ground.filter fun r => a ≠ r ∧ D.label a r = b

/-- Pair tails supporting a distinct-witness reciprocal. -/
noncomputable def reciprocalWitnessTailFiber
    (D : FiniteCompletionCliqueData α) (a b r s : α) : Family α := by
  classical
  exact (D.ground.powersetCard 2).filter fun P =>
    a ≠ b ∧ a ≠ r ∧ a ≠ s ∧ b ≠ r ∧ b ≠ s ∧ r ≠ s ∧
    (completionPairLinkGraph D P).Adj a b ∧
    (completionPairLinkGraph D P).Adj b r ∧
    (completionPairLinkGraph D P).Adj a s

/-- Finite tuples `(ab, (rs, P))` witnessing the bad deletion pattern. -/
noncomputable def reciprocalDifferentWitnessTuples
    (D : FiniteCompletionCliqueData α) :
    Finset ((α × α) × ((α × α) × Edge α)) := by
  classical
  exact (D.ground.product D.ground).biUnion fun ab =>
    ((reciprocalLabelFiber D ab.1 ab.2).product
      (reciprocalLabelFiber D ab.2 ab.1)).biUnion fun rs =>
        (reciprocalWitnessTailFiber D ab.1 ab.2 rs.1 rs.2).image
          fun P => (ab, (rs, P))

/-- Edges represented by distinct-witness tuples. -/
noncomputable def reciprocalDifferentWitnessTupleEdges
    (D : FiniteCompletionCliqueData α) : Family α := by
  classical
  exact (reciprocalDifferentWitnessTuples D).image fun z =>
    insert z.1.1 (insert z.1.2 z.2.2)

omit [Fintype α] in
/-- The nested witness count: label fibers contribute `K_*²` choices and
the disjoint-root common-tail fiber contributes `C_D` choices. -/
theorem reciprocal_different_witness_tuples_card_le
    (D : FiniteCompletionCliqueData α) (Kstar C_D : ℕ)
    (hLabelFiber : ∀ a b : α,
      (reciprocalLabelFiber D a b).card ≤ Kstar)
    (hTailFiber : ∀ a b r s : α,
      (reciprocalWitnessTailFiber D a b r s).card ≤ C_D) :
    (reciprocalDifferentWitnessTuples D).card ≤
      D.ground.card * D.ground.card * Kstar * Kstar * C_D := by
  classical
  let pairs := D.ground.product D.ground
  have hPerPair : ∀ ab ∈ pairs,
      (((reciprocalLabelFiber D ab.1 ab.2).product
        (reciprocalLabelFiber D ab.2 ab.1)).biUnion fun rs =>
          (reciprocalWitnessTailFiber D ab.1 ab.2 rs.1 rs.2).image
            fun P => (ab, (rs, P))).card ≤ Kstar * Kstar * C_D := by
    intro ab hab
    let witnesses := (reciprocalLabelFiber D ab.1 ab.2).product
      (reciprocalLabelFiber D ab.2 ab.1)
    have hWitnessCard : witnesses.card ≤ Kstar * Kstar := by
      dsimp [witnesses]
      rw [Finset.card_product]
      exact Nat.mul_le_mul (hLabelFiber ab.1 ab.2)
        (hLabelFiber ab.2 ab.1)
    have hUnionCard :
        (witnesses.biUnion fun rs =>
          (reciprocalWitnessTailFiber D ab.1 ab.2 rs.1 rs.2).image
            fun P => (ab, (rs, P))).card ≤ witnesses.card * C_D := by
      apply Finset.card_biUnion_le_card_mul
      intro rs hrs
      exact (Finset.card_image_le).trans (hTailFiber ab.1 ab.2 rs.1 rs.2)
    dsimp [witnesses]
    exact hUnionCard.trans (Nat.mul_le_mul_right C_D hWitnessCard)
  have hTotal := Finset.card_biUnion_le_card_mul pairs _
      (Kstar * Kstar * C_D) hPerPair
  simpa [reciprocalDifferentWitnessTuples, pairs, Finset.card_product,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hTotal

/-- Every deleted edge is represented by at least one distinct-witness
tuple. -/
theorem reciprocal_different_witness_deletion_set_all_subset_tuple_edges
    (D : FiniteCompletionCliqueData α) :
    reciprocalDifferentWitnessDeletionSetAll D ⊆
      reciprocalDifferentWitnessTupleEdges D := by
  classical
  intro E hE
  rcases Finset.mem_biUnion.mp hE with ⟨P, hP, hEP⟩
  rcases Finset.mem_filter.mp hEP with ⟨hEK, hBad⟩
  rcases hBad with
    ⟨a, b, r, s, hEq, hAB, hBR, hAS, hLabAR, hLabBS,
      hNeAR, hNeBS, hrs⟩
  have hAB' := hAB
  have hBR' := hBR
  have hAS' := hAS
  change a ∉ P ∧ b ∉ P ∧ a ∈ D.ground ∧ b ∈ D.ground ∧
    a ≠ b ∧ insert a (insert b P) ∈ D.K at hAB'
  change b ∉ P ∧ r ∉ P ∧ b ∈ D.ground ∧ r ∈ D.ground ∧
    b ≠ r ∧ insert b (insert r P) ∈ D.K at hBR'
  change a ∉ P ∧ s ∉ P ∧ a ∈ D.ground ∧ s ∈ D.ground ∧
    a ≠ s ∧ insert a (insert s P) ∈ D.K at hAS'
  have hr : r ∈ reciprocalLabelFiber D a b := by
    apply Finset.mem_filter.mpr
    exact ⟨hBR'.2.2.2.1, hNeAR, hLabAR⟩
  have hs : s ∈ reciprocalLabelFiber D b a := by
    apply Finset.mem_filter.mpr
    exact ⟨hAS'.2.2.2.1, hNeBS, hLabBS⟩
  have hTuple : ((a, b), ((r, s), P)) ∈
      reciprocalDifferentWitnessTuples D := by
    apply Finset.mem_biUnion.mpr
    refine ⟨(a, b), Finset.mem_product.mpr
      ⟨hAB'.2.2.1, hAB'.2.2.2.1⟩, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨(r, s), Finset.mem_product.mpr ⟨hr, hs⟩, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨P, Finset.mem_filter.mpr ⟨hP, ?_⟩, ?_⟩
    · exact ⟨hAB'.2.2.2.2.1, hNeAR, hAS'.2.2.2.2.1,
        hBR'.2.2.2.2.1, hNeBS, hrs, hAB, hBR, hAS⟩
    · rfl
  apply Finset.mem_image.mpr
  refine ⟨((a, b), ((r, s), P)), hTuple, ?_⟩
  simpa using hEq.symm

/-- Quantitative deletion bound from the two actual finite fiber inputs.
With `Kstar = K_*` and `C_D = max(D,3)`, this is the stated
`n² K_*² C_D` estimate. -/
theorem reciprocal_different_witness_deletion_set_all_card_le
    (D : FiniteCompletionCliqueData α) (Kstar C_D : ℕ)
    (hLabelFiber : ∀ a b : α,
      (reciprocalLabelFiber D a b).card ≤ Kstar)
    (hTailFiber : ∀ a b r s : α,
      (reciprocalWitnessTailFiber D a b r s).card ≤ C_D) :
    (reciprocalDifferentWitnessDeletionSetAll D).card ≤
      D.ground.card * D.ground.card * Kstar * Kstar * C_D := by
  calc
    _ ≤ (reciprocalDifferentWitnessTupleEdges D).card :=
      Finset.card_le_card
        (reciprocal_different_witness_deletion_set_all_subset_tuple_edges D)
    _ ≤ (reciprocalDifferentWitnessTuples D).card := Finset.card_image_le
    _ ≤ D.ground.card * D.ground.card * Kstar * Kstar * C_D :=
      reciprocal_different_witness_tuples_card_le D Kstar C_D
        hLabelFiber hTailFiber

/-- The concrete finite cleanup: remove the union of all distinct-witness
deletion sets, preserving the parent labels and ground set. -/
noncomputable def clearReciprocalDifferentWitnesses
    (D : FiniteCompletionCliqueData α) : FiniteCompletionCliqueData α := by
  classical
  let K' := D.K \ reciprocalDifferentWitnessDeletionSetAll D
  have hSub : K' ⊆ D.K := Finset.sdiff_subset
  refine ⟨D.ground, K', ?_, ?_, D.label, D.label_symm, ?_, ?_⟩
  · intro E hE
    exact D.uniform_four (hSub hE)
  · exact admissible_mono hSub D.admissible
  · intro x y hxy P hP
    have hCell := mem_common_triple_cell.mp hP
    exact D.label_center x y hxy P (mem_common_triple_cell.mpr
      ⟨hCell.1, hCell.2.1, hCell.2.2.1,
        hSub hCell.2.2.2.1, hSub hCell.2.2.2.2⟩)
  · intro T x hx y hy z hz hxy hxz hyz
    have hx' : x ∈ graphFacetCompletions D.K D.ground T := by
      apply Finset.mem_filter.mpr
      exact ⟨(Finset.mem_filter.mp hx).1,
        hSub (Finset.mem_filter.mp hx).2⟩
    have hy' : y ∈ graphFacetCompletions D.K D.ground T := by
      apply Finset.mem_filter.mpr
      exact ⟨(Finset.mem_filter.mp hy).1,
        hSub (Finset.mem_filter.mp hy).2⟩
    have hz' : z ∈ graphFacetCompletions D.K D.ground T := by
      apply Finset.mem_filter.mpr
      exact ⟨(Finset.mem_filter.mp hz).1,
        hSub (Finset.mem_filter.mp hz).2⟩
    exact D.no_bicolored_triangle T x hx' y hy' z hz' hxy hxz hyz

theorem clear_reciprocal_different_witnesses_sub
    (D : FiniteCompletionCliqueData α) :
    (clearReciprocalDifferentWitnesses D).K ⊆ D.K := by
  classical
  change (D.K \ reciprocalDifferentWitnessDeletionSetAll D) ⊆ D.K
  exact Finset.sdiff_subset

theorem clear_reciprocal_different_witnesses_avoids_all
    (D : FiniteCompletionCliqueData α) :
    ∀ E ∈ reciprocalDifferentWitnessDeletionSetAll D,
      E ∉ (clearReciprocalDifferentWitnesses D).K := by
  classical
  intro E hE hClean
  change E ∈ D.K \ reciprocalDifferentWitnessDeletionSetAll D at hClean
  have hDiff := Finset.mem_sdiff.mp hClean
  exact hDiff.2 hE

theorem clear_reciprocal_different_witnesses_avoids_root
    (D : FiniteCompletionCliqueData α) (P : Edge α)
    (hPcard : P.card = 2) (hPground : P ⊆ D.ground) :
    ∀ E ∈ reciprocalDifferentWitnessDeletionSet D P,
      E ∉ (clearReciprocalDifferentWitnesses D).K := by
  classical
  intro E hE hClean
  have hUnion : E ∈ reciprocalDifferentWitnessDeletionSetAll D :=
    Finset.mem_biUnion.mpr ⟨P,
      Finset.mem_powersetCard.mpr ⟨hPground, hPcard⟩, hE⟩
  exact clear_reciprocal_different_witnesses_avoids_all D E hUnion hClean

theorem mem_reciprocal_different_witness_deletion_set
    (D : FiniteCompletionCliqueData α) (P E : Edge α)
    (hE : E ∈ D.K)
    (hBad : ∃ a b r s : α,
      E = insert a (insert b P) ∧
      (completionPairLinkGraph D P).Adj a b ∧
      (completionPairLinkGraph D P).Adj b r ∧
      (completionPairLinkGraph D P).Adj a s ∧
      D.label a r = b ∧ D.label b s = a ∧
      a ≠ r ∧ b ≠ s ∧ r ≠ s) :
    E ∈ reciprocalDifferentWitnessDeletionSet D P := by
  classical
  exact Finset.mem_filter.mpr ⟨hE, hBad⟩

omit [Fintype α] in
/-- Pair-link edges are monotone under deleting four-edges. -/
theorem completion_pair_link_graph_adj_mono
    (D₀ D : FiniteCompletionCliqueData α) (P : Edge α)
    (hGround : D.ground = D₀.ground) (hSub : D.K ⊆ D₀.K)
    {a b : α}
    (h : (completionPairLinkGraph D P).Adj a b) :
    (completionPairLinkGraph D₀ P).Adj a b := by
  change a ∉ P ∧ b ∉ P ∧ a ∈ D.ground ∧ b ∈ D.ground ∧ a ≠ b ∧
    insert a (insert b P) ∈ D.K at h
  change a ∉ P ∧ b ∉ P ∧ a ∈ D₀.ground ∧ b ∈ D₀.ground ∧ a ≠ b ∧
    insert a (insert b P) ∈ D₀.K
  exact ⟨h.1, h.2.1, hGround ▸ h.2.2.1, hGround ▸ h.2.2.2.1,
    h.2.2.2.2.1, hSub h.2.2.2.2.2⟩

/-- If the final family is a subfamily of its parent and excludes every
parent edge in the explicit distinct-witness deletion set, then no
surviving reciprocal edge has distinct witnesses.  This is the precise
monotonicity bridge from the finite deletion operation to `hNoSecond`. -/
theorem no_second_reciprocal_witness_of_deletion
    (D₀ D : FiniteCompletionCliqueData α) (P : Edge α)
    (hGround : D.ground = D₀.ground)
    (hLabel : D.label = D₀.label)
    (hSub : D.K ⊆ D₀.K)
    (hAvoid : ∀ E ∈ reciprocalDifferentWitnessDeletionSet D₀ P,
      E ∉ D.K) :
    ∀ a b r s : α,
      (completionPairLinkGraph D P).Adj a b →
      (completionPairLinkGraph D P).Adj b r →
      (completionPairLinkGraph D P).Adj a s →
      a ≠ r → b ≠ s →
      D.label a r = b → D.label b s = a → r = s := by
  classical
  intro a b r s hAB hBR hAS hNeAR hNeBS hLabAR hLabBS
  by_contra hrs
  have hAB₀ := completion_pair_link_graph_adj_mono D₀ D P hGround hSub hAB
  have hBR₀ := completion_pair_link_graph_adj_mono D₀ D P hGround hSub hBR
  have hAS₀ := completion_pair_link_graph_adj_mono D₀ D P hGround hSub hAS
  have hLabAR₀ : D₀.label a r = b := by simpa [hLabel] using hLabAR
  have hLabBS₀ : D₀.label b s = a := by simpa [hLabel] using hLabBS
  have hTarget : insert a (insert b P) ∈ D.K := by
    change a ∉ P ∧ b ∉ P ∧ a ∈ D.ground ∧ b ∈ D.ground ∧ a ≠ b ∧
      insert a (insert b P) ∈ D.K at hAB
    exact hAB.2.2.2.2.2
  have hBad : insert a (insert b P) ∈
      reciprocalDifferentWitnessDeletionSet D₀ P := by
    exact mem_reciprocal_different_witness_deletion_set
      D₀ P (insert a (insert b P)) (hSub hTarget)
      ⟨a, b, r, s, rfl, hAB₀, hBR₀, hAS₀,
        hLabAR₀, hLabBS₀, hNeAR, hNeBS, hrs⟩
  exact hAvoid _ hBad hTarget

/-- The explicit deletion constructor yields the uniqueness condition used
by the reciprocal-triangle isolation argument. -/
theorem clear_reciprocal_different_witnesses_no_second
    (D : FiniteCompletionCliqueData α) (P : Edge α)
    (hPcard : P.card = 2) (hPground : P ⊆ D.ground) :
    ∀ a b r s : α,
      (completionPairLinkGraph (clearReciprocalDifferentWitnesses D) P).Adj a b →
      (completionPairLinkGraph (clearReciprocalDifferentWitnesses D) P).Adj b r →
      (completionPairLinkGraph (clearReciprocalDifferentWitnesses D) P).Adj a s →
      a ≠ b → a ≠ r → a ≠ s → b ≠ r → b ≠ s → r ≠ s →
      (clearReciprocalDifferentWitnesses D).label a r = b →
      (clearReciprocalDifferentWitnesses D).label b s = a → r = s := by
  classical
  have hAvoid := clear_reciprocal_different_witnesses_avoids_root D P hPcard hPground
  have hSub := clear_reciprocal_different_witnesses_sub D
  have hLabel : (clearReciprocalDifferentWitnesses D).label = D.label := by
    rfl
  intro a b r s hAB hBR hAS _hab hAR _haS _hbR hBS _hrs hLabAR hLabBS
  exact no_second_reciprocal_witness_of_deletion
    D (clearReciprocalDifferentWitnesses D) P rfl hLabel hSub hAvoid
    a b r s hAB hBR hAS hAR hBS hLabAR hLabBS

/-- The actual loss in the deletion constructor is bounded by the bad-edge
union. -/
theorem clear_reciprocal_different_witnesses_loss_card_le
    (D : FiniteCompletionCliqueData α) :
    (D.K \ (clearReciprocalDifferentWitnesses D).K).card ≤
      (reciprocalDifferentWitnessDeletionSetAll D).card := by
  classical
  apply Finset.card_le_card
  intro E hE
  have hEH := (Finset.mem_sdiff.mp hE).1
  have hENot := (Finset.mem_sdiff.mp hE).2
  by_contra hENotBad
  have hClean : E ∈ (clearReciprocalDifferentWitnesses D).K := by
    change E ∈ D.K \ reciprocalDifferentWitnessDeletionSetAll D
    exact Finset.mem_sdiff.mpr ⟨hEH, hENotBad⟩
  exact hENot hClean

/-- The deletion budget obtained from the label and common-tail fiber
bounds. -/
theorem clear_reciprocal_different_witnesses_loss_card_le_of_fibers
    (D : FiniteCompletionCliqueData α) (Kstar C_D : ℕ)
    (hLabelFiber : ∀ a b : α,
      (reciprocalLabelFiber D a b).card ≤ Kstar)
    (hTailFiber : ∀ a b r s : α,
      (reciprocalWitnessTailFiber D a b r s).card ≤ C_D) :
    (D.K \ (clearReciprocalDifferentWitnesses D).K).card ≤
      D.ground.card * D.ground.card * Kstar * Kstar * C_D := by
  exact clear_reciprocal_different_witnesses_loss_card_le D |>.trans
    (reciprocal_different_witness_deletion_set_all_card_le D Kstar C_D
      hLabelFiber hTailFiber)

end JSP523.Rank4
