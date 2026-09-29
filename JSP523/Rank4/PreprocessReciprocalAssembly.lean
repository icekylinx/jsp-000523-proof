import JSP523.Rank4.PreprocessUsedParentCleanup
import JSP523.Rank4.GraphReciprocalDegreeTwo
import JSP523.Rank4.PreprocessUsedParentWedgeBudget
import JSP523.Rank4.PreprocessParentTails

/-!
# Actual rank-four reciprocal preprocessing assembly

First remove pair-label separation violations in the used parent system.
Then remove the distinct-witness and wrong-common-witness reciprocal
targets. All three removals preserve ground and labels. The final family
obeys the actual finite `R ≤ b` bound without a separation premise.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
theorem reciprocal_label_fiber_eq_of_ground_label
    (D' D : FiniteCompletionCliqueData α)
    (h_ground : D'.ground = D.ground)
    (h_label : D'.label = D.label)
    (a b : α) :
    reciprocalLabelFiber D' a b = reciprocalLabelFiber D a b := by
  simp only [reciprocalLabelFiber, h_ground, h_label]

omit [Fintype α] in
/-- Restricting the parent family can only shrink the used center-graph
label fiber when the ground and label function are preserved. -/
theorem reciprocal_used_label_fiber_mono_of_family
    (D' D : FiniteCompletionCliqueData α)
    (h_ground : D'.ground = D.ground)
    (h_label : D'.label = D.label)
    (h_family : D'.K ⊆ D.K) (a b : α) :
    reciprocalUsedLabelFiber D' a b ⊆
      reciprocalUsedLabelFiber D a b := by
  intro r hr
  have hparts := Finset.mem_filter.mp hr
  apply Finset.mem_filter.mpr
  refine ⟨?_, ?_⟩
  · simpa only [reciprocal_label_fiber_eq_of_ground_label D' D
      h_ground h_label] using hparts.1
  · obtain ⟨T, hT⟩ := hparts.2
    exact ⟨T, common_triple_cell_mono_family_ground h_family
      (by rw [h_ground]) hT⟩

omit [Fintype α] in
theorem reciprocal_witness_tail_fiber_mono_data
    (D' D : FiniteCompletionCliqueData α)
    (h_ground : D'.ground = D.ground)
    (h_sub : D'.K ⊆ D.K)
    (a b r s : α) :
    reciprocalWitnessTailFiber D' a b r s ⊆
      reciprocalWitnessTailFiber D a b r s := by
  classical
  have hAdj (P : Edge α) (u v : α)
      (h : (completionPairLinkGraph D' P).Adj u v) :
      (completionPairLinkGraph D P).Adj u v := by
    change u ∉ P ∧ v ∉ P ∧ u ∈ D'.ground ∧ v ∈ D'.ground ∧
      u ≠ v ∧ insert u (insert v P) ∈ D'.K at h
    change u ∉ P ∧ v ∉ P ∧ u ∈ D.ground ∧ v ∈ D.ground ∧
      u ≠ v ∧ insert u (insert v P) ∈ D.K
    exact ⟨h.1, h.2.1, h_ground ▸ h.2.2.1,
      h_ground ▸ h.2.2.2.1, h.2.2.2.2.1, h_sub h.2.2.2.2.2⟩
  intro P hP
  have hParts := Finset.mem_filter.mp hP
  apply Finset.mem_filter.mpr
  refine ⟨?_, ?_⟩
  · simpa only [h_ground] using hParts.1
  · rcases hParts.2 with
      ⟨hab, har, has, hbr, hbs, hrs, hAB, hBR, hAS⟩
    exact ⟨hab, har, has, hbr, hbs, hrs,
      hAdj P a b hAB, hAdj P b r hBR, hAdj P a s hAS⟩

noncomputable def clearUsedParentThenReciprocal
    (D : FiniteCompletionCliqueData α) : FiniteCompletionCliqueData α :=
  clearReciprocalFully (clearUsedParentPairSeparation D)

/-- The full reciprocal survivor has actual used-parent pair separation.
This property is retained through both later reciprocal deletions. -/
theorem clear_used_parent_then_reciprocal_separated
    (D : FiniteCompletionCliqueData α) :
    ReciprocalUsedParentPairSeparation
      (clearUsedParentThenReciprocal D) := by
  let D₁ := clearUsedParentPairSeparation D
  let D₂ := clearReciprocalDifferentWitnesses D₁
  let D₃ := clearUsedParentThenReciprocal D
  have h_sub_1 : D₂.K ⊆ D₁.K :=
    clear_reciprocal_different_witnesses_sub D₁
  have h_sub_2 : D₃.K ⊆ D₂.K :=
    clear_reciprocal_wrong_common_witnesses_sub D₂
  exact reciprocal_used_parent_pair_separation_mono_data
    D₃ D₁ rfl rfl (h_sub_2.trans h_sub_1)
      (clear_used_parent_pair_separation_actual D)

/-- The corrected three-stage preprocessing proves the actual finite
`R ≤ b` for its final family. The only input is containment in the
specified ground set. -/
theorem clear_used_parent_then_reciprocal_unordered_card_le_nonprivate
    (D : FiniteCompletionCliqueData α)
    (h_ground : ∀ E ∈ D.K, E ⊆ D.ground) :
    (actualReciprocalUnorderedOccurrences
      (clearUsedParentThenReciprocal D)).card ≤
      (rankFourNonprivateFacets
        (clearUsedParentThenReciprocal D).K D.ground).card := by
  let D₁ := clearUsedParentPairSeparation D
  have h_ground_1 : ∀ E ∈ D₁.K, E ⊆ D.ground := by
    intro E hE
    exact h_ground E (clear_used_parent_pair_separation_sub D hE)
  exact clear_reciprocal_fully_unordered_card_le_nonprivate
    D₁ h_ground_1
    (clear_used_parent_then_reciprocal_separated D)

/-- Exact finite loss budget for the three actual deletion rounds. -/
theorem clear_used_parent_then_reciprocal_loss_card_le
    (D : FiniteCompletionCliqueData α) :
    (D.K \ (clearUsedParentThenReciprocal D).K).card ≤
      (usedParentPairSeparationBadEdges D).card +
      (reciprocalDifferentWitnessDeletionSetAll
        (clearUsedParentPairSeparation D)).card +
      (reciprocalWrongCommonWitnessDeletionSetAll
        (clearReciprocalDifferentWitnesses
          (clearUsedParentPairSeparation D))).card := by
  classical
  let D₁ := clearUsedParentPairSeparation D
  let D₃ := clearUsedParentThenReciprocal D
  have h_sub_1 : D₁.K ⊆ D.K :=
    clear_used_parent_pair_separation_sub D
  have h_sub_3 : D₃.K ⊆ D₁.K := by
    exact (clear_reciprocal_wrong_common_witnesses_sub
      (clearReciprocalDifferentWitnesses D₁)).trans
        (clear_reciprocal_different_witnesses_sub D₁)
  have h_sub : D₃.K ⊆ D.K := h_sub_3.trans h_sub_1
  have h_card_1 := Finset.card_sdiff_add_card_eq_card h_sub_1
  have h_card_3 := Finset.card_sdiff_add_card_eq_card h_sub_3
  have h_card := Finset.card_sdiff_add_card_eq_card h_sub
  have h_loss_1 := clear_used_parent_pair_separation_loss_card_le D
  have h_loss_3 := clear_reciprocal_fully_loss_card_le D₁
  change (D.K \ D₁.K).card ≤
    (usedParentPairSeparationBadEdges D).card at h_loss_1
  change (D₁.K \ D₃.K).card ≤
    (reciprocalDifferentWitnessDeletionSetAll D₁).card +
      (reciprocalWrongCommonWitnessDeletionSetAll
        (clearReciprocalDifferentWitnesses D₁)).card at h_loss_3
  change (D.K \ D₃.K).card ≤
    (usedParentPairSeparationBadEdges D).card +
      (reciprocalDifferentWitnessDeletionSetAll D₁).card +
      (reciprocalWrongCommonWitnessDeletionSetAll
        (clearReciprocalDifferentWitnesses D₁)).card
  omega

/-- The three-stage reciprocal cleanup budget with the actual bounded
label separation cost expanded into C4 and shared-endpoint wedge terms. -/
theorem clear_used_parent_then_reciprocal_loss_card_le_actual_budget
    (D : FiniteCompletionCliqueData α) (Dcap κ : ℕ)
    (h_ground : ∀ E ∈ D.K, E ⊆ D.ground)
    (h_pair : ∀ P ∈ D.ground.powersetCard 2,
      qPairDegree (reciprocalUsedParentLabelTriples D) P ≤ κ)
    (h_facet : ∀ T : Edge α, T.card = 3 →
      (D.K.filter fun E => T ⊆ E).card ≤ Dcap) :
    (D.K \ (clearUsedParentThenReciprocal D).K).card ≤
      (∑ x ∈ D.ground,
        (fixedCenterPairNodeDeletion D.K
          (reciprocalUsedParentLabelTriples D) D.ground x).card) +
      Dcap * D.ground.card ^ 2 * κ ^ 2 +
      (reciprocalDifferentWitnessDeletionSetAll
        (clearUsedParentPairSeparation D)).card +
      (reciprocalWrongCommonWitnessDeletionSetAll
        (clearReciprocalDifferentWitnesses
          (clearUsedParentPairSeparation D))).card := by
  have hLoss := clear_used_parent_then_reciprocal_loss_card_le D
  have hSep := used_parent_separation_bad_card_le_actual_budget
    D Dcap κ h_ground h_pair h_facet
  omega

/-- Fully expanded finite loss ledger. The only nonnumeric term is the
existing fixed-center C4 deletion, already bounded by its graph theorem. -/
theorem clear_used_parent_then_reciprocal_loss_card_le_degree_caps
    (D : FiniteCompletionCliqueData α) (Dcap κ Kstar C_D : ℕ)
    (h_ground : ∀ E ∈ D.K, E ⊆ D.ground)
    (h_pair : ∀ P ∈ D.ground.powersetCard 2,
      qPairDegree (reciprocalUsedParentLabelTriples D) P ≤ κ)
    (h_facet : ∀ T : Edge α, T.card = 3 →
      (D.K.filter fun E => T ⊆ E).card ≤ Dcap)
    (h_label : ∀ a b : α,
      (reciprocalUsedLabelFiber D a b).card ≤ Kstar)
    (h_tail : ∀ a b r s : α,
      (reciprocalWitnessTailFiber D a b r s).card ≤ C_D) :
    (D.K \ (clearUsedParentThenReciprocal D).K).card ≤
      (∑ x ∈ D.ground,
        (fixedCenterPairNodeDeletion D.K
          (reciprocalUsedParentLabelTriples D) D.ground x).card) +
      Dcap * D.ground.card ^ 2 * κ ^ 2 +
      D.ground.card ^ 2 * Kstar ^ 2 * C_D +
      D.ground.card ^ 2 * Dcap := by
  let D₁ := clearUsedParentPairSeparation D
  let D₂ := clearReciprocalDifferentWitnesses D₁
  have hD₁sub : D₁.K ⊆ D.K :=
    clear_used_parent_pair_separation_sub D
  have hD₂sub : D₂.K ⊆ D.K :=
    (clear_reciprocal_different_witnesses_sub D₁).trans hD₁sub
  have hLabel₁ : ∀ a b : α,
      (reciprocalUsedLabelFiber D₁ a b).card ≤ Kstar := by
    intro a b
    exact (Finset.card_le_card
      (reciprocal_used_label_fiber_mono_of_family D₁ D rfl rfl
        hD₁sub a b)).trans (h_label a b)
  have hTail₁ : ∀ a b r s : α,
      (reciprocalWitnessTailFiber D₁ a b r s).card ≤ C_D := by
    intro a b r s
    exact (Finset.card_le_card
      (reciprocal_witness_tail_fiber_mono_data
        D₁ D rfl hD₁sub a b r s)).trans (h_tail a b r s)
  have hDistinct :=
    reciprocal_different_witness_deletion_set_all_card_le
      D₁ Kstar C_D hLabel₁ hTail₁
  have hFacet₂ : ∀ T : Edge α, T.card = 3 →
      (D₂.K.filter fun E => T ⊆ E).card ≤ Dcap := by
    intro T hT
    apply le_trans (Finset.card_le_card ?_) (h_facet T hT)
    intro E hE
    exact Finset.mem_filter.mpr
      ⟨hD₂sub (Finset.mem_filter.mp hE).1,
        (Finset.mem_filter.mp hE).2⟩
  have hWrong :=
    reciprocal_wrong_common_witness_deletion_card_le_triple_cap
      D₂ Dcap hFacet₂
  have hLoss := clear_used_parent_then_reciprocal_loss_card_le_actual_budget
    D Dcap κ h_ground h_pair h_facet
  change (reciprocalDifferentWitnessDeletionSetAll D₁).card ≤
    D.ground.card * D.ground.card * Kstar * Kstar * C_D at hDistinct
  change (reciprocalWrongCommonWitnessDeletionSetAll D₂).card ≤
    D.ground.card * D.ground.card * Dcap at hWrong
  nlinarith [hLoss]

end JSP523.Rank4
