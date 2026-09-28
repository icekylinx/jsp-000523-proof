import JSP523.Rank4.PreprocessUsedParentCleanup
import JSP523.Rank4.GraphReciprocalDegreeTwo

/-!
# Actual rank-four reciprocal preprocessing assembly

First remove pair-label separation violations in the used parent system.
Then remove the distinct-witness and wrong-common-witness reciprocal
targets. All three removals preserve ground and labels. The final family
obeys the actual finite `R ≤ b` bound without a separation premise.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

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

end JSP523.Rank4
