import JSP523.Rank4.GlobalActualSingleCenterMaster
import JSP523.Rank4.PreprocessActualDegreeTailChoice

/-! # Actual master data and the independently chosen degree tail

The master survivor is always the actual reciprocal survivor of `completion`.
The auxiliary degree-tail family is chosen in the original induced parent.
-/
namespace JSP523.Rank4

structure ActualMasterStabilityData {n : ℕ} (H : Family (Fin (n + 1))) where
  ground : Edge (Fin (n + 1))
  centers : Edge (Fin (n + 1))
  links : Fin (n + 1) → Family (Fin (n + 1))
  owner : Edge (Fin (n + 1)) → Fin (n + 1)
  regularized : Family (Fin (n + 1))
  completion : FiniteCompletionCliqueData (Fin (n + 1))
  normalization : ℕ
  masterError : ℕ
  highError : ℕ
  outerLoss : ℕ
  completion_ground : completion.ground = ground
  regularized_sub : regularized ⊆ fixedDecompositionCore H ground
  completion_sub : completion.K ⊆ regularized
  centers_outside : ∀ c ∈ centers, c ∉ ground
  links_ground : ∀ c ∈ centers, ∀ T ∈ links c, T ∈ ground.powersetCard 3
  links_edges : ∀ c ∈ centers, ∀ T ∈ links c, insert c T ∈ H
  original_mass : H.card ≤ (centers.biUnion (pairOwnerCleanedLink links owner)).card +
    (fixedDecompositionCore H ground).card + outerLoss
  master : 10 * H.card +
    (rankFourNonprivateFacets (clearUsedParentThenReciprocal completion).K ground).card +
    6 * (rankFourAllPrivateEdges (clearUsedParentThenReciprocal completion).K ground).card ≤
      10 * normalization + masterError
  near_master : normalization ≤ H.card + highError

namespace ActualMasterStabilityData

variable {n : ℕ} {H : Family (Fin (n + 1))}

def parent (d : ActualMasterStabilityData H) : Family (Fin (n + 1)) :=
  fixedDecompositionCore H d.ground

noncomputable def final_core (d : ActualMasterStabilityData H) : Family (Fin (n + 1)) :=
  (clearUsedParentThenReciprocal d.completion).K

/-- Three actual deletions, measured against their own fixed parents. -/
noncomputable def cleanup_loss (d : ActualMasterStabilityData H) : ℕ :=
  (d.parent \ d.regularized).card + (d.regularized \ d.completion.K).card +
    (d.completion.K \ d.final_core).card

theorem final_core_sub_completion (d : ActualMasterStabilityData H) :
    d.final_core ⊆ d.completion.K :=
  (clear_reciprocal_wrong_common_witnesses_sub
    (clearReciprocalDifferentWitnesses (clearUsedParentPairSeparation d.completion))).trans
    ((clear_reciprocal_different_witnesses_sub
      (clearUsedParentPairSeparation d.completion)).trans
      (clear_used_parent_pair_separation_sub d.completion))

theorem final_core_sub_parent (d : ActualMasterStabilityData H) :
    d.final_core ⊆ d.parent :=
  d.final_core_sub_completion.trans (d.completion_sub.trans d.regularized_sub)

/-- The loss entering parent stability is exactly the sum of the three
actual stages; no independently chosen cleaned family occurs here. -/
theorem cleanup_loss_eq_parent_sdiff (d : ActualMasterStabilityData H) :
    d.cleanup_loss = (d.parent \ d.final_core).card := by
  have h₁ := Finset.card_sdiff_add_card_eq_card d.regularized_sub
  have h₂ := Finset.card_sdiff_add_card_eq_card d.completion_sub
  have h₃ := Finset.card_sdiff_add_card_eq_card d.final_core_sub_completion
  have hAll := Finset.card_sdiff_add_card_eq_card d.final_core_sub_parent
  unfold cleanup_loss parent at *
  omega

end ActualMasterStabilityData

/-- Ordinary initial caps on the original induced parent, before either
the main cleanup or the auxiliary degree-tail cleanup. -/
def actual_master_stability_initial_caps {n : ℕ} {H : Family (Fin (n + 1))}
    (d : ActualMasterStabilityData H) (q : ℕ) : Prop :=
  (∀ v, (d.parent.filter fun E => v ∈ E).card ≤ q ^ 8 * (n + 1) ^ 2) ∧
  (∀ P : Edge (Fin (n + 1)), P.card = 2 → rankFourPairDegree d.parent P ≤ q ^ 8 * (n + 1)) ∧
  (∀ T : Edge (Fin (n + 1)), T.card = 3 →
    (facetCompletions d.parent Finset.univ T).card ≤ q ^ 8)

/-- Choose the auxiliary degree-tail cleanup after τ, and apply the actual
master to its own survivor. This supplies the complete finite stability
bound without a small-parent or preassigned-center assumption. -/
theorem actual_master_stability_with_chosen_tail
    {n : ℕ} (H : Family (Fin (n + 1))) (d : ActualMasterStabilityData H)
    (q : ℕ) (τ : ℝ) (hτ : 0 < τ)
    (hn : 2 ≤ n) (hScale : q ^ 11 ≤ n + 1)
    (hAdm : Admissible H) (hUniform : Uniform 4 H) (hLower : n.choose 3 ≤ H.card)
    (hVertex : ∀ v, (d.parent.filter fun E => v ∈ E).card ≤ q ^ 8 * (n + 1) ^ 2)
    (hPair : ∀ P : Edge (Fin (n + 1)), P.card = 2 → rankFourPairDegree d.parent P ≤ q ^ 8 * (n + 1))
    (hFacet : ∀ T : Edge (Fin (n + 1)), T.card = 3 →
      (facetCompletions d.parent Finset.univ T).card ≤ q ^ 8) :
    ((outsideEdges H (Finset.univ.erase (actualGlobalMainCenter H))).card : ℝ) ≤
      3 * (actualDegreeTailThreshold τ : ℝ) * (d.masterError + 10 * (d.highError : ℝ)) +
      3 * τ * ((n : ℝ) + 1) ^ 3 + 3 * (d.cleanup_loss : ℝ) +
      3 * (d.outerLoss : ℝ) + 5 * ((n : ℝ) + 1) ^ 2 := by
  classical
  have hBH : d.parent ⊆ H := Finset.filter_subset _ _
  obtain ⟨hM, B₁, hB₁, hTail, hCap⟩ := exists_actual_degree_tail_cleanup d.parent q τ hτ hScale
    (admissible_mono hBH hAdm) (fun _ hE => hUniform (hBH hE)) hVertex hPair hFacet
  have hCapGround : ∀ T ∈ d.ground.powersetCard 3,
      2 * (facetCompletions B₁ d.ground T).card ≤ actualDegreeTailThreshold τ := by
    intro T hT
    have hSub : facetCompletions B₁ d.ground T ⊆ facetCompletions B₁ Finset.univ T := by
      intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, (Finset.mem_filter.mp hv).2⟩
    exact (Nat.mul_le_mul_left 2 (Finset.card_le_card hSub)).trans
      (hCap T (Finset.mem_powersetCard.mp hT).2)
  have hFinite := actual_global_center_outside_of_master H d.ground d.centers d.links d.owner
    d.final_core B₁ (actualDegreeTailThreshold τ) d.normalization d.masterError d.highError d.outerLoss
    hn hUniform d.centers_outside d.links_ground d.links_edges hLower d.original_mass
    d.final_core_sub_parent hB₁ hM hCapGround d.master d.near_master
  have hLossEq := d.cleanup_loss_eq_parent_sdiff
  unfold ActualMasterStabilityData.parent at hLossEq
  rw [← hLossEq] at hFinite
  have hReal : ((outsideEdges H (Finset.univ.erase (actualGlobalMainCenter H))).card : ℝ) ≤
      3 * (actualDegreeTailThreshold τ : ℝ) * (d.masterError + 10 * (d.highError : ℝ)) +
      24 * ((d.parent \ B₁).card : ℝ) + 3 * (d.cleanup_loss : ℝ) +
      3 * (d.outerLoss : ℝ) + 5 * ((n : ℝ) + 1) ^ 2 := by exact_mod_cast hFinite
  push_cast at hTail
  nlinarith only [hReal, hTail]

end JSP523.Rank4
