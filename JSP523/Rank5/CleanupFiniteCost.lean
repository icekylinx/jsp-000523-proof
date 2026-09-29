import JSP523.Rank5.LowerCleanupBudget
import JSP523.Rank5.UpperFacetSharp

/-! # Explicit numerical costs for the actual rank-five cleanups -/

namespace JSP523.Rank5

noncomputable def rankFiveLowerCleanupCost (n m t u q D₃ D₄ : ℕ) : ℝ :=
  (n.choose 3 : ℝ) * u +
    (10 * (m : ℝ) + 3200 *
      ((n.choose 2 : ℝ) ^ 2 * ((t : ℝ) + 9 * D₄) + 20 * (D₄ : ℝ) * m +
        (n.choose 2 : ℝ) ^ 2 * D₃ * D₃ * D₄ / ((t : ℝ) * u))) / q

noncomputable def rankFiveUpperCleanupCost (n t D₂ D₃ D₄ : ℕ) : ℝ :=
  2 * (n : ℝ) ^ 2 * ((t : ℝ) + 16 * D₃) + 3 * (n : ℝ) ^ 3 * D₄ +
    9 * ((n : ℝ) ^ 2 * D₂ * D₃ * D₄) / t

variable {α : Type*} [DecidableEq α] [Nonempty α]

theorem lower_cleanup_card_le_explicit_cost
    (H : Family α) (V : Edge α) (t u q D₃ D₄ : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform 5 H)
    (hAmbient : ∀ E ∈ H, E ⊆ V) (hu : 8 ≤ u) (ht : 1 ≤ t) (hq : 0 < q)
    (hD₃ : ∀ S : Edge α, S.card = 3 → (H.filter fun E => S ⊆ E).card ≤ D₃)
    (hD₄ : ∀ S : Edge α, S.card = 4 → (H.filter fun E => S ⊆ E).card ≤ D₄) :
    ((multilevelDeletedEdges H V (V.powersetCard 3) 2 u q
      (fun B P Q => ¬ ActualStrongPartner H V P Q 2 3 t
        (lowerMajorityLabel H V t B))).card : ℝ) ≤
      rankFiveLowerCleanupCost V.card H.card t u q D₃ D₄ := by
  have h := lower_majority_cleanup_explicit_budget H V t u q D₃ D₄
    hAdm hUniform hAmbient hu ht hD₃ hD₄
  rw [Finset.card_powersetCard] at h
  have hqReal : (0 : ℝ) < q := by exact_mod_cast hq
  apply (mul_le_mul_iff_left₀ hqReal).mp
  dsimp [rankFiveLowerCleanupCost]
  have heq : ((V.card.choose 3 : ℝ) * u +
      (10 * (H.card : ℝ) + 3200 *
        ((V.card.choose 2 : ℝ) ^ 2 * ((t : ℝ) + 9 * D₄) + 20 * (D₄ : ℝ) * H.card +
        (V.card.choose 2 : ℝ) ^ 2 * D₃ * D₃ * D₄ / ((t : ℝ) * u))) / q) * q =
      (q : ℝ) * V.card.choose 3 * u + 10 * (H.card : ℝ) + 3200 *
        ((V.card.choose 2 : ℝ) ^ 2 * ((t : ℝ) + 9 * D₄) + 20 * (D₄ : ℝ) * H.card +
        (V.card.choose 2 : ℝ) ^ 2 * D₃ * D₃ * D₄ / ((t : ℝ) * u)) := by
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hqReal)]
    ring
  rw [heq]
  simpa only [mul_comm] using h

omit [Nonempty α] in
theorem upper_cleanup_card_le_explicit_cost
    (H : Family α) (V : Edge α) (t D₂ D₃ D₄ : ℕ)
    (hAdm : Admissible H) (ht : 1 ≤ t)
    (hD₂ : ∀ S : Edge α, S.card = 2 → (H.filter fun E => S ⊆ E).card ≤ D₂)
    (hD₃ : ∀ S : Edge α, S.card = 3 → (H.filter fun E => S ⊆ E).card ≤ D₃)
    (hD₄ : ∀ S : Edge α, S.card = 4 → (H.filter fun E => S ⊆ E).card ≤ D₄) :
    ((upperFacetColorCleanupEdges H V t).card : ℝ) ≤
      rankFiveUpperCleanupCost V.card t D₂ D₃ D₄ := by
  have hNat := upper_facet_color_cleanup_edges_sharp_budget H V t D₃ D₂ D₃ D₄
    hAdm ht hD₃ hD₂ hD₃ hD₄
  have h : (t : ℝ) * (upperFacetColorCleanupEdges H V t).card ≤
      (t : ℝ) * (2 * (V.card : ℝ) ^ 2 * ((t : ℝ) + 16 * D₃) +
        3 * (V.card : ℝ) ^ 3 * D₄) + 9 * ((V.card : ℝ) ^ 2 * D₂ * D₃ * D₄) := by
    exact_mod_cast hNat
  have htReal : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  apply (mul_le_mul_iff_left₀ htReal).mp
  dsimp [rankFiveUpperCleanupCost]
  rw [add_mul, div_mul_cancel₀ _ (ne_of_gt htReal)]
  nlinarith [h]

end JSP523.Rank5
