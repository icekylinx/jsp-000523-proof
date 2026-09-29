import JSP523.Rank5.LowerMajorityCleanup
import JSP523.Rank5.LowerBicoloredReindex

/-! # Explicit actual rank-five lower cleanup cost -/

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α] [Nonempty α]

theorem lower_majority_cleanup_explicit_budget
    (H : Family α) (V : Edge α) (t u q D₃ D₄ : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform 5 H)
    (hAmbient : ∀ E ∈ H, E ⊆ V) (hu : 8 ≤ u) (ht : 1 ≤ t)
    (hD₃ : ∀ S : Edge α, S.card = 3 → (H.filter fun E => S ⊆ E).card ≤ D₃)
    (hD₄ : ∀ S : Edge α, S.card = 4 → (H.filter fun E => S ⊆ E).card ≤ D₄) :
    (q : ℝ) * ((multilevelDeletedEdges H V (V.powersetCard 3) 2 u q
      (fun B P Q => ¬ ActualStrongPartner H V P Q 2 3 t
        (lowerMajorityLabel H V t B))).card : ℝ) ≤
      (q : ℝ) * V.card.choose 3 * u + 10 * (H.card : ℝ) + 3200 *
        (((V.powersetCard 2).card : ℝ) ^ 2 * (t + 9 * (D₄ : ℝ)) +
          20 * (D₄ : ℝ) * H.card +
          ((V.powersetCard 2).card : ℝ) ^ 2 * D₃ * D₃ * D₄ /
            ((t : ℝ) * u)) := by
  have hBase := lower_majority_multilevel_cleanup_budget H V t u q hUniform hAmbient hu
  have hBnat := lower_uncolored_support_sum_budget H V t D₄ hAdm hUniform hAmbient hD₄
  have hTnat := lower_bicolored_support_sum_budget H V t D₃ D₄ ht hD₃ hD₄
  have hB : (∑ B ∈ V.powersetCard 3,
      ((uncoloredEdgeSupports (actualCoreLink H V B 2) (lowerCoreSupportColor H V B t)).card : ℝ)) ≤
      ((V.powersetCard 2).card : ℝ) ^ 2 * (t + 9 * (D₄ : ℝ)) + 20 * (D₄ : ℝ) * H.card := by
    exact_mod_cast hBnat
  have hT : (t : ℝ) * (∑ B ∈ V.powersetCard 3,
      ((bicoloredTriangleSupports (actualCoreLink H V B 2) (lowerCoreSupportColor H V B t)).card : ℝ)) ≤
      ((V.powersetCard 2).card : ℝ) ^ 2 * D₃ * D₃ * D₄ := by exact_mod_cast hTnat
  have htPos : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have huPos : (0 : ℝ) < u := by exact_mod_cast (by omega : 0 < u)
  have hTD : (∑ B ∈ V.powersetCard 3,
      ((bicoloredTriangleSupports (actualCoreLink H V B 2) (lowerCoreSupportColor H V B t)).card : ℝ)) ≤
      ((V.powersetCard 2).card : ℝ) ^ 2 * D₃ * D₃ * D₄ / t :=
    (le_div_iff₀ htPos).2 (by nlinarith [hT])
  have hTDiv := div_le_div_of_nonneg_right hTD huPos.le
  rw [div_div] at hTDiv
  linarith

end JSP523.Rank5
