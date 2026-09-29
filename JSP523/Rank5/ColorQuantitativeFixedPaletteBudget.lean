import JSP523.Rank5.ColorQuantitativeFixedPaletteUncoloredReindex
import JSP523.Rank5.ColorQuantitativeFixedPaletteTriangleReindex

/-! # Explicit actual cleanup costs for every fixed palette -/

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α] [Nonempty α]

theorem fixed_palette_majority_cleanup_explicit_budget
    (H : Family α) (V : Edge α) (r s k t u q D₃ D₄ Dk Dnext : ℕ)
    (hs : 1 ≤ s) (hk : 2 ≤ k) (hAdm : Admissible H) (hUniform : Uniform r H)
    (hAmbient : ∀ E ∈ H, E ⊆ V) (hu : 2 * fixedPaletteSampleSize k ≤ u) (ht : 1 ≤ t)
    (hD₃ : ∀ S : Edge α, S.card = s + 1 → (H.filter fun E => S ⊆ E).card ≤ D₃)
    (hD₄ : ∀ S : Edge α, S.card = s + 2 → (H.filter fun E => S ⊆ E).card ≤ D₄)
    (hDk : ∀ S : Edge α, S.card = k → (H.filter fun E => S ⊆ E).card ≤ Dk)
    (hDnext : ∀ S : Edge α, S.card = k + 1 → (H.filter fun E => S ⊆ E).card ≤ Dnext) :
    (q : ℝ) * ((multilevelDeletedEdges H V (V.powersetCard k) s u q
      (fun B P Q => ¬ ActualStrongPartner H V P Q s k t
        (fixedPaletteMajorityLabel H V s k t B))).card : ℝ) ≤
      (q : ℝ) * V.card.choose k * u + (r.choose k : ℝ) * (H.card : ℝ) + (4 * (fixedPaletteMajorityConstant (fixedPaletteSampleSize k) : ℝ)) *
        (((V.powersetCard s).card : ℝ) ^ 2 * (t + (k : ℝ) * k * D₄) +
          (s : ℝ) * r.choose k * Dnext * H.card +
          ((V.powersetCard s).card : ℝ) ^ 2 * D₃ * Dk * D₄ /
            ((t : ℝ) * u)) := by
  have hBase := fixed_palette_majority_multilevel_cleanup_budget H V r s k t u q hk hUniform hAmbient hu
  have hBnat := fixed_palette_uncolored_support_sum_budget H V r s k t D₄ Dnext hs hk hAdm hUniform hAmbient hD₄ hDnext
  have hTnat := fixed_palette_bicolored_support_sum_budget H V s k t D₃ D₄ Dk ht hD₃ hDk hD₄
  have hB : (∑ B ∈ V.powersetCard k,
      ((uncoloredEdgeSupports (actualCoreLink H V B s) (fixedPaletteCoreSupportColor H V B s k t)).card : ℝ)) ≤
      ((V.powersetCard s).card : ℝ) ^ 2 * (t + (k : ℝ) * k * D₄) + (s : ℝ) * r.choose k * Dnext * H.card := by
    exact_mod_cast hBnat
  have hT : (t : ℝ) * (∑ B ∈ V.powersetCard k,
      ((bicoloredTriangleSupports (actualCoreLink H V B s) (fixedPaletteCoreSupportColor H V B s k t)).card : ℝ)) ≤
      ((V.powersetCard s).card : ℝ) ^ 2 * D₃ * Dk * D₄ := by exact_mod_cast hTnat
  have htPos : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hSample : 4 ≤ fixedPaletteSampleSize k := le_max_left _ _
  have huPos : (0 : ℝ) < u := by exact_mod_cast (by omega : 0 < u)
  have hTD : (∑ B ∈ V.powersetCard k,
      ((bicoloredTriangleSupports (actualCoreLink H V B s) (fixedPaletteCoreSupportColor H V B s k t)).card : ℝ)) ≤
      ((V.powersetCard s).card : ℝ) ^ 2 * D₃ * Dk * D₄ / t :=
    (le_div_iff₀ htPos).2 (by nlinarith [hT])
  have hTDiv := div_le_div_of_nonneg_right hTD huPos.le
  rw [div_div] at hTDiv
  nlinarith [Nat.cast_nonneg (α := ℝ) (fixedPaletteMajorityConstant (fixedPaletteSampleSize k))]

/-- The numerical cost of the actual majority cleanup at root size `s`
and core size `k`. All four degree bounds refer to the fixed parent. -/
noncomputable def fixedPaletteCleanupCost
    (n m r s k t u q D₃ D₄ Dk Dnext : ℕ) : ℝ :=
  (n.choose k : ℝ) * u +
    ((r.choose k : ℝ) * m +
      4 * (fixedPaletteMajorityConstant (fixedPaletteSampleSize k) : ℝ) *
        ((n.choose s : ℝ) ^ 2 * (t + (k : ℝ) * k * D₄) +
          (s : ℝ) * r.choose k * Dnext * m +
          (n.choose s : ℝ) ^ 2 * D₃ * Dk * D₄ / ((t : ℝ) * u))) / q

/-- Division by the positive exception threshold gives the actual edge
loss used in both high-rank cleanup levels. -/
theorem fixed_palette_cleanup_card_le_explicit_cost
    (H : Family α) (V : Edge α) (r s k t u q D₃ D₄ Dk Dnext : ℕ)
    (hs : 1 ≤ s) (hk : 2 ≤ k) (hAdm : Admissible H) (hUniform : Uniform r H)
    (hAmbient : ∀ E ∈ H, E ⊆ V)
    (hu : 2 * fixedPaletteSampleSize k ≤ u) (ht : 1 ≤ t) (hq : 0 < q)
    (hD₃ : ∀ S : Edge α, S.card = s + 1 → (H.filter fun E => S ⊆ E).card ≤ D₃)
    (hD₄ : ∀ S : Edge α, S.card = s + 2 → (H.filter fun E => S ⊆ E).card ≤ D₄)
    (hDk : ∀ S : Edge α, S.card = k → (H.filter fun E => S ⊆ E).card ≤ Dk)
    (hDnext : ∀ S : Edge α, S.card = k + 1 → (H.filter fun E => S ⊆ E).card ≤ Dnext) :
    ((multilevelDeletedEdges H V (V.powersetCard k) s u q
      (fun B P Q => ¬ ActualStrongPartner H V P Q s k t
        (fixedPaletteMajorityLabel H V s k t B))).card : ℝ) ≤
      fixedPaletteCleanupCost V.card H.card r s k t u q D₃ D₄ Dk Dnext := by
  have h := fixed_palette_majority_cleanup_explicit_budget H V r s k t u q D₃ D₄ Dk Dnext
    hs hk hAdm hUniform hAmbient hu ht hD₃ hD₄ hDk hDnext
  rw [Finset.card_powersetCard] at h
  have hqReal : (0 : ℝ) < q := by exact_mod_cast hq
  apply (mul_le_mul_iff_left₀ hqReal).mp
  dsimp [fixedPaletteCleanupCost]
  rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hqReal)]
  nlinarith only [h]

end JSP523.Rank5
