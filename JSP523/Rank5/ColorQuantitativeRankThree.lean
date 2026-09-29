import JSP523.Rank5.ColorQuantitativeSamples
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Bounds

/-! # Three-color quantitative rigidity for the rank-five lower cleanup

A fixed numerical constant suffices for IV.7. The estimate includes
uncolored edges and has the required inverse-degree triangle term.
-/

namespace JSP523.Rank5

private theorem five_sample_exception_bound
    (m M b β : ℕ) (hm : 8 ≤ m)
    (h : M * m.choose 2 * (m - 4) ≤
      100 * (b * (m - 2).choose 3 + β * (m - 3).choose 2)) :
    (M : ℝ) * m ≤ 800 * ((b : ℝ) * m + β) := by
  have hm8 : (8 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hChooseThree : (m - 2).choose 3 ≤ m ^ 3 :=
    (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le m 2) 3)
  have hChooseTwo : (m - 3).choose 2 ≤ m ^ 2 :=
    (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le m 3) 2)
  have hNat : M * m.choose 2 * (m - 4) ≤ 100 * (b * m ^ 3 + β * m ^ 2) :=
    h.trans (Nat.mul_le_mul_left _ (Nat.add_le_add
      (Nat.mul_le_mul_left b hChooseThree) (Nat.mul_le_mul_left β hChooseTwo)))
  have hReal : (M : ℝ) * (m.choose 2 : ℝ) * ((m : ℝ) - 4) ≤
      100 * ((b : ℝ) * (m : ℝ) ^ 3 + (β : ℝ) * (m : ℝ) ^ 2) := by
    have hCast : (M : ℝ) * (m.choose 2 : ℝ) * ((m - 4 : ℕ) : ℝ) ≤
        100 * ((b : ℝ) * (m : ℝ) ^ 3 + (β : ℝ) * (m : ℝ) ^ 2) := by exact_mod_cast hNat
    simpa only [Nat.cast_sub (by omega : 4 ≤ m), Nat.cast_ofNat] using hCast
  have hLower : (m : ℝ) ^ 3 ≤ 8 * (m.choose 2 : ℝ) * ((m : ℝ) - 4) := by
    rw [Nat.cast_choose_two]
    nlinarith [mul_nonneg (sub_nonneg.mpr hm8) (sq_nonneg (m : ℝ))]
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hmpos)).mp
  calc
    (M : ℝ) * m * (m : ℝ) ^ 2 = (M : ℝ) * (m : ℝ) ^ 3 := by ring
    _ ≤ (M : ℝ) * (8 * (m.choose 2 : ℝ) * ((m : ℝ) - 4)) :=
      mul_le_mul_of_nonneg_left hLower (Nat.cast_nonneg M)
    _ ≤ 800 * ((b : ℝ) * (m : ℝ) ^ 3 + (β : ℝ) * (m : ℝ) ^ 2) := by nlinarith [hReal]
    _ = 800 * ((b : ℝ) * m + β) * (m : ℝ) ^ 2 := by ring

/-- IV.6.2 at the actual three-color palette needed by rank five, with a
    harmless enlarged absolute constant. -/
theorem exists_three_color_majority_exception_bound
    {α κ : Type*} [DecidableEq α] [DecidableEq κ] [Fintype κ] [Nonempty κ]
    (V : Finset α) (edgeColor : Finset α → Option κ)
    (hκ : Fintype.card κ = 3) (hV : 8 ≤ V.card) :
    ∃ c : κ,
      (((V.powersetCard 2).filter fun e => edgeColor e ≠ some c).card : ℝ) ≤
        800 * ((uncoloredEdgeSupports V edgeColor).card +
          (bicoloredTriangleSupports V edgeColor).card / (V.card : ℝ)) := by
  classical
  obtain ⟨c, hc⟩ := exists_majority_color_scaled_exception_bound
    V 5 edgeColor (by omega) (by norm_num [hκ]) (by omega)
  refine ⟨c, ?_⟩
  have hScaled : ((V.powersetCard 2).filter fun e => edgeColor e ≠ some c).card *
      V.card.choose 2 * (V.card - 4) ≤
      100 * ((uncoloredEdgeSupports V edgeColor).card * (V.card - 2).choose 3 +
        (bicoloredTriangleSupports V edgeColor).card * (V.card - 3).choose 2) := by
    norm_num at hc ⊢
    exact hc
  have hBound := five_sample_exception_bound _ _ _ _ hV hScaled
  have hPos : (0 : ℝ) < V.card := by exact_mod_cast (by omega : 0 < V.card)
  apply (mul_le_mul_iff_left₀ hPos).mp
  convert hBound using 1
  field_simp

end JSP523.Rank5
