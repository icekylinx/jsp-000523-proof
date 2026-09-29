import JSP523.Rank5.ColorQuantitativeSamples
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Bounds

/-! # Quantitative majority coloring for every fixed palette

The constant depends only on the palette, while the triangle error is
inversely proportional to the actual number of vertices.
-/

namespace JSP523.Rank5

def fixedPaletteMajorityConstant (h : ℕ) : ℕ :=
  4 * 2 ^ (h - 4) * (h - 4).factorial * (h.choose 2) ^ 2

private theorem sample_extension_polynomial_lower
    (m h : ℕ) (hh : 4 ≤ h) (hm : 2 * h ≤ m) :
    (m : ℝ) ^ (h - 2) ≤
      (4 * 2 ^ (h - 4) * (h - 4).factorial : ℕ) *
        (m.choose 2 : ℝ) * ((m - 4).choose (h - 4) : ℝ) := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (by omega : 2 ≤ m)
  have hPair : (m : ℝ) ^ 2 ≤ 4 * (m.choose 2 : ℝ) := by
    rw [Nat.cast_choose_two]
    nlinarith
  have hBaseNat : m ≤ 2 * (m - 4 + 1 - (h - 4)) := by omega
  have hBase : (m : ℝ) ≤ 2 * ((m - 4 + 1 - (h - 4) : ℕ) : ℝ) := by
    exact_mod_cast hBaseNat
  have hFact : (0 : ℝ) < (h - 4).factorial := by
    exact_mod_cast Nat.factorial_pos (h - 4)
  have hChoose := Nat.pow_le_choose (α := ℝ) (h - 4) (m - 4)
  have hC := (div_le_iff₀ hFact).1 hChoose
  have hExt : (m : ℝ) ^ (h - 4) ≤
      (2 : ℝ) ^ (h - 4) * (h - 4).factorial * ((m - 4).choose (h - 4) : ℝ) := by
    calc
      _ ≤ (2 * ((m - 4 + 1 - (h - 4) : ℕ) : ℝ)) ^ (h - 4) := by gcongr
      _ = (2 : ℝ) ^ (h - 4) * (((m - 4 + 1 - (h - 4) : ℕ) : ℝ) ^ (h - 4)) := mul_pow _ _ _
      _ ≤ (2 : ℝ) ^ (h - 4) *
          (((m - 4).choose (h - 4) : ℝ) * (h - 4).factorial) := by gcongr
      _ = _ := by ring
  have hExp : h - 2 = 2 + (h - 4) := by omega
  rw [hExp, pow_add]
  calc
    _ ≤ (4 * (m.choose 2 : ℝ)) *
        ((2 : ℝ) ^ (h - 4) * (h - 4).factorial * ((m - 4).choose (h - 4) : ℝ)) := by
      gcongr
    _ = _ := by push_cast; ring

/-- Converting the exact sample count to the fixed-palette estimate. -/
theorem fixed_sample_exception_bound
    (m M b β h : ℕ) (hh : 4 ≤ h) (hm : 2 * h ≤ m)
    (hCount : M * m.choose 2 * (m - 4).choose (h - 4) ≤
      (h.choose 2) ^ 2 *
        (b * (m - 2).choose (h - 2) + β * (m - 3).choose (h - 3))) :
    (M : ℝ) * m ≤ (fixedPaletteMajorityConstant h : ℝ) * ((b : ℝ) * m + β) := by
  have hmPos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hUpper₂ : (m - 2).choose (h - 2) ≤ m ^ (h - 2) :=
    (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le m 2) _)
  have hUpper₃ : (m - 3).choose (h - 3) ≤ m ^ (h - 3) :=
    (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le m 3) _)
  have hNat := hCount.trans (Nat.mul_le_mul_left _ (Nat.add_le_add
    (Nat.mul_le_mul_left b hUpper₂) (Nat.mul_le_mul_left β hUpper₃)))
  have hReal : (M : ℝ) * (m.choose 2 : ℝ) * ((m - 4).choose (h - 4) : ℝ) ≤
      (h.choose 2 : ℝ) ^ 2 * ((b : ℝ) * (m : ℝ) ^ (h - 2) + (β : ℝ) * (m : ℝ) ^ (h - 3)) := by
    exact_mod_cast hNat
  have hLower := sample_extension_polynomial_lower m h hh hm
  have hMain : (M : ℝ) * (m : ℝ) ^ (h - 2) ≤
      (fixedPaletteMajorityConstant h : ℝ) *
        ((b : ℝ) * (m : ℝ) ^ (h - 2) + (β : ℝ) * (m : ℝ) ^ (h - 3)) := by
    calc
      _ ≤ (M : ℝ) * ((4 * 2 ^ (h - 4) * (h - 4).factorial : ℕ) *
          (m.choose 2 : ℝ) * ((m - 4).choose (h - 4) : ℝ)) :=
        mul_le_mul_of_nonneg_left hLower (Nat.cast_nonneg M)
      _ = ((4 * 2 ^ (h - 4) * (h - 4).factorial : ℕ) : ℝ) *
          ((M : ℝ) * (m.choose 2 : ℝ) * ((m - 4).choose (h - 4) : ℝ)) := by ring
      _ ≤ ((4 * 2 ^ (h - 4) * (h - 4).factorial : ℕ) : ℝ) *
          ((h.choose 2 : ℝ) ^ 2 *
            ((b : ℝ) * (m : ℝ) ^ (h - 2) + (β : ℝ) * (m : ℝ) ^ (h - 3))) := by gcongr
      _ = _ := by simp only [fixedPaletteMajorityConstant, Nat.cast_mul, Nat.cast_pow]; ring
  have hExp : h - 2 = (h - 3) + 1 := by omega
  rw [hExp, pow_succ] at hMain
  apply (mul_le_mul_iff_left₀ (pow_pos hmPos (h - 3))).mp
  convert hMain using 1 <;> ring

/-- A fixed number of colors admits one color with at most
`C(h) * (uncolored + bicolored / degree)` exceptional edges. -/
theorem exists_fixed_palette_majority_exception_bound
    {α κ : Type*} [DecidableEq α] [DecidableEq κ] [Fintype κ] [Nonempty κ]
    (V : Finset α) (edgeColor : Finset α → Option κ) (h : ℕ)
    (hq : 2 ≤ Fintype.card κ)
    (hSize : max 4 ((Fintype.card κ - 1) ^ 2 + 1) ≤ h)
    (hV : 2 * h ≤ V.card) :
    ∃ c : κ,
      (((V.powersetCard 2).filter fun e => edgeColor e ≠ some c).card : ℝ) ≤
        (fixedPaletteMajorityConstant h : ℝ) *
          ((uncoloredEdgeSupports V edgeColor).card +
            (bicoloredTriangleSupports V edgeColor).card / (V.card : ℝ)) := by
  classical
  have hh : 4 ≤ h := (le_max_left _ _).trans hSize
  obtain ⟨c, hc⟩ := exists_majority_color_scaled_exception_bound V h edgeColor
    hq hSize (by omega)
  refine ⟨c, ?_⟩
  have hBound := fixed_sample_exception_bound _ _ _ _ h hh hV hc
  have hPos : (0 : ℝ) < V.card := by exact_mod_cast (by omega : 0 < V.card)
  apply (mul_le_mul_iff_left₀ hPos).mp
  convert hBound using 1
  field_simp

end JSP523.Rank5
