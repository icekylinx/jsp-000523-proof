import JSP523.Rank5.HigherRankUpperSharp
import JSP523.Rank5.HigherRankParameterError

/-! # Actual singleton-cleanup error at the higher-rank integer scale -/
namespace JSP523.Rank5

theorem higher_singleton_cleanup_scale_envelope
    (N U t : ℝ) (k : ℕ) (hU : 1 ≤ U) (hN : U ^ 32 ≤ N)
    (htLo : N ^ (k + 3) / (2 * U ^ 9) ≤ t)
    (htHi : t ≤ N ^ (k + 3) / U ^ 9) :
    2 * N ^ 2 * (t + 4 * ((k : ℝ) + 5) ^ 2 * U ^ 2 * N ^ (k + 2)) +
      12 * U ^ 2 * N ^ (k + 4) + 576 * U ^ 6 * N ^ (2 * k + 7) / t ≤
      (1166 + 8 * ((k : ℝ) + 5) ^ 2) * (N ^ (k + 5) / U) := by
  have hUp : 0 < U := by linarith
  have hNp : 0 < N := lt_of_lt_of_le (by positivity) hN
  have htPos : 0 < t := lt_of_lt_of_le (by positivity) htLo
  have hU9 : U ≤ U ^ 9 := by
    simpa only [pow_one] using pow_le_pow_right₀ hU (by omega : 1 ≤ 9)
  have htSimple : t ≤ N ^ (k + 3) / U := htHi.trans
    (div_le_div_of_nonneg_left (by positivity) hUp hU9)
  have hSmall : 2 * N ^ 2 * t ≤ 2 * (N ^ (k + 5) / U) := by
    calc
      _ ≤ 2 * N ^ 2 * (N ^ (k + 3) / U) := by gcongr
      _ = _ := by simp only [pow_add]; ring
  have hPin : 576 * U ^ 6 * N ^ (2 * k + 7) / t ≤
      1152 * (U ^ 15 * N ^ (k + 4)) := by
    calc
      _ ≤ 576 * U ^ 6 * N ^ (2 * k + 7) /
          (N ^ (k + 3) / (2 * U ^ 9)) := by gcongr
      _ = _ := by
        field_simp
        simp only [show 2 * k + 7 = k + k + 7 by omega, pow_add]
        ring
  have hMono₂ := higher_scale_monomial_bound N U hU hN 2 (k + 4) (by omega)
  have hMono₁₅ := higher_scale_monomial_bound N U hU hN 15 (k + 4) (by omega)
  simp only [show k + 4 + 1 = k + 5 by omega] at hMono₂ hMono₁₅
  have hPinFinal : 576 * U ^ 6 * N ^ (2 * k + 7) / t ≤
      1152 * (N ^ (k + 5) / U) := by linarith
  have hMiddle := mul_le_mul_of_nonneg_left hMono₂
    (by positivity : 0 ≤ 8 * ((k : ℝ) + 5) ^ 2 + 12)
  have hExpand : 2 * N ^ 2 *
      (t + 4 * ((k : ℝ) + 5) ^ 2 * U ^ 2 * N ^ (k + 2)) +
      12 * U ^ 2 * N ^ (k + 4) =
      2 * N ^ 2 * t + (8 * ((k : ℝ) + 5) ^ 2 + 12) * (U ^ 2 * N ^ (k + 4)) := by
    simp only [pow_add]
    ring
  rw [hExpand]
  nlinarith only [hSmall, hMiddle, hPinFinal]

variable {α : Type*} [DecidableEq α]

/-- The actual singleton cleanup with its rounded threshold has vanishing mass. -/
theorem higher_actual_singleton_cleanup_scale_bound
    (H : Family α) (V : Edge α) (U k : ℕ)
    (hU : 2 ≤ U) (hN : U ^ 32 ≤ V.card) (hAdm : Admissible H)
    (hD₂ : ∀ S : Edge α, S.card = 2 →
      (H.filter fun E => S ⊆ E).card ≤ 4 * U ^ 2 * V.card ^ (k + 3))
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ 4 * U ^ 2 * V.card ^ (k + 2))
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ 4 * U ^ 2 * V.card ^ (k + 1))
    (hDFacet : ∀ S : Edge α, S.card = k + 5 →
      (H.filter fun E => S ⊆ E).card ≤ 4 * U ^ 2) :
    let t := V.card ^ (k + 3) / U ^ 9
    ((HigherRankUpper.upperFacetColorCleanupEdges (k + 5) H V t).card : ℝ) ≤
      (1166 + 8 * ((k : ℝ) + 5) ^ 2) * ((V.card : ℝ) ^ (k + 5) / U) := by
  let N := V.card
  let t := N ^ (k + 3) / U ^ 9
  have hUOne : 1 ≤ U := by omega
  have htBounds := higher_power_quotient_real_bounds N U (k + 3) 9 hUOne hN
    (by omega) (by omega)
  have hUp : (0 : ℝ) < U := by exact_mod_cast (by omega : 0 < U)
  have hNR : (U : ℝ) ^ 32 ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hNR
  have htPos : (0 : ℝ) < t := lt_of_lt_of_le (by positivity) htBounds.1
  have htNat : 1 ≤ t := by exact_mod_cast (by exact_mod_cast htPos : 0 < t)
  have hRaw := HigherRankUpper.upper_facet_color_cleanup_edges_sharp_budget
    (k + 5) H V t (4 * U ^ 2 * N ^ (k + 3)) (4 * U ^ 2 * N ^ (k + 2))
    (4 * U ^ 2 * N ^ (k + 1)) (4 * U ^ 2) (by omega) hAdm htNat
    hD₂ hD₃ hD₄ hDFacet
  let loss := (HigherRankUpper.upperFacetColorCleanupEdges (k + 5) H V t).card
  have hReal : (t : ℝ) * loss ≤
      t * (2 * (N : ℝ) ^ 2 * (t + ((k : ℝ) + 5) ^ 2 *
        (4 * (U : ℝ) ^ 2 * (N : ℝ) ^ (k + 2))) +
        3 * (N : ℝ) ^ 3 * (4 * (U : ℝ) ^ 2 * (N : ℝ) ^ (k + 1))) +
      9 * ((N : ℝ) ^ 2 * (4 * (U : ℝ) ^ 2 * (N : ℝ) ^ (k + 3)) *
        (4 * (U : ℝ) ^ 2 * (N : ℝ) ^ (k + 2)) * (4 * (U : ℝ) ^ 2)) := by
    have hCast := hRaw
    simp only [pow_two] at hCast ⊢
    exact_mod_cast hCast
  have hDiv : (loss : ℝ) ≤
      2 * (N : ℝ) ^ 2 * (t + 4 * ((k : ℝ) + 5) ^ 2 * (U : ℝ) ^ 2 * (N : ℝ) ^ (k + 2)) +
      12 * (U : ℝ) ^ 2 * (N : ℝ) ^ (k + 4) +
      576 * (U : ℝ) ^ 6 * (N : ℝ) ^ (2 * k + 7) / t := by
    apply (mul_le_mul_iff_right₀ htPos).mp
    calc
      (t : ℝ) * loss ≤ _ := hReal
      _ = _ := by
        field_simp
        simp only [show 2 * k + 7 = k + k + 7 by omega, pow_add]
        ring
  exact hDiv.trans (higher_singleton_cleanup_scale_envelope N U t k
    (by exact_mod_cast hUOne) hNR htBounds.1 htBounds.2)

end JSP523.Rank5
