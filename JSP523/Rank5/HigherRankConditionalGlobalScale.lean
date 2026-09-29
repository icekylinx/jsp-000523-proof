import JSP523.Rank5.FinalParameterRoot
import Mathlib.Analysis.Real.Sqrt

namespace JSP523.Rank5

open Filter

/-- Both actual cleanup degree thresholds dominate every fixed palette
sample size at the common final parameter root. -/
theorem eventually_higher_rank_scale_parameters (c₁ c₂ : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      2 ≤ finalParameterRoot n ∧ (finalParameterRoot n) ^ 32 ≤ n ∧
      discreteRoundIterate (initialPolynomialScale n) 9 ≤
        4 * (finalParameterRoot n) ^ 2 ∧
      c₁ ≤ n / (finalParameterRoot n) ^ 3 ∧
      c₂ ≤ n ^ 2 / (finalParameterRoot n) ^ 3 := by
  have hLarge := final_parameter_root_tendsto_at_top.eventually
    (eventually_ge_atTop (max 2 (max c₁ c₂)))
  have hRound := (tendsto_discrete_round_iterate_at_top initialPolynomialScale
    initial_polynomial_scale_tendsto_at_top 9).eventually (eventually_ge_atTop 1)
  filter_upwards [hLarge, hRound, eventually_ge_atTop 1] with n hU hR hn
  obtain ⟨hU1, _, hFactor, hPower⟩ := final_parameter_root_bounds n hn hR
  generalize hRoot : finalParameterRoot n = U at hU hU1 hFactor hPower ⊢
  have hU2 : 2 ≤ U := (le_max_left _ _).trans hU
  have hc₁ : c₁ ≤ U := (le_max_left c₁ c₂).trans ((le_max_right _ _).trans hU)
  have hc₂ : c₂ ≤ U := (le_max_right c₁ c₂).trans ((le_max_right _ _).trans hU)
  have hDen : 0 < U ^ 3 := pow_pos (by omega) _
  have h4 : U * U ^ 3 ≤ n := by
    calc
      U * U ^ 3 = U ^ 4 := by ring
      _ ≤ U ^ 32 := pow_le_pow_right₀ hU1 (by decide)
      _ ≤ n := hPower
  have hq : U ≤ n / U ^ 3 := (Nat.le_div_iff_mul_le hDen).2 h4
  have hSquare : n ≤ n ^ 2 := by nlinarith
  have hq₂ : U ≤ n ^ 2 / U ^ 3 := (Nat.le_div_iff_mul_le hDen).2 (h4.trans hSquare)
  exact ⟨hU2, hPower, hFactor, hc₁.trans hq, hc₂.trans hq₂⟩

/-- The explicit finite ambient and parent-mass error coefficients
vanish simultaneously. -/
theorem eventually_higher_rank_scalar_error_bound
    (A B ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ N m : ℝ, 0 ≤ N → 0 ≤ m →
      A * N / finalParameterRoot n +
        3 * N / Real.sqrt (finalParameterRoot n : ℝ) +
        B * m / finalParameterRoot n ≤ ε * (N + m) := by
  have hRoot : Tendsto (fun n : ℕ => (finalParameterRoot n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp final_parameter_root_tendsto_at_top
  have hA : Tendsto (fun n : ℕ => A / (finalParameterRoot n : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hRoot
  have hThree : Tendsto
      (fun n : ℕ => (3 : ℝ) / Real.sqrt (finalParameterRoot n : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hRoot)
  have hAmbient : Tendsto
      (fun n : ℕ => A / (finalParameterRoot n : ℝ) +
        3 / Real.sqrt (finalParameterRoot n : ℝ)) atTop (nhds 0) := by
    simpa only [zero_add] using hA.add hThree
  have hB : Tendsto (fun n : ℕ => B / (finalParameterRoot n : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hRoot
  have hAmbientSmall := (tendsto_order.1 hAmbient).2 ε hε
  have hMassSmall := (tendsto_order.1 hB).2 ε hε
  filter_upwards [hAmbientSmall, hMassSmall] with n hn hmn
  generalize hUR : (finalParameterRoot n : ℝ) = U at hn hmn ⊢
  intro N m hN hm
  have hFirst := mul_le_mul_of_nonneg_right hn.le hN
  have hSecond := mul_le_mul_of_nonneg_right hmn.le hm
  calc
    _ = (A / U +
        3 / Real.sqrt U) * N +
        (B / U) * m := by ring
    _ ≤ _ := by nlinarith only [hFirst, hSecond]

end JSP523.Rank5
