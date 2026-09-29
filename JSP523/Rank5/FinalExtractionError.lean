import JSP523.Rank5.InitialPolynomialExtraction

/-!
# Rank-five extraction errors

The three cover terms in the coefficient-one shadow ledger satisfy an
arbitrary-factor bound against the star baseline.
-/

namespace JSP523.Rank5

open Filter Finset

/-- The three explicit cover terms of the rank-five extraction ledger. -/
def rankFiveCoverError (n : ℕ) (X : Edge (Fin n)) : ℕ :=
  X.card.choose 2 * (n - 2).choose 3 +
    X.card * ((Finset.univ \ X).card *
      (4 * (discreteRoundIterate (initialPolynomialScale n) 9 * n ^ 2))) +
    X.card.choose 2 *
      (4 * (((Finset.univ \ X).card - 1).choose 3))

/-- The cover error is little-o of the rank-five star in the explicit
arbitrary-factor form. The coefficient 3456 is 384 + 1536 + 1536. -/
theorem eventually_rank_five_cover_error_factor_bound (q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ X : Edge (Fin n),
      X.card ≤ initialPolynomialFarSize n + 1 →
      q * rankFiveCoverError n X ≤ 3456 * (n - 1).choose 4 := by
  have hSquare := eventually_initial_polynomial_nonempty_cover_small q
  have hCross := eventually_initial_polynomial_shadow_cross_small 8 q
  filter_upwards [eventually_ge_atTop 9, hSquare, hCross]
    with n hn hSquareN hCrossN
  intro X hX
  classical
  let h := initialPolynomialFarSize n + 1
  let W : Edge (Fin n) := Finset.univ \ X
  let R := discreteRoundIterate (initialPolynomialScale n) 9
  let B := (n - 1).choose 4
  have hXChoose : X.card.choose 2 ≤ h ^ 2 :=
    (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left hX _)
  have hW : W.card ≤ n := by
    calc
      W.card ≤ (Finset.univ : Edge (Fin n)).card :=
        Finset.card_le_card (Finset.sdiff_subset)
      _ = n := by simp
  have hWChoose : (W.card - 1).choose 3 ≤ (n - 1).choose 3 :=
    Nat.choose_le_choose 3 (by omega)
  have hA := initial_polynomial_multihit_star_rate n 5 q
    (by omega) hn hSquareN
  have hC := initial_polynomial_link_collision_star_rate n 5 q
    (by omega) hn hSquareN
  have hB := initial_polynomial_shadow_cross_star_rate n 5 q
    (by omega) hn (by simpa only [show 8 + 1 = 9 by omega] using hCrossN)
  norm_num at hA hB hC
  have hBoundA : q * (X.card.choose 2 * (n - 2).choose 3) ≤ 384 * B := by
    calc
      q * (X.card.choose 2 * (n - 2).choose 3) ≤
          q * (h ^ 2 * (n - 2).choose 3) := by
            gcongr
      _ ≤ 384 * B := by simpa [h, B] using hA
  have hBoundB : q * (X.card * (W.card *
      (4 * (R * n ^ 2)))) ≤ 1536 * B := by
    calc
      q * (X.card * (W.card *
          (4 * (R * n ^ 2)))) ≤
        q * (h * (n * (4 * (R * n ^ 2)))) := by gcongr
      _ ≤ 1536 * B := by simpa [h, B, R] using hB
  have hBoundC : q * (X.card.choose 2 *
      (4 * ((W.card - 1).choose 3))) ≤ 1536 * B := by
    calc
      q * (X.card.choose 2 * (4 * ((W.card - 1).choose 3))) ≤
        q * (h ^ 2 * (4 * ((n - 1).choose 3))) := by gcongr
      _ ≤ 1536 * B := by simpa [h, B] using hC
  dsimp [rankFiveCoverError]
  nlinarith [hBoundA, hBoundB, hBoundC]


def rankFiveRoundLoss (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range 9,
    discreteRoundAdditiveLoss n 5
      (discreteRoundIterate (initialPolynomialScale n) i)

def rankFiveCleanupCharge (H : ∀ n : ℕ, Family (Fin n)) (n : ℕ) : ℕ :=
  5 * 5 * initialScaleMultiplier n (initialPolynomialScale n) *
    initialVertexCap 5 (initialPolynomialFarSize n) (H n).card

noncomputable def rankFiveExtractionError
    (H : ∀ n : ℕ, Family (Fin n))
    (hUniform : ∀ n, Uniform 5 (H n)) (n : ℕ) : ℕ :=
  rankFiveRoundLoss n + rankFiveCleanupCharge H n +
    rankFiveCoverError n (initialPolynomialChosenCover 5 H hUniform n)

/-- A natural-valued little-o estimate supplies any fixed integer
factor saving. -/
theorem eventually_factor_bound_of_nat_little_o
    (f g : ℕ → ℕ)
    (hLittle : (fun n => (f n : ℝ)) =o[atTop] (fun n => (g n : ℝ)))
    (q : ℕ) (hq : 0 < q) :
    ∀ᶠ n : ℕ in atTop, q * f n ≤ g n := by
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  have hc : (0 : ℝ) < 1 / (q : ℝ) := one_div_pos.mpr hqreal
  filter_upwards [hLittle.def hc] with n hn
  have hfNonneg : (0 : ℝ) ≤ (f n : ℝ) := by positivity
  have hgNonneg : (0 : ℝ) ≤ (g n : ℝ) := by positivity
  have hBound : (f n : ℝ) ≤ (1 / (q : ℝ)) * (g n : ℝ) := by
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg hfNonneg, abs_of_nonneg hgNonneg] using hn
  have hScaled : (q : ℝ) * (f n : ℝ) ≤ (g n : ℝ) := by
    calc
      (q : ℝ) * (f n : ℝ) ≤
          (q : ℝ) * ((1 / (q : ℝ)) * (g n : ℝ)) :=
        mul_le_mul_of_nonneg_left hBound hqreal.le
      _ = (g n : ℝ) := by field_simp
  exact_mod_cast hScaled

/-- The complete extraction charge has an arbitrary fixed saving
against the rank-five star baseline. -/
theorem eventually_rank_five_extraction_error_factor_bound
    (H : ∀ n : ℕ, Family (Fin n))
    (hAdm : ∀ n, Admissible (H n))
    (hUniform : ∀ n, Uniform 5 (H n))
    (q : ℕ) (hq : 0 < q) :
    ∀ᶠ n : ℕ in atTop,
      q * rankFiveExtractionError H hUniform n ≤
        3458 * (n - 1).choose 4 := by
  have hScale : ∀ᶠ n : ℕ in atTop,
      (initialPolynomialScale n) ^ 3 ≤ n ^ 2 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (initial_polynomial_scale_bounds n hn).2.2
  have hRoundLittle := iterated_natural_loss_is_little_o 5 9
    initialPolynomialScale (by omega) initial_polynomial_scale_tendsto_at_top hScale
  have hRound := eventually_factor_bound_of_nat_little_o
    rankFiveRoundLoss (fun n => (n - 1).choose 4)
    (by simpa only [rankFiveRoundLoss, Nat.cast_sum,
      show 5 - 1 = 4 by omega] using hRoundLittle) q hq
  let C := 3 * 5 ^ 5 * (2 ^ 4 * Nat.factorial 4)
  let D := 2 ^ 4 * Nat.factorial 4
  have hFamily : ∀ᶠ n : ℕ in atTop,
      (H n).card ≤ C * (n - 1).choose 4 := by
    filter_upwards [eventually_ge_atTop 9] with n hn
    exact initial_polynomial_coarse_star_bound (H n)
      (by omega) hn (hAdm n) (hUniform n)
  have hSet := eventually_initial_polynomial_far_set_le_star_multiple 5 (by omega)
  have hCleanupLittle := initial_polynomial_cleanup_charge_is_little_o
    5 C D H hFamily hSet
  have hCleanup := eventually_factor_bound_of_nat_little_o
    (rankFiveCleanupCharge H) (fun n => (n - 1).choose 4)
    (by simpa only [rankFiveCleanupCharge, Nat.cast_mul,
      show 5 - 1 = 4 by omega] using hCleanupLittle) q hq
  have hCover := eventually_rank_five_cover_error_factor_bound q
  filter_upwards [hRound, hCleanup, hCover] with n hRoundN hCleanupN hCoverN
  have hX := initial_polynomial_chosen_cover_size 5 H hUniform n
  have hCoverN := hCoverN (initialPolynomialChosenCover 5 H hUniform n) hX
  dsimp [rankFiveExtractionError]
  rw [mul_add, mul_add]
  omega

end JSP523.Rank5
