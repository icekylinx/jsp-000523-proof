import JSP523.Rank5.InitialCodegreeCleanup
import JSP523.Rank5.FarStarAsymptotic
import JSP523.Rank5.RegularizationLossAsymptotic
import JSP523.Rank5.ExtractionSurplus
import JSP523.Coarse.AllRank

open Filter Asymptotics

/-!
# Explicit polynomial alternative for the initial logarithmic scales

Writing `U = ⌊n^(1/16)⌋`, the choices `h₀ = U⁷` and `Scale = U¹⁰`
have exactly the separation properties used by the manuscript's
`√n/log n` and `√n log³ n` choices. They avoid transcendental rounding
inside the finite cleanup ledger.
-/

namespace JSP523.Rank5

/-- Theorem I.1 supplies the fixed star-multiple required by the
polynomial initial cleanup. -/
theorem initial_polynomial_coarse_star_bound
    {n r : ℕ} (H : Family (Fin n))
    (hr : 4 ≤ r) (hn : 2 * (r - 1) + 1 ≤ n)
    (hAdm : Admissible H) (hUniform : Uniform r H) :
    H.card ≤
      (3 * r ^ r * (2 ^ (r - 1) * (r - 1).factorial)) *
        (n - 1).choose (r - 1) := by
  have hCoarse := Coarse.coarse_bound_all_rank H r (by omega) hUniform hAdm
  have hFac : 1 ≤ r.factorial := Nat.factorial_pos r
  have hStar := far_star_power_le_choose_multiple n (r - 1) hn
  calc
    H.card = 1 * H.card := by simp
    _ ≤ r.factorial * H.card := Nat.mul_le_mul_right _ hFac
    _ ≤ 3 * r ^ r * n ^ (r - 1) := by
      simpa only [Fintype.card_fin] using hCoarse
    _ ≤ (3 * r ^ r * (2 ^ (r - 1) * (r - 1).factorial)) *
        (n - 1).choose (r - 1) := by
      have h := Nat.mul_le_mul_left (3 * r ^ r) hStar
      nlinarith [h]

def initialPolynomialRoot (n : ℕ) : ℕ := Nat.nthRoot 16 n

def initialPolynomialFarSize (n : ℕ) : ℕ :=
  (initialPolynomialRoot n) ^ 7

def initialPolynomialScale (n : ℕ) : ℕ :=
  (initialPolynomialRoot n) ^ 10

theorem initial_polynomial_root_bounds (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ initialPolynomialRoot n ∧
      (initialPolynomialRoot n) ^ 16 ≤ n ∧
      n ≤ 2 ^ 16 * (initialPolynomialRoot n) ^ 16 := by
  let U := initialPolynomialRoot n
  have hUpos : 1 ≤ U := by
    dsimp [U, initialPolynomialRoot]
    apply (Nat.le_nthRoot_iff (by norm_num : 16 ≠ 0)).2
    simpa using hn
  have hLo : U ^ 16 ≤ n := Nat.pow_nthRoot_le (Or.inl (by norm_num))
  have hHi : n < (U + 1) ^ 16 :=
    Nat.lt_pow_nthRoot_add_one (by norm_num : 16 ≠ 0) n
  have hDouble : U + 1 ≤ 2 * U := by omega
  refine ⟨hUpos, hLo, ?_⟩
  calc
    n ≤ (U + 1) ^ 16 := Nat.le_of_lt hHi
    _ ≤ (2 * U) ^ 16 := Nat.pow_le_pow_left hDouble _
    _ = 2 ^ 16 * U ^ 16 := by rw [mul_pow]

/-- The polynomial removal set is bounded by a fixed multiple of the
extremal star, including the extra vertex used to make it nonempty. -/
theorem initial_polynomial_far_set_le_star_multiple
    (n r : ℕ) (hr : 4 ≤ r)
    (hn : 2 * (r - 1) + 1 ≤ n)
    (hRoot : 2 ≤ initialPolynomialRoot n) :
    initialPolynomialFarSize n + 1 ≤
      (2 ^ (r - 1) * (r - 1).factorial) *
        (n - 1).choose (r - 1) := by
  let U := initialPolynomialRoot n
  have hUone : 1 ≤ U := by omega
  have hU7 : 1 ≤ U ^ 7 := Nat.one_le_pow _ _ hUone
  have hU8 : U ^ 7 + 1 ≤ U ^ 8 := by
    have hMul : 2 * U ^ 7 ≤ U * U ^ 7 :=
      Nat.mul_le_mul_right _ hRoot
    have hEq : U * U ^ 7 = U ^ 8 := by ring
    omega
  have hU16 : U ^ 8 ≤ U ^ 16 :=
    pow_le_pow_right₀ hUone (by omega)
  have hN : U ^ 16 ≤ n :=
    (initial_polynomial_root_bounds n (by omega : 1 ≤ n)).2.1
  have hFarN : initialPolynomialFarSize n + 1 ≤ n := by
    dsimp [initialPolynomialFarSize]
    exact hU8.trans (hU16.trans hN)
  have hPow : n ≤ n ^ (r - 1) :=
    le_self_pow (by omega : 1 ≤ n) (by omega : r - 1 ≠ 0)
  exact hFarN.trans (hPow.trans
    (far_star_power_le_choose_multiple n (r - 1) hn))

theorem eventually_initial_polynomial_far_set_le_star_multiple
    (r : ℕ) (hr : 4 ≤ r) :
    ∀ᶠ n : ℕ in atTop,
      initialPolynomialFarSize n + 1 ≤
        (2 ^ (r - 1) * (r - 1).factorial) *
          (n - 1).choose (r - 1) := by
  filter_upwards [eventually_ge_atTop
    (max (2 * (r - 1) + 1) (2 ^ 16))] with n hn
  have hN : 2 * (r - 1) + 1 ≤ n := (le_max_left _ _).trans hn
  have hU : 2 ≤ initialPolynomialRoot n := by
    apply (Nat.le_nthRoot_iff (by norm_num : 16 ≠ 0)).2
    exact (le_max_right _ _).trans hn
  exact initial_polynomial_far_set_le_star_multiple n r hr hN hU

theorem initial_polynomial_far_square_bound
    (n q : ℕ) (hn : 1 ≤ n)
    (hq : q ≤ (initialPolynomialRoot n) ^ 2) :
    q * (initialPolynomialFarSize n) ^ 2 ≤ n := by
  let U := initialPolynomialRoot n
  have hLo := (initial_polynomial_root_bounds n hn).2.1
  calc
    q * (initialPolynomialFarSize n) ^ 2 = q * U ^ 14 := by
      dsimp [initialPolynomialFarSize, U]
      ring
    _ ≤ U ^ 2 * U ^ 14 := Nat.mul_le_mul_right _ hq
    _ = U ^ 16 := by ring
    _ ≤ n := hLo

theorem initial_polynomial_scale_bounds
    (n : ℕ) (hn : 1 ≤ n) :
    0 < initialPolynomialScale n ∧
      initialPolynomialScale n ≤ n ∧
      (initialPolynomialScale n) ^ 3 ≤ n ^ 2 := by
  let U := initialPolynomialRoot n
  obtain ⟨hUpos, hLo, _⟩ := initial_polynomial_root_bounds n hn
  have hPow10 : U ^ 10 ≤ U ^ 16 := by
    exact pow_le_pow_right₀ (by omega : 1 ≤ U) (by omega : 10 ≤ 16)
  have hPow30 : U ^ 30 ≤ U ^ 32 := by
    exact pow_le_pow_right₀ (by omega : 1 ≤ U) (by omega : 30 ≤ 32)
  refine ⟨?_, hPow10.trans hLo, ?_⟩
  · dsimp [initialPolynomialScale]
    exact pow_pos (by omega : 0 < U) _
  · calc
      (initialPolynomialScale n) ^ 3 = U ^ 30 := by
        dsimp [initialPolynomialScale, U]
        ring
      _ ≤ U ^ 32 := hPow30
      _ = (U ^ 16) ^ 2 := by ring
      _ ≤ n ^ 2 := Nat.pow_le_pow_left hLo 2

/-- A single natural round lowers the polynomial initial factor from
`U¹⁰` to at most `U⁸`; later rounds only lower it further. -/
theorem initial_polynomial_round_iterate_le_root_eight
    (n steps : ℕ) (hn : 1 ≤ n) :
    discreteRoundIterate (initialPolynomialScale n) (steps + 1) ≤
      (initialPolynomialRoot n) ^ 8 := by
  let U := initialPolynomialRoot n
  have hUone : 1 ≤ U := (initial_polynomial_root_bounds n hn).1
  have hTargetPow : (discreteRoundTarget (initialPolynomialScale n)) ^ 4 ≤
      (initialPolynomialScale n) ^ 3 :=
    Nat.pow_nthRoot_le (Or.inl (by norm_num))
  have hPow : (initialPolynomialScale n) ^ 3 ≤ (U ^ 8) ^ 4 := by
    calc
      (initialPolynomialScale n) ^ 3 = U ^ 30 := by
        dsimp [initialPolynomialScale, U]
        ring
      _ ≤ U ^ 32 := pow_le_pow_right₀ hUone (by omega)
      _ = (U ^ 8) ^ 4 := by ring
  have hTarget : discreteRoundTarget (initialPolynomialScale n) ≤ U ^ 8 := by
    by_contra h
    have hlt : U ^ 8 < discreteRoundTarget (initialPolynomialScale n) := by omega
    have hltPow := Nat.pow_lt_pow_left hlt (by norm_num : 4 ≠ 0)
    omega
  have hIter : ∀ t,
      discreteRoundIterate (initialPolynomialScale n) (t + 1) ≤
        discreteRoundTarget (initialPolynomialScale n) := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
        calc
          discreteRoundIterate (initialPolynomialScale n) (t + 1 + 1) =
              discreteRoundTarget
                (discreteRoundIterate (initialPolynomialScale n) (t + 1)) := rfl
          _ ≤ discreteRoundIterate (initialPolynomialScale n) (t + 1) :=
            discrete_round_target_le_self _
          _ ≤ discreteRoundTarget (initialPolynomialScale n) := ih
  exact (hIter steps).trans hTarget

/-- The exact integer iteration obeys the exponent contraction
`R_t^(4^t) ≤ R_0^(3^t)`, including all floor effects. -/
theorem discrete_round_iterate_power_bound (R t : ℕ) :
    (discreteRoundIterate R t) ^ (4 ^ t) ≤ R ^ (3 ^ t) := by
  induction t with
  | zero => simp [discreteRoundIterate]
  | succ t ih =>
      let S := discreteRoundIterate R t
      have hRoot : (discreteRoundTarget S) ^ 4 ≤ S ^ 3 :=
        Nat.pow_nthRoot_le (Or.inl (by norm_num))
      have hPow := Nat.pow_le_pow_left hRoot (4 ^ t)
      have hIH := Nat.pow_le_pow_left ih 3
      calc
        (discreteRoundIterate R (t + 1)) ^ (4 ^ (t + 1)) =
            ((discreteRoundTarget S) ^ 4) ^ (4 ^ t) := by
          change (discreteRoundTarget S) ^ (4 ^ (t + 1)) = _
          rw [pow_succ, mul_comm, pow_mul]
        _ ≤ (S ^ 3) ^ (4 ^ t) := hPow
        _ = (S ^ (4 ^ t)) ^ 3 := by
          rw [← pow_mul, ← pow_mul, mul_comm]
        _ ≤ (R ^ (3 ^ t)) ^ 3 := hIH
        _ = R ^ (3 ^ (t + 1)) := by
          rw [← pow_mul, pow_succ]

/-- Nine fixed natural rounds lower the polynomial factor below the
sixteenth root of the ambient size. Hence the manuscript's `R¹¹/n`
condition follows with room to spare. -/
theorem initial_polynomial_nine_round_factor_bound
    (n : ℕ) (hn : 1 ≤ n) :
    discreteRoundIterate (initialPolynomialScale n) 9 ≤
      initialPolynomialRoot n := by
  let U := initialPolynomialRoot n
  have hUone : 1 ≤ U := (initial_polynomial_root_bounds n hn).1
  have hRaw := discrete_round_iterate_power_bound
    (initialPolynomialScale n) 9
  have hExp : 10 * 3 ^ 9 ≤ 4 ^ 9 := by norm_num
  have hUpper : (initialPolynomialScale n) ^ (3 ^ 9) ≤ U ^ (4 ^ 9) := by
    calc
      (initialPolynomialScale n) ^ (3 ^ 9) = U ^ (10 * 3 ^ 9) := by
        dsimp [initialPolynomialScale, U]
        rw [← pow_mul]
      _ ≤ U ^ (4 ^ 9) := pow_le_pow_right₀ hUone hExp
  have hPow : (discreteRoundIterate (initialPolynomialScale n) 9) ^
      (4 ^ 9) ≤ U ^ (4 ^ 9) := hRaw.trans hUpper
  by_contra h
  have hlt : U < discreteRoundIterate (initialPolynomialScale n) 9 := by omega
  have hltPow := Nat.pow_lt_pow_left hlt (by norm_num : 4 ^ 9 ≠ 0)
  omega

theorem eventually_initial_polynomial_nine_round_eleven_small
    (q : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      q * (discreteRoundIterate (initialPolynomialScale n) 9) ^ 11 ≤ n := by
  filter_upwards [eventually_ge_atTop ((max 1 q) ^ 16)]
    with n hnLarge
  have hn : 1 ≤ n := by
    have hBase : 1 ≤ max 1 q := le_max_left _ _
    have hPow : 1 ≤ (max 1 q) ^ 16 := Nat.one_le_pow _ _ hBase
    omega
  let U := initialPolynomialRoot n
  have hU : max 1 q ≤ U := by
    apply (Nat.le_nthRoot_iff (by norm_num : 16 ≠ 0)).2
    exact hnLarge
  have hq : q ≤ U := (le_max_right _ _).trans hU
  have hRound := initial_polynomial_nine_round_factor_bound n hn
  have hPow := Nat.pow_le_pow_left hRound 11
  have hProd := Nat.mul_le_mul hq hPow
  have hUone : 1 ≤ U := (le_max_left _ _).trans hU
  have hExp : U ^ 12 ≤ U ^ 16 :=
    pow_le_pow_right₀ hUone (by omega)
  have hN := (initial_polynomial_root_bounds n hn).2.1
  calc
    q * (discreteRoundIterate (initialPolynomialScale n) 9) ^ 11 ≤
        U * U ^ 11 := hProd
    _ = U ^ 12 := by ring
    _ ≤ U ^ 16 := hExp
    _ ≤ n := hN

/-- The removed-set size times the codegree factor after one or more
rounds is `o(n)` in the explicit arbitrary-factor form required by the
coefficient-one shadow ledger. -/
theorem eventually_initial_polynomial_shadow_cross_small
    (steps q : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      q * (initialPolynomialFarSize n + 1) *
        discreteRoundIterate (initialPolynomialScale n) (steps + 1) ≤ n := by
  filter_upwards [eventually_ge_atTop ((max 2 (2 * q)) ^ 16)]
    with n hnLarge
  have hn : 1 ≤ n := by
    have hBase : 1 ≤ max 2 (2 * q) := by omega
    have hPow : 1 ≤ (max 2 (2 * q)) ^ 16 := Nat.one_le_pow _ _ hBase
    omega
  have hU : max 2 (2 * q) ≤ initialPolynomialRoot n := by
    apply (Nat.le_nthRoot_iff (by norm_num : 16 ≠ 0)).2
    exact hnLarge
  let U := initialPolynomialRoot n
  have hUone : 1 ≤ U := (initial_polynomial_root_bounds n hn).1
  have hUq : 2 * q ≤ U := (le_max_right _ _).trans hU
  have hFar : 1 ≤ U ^ 7 := Nat.one_le_pow _ _ hUone
  have hFarBound : initialPolynomialFarSize n + 1 ≤ 2 * U ^ 7 := by
    change U ^ 7 + 1 ≤ 2 * U ^ 7
    omega
  have hRound := initial_polynomial_round_iterate_le_root_eight n steps hn
  have hProduct := Nat.mul_le_mul hFarBound hRound
  have hProduct' := Nat.mul_le_mul_left q hProduct
  have hPower : 2 * q * U ^ 15 ≤ U ^ 16 := by
    have h := Nat.mul_le_mul_right (U ^ 15) hUq
    have he : U * U ^ 15 = U ^ 16 := by ring
    omega
  have hN := (initial_polynomial_root_bounds n hn).2.1
  calc
    q * (initialPolynomialFarSize n + 1) *
        discreteRoundIterate (initialPolynomialScale n) (steps + 1) =
      q * ((initialPolynomialFarSize n + 1) *
        discreteRoundIterate (initialPolynomialScale n) (steps + 1)) := by ring
    _ ≤ q * (2 * U ^ 7 * U ^ 8) := hProduct'
    _ = 2 * q * U ^ 15 := by ring
    _ ≤ U ^ 16 := hPower
    _ ≤ n := hN

/-- The rounded matching parameter is at most a fixed rank-independent
multiple of `U⁶`. -/
theorem initial_polynomial_multiplier_bound
    (n : ℕ) (hn : 1 ≤ n) :
    initialScaleMultiplier n (initialPolynomialScale n) ≤
      (3 * 2 ^ 16 + 1) * (initialPolynomialRoot n) ^ 6 := by
  let U := initialPolynomialRoot n
  have hUpos := (initial_polynomial_root_bounds n hn).1
  have hHi := (initial_polynomial_root_bounds n hn).2.2
  have hU10 : 0 < U ^ 10 := pow_pos (by omega : 0 < U) _
  have hProduct : 3 * n ≤ (3 * 2 ^ 16 * U ^ 6) * U ^ 10 := by
    calc
      3 * n ≤ 3 * (2 ^ 16 * U ^ 16) := Nat.mul_le_mul_left 3 hHi
      _ = (3 * 2 ^ 16 * U ^ 6) * U ^ 10 := by ring
  have hDiv : 3 * n / U ^ 10 ≤ 3 * 2 ^ 16 * U ^ 6 := by
    calc
      3 * n / U ^ 10 ≤
          ((3 * 2 ^ 16 * U ^ 6) * U ^ 10) / U ^ 10 :=
        Nat.div_le_div_right hProduct
      _ = 3 * 2 ^ 16 * U ^ 6 := by
        rw [Nat.mul_comm (3 * 2 ^ 16 * U ^ 6) (U ^ 10)]
        exact Nat.mul_div_cancel_left _ hU10
  have hOne : 1 ≤ U ^ 6 := Nat.one_le_pow _ _ hUpos
  dsimp [initialScaleMultiplier, initialPolynomialScale, U]
  nlinarith [hDiv, hOne]

theorem initial_polynomial_cleanup_multiplier_gap
    (n r m : ℕ) (hn : 1 ≤ n)
    (hU : m * (r * r) * (3 * 2 ^ 16 + 1) ≤
      initialPolynomialRoot n) :
    m * (r * r * initialScaleMultiplier n
      (initialPolynomialScale n)) ≤
        initialPolynomialFarSize n + 1 := by
  let U := initialPolynomialRoot n
  have ha := initial_polynomial_multiplier_bound n hn
  have hProduct := Nat.mul_le_mul_left (m * (r * r)) ha
  have hRoot := Nat.mul_le_mul_right (U ^ 6) hU
  have hPow : U * U ^ 6 = U ^ 7 := by ring
  dsimp [initialPolynomialFarSize, U]
  nlinarith [hProduct, hRoot, hPow]

theorem initial_polynomial_scale_separation
    (n r : ℕ) (hn : 1 ≤ n)
    (hU : 16 * r * 2 ^ 16 < (initialPolynomialRoot n) ^ 4) :
    16 * r * n < (initialPolynomialScale n) ^ 2 := by
  let U := initialPolynomialRoot n
  have hUpos := (initial_polynomial_root_bounds n hn).1
  have hN := (initial_polynomial_root_bounds n hn).2.2
  have hUpow : 0 < U ^ 16 := pow_pos (by omega : 0 < U) _
  calc
    16 * r * n ≤ 16 * r * (2 ^ 16 * U ^ 16) :=
      Nat.mul_le_mul_left _ hN
    _ = (16 * r * 2 ^ 16) * U ^ 16 := by ring
    _ < U ^ 4 * U ^ 16 :=
      (Nat.mul_lt_mul_right hUpow).2 hU
    _ = (initialPolynomialScale n) ^ 2 := by
      dsimp [initialPolynomialScale, U]
      ring

theorem initial_polynomial_root_tendsto_at_top :
    Tendsto initialPolynomialRoot atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro m
  filter_upwards [eventually_ge_atTop (m ^ 16)] with n hn
  exact (Nat.le_nthRoot_iff (by norm_num : 16 ≠ 0)).2 hn

theorem eventually_initial_polynomial_far_small (q : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      q * (initialPolynomialFarSize n) ^ 2 ≤ n := by
  have hRoot := initial_polynomial_root_tendsto_at_top.eventually
    (eventually_ge_atTop (max 1 q))
  filter_upwards [eventually_ge_atTop 1, hRoot] with n hn hU
  have hUpos : 1 ≤ initialPolynomialRoot n := (le_max_left _ _).trans hU
  have hq : q ≤ initialPolynomialRoot n := (le_max_right _ _).trans hU
  have hqSq : q ≤ (initialPolynomialRoot n) ^ 2 :=
    hq.trans (le_self_pow hUpos (by norm_num : 2 ≠ 0))
  exact initial_polynomial_far_square_bound n q hn hqSq

/-- Adding one vertex to make the actual high-degree cover nonempty keeps
the small-set condition needed by far-star mass extraction. -/
theorem eventually_initial_polynomial_nonempty_cover_small (q : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      q * (initialPolynomialFarSize n + 1) ^ 2 ≤ n := by
  have hSmall := eventually_initial_polynomial_far_small (4 * q)
  filter_upwards [eventually_ge_atTop 1, hSmall] with n hn hSmallN
  have hRoot : 1 ≤ initialPolynomialRoot n :=
    (initial_polynomial_root_bounds n hn).1
  have hFar : 1 ≤ initialPolynomialFarSize n := by
    dsimp [initialPolynomialFarSize]
    exact Nat.one_le_pow _ _ hRoot
  have hSquare : (initialPolynomialFarSize n + 1) ^ 2 ≤
      4 * (initialPolynomialFarSize n) ^ 2 := by
    nlinarith [sq_nonneg (initialPolynomialFarSize n - 1 : ℤ)]
  have hScaled := Nat.mul_le_mul_left q hSquare
  nlinarith [hScaled, hSmallN]

/-- The high-degree cover may be enlarged by one vertex so that the
coefficient-one shadow ledger has a nonempty removed set. -/
theorem exists_initial_polynomial_nonempty_high_degree_cover
    {n r : ℕ} (H : Family (Fin n))
    (hn : 1 ≤ n) (hUniform : Uniform r H) :
    ∃ X : Edge (Fin n), X.Nonempty ∧
      X.card ≤ initialPolynomialFarSize n + 1 ∧
      ∀ z : Fin n, z ∉ X →
        (H.filter (fun E => z ∈ E)).card <
          initialVertexCap r (initialPolynomialFarSize n) H.card := by
  classical
  obtain ⟨Y, hY, hOutside⟩ := exists_high_degree_vertex_cover H
    hUniform (initial_vertex_cap_budget r (initialPolynomialFarSize n) H.card)
  let z₀ : Fin n := ⟨0, by omega⟩
  refine ⟨insert z₀ Y, ⟨z₀, Finset.mem_insert_self _ _⟩, ?_, ?_⟩
  · exact (Finset.card_insert_le z₀ Y).trans (by omega)
  · intro z hz
    exact hOutside z (fun hYz => hz (Finset.mem_insert_of_mem hYz))

theorem initial_polynomial_far_square_is_little_o :
    (fun n : ℕ => ((initialPolynomialFarSize n) ^ 2 : ℝ))
      =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  apply IsLittleO.of_bound
  intro c hc
  obtain ⟨q, hqgt⟩ := exists_nat_gt ((1 : ℝ) / c)
  have hqpos : 0 < q := by
    have hNonneg : (0 : ℝ) ≤ 1 / c := by positivity
    exact_mod_cast (lt_of_le_of_lt hNonneg hqgt)
  have hCoeff : (1 : ℝ) / q ≤ c := by
    have h := (div_lt_iff₀ hc).mp hqgt
    have hqreal : (0 : ℝ) < q := by exact_mod_cast hqpos
    apply (div_le_iff₀ hqreal).2
    nlinarith
  filter_upwards [eventually_initial_polynomial_far_small q]
    with n hn
  have hReal : (q : ℝ) * (initialPolynomialFarSize n : ℝ) ^ 2 ≤
      (n : ℝ) := by exact_mod_cast hn
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hDiv : (initialPolynomialFarSize n : ℝ) ^ 2 ≤
      (1 / (q : ℝ)) * n := by
    have hDiv' : (initialPolynomialFarSize n : ℝ) ^ 2 ≤
        (n : ℝ) / q := (le_div_iff₀ hqreal).2 (by nlinarith [hReal])
    simpa [div_eq_mul_inv, mul_comm] using hDiv'
  have hBound : (initialPolynomialFarSize n : ℝ) ^ 2 ≤ c * n :=
    hDiv.trans (mul_le_mul_of_nonneg_right hCoeff (by positivity))
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg (initialPolynomialFarSize n : ℝ)),
    abs_of_nonneg (show (0 : ℝ) ≤ n by positivity)] using hBound

theorem initial_polynomial_nonempty_cover_square_is_little_o :
    (fun n : ℕ => ((initialPolynomialFarSize n + 1) ^ 2 : ℝ))
      =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  apply IsLittleO.of_bound
  intro c hc
  obtain ⟨q, hqgt⟩ := exists_nat_gt ((1 : ℝ) / c)
  have hqpos : 0 < q := by
    have hNonneg : (0 : ℝ) ≤ 1 / c := by positivity
    exact_mod_cast (lt_of_le_of_lt hNonneg hqgt)
  have hCoeff : (1 : ℝ) / q ≤ c := by
    have h := (div_lt_iff₀ hc).mp hqgt
    have hqreal : (0 : ℝ) < q := by exact_mod_cast hqpos
    apply (div_le_iff₀ hqreal).2
    nlinarith
  filter_upwards [eventually_initial_polynomial_nonempty_cover_small q]
    with n hn
  have hReal : (q : ℝ) * (initialPolynomialFarSize n + 1 : ℝ) ^ 2 ≤
      (n : ℝ) := by exact_mod_cast hn
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hDiv : (initialPolynomialFarSize n + 1 : ℝ) ^ 2 ≤
      (1 / (q : ℝ)) * n := by
    have hDiv' : (initialPolynomialFarSize n + 1 : ℝ) ^ 2 ≤
        (n : ℝ) / q := (le_div_iff₀ hqreal).2 (by nlinarith [hReal])
    simpa [div_eq_mul_inv, mul_comm] using hDiv'
  have hBound : (initialPolynomialFarSize n + 1 : ℝ) ^ 2 ≤ c * n :=
    hDiv.trans (mul_le_mul_of_nonneg_right hCoeff (by positivity))
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg (initialPolynomialFarSize n + 1 : ℝ)),
    abs_of_nonneg (show (0 : ℝ) ≤ n by positivity)] using hBound

/-- The actual high-degree cover is chosen separately at each ground size.
At size zero it is empty; all asymptotic statements use positive sizes. -/
noncomputable def initialPolynomialChosenCover
    (r : ℕ) (H : ∀ n : ℕ, Family (Fin n))
    (hUniform : ∀ n, Uniform r (H n)) (n : ℕ) : Edge (Fin n) :=
  if hn : 1 ≤ n then
    Classical.choose (exists_initial_polynomial_nonempty_high_degree_cover
      (H n) hn (hUniform n))
  else ∅

theorem initial_polynomial_chosen_cover_spec
    (r : ℕ) (H : ∀ n : ℕ, Family (Fin n))
    (hUniform : ∀ n, Uniform r (H n))
    (n : ℕ) (hn : 1 ≤ n) :
    (initialPolynomialChosenCover r H hUniform n).Nonempty ∧
    (initialPolynomialChosenCover r H hUniform n).card ≤
      initialPolynomialFarSize n + 1 ∧
    ∀ z : Fin n, z ∉ initialPolynomialChosenCover r H hUniform n →
      ((H n).filter (fun E => z ∈ E)).card <
        initialVertexCap r (initialPolynomialFarSize n) (H n).card := by
  classical
  simp only [initialPolynomialChosenCover, dite_eq_left hn]
  exact Classical.choose_spec
    (exists_initial_polynomial_nonempty_high_degree_cover
      (H n) hn (hUniform n))

theorem initial_polynomial_chosen_cover_size
    (r : ℕ) (H : ∀ n : ℕ, Family (Fin n))
    (hUniform : ∀ n, Uniform r (H n)) (n : ℕ) :
    (initialPolynomialChosenCover r H hUniform n).card ≤
      initialPolynomialFarSize n + 1 := by
  by_cases hn : 1 ≤ n
  · exact (initial_polynomial_chosen_cover_spec r H hUniform n hn).2.1
  · have hZero : n = 0 := by omega
    simp [initialPolynomialChosenCover, hZero]

/-- The actual largest-degree construction meets the positive far-tail
mass theorem for every fixed real maximum-degree gap. -/
theorem eventually_initial_polynomial_chosen_far_tail_mass
    (r : ℕ) (δ : ℝ) (hr : 4 ≤ r) (hδ : 0 < δ)
    (H : ∀ n : ℕ, Family (Fin n)) (M : ℕ → ℕ)
    (hAdm : ∀ n, Admissible (H n))
    (hUniform : ∀ n, Uniform r (H n))
    (hMax : ∀ n z, ((H n).filter (fun E => z ∈ E)).card ≤ M n)
    (hDegree : ∀ᶠ n : ℕ in atTop,
      (M n : ℝ) ≤ (1 - δ) * ((n - 1).choose (r - 1) : ℝ))
    (hMass : ∀ᶠ n : ℕ in atTop,
      (n - 1).choose (r - 1) ≤ (H n).card) :
    ∃ α β : ℕ, 0 < α ∧ 0 < β ∧
      ∀ᶠ n : ℕ in atTop,
        (initialPolynomialChosenCover r H hUniform n).Nonempty ∧
        (∀ z : Fin n,
          z ∉ initialPolynomialChosenCover r H hUniform n →
            ((H n).filter (fun E => z ∈ E)).card <
              initialVertexCap r (initialPolynomialFarSize n) (H n).card) ∧
        α * (n - 1).choose (r - 1) ≤
          β * ((H n).filter (fun E =>
            Disjoint E (initialPolynomialChosenCover r H hUniform n))).card := by
  let X := initialPolynomialChosenCover r H hUniform
  obtain ⟨α, β, hα, hβ, hTail⟩ :=
    eventually_far_star_positive_mass_of_real_degree_gap r δ hr hδ
      H X (fun n => initialPolynomialFarSize n + 1) M
      hAdm hUniform
      (by intro n; exact initial_polynomial_chosen_cover_size r H hUniform n)
      hMax hDegree hMass (by
        simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
          initial_polynomial_nonempty_cover_square_is_little_o)
  refine ⟨α, β, hα, hβ, ?_⟩
  filter_upwards [eventually_ge_atTop 1, hTail] with n hn hTailN
  obtain ⟨hNonempty, _, hOutside⟩ :=
    initial_polynomial_chosen_cover_spec r H hUniform n hn
  exact ⟨hNonempty, hOutside, hTailN⟩

/-- The polynomial initial scale tends to infinity, so every fixed
natural-round threshold is eventually met. -/
theorem initial_polynomial_scale_tendsto_at_top :
    Tendsto initialPolynomialScale atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro m
  filter_upwards [initial_polynomial_root_tendsto_at_top.eventually
    (eventually_ge_atTop (max 1 m))] with n hn
  have hOne : 1 ≤ initialPolynomialRoot n :=
    (le_max_left _ _).trans hn
  have hm : m ≤ initialPolynomialRoot n :=
    (le_max_right _ _).trans hn
  exact hm.trans (by
    simpa only [initialPolynomialScale] using
      (le_self_pow hOne (by norm_num : 10 ≠ 0)))

/-- All finite separation conditions needed by the initial cleanup and
any fixed number of natural rounds hold at one common eventual threshold. -/
theorem eventually_initial_polynomial_parameters (r steps m : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      1 ≤ n ∧
      16 * r * n < (initialPolynomialScale n) ^ 2 ∧
      m * (r * r * initialScaleMultiplier n
        (initialPolynomialScale n)) ≤ initialPolynomialFarSize n + 1 ∧
      (∀ i < steps,
        (16 * (36 * r) ^ 3) ^ 8 ≤
          (discreteRoundIterate (initialPolynomialScale n) i) ^ 5) := by
  let C := m * (r * r) * (3 * 2 ^ 16 + 1)
  have hRoot := initial_polynomial_root_tendsto_at_top.eventually
    (eventually_ge_atTop (max 1 (max C (16 * r * 2 ^ 16 + 1))))
  have hRounds := eventually_all_discrete_round_iterates_large
    initialPolynomialScale initial_polynomial_scale_tendsto_at_top
    steps (max 1 ((16 * (36 * r) ^ 3) ^ 8))
  filter_upwards [eventually_ge_atTop 1, hRoot, hRounds]
    with n hn hU hRoundsN
  have hUpos : 1 ≤ initialPolynomialRoot n :=
    (le_max_left _ _).trans hU
  have hC : C ≤ initialPolynomialRoot n :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hU)
  have hSepRoot : 16 * r * 2 ^ 16 <
      (initialPolynomialRoot n) ^ 4 := by
    have hD : 16 * r * 2 ^ 16 + 1 ≤ initialPolynomialRoot n :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hU)
    have hPow := le_self_pow hUpos (by norm_num : 4 ≠ 0)
    omega
  refine ⟨hn, initial_polynomial_scale_separation n r hn hSepRoot,
    initial_polynomial_cleanup_multiplier_gap n r m hn hC, ?_⟩
  intro i hi
  have hIterOne : 1 ≤ discreteRoundIterate
      (initialPolynomialScale n) i :=
    (le_max_left _ _).trans (hRoundsN i hi)
  exact ((le_max_right _ _).trans (hRoundsN i hi)).trans
    (le_self_pow hIterOne
      (by norm_num : 5 ≠ 0))

/-- The complete heavy-root cleanup charge has an arbitrary fixed saving
against the star once the polynomial root clears the explicit threshold.
The two upper bounds are the finite form of the global edge-count bound
and the elementary small-set estimate. -/
theorem initial_polynomial_cleanup_loss_rate
    (n r m C D edgeCount : ℕ) (hn : 1 ≤ n)
    (hRoot : m * (r * r) * (3 * 2 ^ 16 + 1) ≤
      initialPolynomialRoot n)
    (hFamily : edgeCount ≤ C * (n - 1).choose (r - 1))
    (hSet : initialPolynomialFarSize n + 1 ≤
      D * (n - 1).choose (r - 1)) :
    m * (r * r * initialScaleMultiplier n (initialPolynomialScale n) *
      initialVertexCap r (initialPolynomialFarSize n) edgeCount) ≤
      (r * C + D) * (n - 1).choose (r - 1) := by
  exact initial_vertex_cap_loss_rate r (initialPolynomialFarSize n)
    (initialScaleMultiplier n (initialPolynomialScale n)) edgeCount
    ((n - 1).choose (r - 1)) m C D
    (initial_polynomial_cleanup_multiplier_gap n r m hn hRoot)
    hFamily hSet

/-- A positive far-tail mass survives the actual heavy-root cleanup at
the polynomial initial scale. The coefficient condition can always be
met by taking the fixed integer saving `m` sufficiently large and then
increasing `n` through `eventually_initial_polynomial_parameters`. -/
theorem initial_polynomial_positive_mass_after_cleanup
    {n r α β C D m : ℕ} (H : Family (Fin n))
    (X : Edge (Fin n))
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hn : 1 ≤ n) (hr : 4 ≤ r)
    (hOutside : ∀ z : Fin n, z ∉ X →
      (H.filter (fun E => z ∈ E)).card <
        initialVertexCap r (initialPolynomialFarSize n) H.card)
    (hTail : α * (n - 1).choose (r - 1) ≤
      β * (H.filter (fun E => Disjoint E X)).card)
    (hFamily : H.card ≤ C * (n - 1).choose (r - 1))
    (hSet : initialPolynomialFarSize n + 1 ≤
      D * (n - 1).choose (r - 1))
    (hRoot : m * (r * r) * (3 * 2 ^ 16 + 1) ≤
      initialPolynomialRoot n)
    (hSeparation : 16 * r * 2 ^ 16 <
      (initialPolynomialRoot n) ^ 4)
    (hCoeff : 2 * β * (r * C + D) ≤ m * α) :
    ∃ K : Family (Fin n), K ⊆ H ∧
      (∀ E ∈ K, Disjoint E X) ∧ Admissible K ∧ Uniform r K ∧
      (∀ j, 1 ≤ j → j ≤ r - 1 →
        ∀ S : Edge (Fin n), S.card = j →
          (K.filter (fun E => S ⊆ E)).card ≤
            initialPolynomialScale n * n ^ (r - j - 1)) ∧
      (H.filter (fun E => Disjoint E X)).card ≤ K.card +
        r * r * initialScaleMultiplier n (initialPolynomialScale n) *
          initialVertexCap r (initialPolynomialFarSize n) H.card ∧
      m * α * (n - 1).choose (r - 1) ≤
        2 * m * β * K.card := by
  classical
  let F₀ := H.filter (fun E => Disjoint E X)
  have hF₀H : F₀ ⊆ H := Finset.filter_subset _ _
  have hAdm₀ : Admissible F₀ := admissible_mono hF₀H hAdm
  have hUniform₀ : Uniform r F₀ := fun E hE => hUniform (hF₀H hE)
  have hMax₀ : ∀ z : Fin n,
      (F₀.filter (fun E => z ∈ E)).card ≤
        initialVertexCap r (initialPolynomialFarSize n) H.card :=
    avoiding_high_degree_cover_max_degree H X hOutside
  obtain ⟨hPos, hN, _⟩ := initial_polynomial_scale_bounds n hn
  obtain ⟨haT, haSq⟩ := initial_scale_multiplier_bounds n r
    (initialPolynomialScale n) hn hPos hN
    (initial_polynomial_scale_separation n r hn hSeparation)
  let a := initialScaleMultiplier n (initialPolynomialScale n)
  let T := initialVertexCap r (initialPolynomialFarSize n) H.card
  obtain ⟨K, hKF₀, hAdmK, hUniformK, hCaps, hLoss⟩ :=
    initial_codegree_cleanup_from_max_degree F₀
      (fun j => initialPolynomialScale n * n ^ (r - j - 1))
      (fun _ => a) hAdm₀ hUniform₀ hr hMax₀
      (by
        intro j hj hjr
        exact initial_sqrt_scale_gap n r j (initialPolynomialScale n)
          a hn hr hj hjr haT haSq)
  have hCover : F₀.card - K.card ≤ r * r * a * T :=
    hLoss.trans (Nat.mul_le_mul_right T
      (initial_cover_size_le_rank_square r a))
  have hKle : K.card ≤ F₀.card := Finset.card_le_card hKF₀
  have hCharge : m * (r * r * a * T) ≤
      (r * C + D) * (n - 1).choose (r - 1) :=
    initial_polynomial_cleanup_loss_rate n r m C D H.card hn
      hRoot hFamily hSet
  have hF₀Bound : F₀.card ≤ K.card + r * r * a * T := by omega
  have hTail' : α * (n - 1).choose (r - 1) ≤ β * F₀.card := hTail
  have hA := Nat.mul_le_mul_left m hTail'
  have hB := Nat.mul_le_mul_left (m * β) hF₀Bound
  have hC := Nat.mul_le_mul_left β hCharge
  have hD := Nat.mul_le_mul_right ((n - 1).choose (r - 1)) hCoeff
  have hAvoid : ∀ E ∈ K, Disjoint E X := by
    intro E hE
    exact (Finset.mem_filter.mp (hKF₀ hE)).2
  refine ⟨K, hKF₀.trans hF₀H, hAvoid,
    hAdmK, hUniformK, hCaps, hF₀Bound, ?_⟩
  nlinarith [hA, hB, hC, hD]

/-- The actual high-degree cover and polynomial-scale cleanup feed every
fixed finite number of natural regularization rounds. -/
theorem initial_polynomial_natural_iterate_from_actual_cover
    {n r M : ℕ} (steps : ℕ) (H : Family (Fin n))
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hn : 1 ≤ n) (hr : 4 ≤ r)
    (hMax : ∀ z : Fin n,
      (H.filter (fun E => z ∈ E)).card ≤ M)
    (hSeparation : 16 * r * 2 ^ 16 <
      (initialPolynomialRoot n) ^ 4)
    (hLarge : ∀ i < steps,
      (16 * (36 * r) ^ 3) ^ 8 ≤
        (discreteRoundIterate (initialPolynomialScale n) i) ^ 5) :
    ∃ X₀ : Edge (Fin n), ∃ K : Family (Fin n),
      X₀.card ≤ initialPolynomialFarSize n ∧
      K ⊆ H ∧ Admissible K ∧ Uniform r K ∧
      (∀ j, 1 ≤ j → j ≤ r - 1 →
        ∀ S : Edge (Fin n), S.card = j →
          (K.filter (fun E => S ⊆ E)).card ≤
            discreteRoundIterate (initialPolynomialScale n) steps *
              n ^ (r - j - 1)) ∧
      H.card ≤ K.card +
        farStarDeletion n r (initialPolynomialFarSize n) +
        ((farStarRadius r M + (r - 1)) * n.choose (r - 2)) / (r - 1) +
        (initialPolynomialFarSize n).choose 2 *
          (n - 2).choose (r - 2) +
        r * r * initialScaleMultiplier n (initialPolynomialScale n) *
          initialVertexCap r (initialPolynomialFarSize n) H.card +
        ∑ i ∈ Finset.range steps,
          discreteRoundAdditiveLoss n r
            (discreteRoundIterate (initialPolynomialScale n) i) := by
  obtain ⟨hPos, hN, hCube⟩ := initial_polynomial_scale_bounds n hn
  exact far_star_initial_natural_iterate_from_actual_cover steps H
    hAdm hUniform hn hr hMax hPos hN
    (initial_polynomial_scale_separation n r hn hSeparation)
    hCube hLarge

end JSP523.Rank5
