import JSP523.Rank5.InitialCodegreeCleanup
import Mathlib.Analysis.Asymptotics.Basic

/-!
# Fixed-round natural regularization loss

The explicit finite loss bound becomes little-o of the extremal star for
any fixed number of natural rounds when the initial scale diverges and
obeys the manuscript's `R³ ≤ n²` upper bound.
-/

namespace JSP523.Rank5

open Filter Asymptotics

theorem tendsto_discrete_round_target_at_top :
    Tendsto discreteRoundTarget atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro m
  filter_upwards [eventually_ge_atTop (m ^ 2 + 1)] with R hR
  have hMR : m ^ 2 ≤ R := by omega
  have hRpos : 1 ≤ R := by omega
  have hSquare := Nat.pow_le_pow_left hMR 2
  have hRpow : R ^ 2 ≤ R ^ 3 := by
    calc
      R ^ 2 = R ^ 2 * 1 := by simp
      _ ≤ R ^ 2 * R := Nat.mul_le_mul_left _ hRpos
      _ = R ^ 3 := by ring
  have hPow : m ^ 4 ≤ R ^ 3 := by
    calc
      m ^ 4 = (m ^ 2) ^ 2 := by ring
      _ ≤ R ^ 2 := hSquare
      _ ≤ R ^ 3 := hRpow
  exact (Nat.le_nthRoot_iff (by norm_num : 4 ≠ 0)).2 hPow

theorem tendsto_discrete_round_iterate_at_top
    (R : ℕ → ℕ) (hR : Tendsto R atTop atTop) (t : ℕ) :
    Tendsto (fun n => discreteRoundIterate (R n) t) atTop atTop := by
  induction t with
  | zero => simpa only [discreteRoundIterate] using hR
  | succ t ih =>
      simpa only [discreteRoundIterate, Function.comp_def] using
        tendsto_discrete_round_target_at_top.comp ih

theorem eventually_all_discrete_round_iterates_large
    (R : ℕ → ℕ) (hR : Tendsto R atTop atTop)
    (steps threshold : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ i < steps, threshold ≤ discreteRoundIterate (R n) i := by
  have hEach : ∀ i ∈ Finset.range steps,
      ∀ᶠ n : ℕ in atTop,
        threshold ≤ discreteRoundIterate (R n) i := by
    intro i _
    exact (tendsto_discrete_round_iterate_at_top R hR i).eventually
      (eventually_ge_atTop threshold)
  have hAll := (Finset.eventually_all (Finset.range steps)).2 hEach
  filter_upwards [hAll] with n hn
  intro i hi
  exact hn i (Finset.mem_range.mpr hi)

/-- For fixed rank and a fixed number of rounds, the complete explicit
regularization loss is little-o of the extremal star. -/
theorem iterated_natural_loss_is_little_o
    (r steps : ℕ) (R : ℕ → ℕ) (hr : 4 ≤ r)
    (hR : Tendsto R atTop atTop)
    (hScale : ∀ᶠ n : ℕ in atTop, (R n) ^ 3 ≤ n ^ 2) :
    (fun n : ℕ =>
      (∑ i ∈ Finset.range steps,
        discreteRoundAdditiveLoss n r (discreteRoundIterate (R n) i) : ℝ))
      =o[atTop]
    (fun n : ℕ => ((n - 1).choose (r - 1) : ℝ)) := by
  apply IsLittleO.of_bound
  intro c hc
  let C := (6 * r ^ 3 + 2 + 9 * r ^ 4 + 2 * (r - 1)) *
    (2 ^ (r - 1) * (r - 1).factorial)
  obtain ⟨m, hmgt⟩ := exists_nat_gt ((steps * C : ℝ) / c)
  have hmpos : 0 < m := by
    have hq : (0 : ℝ) ≤ (steps * C : ℝ) / c := by positivity
    have hmreal : (0 : ℝ) < m := lt_of_le_of_lt hq hmgt
    exact_mod_cast hmreal
  have hCoeff : (steps * C : ℝ) ≤ c * (m : ℝ) := by
    have h := (div_lt_iff₀ hc).mp hmgt
    nlinarith
  let N := max (2 * (r - 1) + 1)
    (max ((m ^ (r - 1) * (r - 1).factorial) ^ 3) (m * r))
  have hLarge := eventually_all_discrete_round_iterates_large R hR
    steps ((4 * m ^ 2) ^ 4)
  filter_upwards [eventually_ge_atTop N, hScale, hLarge]
    with n hn hnScale hnLarge
  have hnStar : 2 * (r - 1) + 1 ≤ n :=
    (le_max_left _ _).trans hn
  have hnRadius : (m ^ (r - 1) * (r - 1).factorial) ^ 3 ≤ n :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hmn : m * r ≤ n :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hFinite := discrete_round_iterated_loss_star_rate n r (R n)
    steps m hr (by omega) hnStar hnScale hnLarge hnRadius hmn
  have hReal : (m : ℝ) *
      (∑ i ∈ Finset.range steps,
        discreteRoundAdditiveLoss n r (discreteRoundIterate (R n) i) : ℝ) ≤
        (steps * C : ℝ) * ((n - 1).choose (r - 1) : ℝ) := by
    exact_mod_cast hFinite
  have hStarNonneg : (0 : ℝ) ≤ ((n - 1).choose (r - 1) : ℝ) := by positivity
  have hReal' : (∑ i ∈ Finset.range steps,
      discreteRoundAdditiveLoss n r (discreteRoundIterate (R n) i) : ℝ) ≤
        c * ((n - 1).choose (r - 1) : ℝ) := by
    have hmreal : (0 : ℝ) < m := by exact_mod_cast hmpos
    apply le_of_mul_le_mul_left (a0 := hmreal)
    calc
      (m : ℝ) * (∑ i ∈ Finset.range steps,
          discreteRoundAdditiveLoss n r (discreteRoundIterate (R n) i) : ℝ) ≤
        (steps * C : ℝ) * ((n - 1).choose (r - 1) : ℝ) := hReal
      _ ≤ (c * (m : ℝ)) * ((n - 1).choose (r - 1) : ℝ) :=
        mul_le_mul_of_nonneg_right hCoeff hStarNonneg
      _ = (m : ℝ) * (c * ((n - 1).choose (r - 1) : ℝ)) := by ring
  have hSumNonneg : (0 : ℝ) ≤
      (∑ i ∈ Finset.range steps,
        discreteRoundAdditiveLoss n r (discreteRoundIterate (R n) i) : ℝ) := by
    positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg hSumNonneg,
    abs_of_nonneg hStarNonneg] using hReal'

end JSP523.Rank5
