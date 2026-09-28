import JSP523.Rank5.FarStarTail
import JSP523.Rank5.FarStarConstants
import Mathlib.Analysis.Asymptotics.Basic
import Mathlib.Data.Nat.Log

set_option linter.style.haveILetI false

/-!
# Asymptotic small-set input for the finite far-star theorem

The finite positive-mass theorem needs `q h(n)^2 ≤ n` for each fixed
integer `q`. This module derives that condition directly from the
manuscript's `h(n)^2 = o(n)` assumption.
-/

namespace JSP523.Rank5

open Filter Asymptotics

/-- A little-o square-root removal scale satisfies every fixed finite
small-set condition used by the collision and multi-hit budgets. -/
theorem eventually_small_set_of_square_is_little_o
    (h : ℕ → ℕ) (q : ℕ)
    (hLittle : (fun n : ℕ => ((h n) ^ 2 : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ))) :
    ∀ᶠ n : ℕ in atTop, q * (h n) ^ 2 ≤ n := by
  have hc : (0 : ℝ) < (1 : ℝ) / (q + 1) := by positivity
  have hBound := hLittle.def hc
  filter_upwards [hBound] with n hn
  have hReal : (h n : ℝ) ^ 2 ≤
      (1 : ℝ) / (q + 1) * (n : ℝ) := by
    have hnNonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (h n : ℝ)),
      abs_of_nonneg hnNonneg] using hn
  have hMul := mul_le_mul_of_nonneg_left hReal
    (show (0 : ℝ) ≤ q + 1 by positivity)
  have hDiv : (q + 1 : ℝ) * ((1 : ℝ) / (q + 1) * (n : ℝ)) = n := by
    field_simp
  have hReal' : (q + 1 : ℝ) * (h n : ℝ) ^ 2 ≤ (n : ℝ) := by
    simpa only [hDiv] using hMul
  have hQle : (q : ℝ) ≤ q + 1 := by exact_mod_cast Nat.le_succ q
  have hCast : (q : ℝ) * (h n : ℝ) ^ 2 ≤ (n : ℝ) := by
    calc
      (q : ℝ) * (h n : ℝ) ^ 2 ≤
          (q + 1 : ℝ) * (h n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hQle (sq_nonneg _)
      _ ≤ (n : ℝ) := hReal'
  exact_mod_cast hCast

/-- A concrete integer version of the manuscript's initial removal size.
The base-two logarithm is interchangeable with the natural logarithm for
the required little-o scale. -/
def initialFarSetSize (n : ℕ) : ℕ :=
  Nat.nthRoot 2 n / Nat.log 2 n

/-- The concrete `⌊√n / log₂ n⌋` size satisfies every finite
`q h² ≤ n` condition eventually, with an explicit threshold `2^(q+1)`.
This is exactly the small-set input of the positive-mass theorem. -/
theorem eventually_initial_far_set_small (q : ℕ) :
    ∀ᶠ n : ℕ in atTop, q * initialFarSetSize n ^ 2 ≤ n := by
  let N := q + 1
  filter_upwards [eventually_ge_atTop (2 ^ N)] with n hn
  let L := Nat.log 2 n
  let S := Nat.nthRoot 2 n
  let H := initialFarSetSize n
  have hLog : N ≤ L := Nat.le_log_of_pow_le Nat.one_lt_two hn
  have hQL : q ≤ L ^ 2 := by
    have hLpos : 1 ≤ L := by dsimp [N] at hLog; omega
    have hqL : q ≤ L := by dsimp [N] at hLog; omega
    exact hqL.trans (le_self_pow hLpos (by norm_num : 2 ≠ 0))
  have hDiv : H * L ≤ S := by
    dsimp [H, L, S, initialFarSetSize]
    exact Nat.div_mul_le_self _ _
  have hSq : H ^ 2 * L ^ 2 ≤ S ^ 2 := by
    have hPow := Nat.pow_le_pow_left hDiv 2
    simpa only [mul_pow] using hPow
  have hRoot : S ^ 2 ≤ n := Nat.pow_nthRoot_le (Or.inl (by norm_num))
  change q * H ^ 2 ≤ n
  calc
    q * H ^ 2 ≤ L ^ 2 * H ^ 2 := Nat.mul_le_mul_right _ hQL
    _ = H ^ 2 * L ^ 2 := by ring
    _ ≤ S ^ 2 := hSq
    _ ≤ n := hRoot

/-- The concrete initial removal size is `o(√n)` in exactly the squared
form used by the finite far-star estimate. -/
theorem initial_far_set_square_is_little_o :
    (fun n : ℕ => ((initialFarSetSize n) ^ 2 : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ)) := by
  apply IsLittleO.of_bound
  intro c hc
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hc
  let q := m + 1
  have hq : (0 : ℝ) < (q : ℝ) := by positivity
  have hmq : (1 : ℝ) / q ≤ c := by simpa only [q, Nat.cast_add, Nat.cast_one] using hm.le
  have hSmall := eventually_initial_far_set_small q
  filter_upwards [hSmall] with n hn
  have hnReal : (q : ℝ) * (initialFarSetSize n : ℝ) ^ 2 ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hMain : (initialFarSetSize n : ℝ) ^ 2 ≤
      c * (n : ℝ) := by
    have hDiv : (initialFarSetSize n : ℝ) ^ 2 ≤ (n : ℝ) / q := by
      apply (le_div_iff₀ hq).2
      simpa only [mul_comm] using hnReal
    calc
      (initialFarSetSize n : ℝ) ^ 2 ≤ (n : ℝ) / q := hDiv
      _ = (1 / (q : ℝ)) * n := by ring
      _ ≤ c * n := mul_le_mul_of_nonneg_right hmq (by positivity)
  have hFNonneg : (0 : ℝ) ≤ (initialFarSetSize n : ℝ) ^ 2 := sq_nonneg _
  have hNNonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg hFNonneg,
    abs_of_nonneg hNNonneg] using hMain

/-- Uniform positive far-star mass for a sequence of actual families. The
degree gap is stated as an eventual rational inequality relative to the
extremal star; `h² = o(n)` automatically pays the collision and multi-hit
errors. The output has one fixed positive coefficient for every large `n`. -/
theorem eventually_far_star_positive_mass
    (r p p' q s : ℕ)
    (hr : 4 ≤ r) (hpp' : p < p') (hp'q : p' < q)
    (hCollisionCoeff : farStarCollisionConstant r * q ≤ s ^ 2)
    (hErrorCoeff : 2 * (s + 2) *
      (2 ^ (r - 1) * (r - 1).factorial) ≤ q - p')
    (H : ∀ n : ℕ, Family (Fin n))
    (X : ∀ n : ℕ, Edge (Fin n))
    (h M : ℕ → ℕ)
    (hAdm : ∀ n, Admissible (H n))
    (hUniform : ∀ n, Uniform r (H n))
    (hX : ∀ n, (X n).card ≤ h n)
    (hMax : ∀ n z, ((H n).filter (fun E => z ∈ E)).card ≤ M n)
    (hRatio : ∀ᶠ n : ℕ in atTop,
      q ^ (r - 1) * M n ≤ p ^ (r - 1) * (n - 1).choose (r - 1))
    (hMass : ∀ᶠ n : ℕ in atTop,
      (n - 1).choose (r - 1) ≤ (H n).card)
    (hLittle : (fun n : ℕ => ((h n) ^ 2 : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ))) :
    ∀ᶠ n : ℕ in atTop,
      (q - p') * (n - 1).choose (r - 1) ≤
        2 * q * ((H n).filter (fun E => Disjoint E (X n))).card := by
  let N := max (2 * (r - 1) + 1)
    (max q (q * r + 2 * p' * (r - 1)))
  have hSmall := eventually_small_set_of_square_is_little_o h q hLittle
  filter_upwards [eventually_ge_atTop N, hSmall, hRatio, hMass]
    with n hn hTiny hnRatio hnMass
  have hnLarge : 2 * (r - 1) + 1 ≤ n :=
    (le_max_left _ _).trans hn
  have hqN : q ≤ n :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hThresholdLower : q * r + 2 * p' * (r - 1) ≤ n :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hGap : 1 ≤ p' - p := by omega
  have hThreshold : q * r + 2 * p' * (r - 1) ≤
      (p' - p) * n := by
    exact hThresholdLower.trans
      (by simpa using Nat.mul_le_mul_right n hGap)
  have hQ : q ≤ n ^ (r - 1) :=
    hqN.trans (le_self_pow (by omega : 1 ≤ n)
      (by omega : r - 1 ≠ 0))
  have hDegree := far_star_degree_rate_of_star_ratio
    n (r - 1) (M n) p q hnRatio
  letI : Inhabited (Fin n) := ⟨⟨0, by omega⟩⟩
  exact finite_far_star_tail_positive_from_small_set (H n) (X n)
    (hAdm n) (hUniform n) hr hnLarge (hX n)
    (hMax n)
    hpp'.le hp'q hDegree hThreshold hnMass hTiny hQ
    hCollisionCoeff hErrorCoeff

/-- A fixed positive real gap in maximum degree gives a fixed positive
fraction of the extremal star in the far tail of the actual family. -/
theorem eventually_far_star_positive_mass_of_real_degree_gap
    (r : ℕ) (δ : ℝ) (hr : 4 ≤ r) (hδ : 0 < δ)
    (H : ∀ n : ℕ, Family (Fin n))
    (X : ∀ n : ℕ, Edge (Fin n))
    (h M : ℕ → ℕ)
    (hAdm : ∀ n, Admissible (H n))
    (hUniform : ∀ n, Uniform r (H n))
    (hX : ∀ n, (X n).card ≤ h n)
    (hMax : ∀ n z, ((H n).filter (fun E => z ∈ E)).card ≤ M n)
    (hDegree : ∀ᶠ n : ℕ in atTop,
      (M n : ℝ) ≤ (1 - δ) * ((n - 1).choose (r - 1) : ℝ))
    (hMass : ∀ᶠ n : ℕ in atTop,
      (n - 1).choose (r - 1) ≤ (H n).card)
    (hLittle : (fun n : ℕ => ((h n) ^ 2 : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ))) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      ∀ᶠ n : ℕ in atTop,
        a * (n - 1).choose (r - 1) ≤
          b * ((H n).filter (fun E => Disjoint E (X n))).card := by
  obtain ⟨A, B, hAB, hGap⟩ :=
    exists_integer_degree_gap_of_real_gap δ hδ
  obtain ⟨p, p', q, s, hpp', hp'q, hPower, hCollision, hError⟩ :=
    exists_far_star_rational_coefficients r (r - 1) A B hAB (by omega)
  have hBpos : 0 < B := by omega
  have hRatio : ∀ᶠ n : ℕ in atTop,
      q ^ (r - 1) * M n ≤
        p ^ (r - 1) * (n - 1).choose (r - 1) := by
    filter_upwards [hDegree] with n hn
    let t := (n - 1).choose (r - 1)
    have hBDegree : B * M n ≤ A * t := hGap (M n) t hn
    have hMul : B * (q ^ (r - 1) * M n) ≤
        B * (p ^ (r - 1) * t) := by
      calc
        B * (q ^ (r - 1) * M n) =
            q ^ (r - 1) * (B * M n) := by ring
        _ ≤ q ^ (r - 1) * (A * t) :=
          Nat.mul_le_mul_left _ hBDegree
        _ = (A * q ^ (r - 1)) * t := by ring
        _ ≤ (B * p ^ (r - 1)) * t :=
          Nat.mul_le_mul_right _ hPower
        _ = B * (p ^ (r - 1) * t) := by ring
    exact Nat.le_of_mul_le_mul_left hMul hBpos
  refine ⟨q - p', 2 * q, Nat.sub_pos_of_lt hp'q, ?_, ?_⟩
  · omega
  · exact eventually_far_star_positive_mass r p p' q s hr hpp' hp'q
      hCollision hError H X h M hAdm hUniform hX hMax hRatio hMass hLittle

end JSP523.Rank5
