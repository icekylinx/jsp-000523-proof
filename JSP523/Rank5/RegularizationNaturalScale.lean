import JSP523.Rank5.RegularizationScaleClose
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-!
# Concrete natural-number scale choices for IV.4

The manuscript uses `T = R^(5/8)` and `a` of order `2n/T`.  Here the choices
are actual natural numbers: `T = Nat.nthRoot 8 (R^5)` and
`a = 2*n/T + 1`.  The explicit large-scale condition is intentionally
generous; it makes all root-rounding inequalities and the heavy-root gap
available with no real-power rounding assumptions.
-/

namespace JSP523.Rank5

/-- The eighth-root floor of `R^5` obeys both defining inequalities, is no
larger than `R`, and exceeds the explicit large-scale threshold. -/
theorem natural_root_rounding
    (R t : ℕ)
    (ht : 2 ≤ t)
    (hLarge : (16 * (36 * t) ^ 3) ^ 8 ≤ R ^ 5) :
    let T := Nat.nthRoot 8 (R ^ 5)
    T ^ 8 ≤ R ^ 5 ∧ R ^ 5 < (T + 1) ^ 8 ∧
      T ≤ R ∧ 16 * (36 * t) ^ 3 ≤ T := by
  dsimp
  let T := Nat.nthRoot 8 (R ^ 5)
  have htpos : 0 < t := by omega
  have hThresholdPos : 0 < 16 * (36 * t) ^ 3 := by positivity
  have hRpos : 0 < R := by
    by_contra h
    have hR0 : R = 0 := by omega
    simp [hR0] at hLarge
    omega
  have hLo : T ^ 8 ≤ R ^ 5 := Nat.pow_nthRoot_le (Or.inl (by norm_num))
  have hHi : R ^ 5 < (T + 1) ^ 8 := Nat.lt_pow_nthRoot_add_one (by norm_num) _
  have hRpow : R ^ 5 ≤ R ^ 8 := by
    have hR3 : 1 ≤ R ^ 3 := by
      have h : 0 < R ^ 3 := pow_pos hRpos _
      omega
    calc
      R ^ 5 = R ^ 5 * 1 := by simp
      _ ≤ R ^ 5 * R ^ 3 := Nat.mul_le_mul_left _ hR3
      _ = R ^ 8 := by rw [← pow_add, show 5 + 3 = 8 by norm_num]
  have hRLt : R ^ 5 < (R + 1) ^ 8 :=
    hRpow.trans_lt (Nat.pow_lt_pow_left (by omega) (by norm_num))
  have hTleR : T ≤ R := by
    have h : T < R + 1 :=
      (Nat.nthRoot_lt_iff (by norm_num : 8 ≠ 0)).2 hRLt
    omega
  have hTLarge : 16 * (36 * t) ^ 3 ≤ T :=
    (Nat.le_nthRoot_iff (by norm_num : 8 ≠ 0)).2 hLarge
  exact ⟨hLo, hHi, hTleR, hTLarge⟩

/-- Round `2n/T` upward by one integer step. The two inequalities used in
the heavy-root calculation are exact, including the divisible case. -/
theorem rounded_multiplier_exists (n T : ℕ) (hT : 0 < T) :
    ∃ a : ℕ, 2 * n ≤ a * T ∧ a * T ≤ 2 * n + T := by
  refine ⟨2 * n / T + 1, ?_⟩
  have hDiv : (2 * n) % T + T * (2 * n / T) = 2 * n :=
    Nat.mod_add_div (2 * n) T
  rw [Nat.mul_comm T (2 * n / T)] at hDiv
  have hMod : (2 * n) % T < T := Nat.mod_lt _ hT
  constructor
  · simp only [add_mul, one_mul]
    omega
  · simp only [add_mul, one_mul]
    omega

/-- The concrete natural scale and rounded multiplier satisfy the exact
heavy-root numerical gap, provided the same parent codegree hypotheses as
in IV.4 and a finite explicit lower bound on `R`. -/
theorem exists_heavy_root_gap_at_natural_scale
    (n t R : ℕ)
    (ht : 2 ≤ t) (hn : 1 ≤ n)
    (hR23 : R ^ 3 ≤ n ^ 2)
    (hLarge : (16 * (36 * t) ^ 3) ^ 8 ≤ R ^ 5) :
    ∃ T a : ℕ,
      T = Nat.nthRoot 8 (R ^ 5) ∧
      2 * n ≤ a * T ∧ a * T ≤ 2 * n + T ∧
      (∀ d D : ℕ,
        T * n ^ (t - 1) ≤ d → D ≤ R * n ^ (t - 2) →
        n.choose t + a * a * t * D < a * d) := by
  let T := Nat.nthRoot 8 (R ^ 5)
  obtain ⟨hRootLo, hRootHi, hTleR, hTLarge⟩ :=
    natural_root_rounding R t ht hLarge
  have hTpos : 0 < T := by
    have hThresholdPos : 0 < 16 * (36 * t) ^ 3 := by positivity
    omega
  obtain ⟨a, haLo, haHi⟩ := rounded_multiplier_exists n T hTpos
  refine ⟨T, a, rfl, haLo, haHi, ?_⟩
  intro d D hd hD
  exact heavy_root_gap_at_rounded_scale n t R T a d D
    ht hn hR23 hRootLo hRootHi hTleR haLo haHi hTLarge hd hD

end JSP523.Rank5
