import JSP523.Rank5.FarStarTail

/-!
# Integer coefficients from a positive rational degree gap

The finite far-star theorem uses four fixed integers.  This module
constructs them from any rational bound `A/B < 1` on the maximum vertex
degree relative to the extremal star.
-/

namespace JSP523.Rank5

/-- A single elementary coefficient inequality used by the explicit
constant selection. -/
theorem far_star_collision_coefficient_square
    (c B k : ℕ) (hB : 1 ≤ B) (hk : 1 ≤ k) :
    c * (B * k) ≤ (c + 1) ^ 2 * (B * k) ^ 2 := by
  have hC : c ≤ (c + 1) ^ 2 := by nlinarith
  have hBK : 1 ≤ B * k := by nlinarith
  calc
    c * (B * k) ≤ (c + 1) ^ 2 * (B * k) :=
      Nat.mul_le_mul_right _ hC
    _ ≤ (c + 1) ^ 2 * (B * k) ^ 2 := by
      have hSq : B * k ≤ (B * k) ^ 2 :=
        le_self_pow hBK (by norm_num : 2 ≠ 0)
      exact Nat.mul_le_mul_left _ hSq

/-- Every strict rational gap `A/B < 1` admits fixed coefficients for the
finite positive-mass far-star theorem. The proof uses only integer
arithmetic and `power_gap_linear_bound`. -/
theorem exists_far_star_rational_coefficients
    (r k A B : ℕ) (hAB : A < B) (hk : 1 ≤ k) :
    ∃ p p' q s : ℕ,
      p < p' ∧ p' < q ∧
      A * q ^ k ≤ B * p ^ k ∧
      farStarCollisionConstant r * q ≤ s ^ 2 ∧
      2 * (s + 2) * (2 ^ k * k.factorial) ≤ q - p' := by
  let c := farStarCollisionConstant r
  let D := 2 ^ k * k.factorial
  let L := 4 * (c + 1) * B * k * D + 4 * D + 1
  let q := 4 * B * k * L ^ 2
  let d := (B - A) * L ^ 2
  let p := q - 2 * d
  let p' := q - d
  let s := 2 * (c + 1) * B * k * L
  have hB : 1 ≤ B := by omega
  have hBA : 1 ≤ B - A := by omega
  have hD : 1 ≤ D := by
    dsimp [D]
    have hTwo : 1 ≤ 2 ^ k := by exact Nat.one_le_pow _ _ (by norm_num)
    have hFact : 1 ≤ k.factorial := Nat.factorial_pos k
    nlinarith
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hLbase : 4 * (c + 1) * B * k * D + 4 * D ≤ L := by
    dsimp [L]
    omega
  have hq : 2 * d ≤ q := by
    dsimp [d, q]
    have hSub : B - A ≤ B := Nat.sub_le B A
    have hCoef : 2 * (B - A) ≤ 4 * B * k := by nlinarith [hSub, hk]
    have hMul := Nat.mul_le_mul_right (L ^ 2) hCoef
    nlinarith
  have hMargin : 2 * B * k * d ≤ (B - A) * q := by
    have hCoef : 2 * B * k ≤ 4 * B * k := by nlinarith
    have hMul := Nat.mul_le_mul_right ((B - A) * L ^ 2) hCoef
    dsimp [d, q]
    nlinarith
  have hPower : A * q ^ k ≤ B * p ^ k := by
    exact rational_power_gap A B k q d hAB.le hk hq hMargin
  have hdPos : 0 < d := by
    dsimp [d]
    have hLpos : 0 < L := by omega
    exact Nat.mul_pos (by omega) (pow_pos hLpos _)
  have hp' : p < p' := by
    dsimp [p, p']
    omega
  have hp'q : p' < q := by
    dsimp [p']
    omega
  have hCollision : farStarCollisionConstant r * q ≤ s ^ 2 := by
    have hCoeff := far_star_collision_coefficient_square c B k hB hk
    dsimp [c, q, s] at *
    have hScaled := Nat.mul_le_mul_left (4 * L ^ 2) hCoeff
    nlinarith
  have hError : 2 * (s + 2) * D ≤ d := by
    have hLsq : 4 * (c + 1) * B * k * D * L + 4 * D ≤ L ^ 2 := by
      have hMul := Nat.mul_le_mul_right L hLbase
      nlinarith [hMul, hL]
    have hdL : L ^ 2 ≤ d := by
      dsimp [d]
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right (L ^ 2) hBA
    dsimp [s]
    nlinarith
  have hDiff : q - p' = d := by
    dsimp [p']
    omega
  exact ⟨p, p', q, s, hp', hp'q, hPower, hCollision,
    by simpa only [hDiff] using hError⟩

/-- Any fixed positive real degree gap admits an integer rational gap
valid uniformly for every pair of natural cardinalities. -/
theorem exists_integer_degree_gap_of_real_gap
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ A B : ℕ, A < B ∧
      ∀ m t : ℕ, (m : ℝ) ≤ (1 - δ) * (t : ℝ) →
        B * m ≤ A * t := by
  obtain ⟨B, hBgt⟩ := exists_nat_gt ((1 : ℝ) / δ)
  have hBpos : 1 ≤ B := by
    have hDivNonneg : (0 : ℝ) ≤ 1 / δ := by positivity
    have hCast : (0 : ℝ) < B := lt_of_le_of_lt hDivNonneg hBgt
    exact_mod_cast hCast
  let A := B - 1
  have hAB : A < B := by dsimp [A]; omega
  have hBδ : (1 : ℝ) ≤ (B : ℝ) * δ := by
    have h := (div_lt_iff₀ hδ).mp hBgt
    nlinarith
  refine ⟨A, B, hAB, ?_⟩
  intro m t hm
  have hCoef : (B : ℝ) * (1 - δ) ≤ (B : ℝ) - 1 := by
    nlinarith [hBδ]
  have hFirst : (B : ℝ) * (m : ℝ) ≤
      (B : ℝ) * ((1 - δ) * (t : ℝ)) :=
    mul_le_mul_of_nonneg_left hm (by positivity)
  have hSecond : ((B : ℝ) * (1 - δ)) * (t : ℝ) ≤
      ((B : ℝ) - 1) * (t : ℝ) :=
    mul_le_mul_of_nonneg_right hCoef (by positivity)
  have hCastA : (A : ℝ) = (B : ℝ) - 1 := by
    dsimp [A]
    rw [Nat.cast_sub hBpos]
    norm_num
  have hReal : (B : ℝ) * (m : ℝ) ≤ (A : ℝ) * (t : ℝ) := by
    rw [hCastA]
    calc
      _ ≤ (B : ℝ) * ((1 - δ) * (t : ℝ)) := hFirst
      _ = ((B : ℝ) * (1 - δ)) * (t : ℝ) := by ring
      _ ≤ ((B : ℝ) - 1) * (t : ℝ) := hSecond
  exact_mod_cast hReal

end JSP523.Rank5
