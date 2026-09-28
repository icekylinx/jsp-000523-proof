import JSP523.Rank5.RegularizationNumerics

/-!
# Rounded natural-scale arithmetic for IV.4

The natural scale is `T = floor(R^(5/8))`, with `a` rounded upward from
`2n/T`.  The root inequalities are recorded explicitly.  The collision
budget follows from the finite large-scale condition `36*t*R ≤ T^2`;
this is the quantitative form of `T^2/R` tending to infinity for fixed rank.
-/

namespace JSP523.Rank5

/-- The binomial half-budget used in the matching count holds uniformly for
every rank parameter at least two. -/
theorem choose_half_budget (n t : ℕ) (ht : 2 ≤ t) :
    2 * n.choose t ≤ n ^ t := by
  have hfact : 2 ≤ t.factorial := by
    calc
      2 = Nat.factorial 2 := by norm_num [Nat.factorial]
      _ ≤ t.factorial := Nat.factorial_le ht
  have hdesc : n.descFactorial t ≤ n ^ t := Nat.descFactorial_le_pow n t
  have hchooseFact : n.choose t * t.factorial ≤ n ^ t := by
    calc
      n.choose t * t.factorial = t.factorial * n.choose t := Nat.mul_comm _ _
      _ = n.descFactorial t := (Nat.descFactorial_eq_factorial_mul_choose n t).symm
      _ ≤ n ^ t := hdesc
  have hmul : n.choose t * 2 ≤ n.choose t * t.factorial :=
    Nat.mul_le_mul_left (n.choose t) hfact
  omega

/-- The rounded value of `2n/T` is represented by the two adjacent integer
inequalities.  When `T ≤ n`, these imply `n ≤ a*T ≤ 3n`. -/
theorem rounded_multiplier_bounds
    (n T a : ℕ) (hT : T ≤ n)
    (haLower : 2 * n ≤ a * T)
    (haUpper : a * T ≤ 2 * n + T) :
    n ≤ a * T ∧ a * T ≤ 3 * n := by
  constructor <;> omega

/-- A concrete sufficiently-large threshold turns the upper rounding
inequality for `floor(R^(5/8))` into the separation `T^2 ≥ 36*t*R`.
The threshold is deliberately generous and elementary: if
`T ≥ 16*(36*t)^3`, then `T^2 ≥ 256*(36*t)^5`; the root rounding gives
`R^5 < (T+1)^8 ≤ 256*T^8`, which proves the claim after taking fifth powers.
-/
theorem rounded_root_scale_separation
    (R T t : ℕ)
    (ht : 2 ≤ t)
    (hRootHi : R ^ 5 < (T + 1) ^ 8)
    (hTLarge : 16 * (36 * t) ^ 3 ≤ T) :
    36 * t * R ≤ T ^ 2 := by
  have hthresholdpos : 0 < 16 * (36 * t) ^ 3 := by positivity
  have hTpos : 1 ≤ T := by omega
  have hTplus : T + 1 ≤ 2 * T := by omega
  have hRootBound : (T + 1) ^ 8 ≤ 256 * T ^ 8 := by
    calc
      (T + 1) ^ 8 ≤ (2 * T) ^ 8 := Nat.pow_le_pow_left hTplus 8
      _ = 256 * T ^ 8 := by rw [mul_pow]; norm_num
  have hLargeSq : 256 * (36 * t) ^ 5 ≤ T ^ 2 := by
    have h := Nat.pow_le_pow_left hTLarge 2
    have hK : 1 ≤ 36 * t := by omega
    have hKpow : (36 * t) ^ 5 ≤ (36 * t) ^ 6 := by
      calc
        (36 * t) ^ 5 = (36 * t) ^ 5 * 1 := by simp
        _ ≤ (36 * t) ^ 5 * (36 * t) := Nat.mul_le_mul_left _ hK
        _ = (36 * t) ^ 6 := by simp [pow_succ, Nat.mul_assoc]
    have hSquared : 256 * (36 * t) ^ 6 ≤ T ^ 2 := by
      simpa only [show (16 * (36 * t) ^ 3) ^ 2 = 256 * (36 * t) ^ 6 by ring] using h
    exact le_trans (Nat.mul_le_mul_left 256 hKpow) hSquared
  by_contra h
  have hlt : T ^ 2 < 36 * t * R := by omega
  have hpow : (T ^ 2) ^ 5 < (36 * t * R) ^ 5 :=
    Nat.pow_lt_pow_left hlt (by norm_num)
  have hpowT : (T ^ 2) ^ 5 = T ^ 10 := by
    rw [← pow_mul, show 2 * 5 = 10 by norm_num]
  have hpowKR : (36 * t * R) ^ 5 = (36 * t) ^ 5 * R ^ 5 := by ring
  have hlargeR : (36 * t) ^ 5 * R ^ 5 <
      (36 * t) ^ 5 * (T + 1) ^ 8 := by
    have hp : 0 < (36 * t) ^ 5 := by positivity
    exact (Nat.mul_lt_mul_left hp).2 hRootHi
  have hupper : (36 * t) ^ 5 * (T + 1) ^ 8 ≤ T ^ 10 := by
    calc
      (36 * t) ^ 5 * (T + 1) ^ 8 ≤ (36 * t) ^ 5 * (256 * T ^ 8) :=
        Nat.mul_le_mul_left _ hRootBound
      _ = 256 * (36 * t) ^ 5 * T ^ 8 := by ring
      _ ≤ T ^ 2 * T ^ 8 := Nat.mul_le_mul_right (T ^ 8) hLargeSq
      _ = T ^ 10 := by rw [← pow_add, show 2 + 8 = 10 by norm_num]
  have hcontr : T ^ 10 < T ^ 10 := by
    calc
      T ^ 10 = (T ^ 2) ^ 5 := hpowT.symm
      _ < (36 * t * R) ^ 5 := hpow
      _ = (36 * t) ^ 5 * R ^ 5 := hpowKR
      _ < (36 * t) ^ 5 * (T + 1) ^ 8 := hlargeR
      _ ≤ T ^ 10 := hupper
  exact (Nat.lt_irrefl _ hcontr)

/-- Convert the rounded multiplier and the explicit scale separation into
the collision inequality required by `heavy_root_gap_of_scale_parameters`.
-/
theorem rounded_collision_check
    (n t R T a : ℕ)
    (hn : 1 ≤ n) (_ht : 2 ≤ t)
    (hT : T ≤ n)
    (haLower : 2 * n ≤ a * T)
    (haUpper : a * T ≤ 2 * n + T)
    (hScale : 36 * t * R ≤ T ^ 2) :
    2 * a * a * t * R < n ^ 2 := by
  have ha := rounded_multiplier_bounds n T a hT haLower haUpper
  have hSquare : (a * T) ^ 2 ≤ (3 * n) ^ 2 := Nat.pow_le_pow_left ha.2 2
  have hCoef : 36 * a * a * t * R ≤ (a * T) ^ 2 := by
    calc
      36 * a * a * t * R = (a * a) * (36 * t * R) := by ring
      _ ≤ (a * a) * T ^ 2 := Nat.mul_le_mul_left (a * a) hScale
      _ = (a * T) ^ 2 := by ring
  have hBound : 36 * a * a * t * R ≤ 9 * n ^ 2 := by
    calc
      36 * a * a * t * R ≤ (a * T) ^ 2 := hCoef
      _ ≤ (3 * n) ^ 2 := hSquare
      _ = 9 * n ^ 2 := by ring
  nlinarith [hBound, hn]

/-- Apply the existing heavy-root estimate with rounded natural scales.
The hypotheses `hRootFloorLo` and `hRootFloorHi` identify the intended
integer rounding of `R^(5/8)`.  `hScale` is an explicit sufficient
large-`R` condition for its collision check.  The condition `R ≤ n^(2/3)`
is recorded as the cube inequality `R^3 ≤ n^2` and used to ensure `T ≤ n`.
-/
theorem heavy_root_gap_at_rounded_scale
    (n t R T a d D : ℕ)
    (ht : 2 ≤ t)
    (hN : 1 ≤ n)
    (hR23 : R ^ 3 ≤ n ^ 2)
    (_hRootFloorLo : T ^ 8 ≤ R ^ 5)
    (_hRootFloorHi : R ^ 5 < (T + 1) ^ 8)
    (hTleR : T ≤ R)
    (haLower : 2 * n ≤ a * T)
    (haUpper : a * T ≤ 2 * n + T)
    (hTLarge : 16 * (36 * t) ^ 3 ≤ T)
    (hd : T * n ^ (t - 1) ≤ d)
    (hD : D ≤ R * n ^ (t - 2)) :
    n.choose t + a * a * t * D < a * d := by
  have hRleN : R ≤ n := by
    by_contra h
    have hnr : n < R := by omega
    have hpow : n ^ 3 < R ^ 3 := Nat.pow_lt_pow_left hnr (by norm_num)
    have hn2 : n ^ 2 ≤ n ^ 3 := by
      have hmul : 1 ≤ n := hN
      nlinarith [sq_nonneg (n - 1)]
    omega
  have hTleN : T ≤ n := le_trans hTleR hRleN
  have hScale := rounded_root_scale_separation R T t ht _hRootFloorHi hTLarge
  have hCoef := rounded_collision_check n t R T a hN ht hTleN haLower haUpper hScale
  have hCoefStrict : 2 * a * a * t * R < n ^ 2 := hCoef
  have hOverlap : 2 * a * a * t * (R * n ^ (t - 2)) < n ^ t := by
    have hnpos : 0 < n := by omega
    have hmul := (Nat.mul_lt_mul_right (pow_pos hnpos (t - 2))).2 hCoefStrict
    have hexp : 2 + (t - 2) = t := by omega
    calc
      2 * a * a * t * (R * n ^ (t - 2))
          = (2 * a * a * t * R) * n ^ (t - 2) := by ring
      _ < n ^ 2 * n ^ (t - 2) := by simpa using hmul
      _ = n ^ t := by rw [← pow_add, hexp]
  exact heavy_root_gap_of_scale_parameters n t R T a d D ht
    (choose_half_budget n t ht) (by omega) hd hD hOverlap

end JSP523.Rank5
