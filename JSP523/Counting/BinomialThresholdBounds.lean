import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# Explicit fixed-rank binomial threshold estimates

These integer inequalities turn binomial incidence bounds into the
polynomial-scale estimates used in §IV.2. -/

namespace JSP523.Counting

/-- Clearing denominators in Mathlib's binomial lower bound. -/
theorem pow_sub_le_factorial_mul_choose (n t : ℕ) :
    (n + 1 - t) ^ t ≤ t.factorial * n.choose t := by
  have hq := Nat.pow_le_choose (α := ℚ) t n
  have hf : (0 : ℚ) < (t.factorial : ℚ) := by exact_mod_cast Nat.factorial_pos t
  rw [div_le_iff₀ hf] at hq
  have hNat : (n + 1 - t) ^ t ≤ n.choose t * t.factorial := by
    exact_mod_cast hq
  simpa [Nat.mul_comm] using hNat

/-- The standard elementary upper bound for a binomial coefficient. -/
theorem choose_le_ground_power (w t : ℕ) : w.choose t ≤ w ^ t :=
  Nat.choose_le_pow w t

/-- For fixed rank parameters, a binomial coefficient with a linear-size
top argument dominates the corresponding power of the ambient size. The
constant is explicit and intentionally coarse. -/
theorem fixed_rank_choose_lower_bound
    (r k w : ℕ) (hr : 3 ≤ r) (hk₁ : 1 ≤ k) (hk₂ : k ≤ r - 2)
    (hw : 4 * r ≤ w) :
    w ^ (r - 1 - k) ≤
      (4 * r) ^ (r - 1) * (w - r - k).choose (r - 1 - k) := by
  let t := r - 1 - k
  let n := w - r - k
  have htpos : 1 ≤ t := by dsimp [t]; omega
  have htr : t ≤ r - 1 := by dsimp [t]; omega
  have htn : t ≤ n := by dsimp [t, n]; omega
  have hTop : w ≤ 2 * (n + 1 - t) := by
    dsimp [n, t]
    omega
  have hChoose := pow_sub_le_factorial_mul_choose n t
  have hFactor : 2 ^ t * t.factorial ≤ (4 * r) ^ (r - 1) := by
    calc
      2 ^ t * t.factorial ≤ 2 ^ t * t ^ t :=
        Nat.mul_le_mul_left _ (Nat.factorial_le_pow t)
      _ = (2 * t) ^ t := by rw [Nat.mul_pow]
      _ ≤ (4 * r) ^ t := pow_le_pow_left' (by omega) t
      _ ≤ (4 * r) ^ (r - 1) :=
        pow_le_pow_right' (by omega) htr
  calc
    w ^ t ≤ (2 * (n + 1 - t)) ^ t := pow_le_pow_left' hTop t
    _ = 2 ^ t * (n + 1 - t) ^ t := by rw [Nat.mul_pow]
    _ ≤ 2 ^ t * (t.factorial * n.choose t) :=
      Nat.mul_le_mul_left _ hChoose
    _ = (2 ^ t * t.factorial) * n.choose t := by ac_rfl
    _ ≤ (4 * r) ^ (r - 1) * n.choose t :=
      Nat.mul_le_mul_right _ hFactor
    _ = (4 * r) ^ (r - 1) * (w - r - k).choose (r - 1 - k) := by
      simp [n, t]

/-- A telescoping Pascal bound: lowering the top argument by `d` changes a
binomial coefficient by at most `d * n^(t-1)`. -/
theorem choose_drop_difference_le
    (n t d : ℕ) (ht : 1 ≤ t) (hd : d ≤ n) :
    n.choose t - (n - d).choose t ≤ d * n ^ (t - 1) := by
  induction d generalizing n with
  | zero =>
      simp
  | succ d ih =>
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      have hdm : d ≤ m := by omega
      have ht' : t - 1 + 1 = t := Nat.sub_add_cancel ht
      have hPascal : (m + 1).choose t =
          m.choose t + m.choose (t - 1) := by
        calc
          (m + 1).choose t = (m + 1).choose (t - 1 + 1) := by rw [ht']
          _ = m.choose (t - 1) + m.choose (t - 1 + 1) :=
            Nat.choose_succ_succ' m (t - 1)
          _ = m.choose t + m.choose (t - 1) := by rw [ht']; exact Nat.add_comm _ _
      have hmono : (m - d).choose t ≤ m.choose t :=
        Nat.choose_le_choose t (Nat.sub_le _ _)
      have hSplit : (m + 1).choose t - (m - d).choose t =
          (m.choose t - (m - d).choose t) + m.choose (t - 1) := by
        rw [hPascal]
        omega
      have hSub : m + 1 - (d + 1) = m - d := by omega
      have hIH := ih m hdm
      have hSmall : m.choose (t - 1) ≤ m ^ (t - 1) :=
        Nat.choose_le_pow m (t - 1)
      have hPow : m ^ (t - 1) ≤ (m + 1) ^ (t - 1) :=
        pow_le_pow_left' (by omega) (t - 1)
      rw [hSub]
      calc
        (m + 1).choose t - (m - d).choose t =
            (m.choose t - (m - d).choose t) + m.choose (t - 1) := hSplit
        _ ≤ d * m ^ (t - 1) + m.choose (t - 1) :=
          Nat.add_le_add_right hIH _
        _ ≤ d * m ^ (t - 1) + m ^ (t - 1) :=
          Nat.add_le_add_left hSmall _
        _ = (d + 1) * m ^ (t - 1) := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ (d + 1) * (m + 1) ^ (t - 1) := Nat.mul_le_mul_left _ hPow

/-- Explicit form of the difference estimate for the binomial thresholds
in (IV.2.2): for `r ≥ 5` and `w ≥ 4r`,
`choose(w,r-2) - choose(w-r-1,r-2) ≤ (r+1)w^(r-3)`. -/
theorem iv22_delta_binomial_bound
    (r w : ℕ) (hr : 5 ≤ r) (hw : 4 * r ≤ w) :
    w.choose (r - 2) - (w - r - 1).choose (r - 2) ≤
      (r + 1) * w ^ (r - 3) := by
  have hGap := choose_drop_difference_le w (r - 2) (r + 1)
    (by omega) (by omega)
  have hTop : w - (r + 1) = w - r - 1 := by omega
  have hExp : (r - 2) - 1 = r - 3 := by omega
  simpa [hTop, hExp] using hGap

end JSP523.Counting
