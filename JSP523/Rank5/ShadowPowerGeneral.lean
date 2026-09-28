import Mathlib.Combinatorics.SetFamily.KruskalKatona
import Mathlib.Tactic

/-!
# Lovasz-threshold case of the sharp shadow-power bound

This records a rigorous all-ranks consequence of Mathlib's Lovasz form of
Kruskal--Katona. It establishes IV.3.1 when the family size is exactly a
binomial threshold. The remaining arbitrary-size interpolation is discussed
in the accompanying task report.
-/

namespace JSP523.Rank5

open Finset

/-- At a binomial threshold, the factorial-normalized powers have the
required ordering. -/
theorem factorial_choose_power_threshold {m k : ℕ}
    (hk : 2 ≤ k) (hkm : k ≤ m) :
    (k.factorial * m.choose k) ^ (k - 1) ≤
      ((k - 1).factorial * m.choose (k - 1)) ^ k := by
  rw [← Nat.descFactorial_eq_factorial_mul_choose,
    ← Nat.descFactorial_eq_factorial_mul_choose]
  have hkpos : 1 ≤ k := by omega
  have hstep : m.descFactorial k =
      (m - k + 1) * m.descFactorial (k - 1) := by
    have h := Nat.descFactorial_succ m (k - 1)
    have heq : k - 1 + 1 = k := by omega
    have hfac : m - (k - 1) = m - k + 1 := by omega
    rw [heq, hfac] at h
    exact h
  have hbase : (m - k + 1) ^ (k - 1) ≤ m.descFactorial (k - 1) := by
    have harg : m - k + 1 ≤ m + 1 - (k - 1) := by omega
    calc
      (m - k + 1) ^ (k - 1) ≤ (m + 1 - (k - 1)) ^ (k - 1) :=
        Nat.pow_le_pow_left harg _
      _ ≤ m.descFactorial (k - 1) := Nat.pow_sub_le_descFactorial m _
  rw [hstep]
  calc
    ((m - k + 1) * m.descFactorial (k - 1)) ^ (k - 1)
        = (m - k + 1) ^ (k - 1) *
            m.descFactorial (k - 1) ^ (k - 1) := Nat.mul_pow ..
    _ ≤ m.descFactorial (k - 1) *
          m.descFactorial (k - 1) ^ (k - 1) :=
      Nat.mul_le_mul_right _ hbase
    _ = m.descFactorial (k - 1) ^ k := by
      rw [Nat.mul_comm, ← pow_succ, Nat.sub_add_cancel hkpos]

/-- Sharp shadow-power inequality when the size is exactly `choose m k`.
The family is a finite family of `k`-subsets of `Fin n`. -/
theorem shadow_power_at_binomial_threshold
    {n m k : ℕ} (A : Finset (Finset (Fin n)))
    (hSized : (A : Set (Finset (Fin n))).Sized k)
    (hk : 2 ≤ k) (hkm : k ≤ m) (hmn : m ≤ n)
    (hCard : A.card = Nat.choose m k) :
    (k.factorial * A.card) ^ (k - 1) ≤
      ((k - 1).factorial * (Finset.shadow A).card) ^ k := by
  have hShadow :=
      kruskal_katona_lovasz_form (𝒜 := A) (i := 1) (r := k) (k := m)
      (by omega) hkm hmn hSized (by rw [hCard])
  have hArith := factorial_choose_power_threshold hk hkm
  calc
    (k.factorial * A.card) ^ (k - 1) =
          (k.factorial * Nat.choose m k) ^ (k - 1) := by rw [hCard]
    _ ≤ ((k - 1).factorial * Nat.choose m (k - 1)) ^ k := hArith
    _ ≤ ((k - 1).factorial * (Finset.shadow A).card) ^ k :=
      Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hShadow) _

end JSP523.Rank5
