import JSP523.Rank5.ShadowBinomialBracket
import Mathlib.Combinatorics.SetFamily.KruskalKatona
import Mathlib.Tactic

/-!
# Binomial-threshold and finite-error shadow-power bounds

The threshold case follows from the integer Lovasz form of
Kruskal--Katona. A finite-error estimate also covers arbitrary family sizes.
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

/-- One Pascal step gives a lower-order error at the actual binomial
radius `m`, independent of the ambient ground size. -/
theorem shadow_power_with_radius_error
    {n m k : ℕ} (A : Finset (Finset (Fin n)))
    (hSized : (A : Set (Finset (Fin n))).Sized k)
    (hk : 2 ≤ k) (hkm : k ≤ m) (hmn : m + 1 ≤ n)
    (hBelow : m.choose k ≤ A.card)
    (hAbove : A.card ≤ (m + 1).choose k) :
    (k.factorial * A.card) ^ (k - 1) ≤
      ((k - 1).factorial *
        ((Finset.shadow A).card + m.choose (k - 2))) ^ k := by
  have hShadow : m.choose (k - 1) ≤ (Finset.shadow A).card := by
    exact shadow_card_ge_choose_threshold A hSized hk hkm
      (by omega) hBelow
  have hPascal : (m + 1).choose (k - 1) =
      m.choose (k - 2) + m.choose (k - 1) := by
    have hk' : k - 2 + 1 = k - 1 := by omega
    simpa [hk', Nat.add_comm] using Nat.choose_succ_succ' m (k - 2)
  have hShadowBound : (m + 1).choose (k - 1) ≤
      (Finset.shadow A).card + m.choose (k - 2) := by
    rw [hPascal]
    omega
  have hThreshold := factorial_choose_power_threshold hk
    (show k ≤ m + 1 by omega)
  calc
    (k.factorial * A.card) ^ (k - 1) ≤
        (k.factorial * (m + 1).choose k) ^ (k - 1) :=
      Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hAbove) _
    _ ≤ ((k - 1).factorial * (m + 1).choose (k - 1)) ^ k := hThreshold
    _ ≤ ((k - 1).factorial *
        ((Finset.shadow A).card + m.choose (k - 2))) ^ k :=
      Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hShadowBound) _

/-- Every nonempty uniform family admits a binomial radius with the
finite-error shadow-power estimate. -/
theorem exists_shadow_power_radius_error
    {n k : ℕ} (A : Finset (Finset (Fin n)))
    (hSized : (A : Set (Finset (Fin n))).Sized k)
    (hk : 2 ≤ k) (hNonempty : A.Nonempty) :
    ∃ m : ℕ, k ≤ m ∧ m ≤ n ∧
    (k.factorial * A.card) ^ (k - 1) ≤
      ((k - 1).factorial *
        ((Finset.shadow A).card + m.choose (k - 2))) ^ k := by
  classical
  obtain ⟨m, hkm, hmN, hBelow, hAbove⟩ :=
    exists_binomial_card_bracket A hSized hNonempty
  have hSupport : A ⊆ (Finset.univ : Finset (Fin n)).powersetCard k := by
    intro F hF
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ F, hSized hF⟩
  have hCardMax : A.card ≤ n.choose k := by
    have h := Finset.card_le_card hSupport
    simpa [Finset.card_powersetCard] using h
  refine ⟨m, hkm, hmN, ?_⟩
  by_cases hTop : m = n
  · have hEq : A.card = n.choose k := by
      rw [hTop] at hBelow
      omega
    have hkN : k ≤ n := by omega
    have hExact := shadow_power_at_binomial_threshold A hSized hk
      hkN (le_refl n) hEq
    have hExtra : (Finset.shadow A).card ≤
        (Finset.shadow A).card + m.choose (k - 2) := Nat.le_add_right ..
    exact hExact.trans
      (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hExtra) _)
  · have hmn : m + 1 ≤ n := by omega
    exact shadow_power_with_radius_error A hSized hk hkm
      hmn hBelow hAbove

/-- The ambient form follows by comparing the radius to `n`. -/
theorem shadow_power_all_sizes_with_lower_order_error
    {n k : ℕ} (A : Finset (Finset (Fin n)))
    (hSized : (A : Set (Finset (Fin n))).Sized k)
    (hk : 2 ≤ k) :
    (k.factorial * A.card) ^ (k - 1) ≤
      ((k - 1).factorial *
        ((Finset.shadow A).card + n.choose (k - 2))) ^ k := by
  classical
  by_cases hEmpty : A = ∅
  · have hExp : 0 < k - 1 := by omega
    simp [hEmpty, hExp]
  obtain ⟨m, _, hmN, hBound⟩ :=
    exists_shadow_power_radius_error A hSized hk
      (Finset.nonempty_iff_ne_empty.mpr hEmpty)
  have hChoose : m.choose (k - 2) ≤ n.choose (k - 2) :=
    Nat.choose_le_choose (k - 2) hmN
  exact hBound.trans
    (Nat.pow_le_pow_left
      (Nat.mul_le_mul_left _ (Nat.add_le_add_left hChoose _)) _)

end JSP523.Rank5
