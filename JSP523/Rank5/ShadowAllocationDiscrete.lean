import JSP523.Rank5.ShadowPower
import JSP523.Rank5.ShadowPowerGeneral
import Mathlib.Tactic

/-!
# A near-sharp allocation bound without real-parameter interpolation

The extra `k` in the radius below is intentional.  This is an all-size
consequence of the existing integer Kruskal--Katona API, not a claim of
having proved the exact shadow-power inequality.  It avoids a lower-size
hypothesis on each nonempty link and is sufficient for the leading-order
star-allocation estimate after the additive error has been accounted for.
-/

namespace JSP523.Rank5

open Finset
open scoped BigOperators

/-- A largest integer binomial threshold below a nonempty uniform family.
The upper endpoint is allowed to exceed the ambient size by one. -/
theorem exists_binomial_card_bracket
    {n k : ℕ} (A : Family (Fin n)) (hUniform : Uniform k A)
    (hA : A.Nonempty) :
    ∃ t : ℕ, k ≤ t ∧ t ≤ n ∧
      t.choose k ≤ A.card ∧ A.card ≤ (t + 1).choose k := by
  classical
  obtain ⟨E, hE⟩ := hA
  have hkn : k ≤ n := by
    have hEcard := hUniform hE
    have hEbound := Finset.card_le_card (Finset.subset_univ E)
    simpa only [Finset.card_univ, Fintype.card_fin, hEcard] using hEbound
  have hApos : 1 ≤ A.card := by
    have := Finset.card_pos.mpr ⟨E, hE⟩
    omega
  let S := (Finset.range (n + 1)).filter
    (fun t => k ≤ t ∧ t.choose k ≤ A.card)
  have hkS : k ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega), le_rfl, ?_⟩
    simpa only [Nat.choose_self] using hApos
  obtain ⟨t, htS, htmax⟩ :=
    Finset.exists_max_image S (fun t : ℕ => t) ⟨k, hkS⟩
  have ht := Finset.mem_filter.mp htS
  have htn : t ≤ n := by
    have := Finset.mem_range.mp ht.1
    omega
  refine ⟨t, ht.2.1, htn, ht.2.2, ?_⟩
  by_cases htn' : t < n
  · have hnot : ¬ (t + 1).choose k ≤ A.card := by
      intro hnext
      have hnextS : t + 1 ∈ S := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_range.mpr (by omega), by omega, hnext⟩
      have := htmax (t + 1) hnextS
      omega
    omega
  · have hteq : t = n := by omega
    have hSub : A ⊆ (Finset.univ : Finset (Fin n)).powersetCard k := by
      intro T hT
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hUniform hT⟩
    have hBound : A.card ≤ n.choose k := by
      simpa only [Finset.card_powersetCard, Finset.card_univ,
        Fintype.card_fin] using Finset.card_le_card hSub
    exact hBound.trans (Nat.choose_le_choose k (by omega))

/-- The integer binomial radius is at most `L + k - 1` when the
factorial-normalized family size is at most `L ^ k`. -/
theorem binomial_radius_le
    {k t m L : ℕ} (hk : 1 ≤ k) (hkt : k ≤ t)
    (hLower : t.choose k ≤ m) (hSize : k.factorial * m ≤ L ^ k) :
    t + 1 ≤ L + k := by
  have hPower : (t + 1 - k) ^ k ≤ L ^ k := by
    calc
      (t + 1 - k) ^ k ≤ t.descFactorial k :=
        Nat.pow_sub_le_descFactorial t k
      _ = k.factorial * t.choose k :=
        Nat.descFactorial_eq_factorial_mul_choose t k
      _ ≤ k.factorial * m := Nat.mul_le_mul_left _ hLower
      _ ≤ L ^ k := hSize
  have hRadius : t + 1 - k ≤ L := by
    by_contra h
    have hlt : L < t + 1 - k := by omega
    have hPowLt : L ^ k < (t + 1 - k) ^ k :=
      Nat.pow_lt_pow_left hlt (by omega)
    omega
  omega

/-- All-size shadow allocation in division-free form.  The only size
hypothesis is an upper bound; empty and small links are included. -/
theorem uniform_card_le_shadow_radius
    {n k L : ℕ} (A : Family (Fin n)) (hUniform : Uniform k A)
    (hk : 2 ≤ k) (hSize : k.factorial * A.card ≤ L ^ k) :
    k * A.card ≤ (L + k) * (Finset.shadow A).card := by
  classical
  by_cases hA : A.Nonempty
  · obtain ⟨t, hkt, htn, hLower, hUpper⟩ :=
      exists_binomial_card_bracket A hUniform hA
    have hShadow := Rank5.shadow_card_ge_choose_threshold A hUniform
      hk hkt htn hLower
    have hRadius := binomial_radius_le (by omega : 1 ≤ k) hkt hLower hSize
    have hChoose : k * (t + 1).choose k =
        (t + 1) * t.choose (k - 1) := by
      have h := Nat.add_one_mul_choose_eq t (k - 1)
      have hkstep : k - 1 + 1 = k := by omega
      rw [hkstep] at h
      simpa only [Nat.mul_comm] using h.symm
    calc
      k * A.card ≤ k * (t + 1).choose k := Nat.mul_le_mul_left _ hUpper
      _ = (t + 1) * t.choose (k - 1) := hChoose
      _ ≤ (L + k) * t.choose (k - 1) := Nat.mul_le_mul_right _ hRadius
      _ ≤ (L + k) * (Finset.shadow A).card :=
        Nat.mul_le_mul_left _ hShadow
  · have hEmpty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    simp only [hEmpty, Finset.card_empty, Nat.mul_zero, Nat.zero_le]

/-- Disjoint immediate shadows occupy at most the ambient shadow layer. -/
theorem sum_disjoint_shadow_card_le
    {ι : Type*} [DecidableEq ι] {n k : ℕ}
    (I : Finset ι) (A : ι → Family (Fin n))
    (hUniform : ∀ i ∈ I, Uniform k (A i))
    (hDisjoint : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint (Finset.shadow (A i)) (Finset.shadow (A j))) :
    (∑ i ∈ I, (Finset.shadow (A i)).card) ≤ n.choose (k - 1) := by
  classical
  let sh : ι → Family (Fin n) := fun i => Finset.shadow (A i)
  have hPair : (I : Set ι).PairwiseDisjoint sh := by
    intro i hi j hj hij
    exact hDisjoint i hi j hj hij
  have hUnionSub : I.biUnion sh ⊆
      (Finset.univ : Finset (Fin n)).powersetCard (k - 1) := by
    intro S hS
    obtain ⟨i, hi, hSi⟩ := Finset.mem_biUnion.mp hS
    obtain ⟨T, hT, x, hx, hErase⟩ := Finset.mem_shadow_iff.mp hSi
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    have hTcard := hUniform i hi hT
    have hcardErase := Finset.card_erase_add_one hx
    rw [← hErase]
    omega
  calc
    (∑ i ∈ I, (sh i).card) = (I.biUnion sh).card :=
      (Finset.card_biUnion hPair).symm
    _ ≤ ((Finset.univ : Finset (Fin n)).powersetCard (k - 1)).card :=
      Finset.card_le_card hUnionSub
    _ = n.choose (k - 1) := by simp only [Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_fin]

/-- Near-sharp multi-link allocation. Unlike the earlier threshold
allocation interface, this theorem imposes no common lower threshold. -/
theorem disjoint_shadow_radius_allocation
    {ι : Type*} [DecidableEq ι] {n k L : ℕ}
    (I : Finset ι) (A : ι → Family (Fin n))
    (hk : 2 ≤ k)
    (hUniform : ∀ i ∈ I, Uniform k (A i))
    (hSize : ∀ i ∈ I, k.factorial * (A i).card ≤ L ^ k)
    (hDisjoint : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint (Finset.shadow (A i)) (Finset.shadow (A j))) :
    k * (∑ i ∈ I, (A i).card) ≤ (L + k) * n.choose (k - 1) := by
  calc
    k * (∑ i ∈ I, (A i).card) = ∑ i ∈ I, k * (A i).card := by
      rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ I, (L + k) * (Finset.shadow (A i)).card := by
      apply Finset.sum_le_sum
      intro i hi
      exact uniform_card_le_shadow_radius (A i) (hUniform i hi) hk (hSize i hi)
    _ = (L + k) * (∑ i ∈ I, (Finset.shadow (A i)).card) := by
      rw [Finset.mul_sum]
    _ ≤ (L + k) * n.choose (k - 1) :=
      Nat.mul_le_mul_left _ (sum_disjoint_shadow_card_le I A hUniform hDisjoint)

/-- The maximum-link version of the preceding allocation theorem. -/
theorem disjoint_shadow_maximum_allocation
    {ι : Type*} [DecidableEq ι] {n k M L : ℕ}
    (I : Finset ι) (A : ι → Family (Fin n))
    (hk : 2 ≤ k)
    (hUniform : ∀ i ∈ I, Uniform k (A i))
    (hMax : ∀ i ∈ I, (A i).card ≤ M)
    (hSize : k.factorial * M ≤ L ^ k)
    (hDisjoint : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint (Finset.shadow (A i)) (Finset.shadow (A j))) :
    k * (∑ i ∈ I, (A i).card) ≤ (L + k) * n.choose (k - 1) := by
  apply disjoint_shadow_radius_allocation I A hk hUniform ?_ hDisjoint
  intro i hi
  exact (Nat.mul_le_mul_left _ (hMax i hi)).trans hSize

end JSP523.Rank5
