import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev

/-!
# Finite degree inequality for separating star shadows

This is the finite numerical step in Lemma IV.3.2: the sum of all
nonmaximal degrees squared is absorbed by the products with a maximal
degree, and the remaining terms are ordered pair products.
-/

namespace JSP523.Rank5

/-- Sum of products over ordered distinct pairs from a finite index set. -/
def orderedDegreePairs {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (d : ι → ℕ) : ℕ :=
  ∑ i ∈ I, ∑ j ∈ I.erase i, d i * d j

/-- The square of the total nonmaximal degree is bounded by the ordered
pair-product budget, whenever `m` is a maximum-degree index. -/
theorem nonmaximal_degree_sq_le_ordered_pairs
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (d : ι → ℕ)
    (m : ι) (hm : m ∈ I)
    (hmax : ∀ i ∈ I, d i ≤ d m) :
    (∑ i ∈ I.erase m, d i) ^ 2 ≤ orderedDegreePairs I d := by
  classical
  let S := I.erase m
  have hmS : m ∉ S := by simp [S]
  have hSsub : S ⊆ I := Finset.erase_subset _ _
  have hExpand : (∑ i ∈ S, d i) ^ 2 =
      (∑ i ∈ S, d i * d i) +
        (∑ i ∈ S, ∑ j ∈ S.erase i, d i * d j) := by
    rw [pow_two, Finset.sum_mul_sum]
    have hrow : ∀ i ∈ S, (∑ j ∈ S, d i * d j) =
        d i * d i + ∑ j ∈ S.erase i, d i * d j := by
      intro i hi
      rw [← Finset.add_sum_erase S (fun j => d i * d j) hi]
    have hRows : (∑ i ∈ S, ∑ j ∈ S, d i * d j) =
        ∑ i ∈ S, (d i * d i + ∑ j ∈ S.erase i, d i * d j) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hrow i hi
    rw [hRows, Finset.sum_add_distrib]
  have hDiag : (∑ i ∈ S, d i * d i) ≤ d m * (∑ i ∈ S, d i) := by
    calc
      (∑ i ∈ S, d i * d i) ≤ ∑ i ∈ S, d m * d i := by
        apply Finset.sum_le_sum
        intro i hi
        exact Nat.mul_le_mul_right (d i) (hmax i (hSsub hi))
      _ = d m * (∑ i ∈ S, d i) := by rw [Finset.mul_sum]
  have hSubPairs :
      (∑ i ∈ S, ∑ j ∈ S.erase i, d i * d j) +
        d m * (∑ i ∈ S, d i) ≤ orderedDegreePairs I d := by
    unfold orderedDegreePairs
    have hEach : ∀ i ∈ S,
        (∑ j ∈ S.erase i, d i * d j) + d i * d m ≤
          ∑ j ∈ I.erase i, d i * d j := by
      intro i hi
      have him : i ≠ m := by
        intro h
        exact hmS (h.symm ▸ hi)
      have hEq : I.erase i = insert m (S.erase i) := by
        have hI : I = insert m S := by simp [S, Finset.insert_erase hm]
        rw [hI, Finset.erase_insert_of_ne (Ne.symm him)]
      rw [hEq, Finset.sum_insert (by simp [hmS])]
      simp [Nat.mul_comm, Nat.add_comm]
    have hOuter := Finset.sum_le_sum hEach
    have hComm : (∑ i ∈ S, d i * d m) = d m * (∑ i ∈ S, d i) := by
      calc
        (∑ i ∈ S, d i * d m) = (∑ i ∈ S, d i) * d m :=
          (Finset.sum_mul S (fun i => d i) (d m)).symm
        _ = d m * (∑ i ∈ S, d i) := Nat.mul_comm _ _
    rw [Finset.sum_add_distrib, hComm] at hOuter
    calc
      (∑ i ∈ S, ∑ j ∈ S.erase i, d i * d j) +
          d m * (∑ i ∈ S, d i) ≤
        ∑ i ∈ S, ∑ j ∈ I.erase i, d i * d j := by
          simpa [Nat.add_comm] using hOuter
      _ ≤ ∑ i ∈ I, ∑ j ∈ I.erase i, d i * d j :=
        Finset.sum_le_sum_of_subset_of_nonneg hSsub
          (by intro i hi hnot; exact Nat.zero_le _)
  calc
    (∑ i ∈ I.erase m, d i) ^ 2 = (∑ i ∈ S, d i) ^ 2 := by simp [S]
    _ ≤ d m * (∑ i ∈ S, d i) +
          (∑ i ∈ S, ∑ j ∈ S.erase i, d i * d j) := by
      rw [hExpand]
      exact Nat.add_le_add_right hDiag _
    _ ≤ orderedDegreePairs I d := by simpa [Nat.add_comm] using hSubPairs

/-- Summing over shadow sets and applying finite Cauchy–Schwarz gives the
global numerical bound used after the owner assignment in Lemma IV.3.2. -/
theorem total_nonmaximal_degree_sq_le_pair_budget
    {τ ι : Type*} [DecidableEq τ] [DecidableEq ι]
    (P : Finset τ) (I : Finset ι)
    (d : τ → ι → ℕ) (owner : τ → ι)
    (hOwner : ∀ p ∈ P, owner p ∈ I)
    (hMax : ∀ p ∈ P, ∀ i ∈ I, d p i ≤ d p (owner p)) :
    (∑ p ∈ P, ∑ i ∈ I.erase (owner p), d p i) ^ 2 ≤
      P.card * ∑ p ∈ P, orderedDegreePairs I (d p) := by
  have hCauchy := sq_sum_le_card_mul_sum_sq
    (s := P) (f := fun p => ∑ i ∈ I.erase (owner p), d p i)
  have hTerm : ∀ p ∈ P,
      (∑ i ∈ I.erase (owner p), d p i) ^ 2 ≤
        orderedDegreePairs I (d p) := by
    intro p hp
    exact nonmaximal_degree_sq_le_ordered_pairs I (d p)
      (owner p) (hOwner p hp) (hMax p hp)
  have hSum := Finset.sum_le_sum hTerm
  exact hCauchy.trans (Nat.mul_le_mul_left P.card hSum)

end JSP523.Rank5
