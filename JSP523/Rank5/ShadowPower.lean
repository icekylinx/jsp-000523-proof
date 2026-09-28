import JSP523.Basic
import Mathlib.Combinatorics.SetFamily.KruskalKatona
import Mathlib.Combinatorics.SetFamily.LYM

/-!
# Finite shadow lower bounds

Mathlib's Lovász-form Kruskal--Katona theorem gives a useful exact finite
component of the shadow-power argument: if a uniform family contains at least
`choose t k` members, then its immediate shadow contains at least
`choose t (k - 1)` members.  The local LYM incidence estimate is also exposed
in the project's family language.
-/

namespace JSP523.Rank5

open scoped FinsetFamily

/-- Lovász-form Kruskal--Katona in the repository's uniform-family notation. -/
theorem shadow_card_ge_choose_threshold
    {n k t : ℕ} (A : Family (Fin n))
    (hUniform : Uniform k A)
    (hk : 2 ≤ k) (hkr : k ≤ t) (htn : t ≤ n)
    (hSize : t.choose k ≤ A.card) :
    t.choose (k - 1) ≤ (Finset.shadow A).card := by
  have hSized : (A : Set (Finset (Fin n))).Sized k := by
    intro S hS
    exact hUniform hS
  have hKK := Finset.kruskal_katona_lovasz_form
    (i := 1) (r := k) (k := t) (n := n)
    (by omega) hkr htn hSized hSize
  simpa using hKK

/-- The downward local LYM incidence inequality for a uniform family. -/
theorem shadow_card_local_lym
    {n k : ℕ} (A : Family (Fin n))
    (hUniform : Uniform k A) :
    A.card * k ≤ (Finset.shadow A).card * (n - k + 1) := by
  have hSized : (A : Set (Finset (Fin n))).Sized k := by
    intro S hS
    exact hUniform hS
  simpa using
    (Finset.local_lubell_yamamoto_meshalkin_inequality_mul hSized)

/-- Finite allocation from a uniform lower shadow threshold: if every
    nonempty link has at least `q` shadow sets and at most `M` edges, then
    the total edge count is bounded by `M/q` times the total shadow count.
    In division-free form this is the exact multiplicative step used in
    (IV.3.2); `q` can be supplied by `shadow_card_ge_choose_threshold`. -/
theorem finite_shadow_allocation_from_threshold
    {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (edges shadow : ι → ℕ) (M q : ℕ)
    (hMax : ∀ i ∈ I, edges i ≤ M)
    (hThreshold : ∀ i ∈ I, edges i ≠ 0 → q ≤ shadow i) :
    q * (∑ i ∈ I, edges i) ≤ M * (∑ i ∈ I, shadow i) := by
  calc
    q * (∑ i ∈ I, edges i) = ∑ i ∈ I, q * edges i := by
      simp [Finset.mul_sum]
    _ ≤ ∑ i ∈ I, M * shadow i := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases he : edges i = 0
      · simp [he]
      · have hq := hThreshold i hi he
        have hM := hMax i hi
        calc
          q * edges i ≤ shadow i * edges i := Nat.mul_le_mul_right _ hq
          _ ≤ shadow i * M := Nat.mul_le_mul_left _ hM
          _ = M * shadow i := Nat.mul_comm _ _
    _ = M * (∑ i ∈ I, shadow i) := by
      simp [Finset.mul_sum]

/-- A discrete multi-link consequence of Lovász Kruskal--Katona.  Every
    nonempty link is assumed to exceed the same binomial threshold; pairwise
    disjoint shadows then give a global finite allocation bound with no
    externally supplied shadow lower bound. -/
theorem disjoint_link_shadow_threshold_allocation
    {ι : Type*} [DecidableEq ι] {u k t : ℕ} (I : Finset ι)
    (A : ι → Family (Fin u)) (M : ℕ)
    (hk : 3 ≤ k) (hkt : k ≤ t) (htu : t ≤ u)
    (hUniform : ∀ i ∈ I, Uniform k (A i))
    (hThreshold : ∀ i ∈ I, t.choose k ≤ (A i).card)
    (hMax : ∀ i ∈ I, (A i).card ≤ M)
    (hDisjoint : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint (Finset.shadow (A i)) (Finset.shadow (A j))) :
    t.choose (k - 1) * (∑ i ∈ I, (A i).card) ≤
      M * u.choose (k - 1) := by
  let sh : ι → Family (Fin u) := fun i => Finset.shadow (A i)
  have hPair : (I : Set ι).PairwiseDisjoint sh := by
    intro i hi j hj hij
    exact hDisjoint i hi j hj hij
  have hUnionSub : I.biUnion sh ⊆
      (Finset.univ : Finset (Fin u)).powersetCard (k - 1) := by
    intro S hS
    obtain ⟨i, hi, hSi⟩ := Finset.mem_biUnion.mp hS
    obtain ⟨T, hT, x, hx, hErase⟩ := Finset.mem_shadow_iff.mp hSi
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    have hTcard := hUniform i hi hT
    have hcardErase := Finset.card_erase_add_one hx
    rw [← hErase]
    omega
  have hUnionCard : (I.biUnion sh).card =
      ∑ i ∈ I, (sh i).card := Finset.card_biUnion hPair
  have hShadowBound : (∑ i ∈ I, (sh i).card) ≤ u.choose (k - 1) := by
    calc
      (∑ i ∈ I, (sh i).card) = (I.biUnion sh).card := hUnionCard.symm
      _ ≤ ((Finset.univ : Finset (Fin u)).powersetCard (k - 1)).card :=
        Finset.card_le_card hUnionSub
      _ = u.choose (k - 1) := by simp [Finset.card_powersetCard]
  have hAlloc := finite_shadow_allocation_from_threshold I
    (fun i => (A i).card) (fun i => (sh i).card) M (t.choose (k - 1))
    hMax (by
      intro i hi hne
      exact shadow_card_ge_choose_threshold (A i) (hUniform i hi)
        (by omega) hkt htu (hThreshold i hi))
  exact hAlloc.trans (Nat.mul_le_mul_left M hShadowBound)

end JSP523.Rank5
