import JSP523.Rank5.ActualHigherBadRoot
import JSP523.Rank5.UniqueBadPairDeletionBudget
import JSP523.Rank5.BadPairTailPackingActual

/-!
# Actual finite deletion bound for bad pairs in the ordinary outside family

This module instantiates the filtered three-strata count on the actual
ordinary outside edges and the actual missing-star bad pairs. The disjoint
and filtered-intersecting tail caps both simplify to `choose (w) (r-5)` for
all `r ≥ 5`; at rank five this is the exact constant one.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

private theorem disjoint_bad_pair_cap_eq
    (w r : ℕ) (hr : 5 ≤ r) :
    (if 2 ≤ r - 4 then w.choose (r - 4 - 2 + 1) else 1) =
      w.choose (r - 5) := by
  by_cases h5 : r = 5
  · subst r
    simp
  · have h6 : 6 ≤ r := by omega
    have hcond : 2 ≤ r - 4 := by omega
    have hindex : r - 4 - 2 + 1 = r - 5 := by omega
    simp [hcond, hindex]

private theorem intersecting_bad_pair_cap_eq
    (w r : ℕ) (hr : 5 ≤ r) :
    (if 3 ≤ r - 3 then w.choose (r - 3 - 3 + 1) else 1) =
      w.choose (r - 5) := by
  by_cases h5 : r = 5
  · subst r
    simp
  · have h6 : 6 ≤ r := by omega
    have hcond : 3 ≤ r - 3 := by omega
    have hindex : r - 3 - 3 + 1 = r - 5 := by omega
    simp [hcond, hindex]

/-- Exact finite bad-pair deletion bound for the manuscript's ordinary
outside family. The companion conjunct records the stronger scaled unique
root estimate from `UniqueBadPairDeletionBudget`. -/
theorem actual_ordinary_bad_pair_deletion_bound
    (H : Family α) (W : Edge α) (v : α) (r : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hr : 5 ≤ r) (hvW : v ∉ W) :
    let B := ordinaryOutsideFamily H W v r
    let Bad₂ := badMissingSets H W v r 2
      ((W.card - r - 2).choose (r - 3))
    (badPairEdges B Bad₂).card ≤
        Bad₂.card * W.card.choose (r - 4) +
          Bad₂.card * (Bad₂.card * W.card.choose (r - 5)) +
          Bad₂.card * (Bad₂.card * W.card.choose (r - 5)) ∧
      ((W.card - r - 2).choose (r - 3)) *
          ((r - 2).choose (r - 4) * (uniqueBadPairEdges B Bad₂).card) ≤
        (2 * (r - 1).choose 2 *
          (missingStarFacets H W v r).card) * W.card.choose (r - 4) := by
  classical
  let B := ordinaryOutsideFamily H W v r
  let Bad₂ := badMissingSets H W v r 2
    ((W.card - r - 2).choose (r - 3))
  have hBH : B ⊆ H := by
    intro E hE
    exact (Finset.mem_filter.mp hE).1
  have hBuniform : Uniform r B := by
    intro E hE
    exact hUniform (hBH hE)
  have hBW : ∀ E ∈ B, E ⊆ W := by
    intro E hE
    exact ((Finset.mem_filter.mp hE).2).trans Finset.sdiff_subset
  have hBordinary : ∀ E ∈ B,
      E ⊆ W \ badSingletonVertices H W v r := by
    intro E hE
    exact (Finset.mem_filter.mp hE).2
  have hUnique : ∀ P ∈ Bad₂,
      (B.filter fun E =>
        P ⊆ E ∧ (Bad₂.filter fun Q => Q ⊆ E).card = 1).card ≤
        W.card.choose (r - 4) := by
    intro P hP
    let fiber := B.filter fun E =>
      P ⊆ E ∧ (Bad₂.filter fun Q => Q ⊆ E).card = 1
    have hPactual : P ∈ badMissingSets H W v r 2
        ((W.card - r - 2).choose (r - 3)) := by
      simpa [Bad₂] using hP
    have hActual := fixed_unique_bad_pair_outside_tail_packing
      hAdm hUniform hr hvW hPactual
    have hSub : fiber ⊆ uniqueBadPairOutsideEdgeFamily H W v r P := by
      intro E hE
      obtain ⟨hEB, hPE, hOne⟩ := Finset.mem_filter.mp hE
      have hHE := hBH hEB
      have hOneActual :
          ((badMissingSets H W v r 2
            ((W.card - r - 2).choose (r - 3))).filter
              fun Q => Q ⊆ E).card = 1 := by
        simpa [Bad₂] using hOne
      apply Finset.mem_filter.mpr
      exact ⟨hHE, hBordinary E hEB, hPactual, hPE, hOneActual⟩
    have hCard := Finset.card_le_card hSub
    have hp : 0 < (r - 2).choose (r - 4) :=
      Nat.choose_pos (by omega)
    calc
      fiber.card ≤ (r - 2).choose (r - 4) * fiber.card :=
        Nat.le_mul_of_pos_left _ hp
      _ ≤ (r - 2).choose (r - 4) *
          (uniqueBadPairOutsideEdgeFamily H W v r P).card :=
        Nat.mul_le_mul_left _ hCard
      _ ≤ W.card.choose (r - 4) := by simpa [Nat.mul_comm] using hActual
  have hDisjoint : ∀ P ∈ Bad₂, ∀ Q ∈ Bad₂, Disjoint P Q →
      (B.filter fun E => P ∪ Q ⊆ E).card ≤ W.card.choose (r - 5) := by
    intro P hP Q hQ hPQ
    have hBound := disjoint_bad_pair_root_tail_packing_bound
      hAdm hBH hBuniform hBW hBordinary hvW rfl hP hQ hPQ
    rw [disjoint_bad_pair_cap_eq W.card r hr] at hBound
    exact hBound
  have hIntersect : ∀ P ∈ Bad₂, ∀ Q ∈ Bad₂, P ≠ Q →
      ¬ Disjoint P Q →
      ((noDisjointBadPairEdges B Bad₂).filter
        fun E => P ∪ Q ⊆ E).card ≤ W.card.choose (r - 5) := by
    intro P hP Q hQ hPQ hNotDisj
    have hBound := intersecting_bad_pair_root_tail_packing_bound
      hAdm hBH hBuniform hBW hBordinary hvW rfl hP hQ hPQ hNotDisj
    rw [intersecting_bad_pair_cap_eq W.card r hr] at hBound
    exact hBound
  have hCount := bad_pair_edges_filtered_deletion_bound
    hUnique hDisjoint hIntersect
  have hUniqueStrong := unique_bad_pair_outside_deletion_budget
    hAdm hUniform hr hvW hBH hBordinary rfl
  simpa [B, Bad₂] using And.intro hCount hUniqueStrong

end JSP523
