import JSP523.Counting.OverlapTrade
import JSP523.Counting.StarDecomposition
import JSP523.Matching

/-!
# Exact linearity criteria near a star

These are direct finite consequences of the missing-facet bound (IV.2.2)
in `jsp-000523-proof/paper/proof.md`.
They make explicit the binomial threshold used in the linearization and
equality arguments of §§III.C and IV.2.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

/-- If the missing-star budget is below every overlap threshold with
intersection size at least two, the outside family is linear. -/
theorem outside_linear_of_small_missing
    {H B : Family α} {W : Edge α} {v : α} {r : ℕ}
    (hH : Admissible H) (hBH : B ⊆ H)
    (hU : Uniform r B)
    (hW : ∀ E ∈ B, E ⊆ W) (hvW : v ∉ W)
    (hSmall : ∀ k : ℕ, 1 ≤ k → k ≤ r - 2 →
      (missingStarFacets H W v r).card <
        (W.card - r - k).choose (r - 1 - k)) :
    LinearFamily B := by
  intro E F hE hF hEF
  have hEcard := hU hE
  have hFcard := hU hF
  by_contra hNot
  have hTwo : 2 ≤ (E ∩ F).card := by omega
  have hShared : (E ∩ F).Nonempty := Finset.card_pos.mp (by omega)
  have hkPos : 1 ≤ (E \ F).card := by
    by_contra hZero
    have hEmpty : E \ F = ∅ := Finset.card_eq_zero.mp (by omega)
    have hSub : E ⊆ F := Finset.sdiff_eq_empty_iff_subset.mp hEmpty
    exact hEF (Finset.eq_of_subset_of_card_le hSub (by omega))
  have hDiff := Finset.card_sdiff_add_card_inter E F
  have hkBound : (E \ F).card ≤ r - 2 := by omega
  have hCount := overlap_trade_missing_star_binomial
    hH (hBH hE) (hBH hF) (hW E hE) (hW F hF)
    hEcard hFcard hEF hShared hvW
  exact (Nat.not_lt.mpr hCount)
    (hSmall (E \ F).card hkPos hkBound)

/-- With a complete star on at least `2r-1` outside vertices, all outside
edges are pairwise disjoint. -/
theorem complete_star_outside_matching
    {H B : Family α} {W : Edge α} {v : α} {r : ℕ}
    (hH : Admissible H) (hBH : B ⊆ H)
    (hU : Uniform r B)
    (hW : ∀ E ∈ B, E ⊆ W) (hvW : v ∉ W)
    (hWcard : 2 * r - 1 ≤ W.card)
    (hFull : (missingStarFacets H W v r).card = 0) :
    IsMatching B := by
  intro E F hE hF hEF
  by_cases hShared : (E ∩ F).Nonempty
  · have hEcard := hU hE
    have hFcard := hU hF
    have hPpos : 0 < (E ∩ F).card := Finset.card_pos.mpr hShared
    have hDiff := Finset.card_sdiff_add_card_inter E F
    have hk : (E \ F).card ≤ r - 1 := by omega
    have hChooseBound : r - 1 - (E \ F).card ≤
        W.card - r - (E \ F).card := by omega
    have hChoosePos : 0 <
        (W.card - r - (E \ F).card).choose
          (r - 1 - (E \ F).card) := Nat.choose_pos hChooseBound
    have hCount := overlap_trade_missing_star_binomial
      hH (hBH hE) (hBH hF) (hW E hE) (hW F hF)
      hEcard hFcard hEF hShared hvW
    omega
  · exact Finset.disjoint_iff_inter_eq_empty.mpr
      (Finset.not_nonempty_iff_eq_empty.mp hShared)

/-- A fully finite conditional local theorem: if every possible overlap
threshold exceeds the missing-star budget, then the exact near-star upper
bound follows. This packages the final part of Theorem IV.2.1 without
assuming its still-open quantitative linearization estimate. -/
theorem near_star_upper_of_overlap_thresholds
    {H : Family α} {W : Edge α} {v : α} {r : ℕ}
    (hH : Admissible H) (hU : Uniform r H)
    (hSupport : ∀ E ∈ H, E ⊆ insert v W)
    (hvW : v ∉ W) (hr : 3 ≤ r)
    (hSmall : ∀ k : ℕ, 1 ≤ k → k ≤ r - 2 →
      (missingStarFacets H W v r).card <
        (W.card - r - k).choose (r - 1 - k)) :
    H.card ≤ W.card.choose (r - 1) + W.card / r := by
  let B := outsideFamily H W
  have hBH : B ⊆ H := Finset.filter_subset _ _
  have hBU : Uniform r B := by
    intro E hE
    exact hU (hBH hE)
  have hBW : ∀ E ∈ B, E ⊆ W := by
    intro E hE
    exact (Finset.mem_filter.mp hE).2
  have hLin : LinearFamily B :=
    outside_linear_of_small_missing hH hBH hBU hBW hvW hSmall
  exact near_star_upper_of_linear_outside
    hH hU hSupport hvW hr hLin

/-- The complete-star equality branch: the outside edges are a maximum
matching. -/
theorem complete_star_equality_max_matching
    {H : Family α} {W : Edge α} {v : α} {r : ℕ}
    (hH : Admissible H) (hU : Uniform r H)
    (hSupport : ∀ E ∈ H, E ⊆ insert v W)
    (hvW : v ∉ W)
    (hWcard : 2 * r - 1 ≤ W.card)
    (hFull : (missingStarFacets H W v r).card = 0)
    (hEquality : H.card = W.card.choose (r - 1) + W.card / r) :
    IsMatching (outsideFamily H W) ∧
      (outsideFamily H W).card = W.card / r := by
  let B := outsideFamily H W
  have hBH : B ⊆ H := Finset.filter_subset _ _
  have hBU : Uniform r B := by
    intro E hE
    exact hU (hBH hE)
  have hBW : ∀ E ∈ B, E ⊆ W := by
    intro E hE
    exact (Finset.mem_filter.mp hE).2
  have hMatch : IsMatching B :=
    complete_star_outside_matching hH hBH hBU hBW hvW hWcard hFull
  have hId := near_star_card_identity hU hSupport hvW
  change H.card = W.card.choose (r - 1) -
    (missingStarFacets H W v r).card + B.card at hId
  constructor
  · exact hMatch
  · change B.card = W.card / r
    rw [hFull] at hId
    simp only [Nat.sub_zero] at hId
    omega

end JSP523
