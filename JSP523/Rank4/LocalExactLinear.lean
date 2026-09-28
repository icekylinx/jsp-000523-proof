import JSP523.Rank4.CommonTripleCells
import JSP523.Rank4.LocalExactTrade
import JSP523.Counting.LinearNearStar
import JSP523.Counting.StarDecomposition
import JSP523.Counting.LocalLinearity
import JSP523.Matching

/-!
# Linear outside families near a star

This is equation (III.C.3) of the all-rank manuscript: if the outside four-edges are
linear, then each incidence `(E,a)` is paid either by its missing opposite
star facet or by the vertex `a`.  The first class is injective by
linearity; the second is injective by the forbidden switch in the common
cell `J_{va}`.  The rank-four inequality below is obtained from the
general proof of (IV.2.6) in `Counting/LinearNearStar.lean`.
-/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- Outside edges in a specified near-star presentation. -/
def outsideEdges (H : Family α) (W : Edge α) : Family α :=
  H.filter fun E => E ⊆ W

/-- Present star facets, complementary to `missingStarTriples`. -/
def presentStarTriples (H : Family α) (W : Edge α) (v : α) : Family α :=
  (W.powersetCard 3).filter fun T => insert v T ∈ H

/-- The rank-four incidence inequality (III.C.3), now specialized from the
general rank proof of (IV.2.6). -/
theorem linear_outside_edges_incidence_bound
    {H B : Family α} {W : Edge α} {v : α}
    (hH : Admissible H) (hBH : B ⊆ H)
    (hU : Uniform 4 B) (hLin : LinearFamily B)
    (hW : ∀ E ∈ B, E ⊆ W) (hvW : v ∉ W) :
    4 * B.card ≤ W.card + (missingStarTriples H W v).card := by
  simpa only [missingStarFacets, missingStarTriples, Nat.reduceSubDiff]
    using (linear_near_star_incidence_bound hH hBH hU hLin
      (by omega : 3 ≤ 4) hW hvW)

/-- With a complete star on at least seven outside vertices, distinct
outside four-edges cannot overlap.  This is the `q = 0` equality branch
of the local theorem. -/
theorem complete_star_outside_is_matching
    {H B : Family α} {W : Edge α} {v : α}
    (hH : Admissible H) (hBH : B ⊆ H)
    (hU : Uniform 4 B) (hW : ∀ E ∈ B, E ⊆ W)
    (hvW : v ∉ W) (hWcard : 7 ≤ W.card)
    (hFull : (missingStarTriples H W v).card = 0) :
    IsMatching B := by
  apply complete_star_outside_matching hH hBH hU hW hvW
    (by omega : 2 * 4 - 1 ≤ W.card)
  simpa only [missingStarFacets, missingStarTriples, Nat.reduceSubDiff]
    using hFull

/-- After the missing-star budget falls below `w - 6`, the pointwise
overlap count excludes outside intersections of size two or three.  The
hard earlier part of §III.C of the all-rank manuscript is the quantitative reduction to
this small budget. -/
theorem small_missing_implies_outside_linear
    {H B : Family α} {W : Edge α} {v : α}
    (hH : Admissible H) (hBH : B ⊆ H)
    (hU : Uniform 4 B) (hW : ∀ E ∈ B, E ⊆ W)
    (hvW : v ∉ W) (hWcard : 7 ≤ W.card)
    (hSmall : (missingStarTriples H W v).card < W.card - 6) :
    LinearFamily B := by
  intro E F hE hF hEF
  by_contra hLarge
  have hTwo : 2 ≤ (E ∩ F).card := by omega
  have hShared : (E ∩ F).Nonempty := Finset.card_pos.mp (by omega)
  have hEcard := hU hE
  have hFcard := hU hF
  have hDiff := Finset.card_sdiff_add_card_inter E F
  have hkLe : (E \ F).card ≤ 2 := by omega
  have hkPos : 0 < (E \ F).card := by
    by_contra hZero
    have hEqZero : (E \ F).card = 0 := by omega
    have hSub : E ⊆ F := Finset.sdiff_eq_empty_iff_subset.mp
      (Finset.card_eq_zero.mp hEqZero)
    exact hEF (Finset.eq_of_subset_of_card_le hSub (by omega))
  have hCount := overlapping_outside_edges_missing_star_binomial
    hH (hBH hE) (hBH hF) (hW E hE) (hW F hF)
    hEcard hFcard hEF hShared hvW
  have hPascalBound (n : ℕ) (hn : 2 ≤ n) :
      n - 1 ≤ n.choose 2 := by
    have hPred : n - 1 + 1 = n := by omega
    have hPascal := Nat.choose_succ_succ' (n - 1) 1
    rw [hPred, Nat.choose_one_right] at hPascal
    norm_num only at hPascal
    omega
  rcases (by omega : (E \ F).card = 1 ∨ (E \ F).card = 2) with
    hk | hk
  · have hN : 2 ≤ W.card - 5 := by omega
    have hBound := hPascalBound (W.card - 5) hN
    have hArg : W.card - 4 - (E \ F).card = W.card - 5 := by omega
    have hChoose : 3 - (E \ F).card = 2 := by omega
    rw [hArg, hChoose] at hCount
    omega
  · have hArg : W.card - 4 - (E \ F).card = W.card - 6 := by omega
    have hChoose : 3 - (E \ F).card = 1 := by omega
    rw [hArg, hChoose, Nat.choose_one_right] at hCount
    omega

/-- Exact rank-four star/outside decomposition, specialized from (IV.2.1). -/
theorem rank_four_star_outside_card
    {H : Family α} {W : Edge α} {v : α}
    (hU : Uniform 4 H)
    (hSupport : ∀ E ∈ H, E ⊆ insert v W)
    (hvW : v ∉ W) :
    H.card = (presentStarTriples H W v).card +
      (outsideEdges H W).card := by
  simpa [presentStarFacets, presentStarTriples, outsideFamily, outsideEdges]
    using (star_outside_card hU hSupport hvW)

/-- Present and missing rank-four star facets partition all triples on `W`. -/
theorem present_add_missing_star
    (H : Family α) (W : Edge α) (v : α) :
    (presentStarTriples H W v).card +
      (missingStarTriples H W v).card = W.card.choose 3 := by
  simpa [presentStarFacets, presentStarTriples, missingStarFacets,
    missingStarTriples] using
    (present_add_missing_star_facets H W v 4)

/-- The exact local upper bound once the outside family has been
linearized. This is the final numerical step in §III.C of the all-rank
manuscript, specialized from the general rank result in
`Counting/StarDecomposition.lean`. -/
theorem rank_four_local_upper_of_linear_outside
    {H : Family α} {W : Edge α} {v : α}
    (hH : Admissible H) (hU : Uniform 4 H)
    (hSupport : ∀ E ∈ H, E ⊆ insert v W)
    (hvW : v ∉ W)
    (hLin : LinearFamily (outsideEdges H W)) :
    H.card ≤ W.card.choose 3 + W.card / 4 := by
  have hLin' : LinearFamily (outsideFamily H W) := by
    simpa only [outsideFamily, outsideEdges] using hLin
  simpa only [Nat.reduceSubDiff] using
    (near_star_upper_of_linear_outside hH hU hSupport hvW
      (by omega : 3 ≤ 4) hLin')

/-- A directly checkable near-star range of the local theorem: fewer than
`w - 6` missing star triples already force outside linearity. -/
theorem rank_four_local_upper_of_small_missing
    {H : Family α} {W : Edge α} {v : α}
    (hH : Admissible H) (hU : Uniform 4 H)
    (hSupport : ∀ E ∈ H, E ⊆ insert v W)
    (hvW : v ∉ W) (hWcard : 7 ≤ W.card)
    (hSmall : (missingStarTriples H W v).card < W.card - 6) :
    H.card ≤ W.card.choose 3 + W.card / 4 := by
  let B := outsideEdges H W
  have hBH : B ⊆ H := Finset.filter_subset _ _
  have hBU : Uniform 4 B := by
    intro E hE
    exact hU (hBH hE)
  have hBW : ∀ E ∈ B, E ⊆ W := by
    intro E hE
    exact (Finset.mem_filter.mp hE).2
  have hLin : LinearFamily B :=
    small_missing_implies_outside_linear
      hH hBH hBU hBW hvW hWcard hSmall
  exact rank_four_local_upper_of_linear_outside
    hH hU hSupport hvW hLin

/-- At equality in the linear-outside bound, at most one star triple is
missing.  A single missing triple requires `w ≡ 3 (mod 4)`, as in the
two equality branches of §III.C of the all-rank manuscript. -/
theorem linear_outside_equality_missing_restriction
    {H : Family α} {W : Edge α} {v : α}
    (hH : Admissible H) (hU : Uniform 4 H)
    (hSupport : ∀ E ∈ H, E ⊆ insert v W)
    (hvW : v ∉ W)
    (hLin : LinearFamily (outsideEdges H W))
    (hEquality : H.card = W.card.choose 3 + W.card / 4) :
    (missingStarTriples H W v).card ≤ 1 ∧
      ((missingStarTriples H W v).card = 1 → W.card % 4 = 3) := by
  have hLin' : LinearFamily (outsideFamily H W) := by
    simpa only [outsideFamily, outsideEdges] using hLin
  simpa only [missingStarFacets, missingStarTriples,
    Nat.reduceSubDiff] using
    (near_star_equality_missing_restriction hH hU hSupport hvW
      (by omega : 3 ≤ 4) hLin' hEquality)

/-- At a complete star, every outside edge belongs to a matching.  If
the extremal count is attained, that matching has the maximum size. -/
theorem complete_star_equality_matching
    {H : Family α} {W : Edge α} {v : α}
    (hH : Admissible H) (hU : Uniform 4 H)
    (hSupport : ∀ E ∈ H, E ⊆ insert v W)
    (hvW : v ∉ W) (hWcard : 7 ≤ W.card)
    (hFull : (missingStarTriples H W v).card = 0)
    (hEquality : H.card = W.card.choose 3 + W.card / 4) :
    IsMatching (outsideEdges H W) ∧
      (outsideEdges H W).card = W.card / 4 := by
  have hFull' : (missingStarFacets H W v 4).card = 0 := by
    simpa only [missingStarFacets, missingStarTriples,
      Nat.reduceSubDiff] using hFull
  simpa only [outsideFamily, outsideEdges, Nat.reduceSubDiff] using
    (complete_star_equality_max_matching hH hU hSupport hvW
      (by omega : 2 * 4 - 1 ≤ W.card) hFull' hEquality)

end JSP523.Rank4
