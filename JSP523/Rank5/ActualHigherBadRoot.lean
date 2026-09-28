import JSP523.Rank5.LocalExactDeletion
import JSP523.Rank5.MinimalBadRootGeometry
import JSP523.Counting.StarDecomposition
import Mathlib.Order.Interval.Finset.Nat

/-!
# Actual higher bad-root strata in the local cleaning argument

For each `k ≥ 3`, this module uses the actual outside edges on `U` that
contain no bad set of smaller positive size.  It applies the finite
incidence count and fixed-root tail packing already proved in
`LocalExactDeletion` to this concrete stratum.  This is the higher-root
part of (IV.2.5) in `paper/proof.pdf`.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

/-- Outside edges on the ordinary vertex set with no smaller bad root. -/
noncomputable def outsideNoSmallerBadRoot
    (H : Family α) (W : Edge α) (v : α) (r k : ℕ) : Family α :=
  by
    classical
    exact (outsideFamily H (W \ badSingletonVertices H W v r)).filter
      (NoSmallerBadSubset H W v r k)

/-- The exact finite deletion budget for one higher bad-root stratum.
The numerator comes from (IV.2.3), and the final factor is the
distance-packing count for tails of actual edges. -/
theorem actual_higher_bad_root_stratum_bound
    (H : Family α) (W : Edge α) (v : α) (r k : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hvW : v ∉ W) (hk : 3 ≤ k) (hkr : k ≤ r - 2)
    (hLambda : 0 < (W.card - r - k).choose (r - 1 - k)) :
    (edgesMeetingBadRoot (outsideNoSmallerBadRoot H W v r k)
      (badMissingSets H W v r k
        ((W.card - r - k).choose (r - 1 - k)))).card ≤
      (2 * (r - 1).choose k *
        (missingStarFacets H W v r).card /
          ((W.card - r - k).choose (r - 1 - k))) *
        (if k ≤ r - k then W.card.choose (r - k - k + 1) else 1) := by
  classical
  let B := outsideNoSmallerBadRoot H W v r k
  have hBmem (E : Edge α) (hE : E ∈ B) :
      E ∈ outsideFamily H (W \ badSingletonVertices H W v r) ∧
      NoSmallerBadSubset H W v r k E := by
    exact Finset.mem_filter.mp hE
  have hBH : B ⊆ H := by
    intro E hE
    exact (Finset.mem_filter.mp (hBmem E hE).1).1
  have hBU : Uniform r B := by
    intro E hE
    exact hUniform (hBH hE)
  have hBW : ∀ E ∈ B, E ⊆ W := by
    intro E hE
    exact ((Finset.mem_filter.mp (hBmem E hE).1).2).trans
      Finset.sdiff_subset
  have hClean : ∀ E ∈ B, ∀ P : Edge α, P ⊆ E → P.card = k →
      ∀ j : ℕ, 1 ≤ j → j < k →
        ∀ Q : Edge α, Q ⊆ E \ P → Q.card = j →
          Q ∉ badMissingSets H W v r j
            ((W.card - r - j).choose (r - 1 - j)) := by
    intro E hE P _hPE _hPcard j hj hjk Q hQ hQcard
    exact (hBmem E hE).2 j hj hjk Q
      (hQ.trans Finset.sdiff_subset) hQcard
  exact higher_bad_set_stratum_deletion_bound hAdm hBH hBU hBW
    hvW hk (by omega) hLambda hClean

/-- All actual higher-root deletion classes, with each edge assigned to
its first possible bad-root size by the no-smaller-root condition. -/
noncomputable def actualHigherBadRootEdges
    (H : Family α) (W : Edge α) (v : α) (r : ℕ) : Family α :=
  by
    classical
    exact (Finset.Icc 3 (r - 2)).biUnion fun k =>
      edgesMeetingBadRoot (outsideNoSmallerBadRoot H W v r k)
        (badMissingSets H W v r k
          ((W.card - r - k).choose (r - 1 - k)))

/-- Sum the exact finite budgets for all higher bad-root sizes. -/
theorem actual_higher_bad_root_edges_bound
    (H : Family α) (W : Edge α) (v : α) (r : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hvW : v ∉ W)
    (hLambda : ∀ k ∈ Finset.Icc 3 (r - 2),
      0 < (W.card - r - k).choose (r - 1 - k)) :
    (actualHigherBadRootEdges H W v r).card ≤
      ∑ k ∈ Finset.Icc 3 (r - 2),
        (2 * (r - 1).choose k *
          (missingStarFacets H W v r).card /
            ((W.card - r - k).choose (r - 1 - k))) *
          (if k ≤ r - k then W.card.choose (r - k - k + 1) else 1) := by
  classical
  unfold actualHigherBadRootEdges
  calc
    ((Finset.Icc 3 (r - 2)).biUnion fun k =>
      edgesMeetingBadRoot (outsideNoSmallerBadRoot H W v r k)
        (badMissingSets H W v r k
          ((W.card - r - k).choose (r - 1 - k)))).card
        ≤ ∑ k ∈ Finset.Icc 3 (r - 2),
            (edgesMeetingBadRoot (outsideNoSmallerBadRoot H W v r k)
              (badMissingSets H W v r k
                ((W.card - r - k).choose (r - 1 - k)))).card :=
          Finset.card_biUnion_le
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k hk
      have hkData := Finset.mem_Icc.mp hk
      exact actual_higher_bad_root_stratum_bound H W v r k hAdm
        hUniform hvW hkData.1 hkData.2 (hLambda k hk)

/-- The ordinary outside edges used throughout §IV.2.1. -/
def ordinaryOutsideFamily
    (H : Family α) (W : Edge α) (v : α) (r : ℕ) : Family α :=
  outsideFamily H (W \ badSingletonVertices H W v r)

/-- All actual edges deleted by the bad-pair and higher-root cleaning
steps. A bad singleton cannot occur in the ordinary outside family. -/
noncomputable def actualDirtyOutsideEdges
    (H : Family α) (W : Edge α) (v : α) (r : ℕ) : Family α :=
  by
    classical
    exact badPairEdges (ordinaryOutsideFamily H W v r)
      (badMissingSets H W v r 2
        ((W.card - r - 2).choose (r - 3))) ∪
      actualHigherBadRootEdges H W v r

/-- Ordinary outside edges contain no actual bad singleton root. -/
theorem ordinary_outside_no_bad_singleton
    (H : Family α) (W : Edge α) (v : α) (r : ℕ)
    {E Q : Edge α} (hE : E ∈ ordinaryOutsideFamily H W v r)
    (hQE : Q ⊆ E) (hQcard : Q.card = 1) :
    Q ∉ badMissingSets H W v r 1
      ((W.card - r - 1).choose (r - 2)) := by
  intro hQbad
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hQcard
  have hxQ : x ∈ Q := by rw [hx]; simp
  have hxE : x ∈ E := hQE hxQ
  have hEU : E ⊆ W \ badSingletonVertices H W v r :=
    (Finset.mem_filter.mp hE).2
  have hxU := Finset.mem_sdiff.mp (hEU hxE)
  have hxD : x ∈ badSingletonVertices H W v r := by
    exact Finset.mem_filter.mpr ⟨hxU.1, by simpa [hx] using hQbad⟩
  exact hxU.2 hxD

/-- A bad pair contained in an ordinary outside edge is recorded in the
pair-deletion family. -/
theorem ordinary_outside_bad_pair_mem_dirty
    (H : Family α) (W : Edge α) (v : α) (r : ℕ)
    {E P : Edge α} (hE : E ∈ ordinaryOutsideFamily H W v r)
    (hP : P ∈ badMissingSets H W v r 2
      ((W.card - r - 2).choose (r - 3))) (hPE : P ⊆ E) :
    E ∈ actualDirtyOutsideEdges H W v r := by
  classical
  apply Finset.mem_union_left
  exact Finset.mem_biUnion.mpr
    ⟨P, hP, Finset.mem_filter.mpr ⟨hE, hPE⟩⟩

/-- Every actual bad root of size at most `r-2` in an ordinary outside
edge is covered by the deletion family. For larger roots we descend to
a smaller bad root until reaching the minimal size. -/
theorem ordinary_outside_bad_root_mem_dirty
    (H : Family α) (W : Edge α) (v : α) (r : ℕ)
    {E : Edge α} (hE : E ∈ ordinaryOutsideFamily H W v r) :
    ∀ k : ℕ, 1 ≤ k → k ≤ r - 2 →
      ∀ P : Edge α, P ⊆ E → P.card = k →
        P ∈ badMissingSets H W v r k
          ((W.card - r - k).choose (r - 1 - k)) →
        E ∈ actualDirtyOutsideEdges H W v r := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hkPos hkBound P hPE hPcard hPbad
    by_cases hkOne : k = 1
    · have hPcardOne : P.card = 1 := hPcard.trans hkOne
      have hPbadOne : P ∈ badMissingSets H W v r 1
          ((W.card - r - 1).choose (r - 2)) := by
        simpa [hkOne, Nat.sub_sub] using hPbad
      exact False.elim ((ordinary_outside_no_bad_singleton H W v r hE
        hPE hPcardOne) hPbadOne)
    by_cases hkTwo : k = 2
    · have hPbadTwo : P ∈ badMissingSets H W v r 2
          ((W.card - r - 2).choose (r - 3)) := by
        simpa [hkTwo, Nat.sub_sub] using hPbad
      exact ordinary_outside_bad_pair_mem_dirty H W v r hE hPbadTwo hPE
    have hkThree : 3 ≤ k := by omega
    by_cases hNo : NoSmallerBadSubset H W v r k E
    · apply Finset.mem_union_right
      unfold actualHigherBadRootEdges
      apply Finset.mem_biUnion.mpr
      refine ⟨k, Finset.mem_Icc.mpr ⟨hkThree, hkBound⟩, ?_⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨P, hPbad, ?_⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hE, hNo⟩, hPE⟩
    · unfold NoSmallerBadSubset at hNo
      push Not at hNo
      obtain ⟨j, hjPos, hjSmall, Q, hQE, hQcard, hQbad⟩ := hNo
      exact ih j hjSmall hjPos (by omega) Q hQE hQcard hQbad

/-- The surviving ordinary outside family is genuinely free of bad
roots in every size relevant to non-linear intersections. -/
theorem ordinary_outside_after_cleaning_bad_free
    (H : Family α) (W : Edge α) (v : α) (r : ℕ)
    {E : Edge α}
    (hE : E ∈ ordinaryOutsideFamily H W v r \
      actualDirtyOutsideEdges H W v r) :
    BadFreeOutsideEdge H W v r E := by
  have hData := Finset.mem_sdiff.mp hE
  intro k hkPos hkBound P hPE hPcard hPbad
  exact hData.2 (ordinary_outside_bad_root_mem_dirty H W v r
    hData.1 k hkPos hkBound P hPE hPcard hPbad)

/-- The actual deletion family lies in the ordinary outside family. -/
theorem actual_dirty_outside_subset_ordinary
    (H : Family α) (W : Edge α) (v : α) (r : ℕ) :
    actualDirtyOutsideEdges H W v r ⊆
      ordinaryOutsideFamily H W v r := by
  classical
  intro E hE
  rcases Finset.mem_union.mp hE with hPair | hHigher
  · obtain ⟨P, _hP, hPE⟩ := Finset.mem_biUnion.mp hPair
    exact (Finset.mem_filter.mp hPE).1
  · obtain ⟨k, _hk, hRoot⟩ := Finset.mem_biUnion.mp hHigher
    obtain ⟨P, _hP, hPE⟩ := Finset.mem_biUnion.mp hRoot
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hPE).1).1

/-- The cleaned outside family is linear, as asserted at the end of the
deletion argument for (IV.2.5). -/
theorem ordinary_outside_after_cleaning_linear
    (H : Family α) (W : Edge α) (v : α) (r : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform r H) (hvW : v ∉ W) :
    LinearFamily (ordinaryOutsideFamily H W v r \
      actualDirtyOutsideEdges H W v r) := by
  let C := ordinaryOutsideFamily H W v r \
    actualDirtyOutsideEdges H W v r
  have hCH : C ⊆ H := by
    intro E hE
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hE).1).1
  have hCU : Uniform r C := by
    intro E hE
    exact hUniform (hCH hE)
  have hCW : ∀ E ∈ C, E ⊆ W := by
    intro E hE
    have hEU : E ⊆ W \ badSingletonVertices H W v r :=
      (Finset.mem_filter.mp (Finset.mem_sdiff.mp hE).1).2
    exact hEU.trans Finset.sdiff_subset
  exact bad_free_outside_family_linear hAdm hCH hCU hCW hvW
    (fun E hE => ordinary_outside_after_cleaning_bad_free H W v r hE)

/-- Exact finite form of (IV.2.7): the clean contribution is paid by
ordinary vertices and missing facets inside `U`, while each deleted edge
is charged at full rank. -/
theorem ordinary_outside_incidence_with_deletion
    (H : Family α) (W : Edge α) (v : α) (r : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hr : 3 ≤ r) (hvW : v ∉ W) :
    let U := W \ badSingletonVertices H W v r
    r * (ordinaryOutsideFamily H W v r).card ≤
      U.card + (missingStarFacets H U v r).card +
        r * (actualDirtyOutsideEdges H W v r).card := by
  classical
  let U := W \ badSingletonVertices H W v r
  let B := ordinaryOutsideFamily H W v r
  let X := actualDirtyOutsideEdges H W v r
  let C := B \ X
  have hXSub : X ⊆ B := actual_dirty_outside_subset_ordinary H W v r
  have hCH : C ⊆ H := by
    intro E hE
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hE).1).1
  have hCU : Uniform r C := by
    intro E hE
    exact hUniform (hCH hE)
  have hCSub : ∀ E ∈ C, E ⊆ U := by
    intro E hE
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hE).1).2
  have hvU : v ∉ U := by
    intro hv
    exact hvW ((Finset.mem_sdiff.mp hv).1)
  have hLin : LinearFamily C :=
    ordinary_outside_after_cleaning_linear H W v r hAdm hUniform hvW
  have hInc : r * C.card ≤ U.card +
      (missingStarFacets H U v r).card :=
    linear_near_star_incidence_bound hAdm hCH hCU hLin hr hCSub hvU
  have hPartition : B.card = C.card + X.card := by
    have hDiff := Finset.card_sdiff_add_card_inter B X
    have hInter : B ∩ X = X := Finset.inter_eq_right.mpr hXSub
    simpa only [C, hInter] using hDiff.symm
  dsimp [U, B, X, C]
  rw [hPartition]
  calc
    r * (C.card + X.card) = r * C.card + r * X.card := Nat.mul_add _ _ _
    _ ≤ U.card + (missingStarFacets H U v r).card +
          r * X.card := Nat.add_le_add_right hInc _

/-- The ordinary-edge inequality with pair and higher-root deletion
charges displayed separately. This is the exact finite accounting form
preceding the asymptotic estimate (IV.2.7). -/
theorem ordinary_outside_incidence_with_split_deletion
    (H : Family α) (W : Edge α) (v : α) (r : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hr : 3 ≤ r) (hvW : v ∉ W) :
    let U := W \ badSingletonVertices H W v r
    let Bad₂ := badMissingSets H W v r 2
      ((W.card - r - 2).choose (r - 3))
    r * (ordinaryOutsideFamily H W v r).card ≤
      U.card + (missingStarFacets H U v r).card +
        r * ((badPairEdges (ordinaryOutsideFamily H W v r) Bad₂).card +
          (actualHigherBadRootEdges H W v r).card) := by
  classical
  let U := W \ badSingletonVertices H W v r
  let Bad₂ := badMissingSets H W v r 2
    ((W.card - r - 2).choose (r - 3))
  let X₁ := badPairEdges (ordinaryOutsideFamily H W v r) Bad₂
  let X₂ := actualHigherBadRootEdges H W v r
  have hInc := ordinary_outside_incidence_with_deletion H W v r
    hAdm hUniform hr hvW
  have hUnion : (actualDirtyOutsideEdges H W v r).card ≤
      X₁.card + X₂.card := by
    exact Finset.card_union_le _ _
  have hMul := Nat.mul_le_mul_left r hUnion
  dsimp [U, Bad₂, X₁, X₂] at *
  omega

end JSP523
