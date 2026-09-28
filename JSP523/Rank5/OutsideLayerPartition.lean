import JSP523.Rank5.ActualHigherBadRoot
import JSP523.Rank5.ExceptionalOneVertex
import JSP523.Rank5.ExceptionalMultiVertex

/-!
# Partition of outside edges by exceptional-vertex count

This is the finite layer decomposition used in §IV.2.2 of
`paper/proof.pdf`. The four classes are the ordinary
outside family `B[U]`, the one-exceptional-vertex class `b₁`, the mixed
classes `b₂+⋯+b_{r-1}`, and the all-exceptional class `b_r`.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

/-- Every outside edge lies in one of the four actual classes used by
the contraction argument. -/
theorem outside_edge_layer_cover
    (H : Family α) (W : Edge α) (v : α) (r : ℕ) :
    outsideFamily H W ⊆
      (((ordinaryOutsideFamily H W v r ∪
          outsideOneBadSingleton H W v r) ∪
          outsideSeveralBadWithOrdinary H W v r) ∪
          outsideFamily H (badSingletonVertices H W v r)) := by
  classical
  intro E hE
  let D := badSingletonVertices H W v r
  let U := W \ D
  have hEH : E ∈ H := (Finset.mem_filter.mp hE).1
  have hEW : E ⊆ W := (Finset.mem_filter.mp hE).2
  by_cases hZero : (E ∩ D).card = 0
  · have hNoD : E ∩ D = ∅ := Finset.card_eq_zero.mp hZero
    have hEU : E ⊆ U := by
      intro x hxE
      refine Finset.mem_sdiff.mpr ⟨hEW hxE, ?_⟩
      intro hxD
      have hxInter : x ∈ E ∩ D := Finset.mem_inter.mpr ⟨hxE, hxD⟩
      rw [hNoD] at hxInter
      simp at hxInter
    exact Finset.mem_union.mpr (Or.inl
      (Finset.mem_union.mpr (Or.inl
        (Finset.mem_union.mpr (Or.inl
          (Finset.mem_filter.mpr ⟨hEH, hEU⟩))))))
  by_cases hOne : (E ∩ D).card = 1
  · exact Finset.mem_union.mpr (Or.inl
      (Finset.mem_union.mpr (Or.inl
        (Finset.mem_union.mpr (Or.inr
          (Finset.mem_filter.mpr ⟨hE, hOne⟩))))))
  have hMany : 2 ≤ (E ∩ D).card := by omega
  by_cases hOrd : (E ∩ U).Nonempty
  · exact Finset.mem_union.mpr (Or.inl
      (Finset.mem_union.mpr (Or.inr
        (Finset.mem_filter.mpr ⟨hE, hMany, hOrd⟩))))
  · have hED : E ⊆ D := by
      intro x hxE
      by_contra hxNotD
      have hxU : x ∈ U := Finset.mem_sdiff.mpr ⟨hEW hxE, hxNotD⟩
      exact hOrd ⟨x, Finset.mem_inter.mpr ⟨hxE, hxU⟩⟩
    exact Finset.mem_union.mpr (Or.inr
      (Finset.mem_filter.mpr ⟨hEH, hED⟩))

/-- The corresponding cardinal bound, without assuming disjointness or
rank uniformity. -/
theorem outside_edge_layer_card_bound
    (H : Family α) (W : Edge α) (v : α) (r : ℕ) :
    (outsideFamily H W).card ≤
      (ordinaryOutsideFamily H W v r).card +
      (outsideOneBadSingleton H W v r).card +
      (outsideSeveralBadWithOrdinary H W v r).card +
      (outsideFamily H (badSingletonVertices H W v r)).card := by
  have hCover := Finset.card_le_card (outside_edge_layer_cover H W v r)
  have hUnion₁ := Finset.card_union_le
    (ordinaryOutsideFamily H W v r) (outsideOneBadSingleton H W v r)
  have hUnion₂ := Finset.card_union_le
    (ordinaryOutsideFamily H W v r ∪ outsideOneBadSingleton H W v r)
    (outsideSeveralBadWithOrdinary H W v r)
  have hUnion₃ := Finset.card_union_le
    ((ordinaryOutsideFamily H W v r ∪ outsideOneBadSingleton H W v r) ∪
      outsideSeveralBadWithOrdinary H W v r)
    (outsideFamily H (badSingletonVertices H W v r))
  omega

end JSP523
