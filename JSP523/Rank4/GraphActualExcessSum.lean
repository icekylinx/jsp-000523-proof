import JSP523.Rank4.GraphActualExcessReindex

/-!
# Summing actual on-label pair-link excess

The label-containing base pairs are reindexed by tail vertices of the
native graph. This module keeps the sum algebra separate from the
finite-set bijection.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
/-- Reindex any finite sum over on-label base pairs by its unique tail
vertex. -/
theorem on_label_pair_bases_sum_eq_tail_sum
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (hCenters : UniqueCommonRootCenters D.K D.ground)
    (P : Edge α) (hUsed : P ∈ nonemptyCommonRoots D.K D.ground)
    (f : Edge α → ℕ) :
    let z := chosenCommonRootLabel D.K D.ground fallback hCenters P
    ((D.ground.powersetCard 2).filter
      (fun Q => z ∈ Q ∧ Disjoint Q P)).sum f =
      (D.ground \ insert z P).sum
        (fun w => f ({z, w} : Edge α)) := by
  classical
  dsimp only
  let z := chosenCommonRootLabel D.K D.ground fallback hCenters P
  change ((D.ground.powersetCard 2).filter
      (fun Q => z ∈ Q ∧ Disjoint Q P)).sum f =
    (D.ground \ insert z P).sum
      (fun w => f ({z, w} : Edge α))
  rw [← on_label_pair_bases_eq_tail_image D fallback hCenters P hUsed]
  exact Finset.sum_image
    (on_label_tail_pair_map_injOn D fallback hCenters P)

end JSP523.Rank4
