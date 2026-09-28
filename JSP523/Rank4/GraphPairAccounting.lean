import JSP523.Rank4.GraphVertexDeficit

/-!
# Ordered pair accounting for common neighbors

The manuscript counts unordered pairs.  Each off-diagonal ordered pair is
counted twice, so these rational sums have the same normalization while
avoiding a quotient representation during the graph-deficit proof.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

def orderedCommonPairCount (F : SimpleGraph α) [DecidableRel F.Adj] : ℚ :=
  ∑ x : α, ∑ y ∈ Finset.univ.erase x,
    if 0 < graphCommonMultiplicity F x y then (1 : ℚ) else 0

def orderedUniquePairCount (F : SimpleGraph α) [DecidableRel F.Adj] : ℚ :=
  ∑ x : α, ∑ y ∈ Finset.univ.erase x,
    if graphCommonMultiplicity F x y = 1 then (1 : ℚ) else 0

private theorem capped_pair_scalar (m : ℕ) :
    (min 2 m : ℚ) + (if m = 1 then 1 else 0) =
      2 * (if 0 < m then 1 else 0) := by
  rcases (by omega : m = 0 ∨ m = 1 ∨ 2 ≤ m) with h | h | h
  · subst m; norm_num
  · subst m; norm_num
  · have hne : m ≠ 1 := by omega
    have hpos : 0 < m := by omega
    simpa [hne, hpos] using h

/-- Exact conversion between capped multiplicities and the common-pair
and unique-pair counts. -/
theorem capped_common_pair_accounting
    (F : SimpleGraph α) [DecidableRel F.Adj] :
    (∑ x : α, graphOffDiagonalCappedSum F x) +
      orderedUniquePairCount F =
      2 * orderedCommonPairCount F := by
  unfold graphOffDiagonalCappedSum orderedUniquePairCount
    orderedCommonPairCount
  rw [← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib]
  simp_rw [capped_pair_scalar]
  simp only [Finset.mul_sum]

end JSP523.Rank4
