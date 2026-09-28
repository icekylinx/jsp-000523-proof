import JSP523.Rank4.GraphPairAccounting
import JSP523.Rank4.GraphPaymentScalar
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.BigOperators.Field

/-!
# Directed edge accounting for the graph deficit

The local `D_x` estimates become a global graph inequality after the
degree-ratio terms are paired across the two orientations of every edge.
This file establishes the finite sum identities for that pairing.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α]

/-- Swapping the two ends of every directed edge preserves a finite sum. -/
theorem sum_neighborFinset_swap
    (F : SimpleGraph α) [DecidableRel F.Adj]
    (f : α → α → ℚ) :
    (∑ x : α, ∑ y ∈ F.neighborFinset x, f x y) =
      ∑ x : α, ∑ y ∈ F.neighborFinset x, f y x := by
  have hSum (x : α) (g : α → ℚ) :
      (∑ y ∈ F.neighborFinset x, g y) =
        ∑ y : α, if F.Adj x y then g y else 0 := by
    rw [F.neighborFinset_eq_filter]
    simp only [Finset.sum_filter]
  calc
    (∑ x : α, ∑ y ∈ F.neighborFinset x, f x y) =
        ∑ x : α, ∑ y : α,
          if F.Adj x y then f x y else 0 := by
            apply Finset.sum_congr rfl
            intro x _
            exact hSum x (f x)
    _ = ∑ y : α, ∑ x : α,
          if F.Adj x y then f x y else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ y : α, ∑ x : α,
          if F.Adj y x then f x y else 0 := by
            simp_rw [F.adj_comm]
    _ = ∑ x : α, ∑ y ∈ F.neighborFinset x, f y x := by
            apply Finset.sum_congr rfl
            intro x _
            exact (hSum x (fun y => f y x)).symm

/-- The directed degree-ratio excess, with every graph edge counted in
both orientations. -/
def directedRatioExcess (F : SimpleGraph α) [DecidableRel F.Adj] : ℚ :=
  ∑ x : α, ∑ y ∈ F.neighborFinset x,
    ((F.degree y : ℚ) / (F.degree x : ℚ) - 1)

/-- Leaf corrections allocated to the outgoing orientation of leaf edges. -/
def directedLeafCredit (F : SimpleGraph α) [DecidableRel F.Adj] : ℚ :=
  ∑ x : α, ∑ y ∈ F.neighborFinset x,
    if F.degree x = 1 then (F.degree y : ℚ) - 1 else 0

def leafCreditAt (F : SimpleGraph α) [DecidableRel F.Adj] (x : α) : ℚ :=
  ∑ y ∈ F.neighborFinset x,
    if F.degree x = 1 then (F.degree y : ℚ) - 1 else 0

def activeVertexCount (F : SimpleGraph α) [DecidableRel F.Adj] : ℚ :=
  ∑ x : α, if 0 < F.degree x then (1 : ℚ) else 0

theorem leafCreditAt_eq_capped
    (F : SimpleGraph α) [DecidableEq α] [DecidableRel F.Adj]
    (x : α) :
    leafCreditAt F x =
      if F.degree x = 1 then graphOffDiagonalCappedSum F x else 0 := by
  by_cases hx : F.degree x = 1
  · obtain ⟨z, hAdj, hS⟩ := graphOffDiagonalCappedSum_leaf F x hx
    have hNcard : (F.neighborFinset x).card = 1 := hx
    obtain ⟨z', hN⟩ := Finset.card_eq_one.mp hNcard
    have hzMem : z ∈ F.neighborFinset x := by
      simpa [SimpleGraph.mem_neighborFinset] using hAdj
    rw [hN] at hzMem
    have hzz' : z = z' := by simpa using hzMem
    subst z'
    simp [leafCreditAt, hx, hN, hS]
  · simp [leafCreditAt, hx]

/-- Summing the scalar edge inequality across both orientations pays the
entire leaf correction. -/
theorem directed_ratio_pays_leaf_credit
    (F : SimpleGraph α) [DecidableRel F.Adj] :
    directedLeafCredit F ≤ 2 * directedRatioExcess F := by
  let c : α → α → ℚ := fun x y =>
    if F.degree x = 1 then (F.degree y : ℚ) - 1 else 0
  let r : α → α → ℚ := fun x y =>
    (F.degree y : ℚ) / (F.degree x : ℚ) - 1
  have hPoint (x y : α) (hy : y ∈ F.neighborFinset x) :
      c x y + c y x ≤ 2 * (r x y + r y x) := by
    have hdx : 1 ≤ F.degree x := by
      have hpos : 0 < (F.neighborFinset x).card :=
        Finset.card_pos.mpr ⟨y, hy⟩
      exact hpos
    have hxy : F.Adj x y := by
      simpa [SimpleGraph.mem_neighborFinset] using hy
    have hyx : x ∈ F.neighborFinset y := by
      simpa [SimpleGraph.mem_neighborFinset] using hxy.symm
    have hdy : 1 ≤ F.degree y := by
      have hpos : 0 < (F.neighborFinset y).card :=
        Finset.card_pos.mpr ⟨x, hyx⟩
      exact hpos
    have hScalar := edge_ratio_pays_leaf_correction
      (F.degree x) (F.degree y) hdx hdy
    dsimp [c, r]
    linarith
  have hTotal :
      (∑ x : α, ∑ y ∈ F.neighborFinset x,
        (c x y + c y x)) ≤
      ∑ x : α, ∑ y ∈ F.neighborFinset x,
        2 * (r x y + r y x) := by
    apply Finset.sum_le_sum
    intro x _
    apply Finset.sum_le_sum
    intro y hy
    exact hPoint x y hy
  have hSwapC := sum_neighborFinset_swap F c
  have hSwapR := sum_neighborFinset_swap F r
  have hLeft :
      (∑ x : α, ∑ y ∈ F.neighborFinset x,
        (c x y + c y x)) = 2 * directedLeafCredit F := by
    simp_rw [Finset.sum_add_distrib]
    change (∑ x : α, ∑ y ∈ F.neighborFinset x, c x y) +
      (∑ x : α, ∑ y ∈ F.neighborFinset x, c y x) = _
    rw [← hSwapC]
    unfold directedLeafCredit
    dsimp [c]
    ring
  have hRight :
      (∑ x : α, ∑ y ∈ F.neighborFinset x,
        2 * (r x y + r y x)) = 4 * directedRatioExcess F := by
    simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    change 2 * (∑ x : α, ∑ y ∈ F.neighborFinset x, r x y) +
      2 * (∑ x : α, ∑ y ∈ F.neighborFinset x, r y x) = _
    rw [← hSwapR]
    have hRdef : (∑ x : α, ∑ y ∈ F.neighborFinset x, r x y) =
        directedRatioExcess F := by
      simp only [r, directedRatioExcess]
    rw [hRdef]
    ring
  rw [hLeft, hRight] at hTotal
  linarith

/-- The oriented ratio sum is the difference between the neighbor-degree
sum divided by vertex degree and twice the number of graph edges. -/
theorem directedRatioExcess_eq_degree_sum
    (F : SimpleGraph α) [DecidableRel F.Adj] :
    directedRatioExcess F =
      (∑ x : α,
        (graphNeighborDegreeSum F x : ℚ) / (F.degree x : ℚ)) -
      2 * (F.edgeFinset.card : ℚ) := by
  have hAt (x : α) :
      (graphNeighborDegreeSum F x : ℚ) / (F.degree x : ℚ) =
        ∑ y ∈ F.neighborFinset x,
          (F.degree y : ℚ) / (F.degree x : ℚ) := by
    unfold graphNeighborDegreeSum
    push_cast
    exact Finset.sum_div _ _ _
  have hOnes (x : α) :
      (∑ _y ∈ F.neighborFinset x, (1 : ℚ)) =
        (F.degree x : ℚ) := by
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one,
      SimpleGraph.card_neighborFinset_eq_degree]
  have hHand : (∑ x : α, (F.degree x : ℚ)) =
      2 * (F.edgeFinset.card : ℚ) := by
    exact_mod_cast F.sum_degrees_eq_twice_card_edges
  unfold directedRatioExcess
  simp_rw [Finset.sum_sub_distrib]
  simp_rw [← hAt, hOnes]
  rw [hHand]

/-- At each vertex, the capped common-neighbor sum, two units for a
nonisolated vertex, and the leaf correction pay twice the normalized
neighbor-degree sum. -/
theorem vertex_capped_plus_leaf_bound
    (F : SimpleGraph α) [DecidableEq α] [DecidableRel F.Adj]
    (x : α) :
    2 * (graphNeighborDegreeSum F x : ℚ) / (F.degree x : ℚ) ≤
      graphOffDiagonalCappedSum F x +
      2 * (if 0 < F.degree x then (1 : ℚ) else 0) +
      leafCreditAt F x := by
  by_cases hx0 : F.degree x = 0
  · have hA := graphNeighborDegreeSum_isolated F x hx0
    have hS := graphOffDiagonalCappedSum_isolated F x hx0
    have hC : leafCreditAt F x = 0 := by
      rw [leafCreditAt_eq_capped]
      simp [hx0]
    simp [hx0, hA, hS, hC]
  by_cases hx1 : F.degree x = 1
  · obtain ⟨z, hAdj, hS⟩ := graphOffDiagonalCappedSum_leaf F x hx1
    have hNcard : (F.neighborFinset x).card = 1 := hx1
    obtain ⟨z', hN⟩ := Finset.card_eq_one.mp hNcard
    have hzMem : z ∈ F.neighborFinset x := by
      simpa [SimpleGraph.mem_neighborFinset] using hAdj
    rw [hN] at hzMem
    have hzz' : z = z' := by simpa using hzMem
    subst z'
    have hA : graphNeighborDegreeSum F x = F.degree z := by
      simp [graphNeighborDegreeSum, hN]
    have hC : leafCreditAt F x = graphOffDiagonalCappedSum F x := by
      rw [leafCreditAt_eq_capped]
      simp [hx1]
    rw [hA, hC, hS, hx1]
    norm_num
    linarith
  · have hx2 : 2 ≤ F.degree x := by omega
    have hDef := graphVertexDeficit_nonneg F x hx2
    rw [graphVertexDeficit_eq_manuscript F x hx2] at hDef
    have hC : leafCreditAt F x = 0 := by
      rw [leafCreditAt_eq_capped]
      simp [hx1]
    rw [hC]
    have hxPos : 0 < F.degree x := by omega
    have hIndicator : (if 0 < F.degree x then (1 : ℚ) else 0) = 1 := by
      simp [hxPos]
    rw [hIndicator]
    linarith

/-- The unmarked graph inequality in ordered-pair normalization:
`∑_x S_x + 2v(F) ≥ 4e(F)`.  Combined with the pair-accounting identity,
this is `q(F)-e(F)+v(F)/2 ≥ U(F)/2`, stronger than the basic
`q(F)-e(F)+v(F)/2 ≥ 0`. -/
theorem capped_total_ge_edges
    (F : SimpleGraph α) [DecidableEq α] [DecidableRel F.Adj] :
    4 * (F.edgeFinset.card : ℚ) ≤
      (∑ x : α, graphOffDiagonalCappedSum F x) +
      2 * activeVertexCount F := by
  have hPoint := Finset.sum_le_sum (s := Finset.univ)
    (fun x _ => vertex_capped_plus_leaf_bound F x)
  have hAt (x : α) :
      2 * (graphNeighborDegreeSum F x : ℚ) / (F.degree x : ℚ) =
      2 * ((graphNeighborDegreeSum F x : ℚ) / (F.degree x : ℚ)) := by
    ring
  simp_rw [hAt] at hPoint
  simp_rw [Finset.sum_add_distrib] at hPoint
  have hA :
      (∑ x : α, 2 *
        ((graphNeighborDegreeSum F x : ℚ) / (F.degree x : ℚ))) =
      2 * (∑ x : α,
        (graphNeighborDegreeSum F x : ℚ) / (F.degree x : ℚ)) := by
    rw [Finset.mul_sum]
  have hV :
      (∑ x : α,
        2 * (if 0 < F.degree x then (1 : ℚ) else 0)) =
      2 * activeVertexCount F := by
    unfold activeVertexCount
    rw [Finset.mul_sum]
  have hC : (∑ x : α, leafCreditAt F x) =
      directedLeafCredit F := rfl
  rw [hA, hV, hC] at hPoint
  have hRatio := directedRatioExcess_eq_degree_sum F
  have hLeaf := directed_ratio_pays_leaf_credit F
  linarith

/-- The manuscript's graph deficit, with unordered pair counts represented
as half their ordered counts. -/
def graphDeficit (F : SimpleGraph α) [DecidableRel F.Adj]
    [DecidableEq α] : ℚ :=
  orderedCommonPairCount F / 2 - (F.edgeFinset.card : ℚ) +
    activeVertexCount F / 2

/-- Rank-four graph lemma, unmarked form of equation (III.B.5).  The stronger
unique-pair credit is retained for the later colored-slot payment. -/
theorem graphDeficit_ge_unique_pair_half
    (F : SimpleGraph α) [DecidableEq α] [DecidableRel F.Adj] :
    orderedUniquePairCount F / 4 ≤ graphDeficit F := by
  have hPairs := capped_common_pair_accounting F
  have hEdges := capped_total_ge_edges F
  unfold graphDeficit
  linarith

theorem orderedUniquePairCount_nonneg
    (F : SimpleGraph α) [DecidableEq α] [DecidableRel F.Adj] :
    0 ≤ orderedUniquePairCount F := by
  unfold orderedUniquePairCount
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro y _
  split_ifs <;> norm_num

theorem graphDeficit_nonneg
    (F : SimpleGraph α) [DecidableEq α] [DecidableRel F.Adj] :
    0 ≤ graphDeficit F := by
  have hCredit := graphDeficit_ge_unique_pair_half F
  have hNonneg := orderedUniquePairCount_nonneg F
  linarith

/-- The nonnegative local deficit is used only at vertices of degree at
least two; zero and leaf vertices have separate exact formulas. -/
def nonleafVertexDeficit (F : SimpleGraph α) [DecidableRel F.Adj]
    (x : α) : ℚ :=
  if 2 ≤ F.degree x then graphVertexDeficit F x else 0

theorem vertex_capped_exact_accounting
    (F : SimpleGraph α) [DecidableEq α] [DecidableRel F.Adj]
    (x : α) :
    graphOffDiagonalCappedSum F x +
      2 * (if 0 < F.degree x then (1 : ℚ) else 0) +
      leafCreditAt F x =
    2 * (graphNeighborDegreeSum F x : ℚ) / (F.degree x : ℚ) +
      nonleafVertexDeficit F x := by
  by_cases hx0 : F.degree x = 0
  · have hA := graphNeighborDegreeSum_isolated F x hx0
    have hS := graphOffDiagonalCappedSum_isolated F x hx0
    have hC : leafCreditAt F x = 0 := by
      rw [leafCreditAt_eq_capped]
      simp [hx0]
    simp [nonleafVertexDeficit, hx0, hA, hS, hC]
  by_cases hx1 : F.degree x = 1
  · obtain ⟨z, hAdj, hS⟩ := graphOffDiagonalCappedSum_leaf F x hx1
    have hNcard : (F.neighborFinset x).card = 1 := hx1
    obtain ⟨z', hN⟩ := Finset.card_eq_one.mp hNcard
    have hzMem : z ∈ F.neighborFinset x := by
      simpa [SimpleGraph.mem_neighborFinset] using hAdj
    rw [hN] at hzMem
    have hzz' : z = z' := by simpa using hzMem
    subst z'
    have hA : graphNeighborDegreeSum F x = F.degree z := by
      simp [graphNeighborDegreeSum, hN]
    have hC : leafCreditAt F x = graphOffDiagonalCappedSum F x := by
      rw [leafCreditAt_eq_capped]
      simp [hx1]
    have hD : nonleafVertexDeficit F x = 0 := by
      simp [nonleafVertexDeficit, hx1]
    rw [hA, hC, hS, hD, hx1]
    norm_num
    ring
  · have hx2 : 2 ≤ F.degree x := by omega
    have hD := graphVertexDeficit_eq_manuscript F x hx2
    have hC : leafCreditAt F x = 0 := by
      rw [leafCreditAt_eq_capped]
      simp [hx1]
    have hIndicator : (if 0 < F.degree x then (1 : ℚ) else 0) = 1 := by
      simp [show 0 < F.degree x by omega]
    rw [hC, hIndicator]
    simp only [nonleafVertexDeficit, hx2, ↓reduceIte]
    linarith

/-- Exact ordered-pair version of the manuscript's equation (III.B.6).  The
three right-hand terms are respectively the nonleaf `D_x` sum, the degree
ratio term, and the leaf subtraction. -/
theorem graphDeficit_exact_local_identity
    (F : SimpleGraph α) [DecidableEq α] [DecidableRel F.Adj] :
    4 * graphDeficit F - orderedUniquePairCount F =
      (∑ x : α, nonleafVertexDeficit F x) +
      2 * directedRatioExcess F - directedLeafCredit F := by
  have hPoint := Finset.sum_congr rfl
    (fun x (_ : x ∈ (Finset.univ : Finset α)) =>
      vertex_capped_exact_accounting F x)
  have hPairs := capped_common_pair_accounting F
  have hRatio := directedRatioExcess_eq_degree_sum F
  unfold graphDeficit
  simp_rw [Finset.sum_add_distrib] at hPoint
  have hC : (∑ x : α, leafCreditAt F x) =
      directedLeafCredit F := rfl
  have hV :
      (∑ x : α,
        2 * (if 0 < F.degree x then (1 : ℚ) else 0)) =
      2 * activeVertexCount F := by
    unfold activeVertexCount
    rw [Finset.mul_sum]
  have hA :
      (∑ x : α,
        2 * (graphNeighborDegreeSum F x : ℚ) / (F.degree x : ℚ)) =
      2 * (∑ x : α,
        (graphNeighborDegreeSum F x : ℚ) / (F.degree x : ℚ)) := by
    simp_rw [show ∀ x : α,
      2 * (graphNeighborDegreeSum F x : ℚ) / (F.degree x : ℚ) =
        2 * ((graphNeighborDegreeSum F x : ℚ) / (F.degree x : ℚ))
      from fun _ => by ring]
    rw [Finset.mul_sum]
  rw [hC, hV, hA] at hPoint
  linarith

end JSP523.Rank4
