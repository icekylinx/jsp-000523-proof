import JSP523.Rank4.GraphEdgeAccounting
import Mathlib.Data.Nat.Choose.Cast

/-!
# Exact common-neighbor excess ledger

The graph term `W = ∑ₓ choose (degree x) 2` is the total common-neighbor
multiplicity over unordered pairs. Subtracting the common-pair indicator
leaves exactly the positive multiplicity excess. We use ordered pairs and
rational coefficients so that no quotient of a pair type is needed.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The ordered common-neighbor excess of a finite graph. -/
def orderedCommonExcessCount (F : SimpleGraph α)
    [DecidableRel F.Adj] : ℚ :=
  ∑ x : α, ∑ y ∈ Finset.univ.erase x,
    ((graphCommonMultiplicity F x y - 1 : ℕ) : ℚ)

/-- The off-diagonal common-neighbor multiplicity at a vertex is its
neighbor-degree sum minus its own degree. -/
theorem ordered_common_multiplicity_at_vertex
    (F : SimpleGraph α) [DecidableRel F.Adj] (x : α) :
    (∑ y ∈ Finset.univ.erase x,
      (graphCommonMultiplicity F x y : ℚ)) =
      (graphNeighborDegreeSum F x : ℚ) - F.degree x := by
  have hTotal := sum_graphCommonMultiplicity F x
  have hTotalQ :
      (∑ y : α, (graphCommonMultiplicity F x y : ℚ)) =
        (graphNeighborDegreeSum F x : ℚ) := by
    exact_mod_cast hTotal
  have hSplit := Finset.sum_erase_add Finset.univ
    (fun y : α => (graphCommonMultiplicity F x y : ℚ))
    (Finset.mem_univ x)
  rw [graphCommonMultiplicity_self] at hSplit
  linarith

omit [DecidableEq α] in
/-- Summing neighbor degrees over all vertices counts each degree once
per incident edge, hence gives the sum of squared degrees. -/
theorem sum_graph_neighbor_degrees_eq_sum_degree_squares
    (F : SimpleGraph α) [DecidableRel F.Adj] :
    (∑ x : α, (graphNeighborDegreeSum F x : ℚ)) =
      ∑ x : α, (F.degree x : ℚ) ^ 2 := by
  calc
    (∑ x : α, (graphNeighborDegreeSum F x : ℚ)) =
        ∑ x : α, ∑ y ∈ F.neighborFinset x, (F.degree y : ℚ) := by
          apply Finset.sum_congr rfl
          intro x _
          simp only [graphNeighborDegreeSum, Nat.cast_sum]
    _ = ∑ x : α, ∑ y ∈ F.neighborFinset x,
          (F.degree x : ℚ) := by
            exact sum_neighborFinset_swap F (fun _ y => (F.degree y : ℚ))
    _ = ∑ x : α, (F.degree x : ℚ) ^ 2 := by
          apply Finset.sum_congr rfl
          intro x _
          simp only [Finset.sum_const, nsmul_eq_mul,
            SimpleGraph.card_neighborFinset_eq_degree]
          ring

/-- The degree-pair count equals half of the off-diagonal ordered
common-neighbor multiplicity sum. -/
theorem ordered_common_multiplicity_eq_twice_degree_pairs
    (F : SimpleGraph α) [DecidableRel F.Adj] :
    (∑ x : α, ∑ y ∈ Finset.univ.erase x,
      (graphCommonMultiplicity F x y : ℚ)) =
      2 * ∑ x : α, ((F.degree x).choose 2 : ℚ) := by
  have hAt : ∀ x : α,
      (∑ y ∈ Finset.univ.erase x,
        (graphCommonMultiplicity F x y : ℚ)) =
      (graphNeighborDegreeSum F x : ℚ) - F.degree x :=
    ordered_common_multiplicity_at_vertex F
  have hChoose (x : α) :
      2 * ((F.degree x).choose 2 : ℚ) =
        (F.degree x : ℚ) ^ 2 - F.degree x := by
    rw [Nat.cast_choose_two]
    ring
  calc
    (∑ x : α, ∑ y ∈ Finset.univ.erase x,
      (graphCommonMultiplicity F x y : ℚ)) =
        ∑ x : α, ((graphNeighborDegreeSum F x : ℚ) - F.degree x) := by
          apply Finset.sum_congr rfl
          intro x _
          exact hAt x
    _ = (∑ x : α, (F.degree x : ℚ) ^ 2) -
        ∑ x : α, (F.degree x : ℚ) := by
          rw [Finset.sum_sub_distrib,
            sum_graph_neighbor_degrees_eq_sum_degree_squares]
    _ = 2 * ∑ x : α, ((F.degree x).choose 2 : ℚ) := by
          rw [Finset.mul_sum]
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro x _
          exact (hChoose x).symm

private theorem common_excess_scalar (m : ℕ) :
    (m : ℚ) = ((m - 1 : ℕ) : ℚ) +
      if 0 < m then 1 else 0 := by
  cases m with
  | zero => norm_num
  | succ n =>
      simp only [Nat.succ_sub_one, Nat.zero_lt_succ, ite_true]
      push_cast
      ring

/-- Exact graph identity `2W = 2q + excess_ordered`, where `W` is the
sum of degree-binomial terms and `q` counts unordered pairs with a
common neighbor. -/
theorem ordered_common_excess_ledger
    (F : SimpleGraph α) [DecidableRel F.Adj] :
    2 * (∑ x : α, ((F.degree x).choose 2 : ℚ)) =
      orderedCommonExcessCount F + orderedCommonPairCount F := by
  rw [← ordered_common_multiplicity_eq_twice_degree_pairs]
  unfold orderedCommonExcessCount orderedCommonPairCount
  rw [← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  exact common_excess_scalar (graphCommonMultiplicity F x y)

end JSP523.Rank4
