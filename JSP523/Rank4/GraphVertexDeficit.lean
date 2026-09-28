import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-!
# A nonnegative local deficit on an actual finite graph

This is the `D_x ≥ 0` step of equation (III.B.6) in the rank-four proof.  The
common-neighbor multiplicities are computed from a genuine `SimpleGraph`.
The later global identity relating these local deficits to
`q(F)-e(F)+v(F)/2` remains separate.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α]

/-- Common-neighbor multiplicity, counted inside the first neighborhood. -/
def graphCommonMultiplicity (F : SimpleGraph α) [DecidableRel F.Adj]
    (x y : α) : ℕ :=
  ((F.neighborFinset x).filter fun z => F.Adj y z).card

theorem graphCommonMultiplicity_eq_inter
    (F : SimpleGraph α) [DecidableEq α] [DecidableRel F.Adj] (x y : α) :
    graphCommonMultiplicity F x y =
      (F.neighborFinset x ∩ F.neighborFinset y).card := by
  unfold graphCommonMultiplicity
  congr 1
  ext z
  simp [SimpleGraph.mem_neighborFinset]

theorem graphCommonMultiplicity_symm
    (F : SimpleGraph α) [DecidableEq α] [DecidableRel F.Adj] (x y : α) :
    graphCommonMultiplicity F x y = graphCommonMultiplicity F y x := by
  rw [graphCommonMultiplicity_eq_inter,
    graphCommonMultiplicity_eq_inter, Finset.inter_comm]

/-- The sum of degrees of all neighbors of `x`. -/
def graphNeighborDegreeSum (F : SimpleGraph α) [DecidableRel F.Adj]
    (x : α) : ℕ :=
  ∑ z ∈ F.neighborFinset x, F.degree z

/-- The capped common-neighbor sum, including the diagonal pair `(x,x)`.
For degree at least two this adds exactly two to the manuscript's `S_x`. -/
def graphCappedCommonSum (F : SimpleGraph α) [DecidableRel F.Adj]
    (x : α) : ℚ :=
  ∑ y : α, (min 2 (graphCommonMultiplicity F x y) : ℚ)

/-- The actual local `D_x`, written with the diagonal term included. -/
def graphVertexDeficit (F : SimpleGraph α) [DecidableRel F.Adj]
    (x : α) : ℚ :=
  graphCappedCommonSum F x -
    2 * (graphNeighborDegreeSum F x : ℚ) / (F.degree x : ℚ)

/-- The manuscript's `S_x` omits the diagonal pair `(x,x)`. -/
def graphOffDiagonalCappedSum (F : SimpleGraph α) [DecidableEq α]
    [DecidableRel F.Adj]
    (x : α) : ℚ :=
  ∑ y ∈ (Finset.univ.erase x),
    (min 2 (graphCommonMultiplicity F x y) : ℚ)

theorem graphCommonMultiplicity_self
    (F : SimpleGraph α) [DecidableRel F.Adj] (x : α) :
    graphCommonMultiplicity F x x = F.degree x := by
  unfold graphCommonMultiplicity SimpleGraph.degree
  congr 1
  ext z
  simp [SimpleGraph.mem_neighborFinset]

theorem graphVertexDeficit_eq_manuscript
    (F : SimpleGraph α) [DecidableEq α] [DecidableRel F.Adj] (x : α)
    (hx : 2 ≤ F.degree x) :
    graphVertexDeficit F x = graphOffDiagonalCappedSum F x -
      2 * (graphNeighborDegreeSum F x : ℚ) / (F.degree x : ℚ) + 2 := by
  have hSplit := Finset.sum_erase_add Finset.univ
    (fun y : α => (min 2 (graphCommonMultiplicity F x y) : ℚ))
    (Finset.mem_univ x)
  have hDiag : min (2 : ℚ) (graphCommonMultiplicity F x x : ℚ) = 2 := by
    rw [graphCommonMultiplicity_self]
    exact min_eq_left (by exact_mod_cast hx)
  unfold graphVertexDeficit graphCappedCommonSum graphOffDiagonalCappedSum
  rw [hDiag] at hSplit
  linarith

theorem graphCommonMultiplicity_le_degree
    (F : SimpleGraph α) [DecidableRel F.Adj] (x y : α) :
    graphCommonMultiplicity F x y ≤ F.degree x := by
  unfold graphCommonMultiplicity SimpleGraph.degree
  exact Finset.card_filter_le _ _

/-- Double-count length-two walks beginning at `x`. -/
theorem sum_graphCommonMultiplicity
    (F : SimpleGraph α) [DecidableRel F.Adj] (x : α) :
    (∑ y : α, graphCommonMultiplicity F x y) =
      graphNeighborDegreeSum F x := by
  classical
  unfold graphCommonMultiplicity graphNeighborDegreeSum
  calc
    (∑ y : α, ((F.neighborFinset x).filter fun z => F.Adj y z).card) =
        ∑ y : α, ∑ z ∈ F.neighborFinset x,
          if F.Adj y z then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro y _
            exact Finset.card_filter _ _
    _ = ∑ z ∈ F.neighborFinset x,
          ∑ y : α, if F.Adj y z then 1 else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ z ∈ F.neighborFinset x, F.degree z := by
          apply Finset.sum_congr rfl
          intro z _
          rw [← Finset.card_filter]
          unfold SimpleGraph.degree
          congr 1
          ext y
          simp [SimpleGraph.mem_neighborFinset, F.adj_comm]

private theorem capped_fraction_le
    (d m : ℕ) (hd : 2 ≤ d) (hm : m ≤ d) :
    (2 * (m : ℚ)) / d ≤ (min 2 m : ℚ) := by
  have hdq : (2 : ℚ) ≤ d := by exact_mod_cast hd
  have hmq : (m : ℚ) ≤ d := by exact_mod_cast hm
  have hdpos : (0 : ℚ) < d := by linarith
  apply (div_le_iff₀ hdpos).mpr
  by_cases hm2 : m ≤ 2
  · have hm2q : (m : ℚ) ≤ 2 := by exact_mod_cast hm2
    rw [min_eq_right hm2q]
    nlinarith [mul_nonneg (show (0 : ℚ) ≤ m by positivity)
      (show (0 : ℚ) ≤ (d : ℚ) - 2 by linarith)]
  · have hm2q : (2 : ℚ) ≤ m := by
      exact_mod_cast (by omega : 2 ≤ m)
    rw [min_eq_left hm2q]
    nlinarith

/-- The manuscript's local graph deficit is nonnegative at every vertex
of degree at least two. -/
theorem graphVertexDeficit_nonneg
    (F : SimpleGraph α) [DecidableRel F.Adj] (x : α)
    (hx : 2 ≤ F.degree x) :
    0 ≤ graphVertexDeficit F x := by
  have hsum := sum_graphCommonMultiplicity F x
  have hsumQ :
      (∑ y : α, (graphCommonMultiplicity F x y : ℚ)) =
        (graphNeighborDegreeSum F x : ℚ) := by
    exact_mod_cast hsum
  have hterm : ∀ y : α,
      (2 * (graphCommonMultiplicity F x y : ℚ)) /
          (F.degree x : ℚ) ≤
        (min 2 (graphCommonMultiplicity F x y) : ℚ) := by
    intro y
    exact capped_fraction_le _ _ hx
      (graphCommonMultiplicity_le_degree F x y)
  have hSumTerm := Finset.sum_le_sum
    (s := Finset.univ) (fun y _ => hterm y)
  have hEq :
      (∑ y : α,
        (2 * (graphCommonMultiplicity F x y : ℚ)) /
          (F.degree x : ℚ)) =
        2 * (graphNeighborDegreeSum F x : ℚ) /
          (F.degree x : ℚ) := by
    rw [← Finset.sum_div, ← Finset.mul_sum]
    rw [hsumQ]
  unfold graphVertexDeficit graphCappedCommonSum
  rw [hEq] at hSumTerm
  linarith

/-- At a marked vertex, all off-diagonal common-neighbor counts are at
most two.  The capped sum then has the exact linear form used in the
marked-vertex allocation of §III.B of the all-rank manuscript equation (III.B.6). -/
theorem graphVertexDeficit_marked_formula
    (F : SimpleGraph α) [DecidableEq α] [DecidableRel F.Adj]
    (x : α) (hx : 2 ≤ F.degree x)
    (hMarked : ∀ y : α, y ≠ x →
      graphCommonMultiplicity F x y ≤ 2) :
    graphVertexDeficit F x =
      (1 - 2 / (F.degree x : ℚ)) *
        (graphNeighborDegreeSum F x : ℚ) -
      (F.degree x : ℚ) + 2 := by
  have hCap : graphOffDiagonalCappedSum F x =
      ∑ y ∈ Finset.univ.erase x,
        (graphCommonMultiplicity F x y : ℚ) := by
    unfold graphOffDiagonalCappedSum
    apply Finset.sum_congr rfl
    intro y hy
    have hyNe : y ≠ x := Finset.ne_of_mem_erase hy
    have hmu := hMarked y hyNe
    norm_cast
    exact min_eq_right hmu
  have hTotal := sum_graphCommonMultiplicity F x
  have hTotalQ :
      (∑ y : α, (graphCommonMultiplicity F x y : ℚ)) =
        (graphNeighborDegreeSum F x : ℚ) := by
    exact_mod_cast hTotal
  have hSplit := Finset.sum_erase_add Finset.univ
    (fun y : α => (graphCommonMultiplicity F x y : ℚ))
    (Finset.mem_univ x)
  rw [graphCommonMultiplicity_self] at hSplit
  have hOff :
      (∑ y ∈ Finset.univ.erase x,
        (graphCommonMultiplicity F x y : ℚ)) =
      (graphNeighborDegreeSum F x : ℚ) - (F.degree x : ℚ) := by
    linarith
  rw [graphVertexDeficit_eq_manuscript F x hx, hCap, hOff]
  ring

/-- At a leaf, the off-diagonal capped sum is the degree of its unique
neighbor minus one.  This is exactly the leaf correction in equation (III.B.6). -/
theorem graphOffDiagonalCappedSum_leaf
    (F : SimpleGraph α) [DecidableEq α] [DecidableRel F.Adj]
    (x : α) (hx : F.degree x = 1) :
    ∃ z : α, F.Adj x z ∧
      graphOffDiagonalCappedSum F x = (F.degree z : ℚ) - 1 := by
  have hNcard : (F.neighborFinset x).card = 1 := hx
  obtain ⟨z, hNeq⟩ := Finset.card_eq_one.mp hNcard
  have hAdj : F.Adj x z := by
    have hz : z ∈ F.neighborFinset x := by simp [hNeq]
    simpa [SimpleGraph.mem_neighborFinset] using hz
  have hzx : z ≠ x := by
    intro hEq
    subst z
    exact F.loopless.irrefl x hAdj
  have hxNbr : x ∈ F.neighborFinset z := by
    simpa [SimpleGraph.mem_neighborFinset] using hAdj.symm
  have hTerm (y : α) :
      (min 2 (graphCommonMultiplicity F x y) : ℚ) =
        (if F.Adj y z then (1 : ℚ) else 0) := by
    unfold graphCommonMultiplicity
    rw [hNeq]
    by_cases hyz : F.Adj y z
    · simp [Finset.filter_singleton, hyz]
    · simp [Finset.filter_singleton, hyz]
  have hFilter :
      (Finset.univ.erase x).filter (fun y => F.Adj y z) =
        (F.neighborFinset z).erase x := by
    ext y
    simp [SimpleGraph.mem_neighborFinset, F.adj_comm]
  have hCard := Finset.card_erase_add_one hxNbr
  have hCardQ : (((F.neighborFinset z).erase x).card : ℚ) =
      (F.degree z : ℚ) - 1 := by
    have hCardQR : (((F.neighborFinset z).erase x).card : ℚ) + 1 =
        (F.degree z : ℚ) := by exact_mod_cast hCard
    linarith
  refine ⟨z, hAdj, ?_⟩
  unfold graphOffDiagonalCappedSum
  simp_rw [hTerm]
  rw [Finset.sum_boole, hFilter]
  exact hCardQ

theorem graphOffDiagonalCappedSum_isolated
    (F : SimpleGraph α) [DecidableEq α] [DecidableRel F.Adj]
    (x : α) (hx : F.degree x = 0) :
    graphOffDiagonalCappedSum F x = 0 := by
  have hN : F.neighborFinset x = ∅ := Finset.card_eq_zero.mp hx
  unfold graphOffDiagonalCappedSum graphCommonMultiplicity
  simp [hN]

theorem graphNeighborDegreeSum_isolated
    (F : SimpleGraph α) [DecidableRel F.Adj]
    (x : α) (hx : F.degree x = 0) :
    graphNeighborDegreeSum F x = 0 := by
  have hN : F.neighborFinset x = ∅ := Finset.card_eq_zero.mp hx
  simp [graphNeighborDegreeSum, hN]

end JSP523.Rank4
