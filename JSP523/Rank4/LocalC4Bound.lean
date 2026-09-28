import JSP523.Coarse.GraphDeletion
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Analysis.Real.Sqrt

namespace JSP523.Rank4
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]

private theorem local_count (G : SimpleGraph α) [DecidableRel G.Adj]
    (z x : α) :
    (∑ y : α, if x ≠ y ∧ G.Adj z x ∧ G.Adj z y then 1 else 0) =
      if G.Adj z x then G.degree z - 1 else 0 := by
  classical
  by_cases hx : G.Adj z x
  · rw [ite_eq_left hx]
    have hfilter :
        (Finset.univ.filter fun y : α => x ≠ y ∧ G.Adj z x ∧ G.Adj z y) =
          (G.neighborFinset z).erase x := by
      ext y
      simp [hx, SimpleGraph.mem_neighborFinset, ne_comm]
    have hsum :
        (∑ y : α, if x ≠ y ∧ G.Adj z x ∧ G.Adj z y then 1 else 0) =
          (Finset.univ.filter fun y : α => x ≠ y ∧ G.Adj z x ∧ G.Adj z y).card := by
      rw [← Finset.sum_filter]
      simp
    rw [hsum, hfilter, Finset.card_erase_of_mem]
    · rfl
    · simpa [SimpleGraph.mem_neighborFinset] using hx
  · rw [ite_eq_right hx]
    simp [hx]

private def wedgeSum (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  ∑ z : α, ∑ x : α, ∑ y : α,
    if x ≠ y ∧ G.Adj z x ∧ G.Adj z y then 1 else 0

theorem wedgeSum_degree_identity (G : SimpleGraph α) [DecidableRel G.Adj] :
    wedgeSum G = ∑ z : α, G.degree z * (G.degree z - 1) := by
  classical
  unfold wedgeSum
  apply Finset.sum_congr rfl
  intro z hz
  calc
    (∑ x : α, ∑ y : α,
      if x ≠ y ∧ G.Adj z x ∧ G.Adj z y then 1 else 0) =
        ∑ x : α, if G.Adj z x then G.degree z - 1 else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          exact local_count G z x
    _ = G.degree z * (G.degree z - 1) := by
      rw [← Finset.sum_filter]
      have hfilter : Finset.univ.filter (fun x : α => G.Adj z x) =
          G.neighborFinset z := by
        ext x
        simp [SimpleGraph.mem_neighborFinset]
      rw [hfilter]
      rw [Finset.sum_const, nsmul_eq_mul, ← G.card_neighborFinset_eq_degree]
      rfl

private def codegreeIndicatorSum (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  ∑ x : α, ∑ y : α, ∑ z : α,
    if x ≠ y ∧ G.Adj x z ∧ G.Adj y z then 1 else 0

private theorem common_count (G : SimpleGraph α) [DecidableRel G.Adj]
    (x y : α) :
    (∑ z : α, if x ≠ y ∧ G.Adj x z ∧ G.Adj y z then 1 else 0) =
      if x ≠ y then JSP523.Coarse.graphCodegree G x y else 0 := by
  classical
  by_cases hxy : x ≠ y
  · rw [ite_eq_left hxy]
    have hfilter :
        (Finset.univ.filter fun z : α => x ≠ y ∧ G.Adj x z ∧ G.Adj y z) =
          G.neighborFinset x ∩ G.neighborFinset y := by
      ext z
      simp [hxy, SimpleGraph.mem_neighborFinset]
    have hsum :
        (∑ z : α, if x ≠ y ∧ G.Adj x z ∧ G.Adj y z then 1 else 0) =
          (Finset.univ.filter fun z : α => x ≠ y ∧ G.Adj x z ∧ G.Adj y z).card := by
      rw [← Finset.sum_filter]
      simp
    rw [hsum, hfilter]
    rfl
  · rw [ite_eq_right hxy]
    simp [hxy]

private theorem codegreeIndicatorSum_eq_wedgeSum
    (G : SimpleGraph α) [DecidableRel G.Adj] :
    codegreeIndicatorSum G = wedgeSum G := by
  classical
  unfold codegreeIndicatorSum wedgeSum
  calc
    (∑ x : α, ∑ y : α, ∑ z : α,
      if x ≠ y ∧ G.Adj x z ∧ G.Adj y z then 1 else 0) =
      ∑ y : α, ∑ x : α, ∑ z : α,
        if x ≠ y ∧ G.Adj x z ∧ G.Adj y z then 1 else 0 := by
          exact Finset.sum_comm
    _ = ∑ y : α, ∑ z : α, ∑ x : α,
        if x ≠ y ∧ G.Adj x z ∧ G.Adj y z then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro y hy
          exact Finset.sum_comm
    _ = ∑ z : α, ∑ y : α, ∑ x : α,
        if x ≠ y ∧ G.Adj x z ∧ G.Adj y z then 1 else 0 := by
          exact Finset.sum_comm
    _ = ∑ z : α, ∑ x : α, ∑ y : α,
        if x ≠ y ∧ G.Adj z x ∧ G.Adj z y then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro z hz
          exact Finset.sum_comm.trans (by
            apply Finset.sum_congr rfl
            intro x hx
            apply Finset.sum_congr rfl
            intro y hy
            by_cases hxy : x = y
            · simp [hxy]
            · simp [hxy, G.adj_comm])

theorem codegreeIndicatorSum_eq (G : SimpleGraph α) [DecidableRel G.Adj] :
    codegreeIndicatorSum G =
      ∑ x : α, ∑ y : α, if x ≠ y then JSP523.Coarse.graphCodegree G x y else 0 := by
  classical
  unfold codegreeIndicatorSum
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  exact common_count G x y

theorem codegreeIndicatorSum_le_paircount (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : JSP523.Coarse.FourCycleFree G) :
    codegreeIndicatorSum G ≤ Fintype.card α * (Fintype.card α - 1) := by
  classical
  rw [codegreeIndicatorSum_eq]
  calc
    (∑ x : α, ∑ y : α, if x ≠ y then JSP523.Coarse.graphCodegree G x y else 0) ≤
      ∑ x : α, ∑ y : α, if x ≠ y then 1 else 0 := by
        apply Finset.sum_le_sum
        intro x hx
        apply Finset.sum_le_sum
        intro y hy
        by_cases hxy : x = y
        · simp [hxy]
        · simp [hxy, hG x y hxy]
    _ = Fintype.card α * (Fintype.card α - 1) := by
      have hinner (x : α) :
          (∑ y : α, if x ≠ y then 1 else 0) = Fintype.card α - 1 := by
        have hfilter : (Finset.univ.filter fun y : α => x ≠ y) = Finset.univ.erase x := by
          ext y
          simp [ne_comm]
        rw [← Finset.sum_filter]
        rw [hfilter]
        simp
      simp_rw [hinner]
      simp [Finset.sum_const]

omit [DecidableEq α] in
theorem cauchy_degree (G : SimpleGraph α) [DecidableRel G.Adj] :
    (∑ x : α, (G.degree x : ℚ)) ^ 2 ≤
      (Fintype.card α : ℚ) * ∑ x : α, (G.degree x : ℚ) ^ 2 := by
  classical
  by_cases hα : Nonempty α
  · have hc : 0 < (Fintype.card α : ℚ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr hα
    have hcs := Finset.sq_sum_div_le_sum_sq_div (Finset.univ : Finset α)
      (fun x : α => (G.degree x : ℚ)) (g := fun _ => (1 : ℚ))
      (by intro x hx; norm_num)
    have hden : (∑ x ∈ (Finset.univ : Finset α), (1 : ℚ)) =
        (Fintype.card α : ℚ) := by simp
    rw [hden] at hcs
    have hright :
        (∑ x ∈ (Finset.univ : Finset α), (G.degree x : ℚ) ^ 2 / 1) =
          ∑ x : α, (G.degree x : ℚ) ^ 2 := by simp
    rw [hright] at hcs
    simpa [mul_comm] using (div_le_iff₀ hc).mp hcs
  · have hCard : Fintype.card α = 0 :=
      Fintype.card_eq_zero_iff.mpr (not_nonempty_iff.mp hα)
    have hUniv : (Finset.univ : Finset α) = ∅ :=
      Finset.card_eq_zero.mp (by simpa using hCard)
    simp [hCard, hUniv]

/-- A finite four-cycle-free graph satisfies the standard quadratic
incidence inequality. It follows from counting ordered two-edge paths by
their endpoints and applying Cauchy to the degree sequence. -/
theorem fourCycleFree_edge_quadratic_bound
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : JSP523.Coarse.FourCycleFree G) :
    (4 : ℚ) * (G.edgeFinset.card : ℚ) ^ 2 ≤
      (Fintype.card α : ℚ) ^ 2 * ((Fintype.card α : ℚ) - 1) +
        2 * (Fintype.card α : ℚ) * (G.edgeFinset.card : ℚ) := by
  classical
  have hWedges :
      (∑ z : α, G.degree z * (G.degree z - 1)) ≤
        Fintype.card α * (Fintype.card α - 1) := by
    calc
      (∑ z : α, G.degree z * (G.degree z - 1)) = wedgeSum G :=
        (wedgeSum_degree_identity G).symm
      _ = codegreeIndicatorSum G :=
        (codegreeIndicatorSum_eq_wedgeSum G).symm
      _ ≤ Fintype.card α * (Fintype.card α - 1) :=
        codegreeIndicatorSum_le_paircount G hG
  have hDegreeSum :
      (∑ z : α, G.degree z) = 2 * G.edgeFinset.card :=
    G.sum_degrees_eq_twice_card_edges
  have hDegreeSquares :
      (∑ z : α, G.degree z ^ 2) ≤
        Fintype.card α * (Fintype.card α - 1) +
          2 * G.edgeFinset.card := by
    have hIdentity :
        (∑ z : α, G.degree z ^ 2) =
          (∑ z : α, G.degree z * (G.degree z - 1)) +
            ∑ z : α, G.degree z := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro z hz
      rcases G.degree z with _ | d
      · simp
      · simp only [Nat.succ_sub_one]
        ring
    rw [hIdentity, hDegreeSum]
    nlinarith [hWedges]
  have hCauchy := cauchy_degree G
  have hDegreeSumQ :
      (∑ z : α, (G.degree z : ℚ)) = 2 * (G.edgeFinset.card : ℚ) := by
    exact_mod_cast hDegreeSum
  have hSquareCast :
      (∑ z : α, (G.degree z : ℚ) ^ 2) ≤
        ((Fintype.card α * (Fintype.card α - 1) +
          2 * G.edgeFinset.card : ℕ) : ℚ) := by
    exact_mod_cast hDegreeSquares
  have hCardCast :
      ((Fintype.card α * (Fintype.card α - 1) : ℕ) : ℚ) =
        (Fintype.card α : ℚ) * ((Fintype.card α : ℚ) - 1) := by
    cases Fintype.card α with
    | zero => simp
    | succ n => simp only [Nat.succ_sub_one]; push_cast; ring
  have hSquareBound :
      (∑ z : α, (G.degree z : ℚ) ^ 2) ≤
        (Fintype.card α : ℚ) * ((Fintype.card α : ℚ) - 1) +
          2 * (G.edgeFinset.card : ℚ) := by
    rw [Nat.cast_add, hCardCast] at hSquareCast
    norm_num at hSquareCast
    exact hSquareCast
  rw [hDegreeSumQ] at hCauchy
  have hTarget := hCauchy.trans (mul_le_mul_of_nonneg_left hSquareBound
    (show 0 ≤ (Fintype.card α : ℚ) by positivity))
  nlinarith [hTarget]

/-- The quadratic incidence inequality solved for the number of edges. -/
theorem fourCycleFree_edge_sqrt_bound
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : JSP523.Coarse.FourCycleFree G) :
    (G.edgeFinset.card : ℝ) ≤
      (Real.sqrt ((Fintype.card α : ℝ) ^ 3) +
        (Fintype.card α : ℝ) / 2) / 2 := by
  have hQuadQ := fourCycleFree_edge_quadratic_bound G hG
  have hQuad :
      4 * (G.edgeFinset.card : ℝ) ^ 2 ≤
        (Fintype.card α : ℝ) ^ 2 * ((Fintype.card α : ℝ) - 1) +
          2 * (Fintype.card α : ℝ) * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast hQuadQ
  have hCard : 0 ≤ (Fintype.card α : ℝ) := by positivity
  have hSquare :
      (2 * (G.edgeFinset.card : ℝ) - (Fintype.card α : ℝ) / 2) ^ 2 ≤
        (Fintype.card α : ℝ) ^ 3 := by
    nlinarith [hQuad, sq_nonneg ((Fintype.card α : ℝ))]
  have hRoot := Real.le_sqrt_of_sq_le hSquare
  linarith

end JSP523.Rank4
