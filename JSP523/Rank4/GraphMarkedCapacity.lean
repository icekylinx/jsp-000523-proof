import JSP523.Rank4.GraphEdgeAccounting

/-!
# Marked vertex payments for the rank-four graph lemma

Ratio credit is allocated only on edges from marked to unmarked vertices.
The local deficits cover marked-marked edges directly.  This proves the
finite graph inequality (III.B.5) with no independence assumption on marks.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Only edges to unmarked vertices receive the ratio term.  This keeps
adjacent marked vertices from charging the same edge twice. -/
def restrictedIncidentCharge
    (F : SimpleGraph α) [DecidableRel F.Adj]
    (M : Finset α) (x : α) : ℚ :=
  ∑ y ∈ F.neighborFinset x,
    if y ∈ M then 0 else
      (2 * ((F.degree x : ℚ) / (F.degree y : ℚ) +
        (F.degree y : ℚ) / (F.degree x : ℚ) - 2) -
        (if F.degree y = 1 then (F.degree x : ℚ) - 1 else 0))

theorem marked_restricted_charge_capacity
    (F : SimpleGraph α) [DecidableRel F.Adj] (M : Finset α)
    (hDegree : ∀ x ∈ M, 3 ≤ F.degree x) :
    (∑ x ∈ M, restrictedIncidentCharge F M x) ≤
      2 * directedRatioExcess F - directedLeafCredit F := by
  let ratio : α → α → ℚ := fun x y =>
    (F.degree y : ℚ) / (F.degree x : ℚ) - 1
  let leaf : α → α → ℚ := fun x y =>
    if F.degree x = 1 then (F.degree y : ℚ) - 1 else 0
  let pair : α → α → ℚ := fun x y =>
    2 * (ratio x y + ratio y x)
  let charge : α → α → ℚ := fun x y =>
    if x ∈ M then
      (if y ∈ M then 0 else pair x y - leaf y x)
    else 0
  have hPoint (x y : α) (hy : y ∈ F.neighborFinset x) :
      charge x y + charge y x ≤
      pair x y - leaf x y - leaf y x := by
    have hxy : F.Adj x y := by
      simpa [SimpleGraph.mem_neighborFinset] using hy
    have hdx : 1 ≤ F.degree x := by
      have hpos : 0 < (F.neighborFinset x).card :=
        Finset.card_pos.mpr ⟨y, hy⟩
      exact hpos
    have hyx : x ∈ F.neighborFinset y := by
      simpa [SimpleGraph.mem_neighborFinset] using hxy.symm
    have hdy : 1 ≤ F.degree y := by
      have hpos : 0 < (F.neighborFinset y).card :=
        Finset.card_pos.mpr ⟨x, hyx⟩
      exact hpos
    by_cases hxM : x ∈ M
    · have hxNeLeaf : F.degree x ≠ 1 := by
        have := hDegree x hxM
        omega
      by_cases hyM : y ∈ M
      · have hyNeLeaf : F.degree y ≠ 1 := by
          have := hDegree y hyM
          omega
        have hScalar := edge_ratio_pays_leaf_correction
          (F.degree x) (F.degree y) hdx hdy
        have hPairNonneg : 0 ≤ pair x y := by
          simp [hxNeLeaf, hyNeLeaf] at hScalar
          dsimp [pair, ratio]
          linarith
        simpa [charge, hxM, hyM, leaf, hxNeLeaf, hyNeLeaf] using
          hPairNonneg
      · simp [charge, hxM, hyM, leaf, hxNeLeaf]
    · by_cases hyM : y ∈ M
      · have hyNeLeaf : F.degree y ≠ 1 := by
          have := hDegree y hyM
          omega
        have hPairSym : pair y x = pair x y := by
          dsimp [pair]
          ring
        simp [charge, hxM, hyM, leaf, hyNeLeaf, hPairSym]
      · have hScalar := edge_ratio_pays_leaf_correction
          (F.degree x) (F.degree y) hdx hdy
        simp [charge, hxM, hyM, pair, ratio, leaf]
        linarith
  have hTotal :
      (∑ x : α, ∑ y ∈ F.neighborFinset x,
        (charge x y + charge y x)) ≤
      ∑ x : α, ∑ y ∈ F.neighborFinset x,
        (pair x y - leaf x y - leaf y x) := by
    apply Finset.sum_le_sum
    intro x _
    apply Finset.sum_le_sum
    intro y hy
    exact hPoint x y hy
  have hCharge :
      (∑ x : α, ∑ y ∈ F.neighborFinset x, charge x y) =
      ∑ x ∈ M, restrictedIncidentCharge F M x := by
    calc
      (∑ x : α, ∑ y ∈ F.neighborFinset x, charge x y) =
          ∑ x : α, if x ∈ M then restrictedIncidentCharge F M x else 0 := by
            apply Finset.sum_congr rfl
            intro x _
            by_cases hxM : x ∈ M
            · simp only [charge, hxM, ↓reduceIte]
              unfold restrictedIncidentCharge
              apply Finset.sum_congr rfl
              intro y _
              by_cases hyM : y ∈ M
              · simp [hyM]
              · simp [hyM, pair, ratio, leaf]
                ring
            · simp [charge, hxM]
      _ = ∑ x ∈ M, restrictedIncidentCharge F M x := by
            simp
  have hSwapCharge := sum_neighborFinset_swap F charge
  have hSwapRatio := sum_neighborFinset_swap F ratio
  have hSwapLeaf := sum_neighborFinset_swap F leaf
  have hLeft :
      (∑ x : α, ∑ y ∈ F.neighborFinset x,
        (charge x y + charge y x)) =
      2 * (∑ x ∈ M, restrictedIncidentCharge F M x) := by
    simp_rw [Finset.sum_add_distrib]
    change (∑ x : α, ∑ y ∈ F.neighborFinset x, charge x y) +
      (∑ x : α, ∑ y ∈ F.neighborFinset x, charge y x) = _
    rw [← hSwapCharge, hCharge]
    ring
  have hRight :
      (∑ x : α, ∑ y ∈ F.neighborFinset x,
        (pair x y - leaf x y - leaf y x)) =
      4 * directedRatioExcess F - 2 * directedLeafCredit F := by
    simp_rw [sub_sub, Finset.sum_sub_distrib]
    have hPairSum :
        (∑ x : α, ∑ y ∈ F.neighborFinset x, pair x y) =
        4 * directedRatioExcess F := by
      dsimp [pair]
      simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
      change 2 * (∑ x : α, ∑ y ∈ F.neighborFinset x, ratio x y) +
        2 * (∑ x : α, ∑ y ∈ F.neighborFinset x, ratio y x) = _
      rw [← hSwapRatio]
      have hR : (∑ x : α, ∑ y ∈ F.neighborFinset x, ratio x y) =
          directedRatioExcess F := by
        simp only [ratio, directedRatioExcess]
      rw [hR]
      ring
    have hLeafSum :
        (∑ x : α, ∑ y ∈ F.neighborFinset x, leaf x y) =
        directedLeafCredit F := by
      simp only [leaf, directedLeafCredit]
    rw [hPairSum]
    simp_rw [Finset.sum_add_distrib]
    rw [hLeafSum, ← hSwapLeaf, hLeafSum]
    ring
  rw [hLeft, hRight] at hTotal
  linarith

/-- A degree-three marked vertex can pay its local two units using only
edges to unmarked vertices.  Marked neighbors have degree at least three,
so their contribution in the exact local deficit needs no ratio credit. -/
theorem marked_three_restricted_local_credit
    (F : SimpleGraph α) [DecidableRel F.Adj]
    (M : Finset α) (hDegree : ∀ y ∈ M, 3 ≤ F.degree y)
    (x : α) (hx : F.degree x = 3)
    (hMarked : ∀ y : α, y ≠ x →
      graphCommonMultiplicity F x y ≤ 2) :
    2 ≤ graphVertexDeficit F x + restrictedIncidentCharge F M x := by
  have hD := graphVertexDeficit_marked_formula F x (by omega) hMarked
  rw [hx] at hD
  have hEach : ∀ y ∈ F.neighborFinset x,
      (1 : ℚ) ≤ (F.degree y : ℚ) / 3 +
        (if y ∈ M then 0 else
          2 * (3 / (F.degree y : ℚ) +
            (F.degree y : ℚ) / 3 - 2) -
            (if F.degree y = 1 then (2 : ℚ) else 0)) := by
    intro y hy
    by_cases hyM : y ∈ M
    · have hdy := hDegree y hyM
      simp [hyM]
      have hdyQ : (3 : ℚ) ≤ F.degree y := by exact_mod_cast hdy
      linarith
    · have hdy : 1 ≤ F.degree y := by
        have hxy : F.Adj x y := by
          simpa [SimpleGraph.mem_neighborFinset] using hy
        have hyx : x ∈ F.neighborFinset y := by
          simpa [SimpleGraph.mem_neighborFinset] using hxy.symm
        exact Finset.card_pos.mpr ⟨x, hyx⟩
      have hScalar := marked_three_edge_charge (F.degree y) hdy
      simp [hyM]
      linarith
  have hSum :
      (∑ _y ∈ F.neighborFinset x, (1 : ℚ)) ≤
      ∑ y ∈ F.neighborFinset x,
        ((F.degree y : ℚ) / 3 +
          (if y ∈ M then 0 else
            2 * (3 / (F.degree y : ℚ) +
              (F.degree y : ℚ) / 3 - 2) -
              (if F.degree y = 1 then (2 : ℚ) else 0))) := by
    apply Finset.sum_le_sum
    intro y hy
    exact hEach y hy
  have hOnes : (∑ _y ∈ F.neighborFinset x, (1 : ℚ)) = 3 := by
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one,
      SimpleGraph.card_neighborFinset_eq_degree, hx]
    norm_num
  have hA : (∑ y ∈ F.neighborFinset x,
      (F.degree y : ℚ) / 3) =
      (graphNeighborDegreeSum F x : ℚ) / 3 := by
    unfold graphNeighborDegreeSum
    push_cast
    exact (Finset.sum_div _ _ _).symm
  have hC : (∑ y ∈ F.neighborFinset x,
        (if y ∈ M then 0 else
          2 * (3 / (F.degree y : ℚ) +
            (F.degree y : ℚ) / 3 - 2) -
            (if F.degree y = 1 then (2 : ℚ) else 0))) =
      restrictedIncidentCharge F M x := by
    unfold restrictedIncidentCharge
    rw [hx]
    norm_num
  rw [hOnes, Finset.sum_add_distrib, hA, hC] at hSum
  norm_num at hD
  linarith

/-- The degree-four counterpart of `marked_three_restricted_local_credit`. -/
theorem marked_four_restricted_local_credit
    (F : SimpleGraph α) [DecidableRel F.Adj]
    (M : Finset α) (hDegree : ∀ y ∈ M, 3 ≤ F.degree y)
    (x : α) (hx : F.degree x = 4)
    (hMarked : ∀ y : α, y ≠ x →
      graphCommonMultiplicity F x y ≤ 2) :
    4 ≤ graphVertexDeficit F x + restrictedIncidentCharge F M x := by
  have hD := graphVertexDeficit_marked_formula F x (by omega) hMarked
  rw [hx] at hD
  have hEach : ∀ y ∈ F.neighborFinset x,
      (3 / 2 : ℚ) ≤ (F.degree y : ℚ) / 2 +
        (if y ∈ M then 0 else
          2 * (4 / (F.degree y : ℚ) +
            (F.degree y : ℚ) / 4 - 2) -
            (if F.degree y = 1 then (3 : ℚ) else 0)) := by
    intro y hy
    by_cases hyM : y ∈ M
    · have hdy := hDegree y hyM
      simp [hyM]
      have hdyQ : (3 : ℚ) ≤ F.degree y := by exact_mod_cast hdy
      linarith
    · have hdy : 1 ≤ F.degree y := by
        have hxy : F.Adj x y := by
          simpa [SimpleGraph.mem_neighborFinset] using hy
        have hyx : x ∈ F.neighborFinset y := by
          simpa [SimpleGraph.mem_neighborFinset] using hxy.symm
        exact Finset.card_pos.mpr ⟨x, hyx⟩
      have hScalar := marked_four_edge_charge (F.degree y) hdy
      simp [hyM]
      linarith
  have hSum :
      (∑ _y ∈ F.neighborFinset x, (3 / 2 : ℚ)) ≤
      ∑ y ∈ F.neighborFinset x,
        ((F.degree y : ℚ) / 2 +
          (if y ∈ M then 0 else
            2 * (4 / (F.degree y : ℚ) +
              (F.degree y : ℚ) / 4 - 2) -
              (if F.degree y = 1 then (3 : ℚ) else 0))) := by
    apply Finset.sum_le_sum
    intro y hy
    exact hEach y hy
  have hOnes : (∑ _y ∈ F.neighborFinset x, (3 / 2 : ℚ)) = 6 := by
    simp only [Finset.sum_const, nsmul_eq_mul,
      SimpleGraph.card_neighborFinset_eq_degree, hx]
    norm_num
  have hA : (∑ y ∈ F.neighborFinset x,
      (F.degree y : ℚ) / 2) =
      (graphNeighborDegreeSum F x : ℚ) / 2 := by
    unfold graphNeighborDegreeSum
    push_cast
    exact (Finset.sum_div _ _ _).symm
  have hC : (∑ y ∈ F.neighborFinset x,
        (if y ∈ M then 0 else
          2 * (4 / (F.degree y : ℚ) +
            (F.degree y : ℚ) / 4 - 2) -
            (if F.degree y = 1 then (3 : ℚ) else 0))) =
      restrictedIncidentCharge F M x := by
    unfold restrictedIncidentCharge
    rw [hx]
    norm_num
  rw [hOnes, Finset.sum_add_distrib, hA, hC] at hSum
  norm_num at hD
  linarith

/-- The rank-four finite graph deficit lemma with arbitrary adjacent
marked vertices.  The two marked sets record the degree-three and
degree-four vertices satisfying the common-neighbor multiplicity bound. -/
theorem graphDeficit_marked
    (F : SimpleGraph α) [DecidableRel F.Adj]
    (M3 M4 : Finset α)
    (hDisj : Disjoint M3 M4)
    (h3 : ∀ x ∈ M3, F.degree x = 3 ∧
      ∀ y : α, y ≠ x → graphCommonMultiplicity F x y ≤ 2)
    (h4 : ∀ x ∈ M4, F.degree x = 4 ∧
      ∀ y : α, y ≠ x → graphCommonMultiplicity F x y ≤ 2) :
    orderedUniquePairCount F / 4 +
        (M3.card : ℚ) / 2 + (M4.card : ℚ) ≤
      graphDeficit F := by
  let M := M3 ∪ M4
  have hDegree : ∀ x ∈ M, 3 ≤ F.degree x := by
    intro x hx
    change x ∈ M3 ∪ M4 at hx
    rcases Finset.mem_union.mp hx with hx3 | hx4
    · have hdeg := (h3 x hx3).1
      omega
    · have hdeg := (h4 x hx4).1
      omega
  have hCapacity :
      (∑ x ∈ M3, restrictedIncidentCharge F M x) +
      (∑ x ∈ M4, restrictedIncidentCharge F M x) ≤
        2 * directedRatioExcess F - directedLeafCredit F := by
    rw [← Finset.sum_union hDisj]
    exact marked_restricted_charge_capacity F M hDegree
  have hDnonneg (x : α) : 0 ≤ nonleafVertexDeficit F x := by
    by_cases hx : 2 ≤ F.degree x
    · simpa [nonleafVertexDeficit, hx] using
        graphVertexDeficit_nonneg F x hx
    · simp [nonleafVertexDeficit, hx]
  have hSubset : M3 ∪ M4 ⊆ (Finset.univ : Finset α) := by simp
  have hDsub :
      (∑ x ∈ M3, nonleafVertexDeficit F x) +
      (∑ x ∈ M4, nonleafVertexDeficit F x) ≤
      ∑ x : α, nonleafVertexDeficit F x := by
    rw [← Finset.sum_union hDisj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hSubset
      (fun x _ _ => hDnonneg x)
  have hThree :
      (2 : ℚ) * M3.card ≤
      (∑ x ∈ M3, nonleafVertexDeficit F x) +
      (∑ x ∈ M3, restrictedIncidentCharge F M x) := by
    have hSum := Finset.sum_le_sum (s := M3)
      (fun x hx => marked_three_restricted_local_credit F M hDegree x
        (h3 x hx).1 (h3 x hx).2)
    simp_rw [Finset.sum_add_distrib] at hSum
    have hD : ∀ x ∈ M3,
        nonleafVertexDeficit F x = graphVertexDeficit F x := by
      intro x hx
      have hdeg := (h3 x hx).1
      simp [nonleafVertexDeficit, hdeg]
    rw [Finset.sum_congr rfl hD]
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using hSum
  have hFour :
      (4 : ℚ) * M4.card ≤
      (∑ x ∈ M4, nonleafVertexDeficit F x) +
      (∑ x ∈ M4, restrictedIncidentCharge F M x) := by
    have hSum := Finset.sum_le_sum (s := M4)
      (fun x hx => marked_four_restricted_local_credit F M hDegree x
        (h4 x hx).1 (h4 x hx).2)
    simp_rw [Finset.sum_add_distrib] at hSum
    have hD : ∀ x ∈ M4,
        nonleafVertexDeficit F x = graphVertexDeficit F x := by
      intro x hx
      have hdeg := (h4 x hx).1
      simp [nonleafVertexDeficit, hdeg]
    rw [Finset.sum_congr rfl hD]
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using hSum
  have hExact := graphDeficit_exact_local_identity F
  linarith

end JSP523.Rank4
