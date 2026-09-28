import JSP523.Rank3.LocalTripartiteComplete

/-!
# Numerical surplus for a marked mixed node

§II.D strengthens the ordinary local graph payment at a mixed node.
This file checks the numerical inequality behind that strengthening.  The
graph-theoretic claim that all three pair-type excesses vanish is a separate
obligation.
-/

namespace JSP523.Rank3

private theorem marked_numeric_core (r : ℚ) (hr : 3 ≤ r) :
    (r - 2) / (r + 1) +
      6 / ((2 * r - 1) * (2 * r)) +
      6 / (r * (r + 1)) ≤ 1 := by
  have hr0 : 0 < r := by linarith
  have hr1 : 0 < r + 1 := by linarith
  have hr2 : 0 < 2 * r - 1 := by linarith
  have hpoly : 0 ≤ 2 * r * (r - 3) + 1 := by nlinarith
  have hBase : (r - 2) / (r + 1) + 6 / (r * (r + 1)) =
      1 - 3 * (r - 2) / (r * (r + 1)) := by
    field_simp [ne_of_gt hr0, ne_of_gt hr1]
    ring
  have hDen₁ : 0 < (2 * r - 1) * (2 * r) := by
    exact mul_pos hr2 (by linarith)
  have hDen₂ : 0 < r * (r + 1) := mul_pos hr0 hr1
  have hBound : 6 / ((2 * r - 1) * (2 * r)) ≤
      3 * (r - 2) / (r * (r + 1)) := by
    apply (div_le_div_iff₀ hDen₁ hDen₂).mpr
    nlinarith [mul_nonneg hr0.le hpoly]
  linarith only [hBase, hBound]

/-- The exact increment in §II.D dominates the smaller marked
neighbor score.  Here `a + 1` is the current first-part size and `r + 1`,
`s + 1` are the current degrees of the two marked neighbors. -/
theorem marked_mixed_numeric_gain
    (a r s : ℕ) (hr : 2 ≤ r) (hrs : r ≤ s)
    (ha : r + s ≤ a) :
    localPhi (r + 1) ≤
      (localGraphBudget (a + 1) - localGraphBudget a) -
      ((localPhi (r + 1) - localPhi r) +
        (localPhi (s + 1) - localPhi s)) := by
  have hs : 2 ≤ s := hr.trans hrs
  rw [localGraphBudget_succ_sub_eq (by omega : 2 ≤ a),
    localPhi_succ_sub_eq hr,
    localPhi_succ_sub_eq hs,
    localPhi_eq_formula (by omega : 2 ≤ r + 1)]
  push_cast
  have hrq : (3 : ℚ) ≤ (r : ℚ) + 1 := by exact_mod_cast (by omega : 3 ≤ r + 1)
  have hsrq : (r : ℚ) ≤ s := by exact_mod_cast hrs
  have harq : (r : ℚ) + s ≤ a := by exact_mod_cast ha
  let R : ℚ := (r : ℚ) + 1
  have hAden : 0 < ((a : ℚ) + 1) * ((a : ℚ) + 2) := by
    apply mul_pos <;> linarith
  have hRden : 0 < ((r : ℚ) + 1) * ((r : ℚ) + 2) := by
    apply mul_pos <;> linarith
  have hSden : 0 < ((s : ℚ) + 1) * ((s : ℚ) + 2) := by
    apply mul_pos <;> linarith
  have hAmin : (2 * R - 1) * (2 * R) ≤
      ((a : ℚ) + 1) * ((a : ℚ) + 2) := by
    dsimp [R]
    nlinarith [mul_nonneg (by linarith : 0 ≤ (a : ℚ) - 2 * (r : ℚ))
      (by linarith : 0 ≤ (a : ℚ) + 2 * (r : ℚ) + 3)]
  have hSmin : ((r : ℚ) + 1) * ((r : ℚ) + 2) ≤
      ((s : ℚ) + 1) * ((s : ℚ) + 2) := by nlinarith
  have hAminPos : 0 < (2 * R - 1) * (2 * R) := by
    apply mul_pos <;> dsimp [R] <;> linarith
  have hAfrac : 6 / (((a : ℚ) + 1) * ((a : ℚ) + 2)) ≤
      6 / ((2 * R - 1) * (2 * R)) := by
    apply (div_le_div_iff₀ hAden hAminPos).mpr
    nlinarith
  have hSfrac : 3 / (((s : ℚ) + 1) * ((s : ℚ) + 2)) ≤
      3 / (((r : ℚ) + 1) * ((r : ℚ) + 2)) := by
    apply (div_le_div_iff₀ hSden hRden).mpr
    nlinarith
  have hCore := marked_numeric_core R hrq
  dsimp [R] at hCore hAfrac
  have hCore' : (((r : ℚ) - 1) / ((r : ℚ) + 2)) +
      6 / ((2 * ((r : ℚ) + 1) - 1) * (2 * ((r : ℚ) + 1))) +
      6 / (((r : ℚ) + 1) * ((r : ℚ) + 2)) ≤ 1 := by
    convert hCore using 1
    ring
  have hGoal : (((r : ℚ) - 1) / ((r : ℚ) + 2)) +
      6 / (((a : ℚ) + 1) * ((a : ℚ) + 2)) +
      3 / (((r : ℚ) + 1) * ((r : ℚ) + 2)) +
      3 / (((s : ℚ) + 1) * ((s : ℚ) + 2)) ≤ 1 := by
    have hHalf : 3 / (((r : ℚ) + 1) * ((r : ℚ) + 2)) +
        3 / (((s : ℚ) + 1) * ((s : ℚ) + 2)) ≤
        6 / (((r : ℚ) + 1) * ((r : ℚ) + 2)) := by
      calc
        _ ≤ 3 / (((r : ℚ) + 1) * ((r : ℚ) + 2)) +
            3 / (((r : ℚ) + 1) * ((r : ℚ) + 2)) :=
              add_le_add_right hSfrac _
        _ = _ := by ring
    calc
      _ ≤ (((r : ℚ) - 1) / ((r : ℚ) + 2)) +
          6 / (((a : ℚ) + 1) * ((a : ℚ) + 2)) +
          6 / (((r : ℚ) + 1) * ((r : ℚ) + 2)) := by
            convert add_le_add_left hHalf
              ((((r : ℚ) - 1) / ((r : ℚ) + 2)) +
                6 / (((a : ℚ) + 1) * ((a : ℚ) + 2))) using 1 <;> ring
      _ ≤ (((r : ℚ) - 1) / ((r : ℚ) + 2)) +
          6 / ((2 * ((r : ℚ) + 1) - 1) * (2 * ((r : ℚ) + 1))) +
          6 / (((r : ℚ) + 1) * ((r : ℚ) + 2)) := by
            convert add_le_add_right
              (add_le_add_left hAfrac (((r : ℚ) - 1) / ((r : ℚ) + 2)))
              (6 / (((r : ℚ) + 1) * ((r : ℚ) + 2))) using 1 <;> ring
      _ ≤ 1 := hCore'
  have hPhiEq : (((r : ℚ) + 1) - 2) / (((r : ℚ) + 1) + 1) =
      (((r : ℚ) - 1) / ((r : ℚ) + 2)) := by ring
  rw [hPhiEq]
  linarith only [hGoal]

/-- The signed surplus of the three pair-type graph payment. -/
def tripartiteLocalSurplus {α : Type*} [DecidableEq α]
    (G : TripartitePairGraphs α) (A B C : Finset α) : ℚ :=
  localGraphPayment A.card B.card C.card
      (bipartitePhiTotal G.ab A B)
      (bipartitePhiTotal G.ac A C)
      (bipartitePhiTotal G.bc B C) -
    (localGraphBudget A.card + localGraphBudget B.card +
      localGraphBudget C.card)

/-- All three signed pair-type weights are nonpositive. -/
def TripartiteNoPositive {α : Type*} [DecidableEq α]
    (G : TripartitePairGraphs α) (A B C : Finset α) : Prop :=
  bipartitePhiTotal G.ab A B ≤
      localGraphBudget A.card + localGraphBudget B.card ∧
  bipartitePhiTotal G.ac A C ≤
      localGraphBudget A.card + localGraphBudget C.card ∧
  bipartitePhiTotal G.bc B C ≤
      localGraphBudget B.card + localGraphBudget C.card

theorem tripartiteLocalSurplus_eq_linear_of_no_positive
    {α : Type*} [DecidableEq α]
    (G : TripartitePairGraphs α) (A B C : Finset α)
    (h : TripartiteNoPositive G A B C) :
    tripartiteLocalSurplus G A B C =
      localGraphBudget A.card + localGraphBudget B.card +
        localGraphBudget C.card -
      (bipartitePhiTotal G.ab A B +
        bipartitePhiTotal G.ac A C +
        bipartitePhiTotal G.bc B C) := by
  obtain ⟨hAB, hAC, hBC⟩ := h
  unfold tripartiteLocalSurplus localGraphPayment
  rw [max_eq_left (sub_nonneg.mpr hAB),
    max_eq_left (sub_nonneg.mpr hAC),
    max_eq_left (sub_nonneg.mpr hBC)]
  ring

private theorem pair_score_nonpositive_of_two_low_left_neighbors
    {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (G₁ : Finset (α × β)) (G₂ : Finset (α × γ))
    (A : Finset α) (B : Finset β) (z : γ)
    (hTwo : 2 ≤ bipRightDegree G₂ A z)
    (hLow : ∀ x ∈ A, (x, z) ∈ G₂ → bipLeftDegree G₁ B x ≤ 1) :
    bipartitePhiTotal G₁ A B ≤
      localGraphBudget A.card + localGraphBudget B.card := by
  by_contra h
  have hPositive : localGraphBudget A.card + localGraphBudget B.card <
      bipartitePhiTotal G₁ A B := lt_of_not_ge h
  have hOne : 1 < (A.filter (fun x => (x, z) ∈ G₂)).card := by
    dsimp [bipRightDegree] at hTwo
    omega
  obtain ⟨x₁, hx₁, x₂, hx₂, hNe⟩ :=
    Finset.one_lt_card.mp hOne
  have hx₁A : x₁ ∈ A := (Finset.mem_filter.mp hx₁).1
  have hx₂A : x₂ ∈ A := (Finset.mem_filter.mp hx₂).1
  have hx₁G : (x₁, z) ∈ G₂ := (Finset.mem_filter.mp hx₁).2
  have hx₂G : (x₂, z) ∈ G₂ := (Finset.mem_filter.mp hx₂).2
  have hEq : (Sum.inl x₁ : Sum α β) = Sum.inl x₂ :=
    positive_pair_type_at_most_one_low G₁ A B hPositive
      hx₁A hx₂A (hLow x₁ hx₁A hx₁G)
      (hLow x₂ hx₂A hx₂G)
  exact hNe (Sum.inl.inj hEq)

/-- The marked neighbors' high degrees force all three signed pair-type
weights to be nonpositive, in both the current and deleted-node graphs. -/
theorem tripartite_no_positive_of_marked_degrees
    {α : Type*} [DecidableEq α]
    (G : TripartitePairGraphs α) (A B C : Finset α)
    (y z : α)
    (hMixed : MixedNodeDegreeTwo G A B C)
    (hy : y ∈ B) (hz : z ∈ C)
    (hyDegree : 2 ≤ bipRightDegree G.ab A y)
    (hzDegree : 2 ≤ bipRightDegree G.ac A z) :
    TripartiteNoPositive G A B C := by
  have hAB : bipartitePhiTotal G.ab A B ≤
      localGraphBudget A.card + localGraphBudget B.card := by
    apply pair_score_nonpositive_of_two_low_left_neighbors
      G.ab G.ac A B z hzDegree
    intro x hxA hxAC
    have hPos : 0 < bipLeftDegree G.ac C x := by
      unfold bipLeftDegree
      exact Finset.card_pos.mpr
        ⟨z, Finset.mem_filter.mpr ⟨hz, hxAC⟩⟩
    exact mixed_a_touching_c_has_low_ab hMixed hxA hPos
  have hAC : bipartitePhiTotal G.ac A C ≤
      localGraphBudget A.card + localGraphBudget C.card := by
    apply pair_score_nonpositive_of_two_low_left_neighbors
      G.ac G.ab A C y hyDegree
    intro x hxA hxAB
    have hABPos : 0 < bipLeftDegree G.ab B x := by
      unfold bipLeftDegree
      exact Finset.card_pos.mpr
        ⟨y, Finset.mem_filter.mpr ⟨hy, hxAB⟩⟩
    by_cases hACZero : bipLeftDegree G.ac C x = 0
    · omega
    · exact (hMixed.1 x hxA hABPos
        (Nat.pos_of_ne_zero hACZero)).2.le
  have hYZero : bipLeftDegree G.bc C y = 0 := by
    by_contra hNonzero
    have hOne := (hMixed.2.1 y hy (by omega :
      0 < bipRightDegree G.ab A y)
      (Nat.pos_of_ne_zero hNonzero)).1
    omega
  have hZZero : bipRightDegree G.bc B z = 0 := by
    by_contra hNonzero
    have hOne := (hMixed.2.2 z hz (by omega :
      0 < bipRightDegree G.ac A z)
      (Nat.pos_of_ne_zero hNonzero)).1
    omega
  have hBC := bipartite_two_low_opposite_parts
    G.bc B C hy hz (by omega : bipLeftDegree G.bc C y ≤ 1)
      (by omega : bipRightDegree G.bc B z ≤ 1)
  exact ⟨hAB, hAC, hBC⟩

/-- §II.D for actual sparse pair graphs.  The marked node has one
neighbor in each other part, both neighbors remain of degree at least two
after its deletion, and their other first-part neighborhoods fit into the
remaining first part.  The no-positive conclusions are proved from the
mixed-node degree condition above. -/
theorem marked_mixed_local_surplus_of_size_bound
    {α : Type*} [DecidableEq α]
    (G : TripartitePairGraphs α) (A B C : Finset α)
    (x y z : α) (r s : ℕ)
    (hMixed : MixedNodeDegreeTwo G A B C)
    (hx : x ∈ A) (hy : y ∈ B) (hz : z ∈ C)
    (hAB : B.filter (fun t => (x, t) ∈ G.ab) = {y})
    (hAC : C.filter (fun t => (x, t) ∈ G.ac) = {z})
    (hrDegree : bipRightDegree G.ab (A.erase x) y = r)
    (hsDegree : bipRightDegree G.ac (A.erase x) z = s)
    (hr : 2 ≤ r) (hrs : r ≤ s)
    (hSize : r + s ≤ (A.erase x).card) :
    localPhi (r + 1) ≤ tripartiteLocalSurplus G A B C := by
  have hMixedOld : MixedNodeDegreeTwo G (A.erase x) B C :=
    mixedNodeDegreeTwo_restrict_left G B C
      (Finset.erase_subset x A) hMixed
  have hABDegree := bipRightDegree_erase_left_neighbor
    G.ab A B x y hx hAB
  have hACDegree := bipRightDegree_erase_left_neighbor
    G.ac A C x z hx hAC
  have hCurrent : TripartiteNoPositive G A B C :=
    tripartite_no_positive_of_marked_degrees G A B C y z
      hMixed hy hz (by rw [hABDegree, hrDegree]; omega)
        (by rw [hACDegree, hsDegree]; omega)
  have hOld : TripartiteNoPositive G (A.erase x) B C :=
    tripartite_no_positive_of_marked_degrees G (A.erase x) B C y z
      hMixedOld hy hz (by rw [hrDegree]; omega)
        (by rw [hsDegree]; omega)
  have hOldPay := tripartite_local_payment G (A.erase x) B C hMixedOld
  have hOldNonneg : 0 ≤ tripartiteLocalSurplus G (A.erase x) B C := by
    unfold tripartiteLocalSurplus
    exact sub_nonneg.mpr hOldPay
  have hABInc := bipartitePhiTotal_erase_left_degree_one
    G.ab A B x y hx hy hAB
  rw [hABDegree, hrDegree] at hABInc
  have hACInc := bipartitePhiTotal_erase_left_degree_one
    G.ac A C x z hx hz hAC
  rw [hACDegree, hsDegree] at hACInc
  have hCard : A.card = (A.erase x).card + 1 := by
    have h := Finset.card_erase_add_one hx
    omega
  have hGain := marked_mixed_numeric_gain
    (A.erase x).card r s hr hrs hSize
  have hCurrentLinear := tripartiteLocalSurplus_eq_linear_of_no_positive
    G A B C hCurrent
  have hOldLinear := tripartiteLocalSurplus_eq_linear_of_no_positive
    G (A.erase x) B C hOld
  rw [hCard] at hCurrentLinear
  linarith only [hOldNonneg, hGain, hCurrentLinear,
    hOldLinear, hABInc, hACInc]

theorem tripartiteLocalSurplus_swapPartsBC
    {α : Type*} [DecidableEq α]
    (G : TripartitePairGraphs α) (A B C : Finset α) :
    tripartiteLocalSurplus (swapPartsBC G) A C B =
      tripartiteLocalSurplus G A B C := by
  unfold tripartiteLocalSurplus
  simp only [swapPartsBC, bipartitePhiTotal_transpose]
  rw [localGraphPayment_swap_last_two]
  ring

/-- The cardinal form of the marked-neighborhood condition: the two
neighbors' remaining first-part neighborhoods are disjoint. -/
theorem marked_mixed_local_surplus_of_disjoint_neighbors
    {α : Type*} [DecidableEq α]
    (G : TripartitePairGraphs α) (A B C : Finset α)
    (x y z : α) (r s : ℕ)
    (hMixed : MixedNodeDegreeTwo G A B C)
    (hx : x ∈ A) (hy : y ∈ B) (hz : z ∈ C)
    (hAB : B.filter (fun t => (x, t) ∈ G.ab) = {y})
    (hAC : C.filter (fun t => (x, t) ∈ G.ac) = {z})
    (hrDegree : bipRightDegree G.ab (A.erase x) y = r)
    (hsDegree : bipRightDegree G.ac (A.erase x) z = s)
    (hr : 2 ≤ r) (hrs : r ≤ s)
    (hDisj : Disjoint
      ((A.erase x).filter (fun t => (t, y) ∈ G.ab))
      ((A.erase x).filter (fun t => (t, z) ∈ G.ac))) :
    localPhi (r + 1) ≤ tripartiteLocalSurplus G A B C := by
  have hSub :
      ((A.erase x).filter (fun t => (t, y) ∈ G.ab)) ∪
        ((A.erase x).filter (fun t => (t, z) ∈ G.ac)) ⊆
        A.erase x :=
    Finset.union_subset (Finset.filter_subset _ _)
      (Finset.filter_subset _ _)
  have hCard := Finset.card_le_card hSub
  rw [Finset.card_union_of_disjoint hDisj] at hCard
  have hSize : r + s ≤ (A.erase x).card := by
    change bipRightDegree G.ab (A.erase x) y +
      bipRightDegree G.ac (A.erase x) z ≤ (A.erase x).card at hCard
    rw [hrDegree, hsDegree] at hCard
    exact hCard
  exact marked_mixed_local_surplus_of_size_bound
    G A B C x y z r s hMixed hx hy hz hAB hAC
      hrDegree hsDegree hr hrs hSize

/-- The marked mixed-node surplus from §II.D, with no ordering
chosen between its two high-degree neighbors. -/
theorem marked_mixed_local_surplus
    {α : Type*} [DecidableEq α]
    (G : TripartitePairGraphs α) (A B C : Finset α)
    (x y z : α) (r s : ℕ)
    (hMixed : MixedNodeDegreeTwo G A B C)
    (hx : x ∈ A) (hy : y ∈ B) (hz : z ∈ C)
    (hAB : B.filter (fun t => (x, t) ∈ G.ab) = {y})
    (hAC : C.filter (fun t => (x, t) ∈ G.ac) = {z})
    (hrDegree : bipRightDegree G.ab (A.erase x) y = r)
    (hsDegree : bipRightDegree G.ac (A.erase x) z = s)
    (hr : 2 ≤ r) (hs : 2 ≤ s)
    (hDisj : Disjoint
      ((A.erase x).filter (fun t => (t, y) ∈ G.ab))
      ((A.erase x).filter (fun t => (t, z) ∈ G.ac))) :
    min (localPhi (r + 1)) (localPhi (s + 1)) ≤
      tripartiteLocalSurplus G A B C := by
  by_cases hrs : r ≤ s
  · rw [min_eq_left (localPhi_mono (by omega : r + 1 ≤ s + 1))]
    exact marked_mixed_local_surplus_of_disjoint_neighbors
      G A B C x y z r s hMixed hx hy hz hAB hAC
        hrDegree hsDegree hr hrs hDisj
  · have hsr : s ≤ r := by omega
    have hMixedSwap := mixedNodeDegreeTwo_swapPartsBC G A B C hMixed
    have hSwap := marked_mixed_local_surplus_of_disjoint_neighbors
      (swapPartsBC G) A C B x z y s r hMixedSwap hx hz hy
        hAC hAB hsDegree hrDegree hs hsr hDisj.symm
    rw [tripartiteLocalSurplus_swapPartsBC] at hSwap
    rw [min_eq_right (localPhi_mono (by omega : s + 1 ≤ r + 1))]
    exact hSwap

end JSP523.Rank3
