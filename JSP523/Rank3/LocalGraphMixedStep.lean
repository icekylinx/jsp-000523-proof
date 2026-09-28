import JSP523.Rank3.LocalTripartiteSymmetry

/-!
# Removing a mixed node from a finite pair graph

§II.A.5 deletes one mixed node and compares the two affected pair
scores.  Here is the exact one-pair score change when the deleted node has
one neighbor.  It is a combinatorial statement about actual edge sets.
-/

namespace JSP523.Rank3

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem bip_right_degree_mono_left
    (G : Finset (α × β)) {A' A : Finset α}
    (hSub : A' ⊆ A) (y : β) :
    bipRightDegree G A' y ≤ bipRightDegree G A y := by
  unfold bipRightDegree
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hxA, hxy⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hSub hxA, hxy⟩

/-- The mixed-node degree-two property survives restriction of the first
part.  A node still mixed after restriction was already mixed before it. -/
theorem mixed_node_degree_two_restrict_left
    (G : TripartitePairGraphs α)
    {A' A : Finset α} (B C : Finset α)
    (hSub : A' ⊆ A)
    (hMixed : MixedNodeDegreeTwo G A B C) :
    MixedNodeDegreeTwo G A' B C := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha hAB hAC
    exact hMixed.1 a (hSub ha) hAB hAC
  · intro b hb hAB hBC
    have hMono := bip_right_degree_mono_left G.ab hSub b
    have hABFull : 0 < bipRightDegree G.ab A b := by omega
    have hFull := hMixed.2.1 b hb hABFull hBC
    exact ⟨by omega, hFull.2⟩
  · intro c hc hAC hBC
    have hMono := bip_right_degree_mono_left G.ac hSub c
    have hACFull : 0 < bipRightDegree G.ac A c := by omega
    have hFull := hMixed.2.2 c hc hACFull hBC
    exact ⟨by omega, hFull.2⟩

/-- Removing a left vertex with exactly one neighbor changes only the
opposite neighbor's `φ` contribution. -/
theorem bipartite_phi_total_erase_left_degree_one
    (G : Finset (α × β)) (A : Finset α) (B : Finset β)
    (v : α) (y : β)
    (hv : v ∈ A) (hy : y ∈ B)
    (hNbr : B.filter (fun z => (v, z) ∈ G) = {y}) :
    bipartitePhiTotal G A B =
      bipartitePhiTotal G (A.erase v) B +
        (localPhi (bipRightDegree G A y) -
          localPhi (bipRightDegree G (A.erase v) y)) := by
  have hLeftOne : bipLeftDegree G B v = 1 := by
    simp [bipLeftDegree, hNbr]
  have hLeftPhi : localPhi (bipLeftDegree G B v) = 0 := by
    rw [hLeftOne]
    exact local_phi_eq_zero_of_le_one (by omega)
  have hLeft :
      (∑ x ∈ A, localPhi (bipLeftDegree G B x)) =
        ∑ x ∈ A.erase v, localPhi (bipLeftDegree G B x) := by
    have hSum := Finset.sum_erase_add A
      (fun x => localPhi (bipLeftDegree G B x)) hv
    rw [hLeftPhi, add_zero] at hSum
    exact hSum.symm
  have hNoOther (z : β) (hz : z ∈ B.erase y) :
      (v, z) ∉ G := by
    intro hEdgeZ
    have hzB : z ∈ B := (Finset.mem_erase.mp hz).2
    have hzFilter : z ∈ B.filter (fun t => (v, t) ∈ G) :=
      Finset.mem_filter.mpr ⟨hzB, hEdgeZ⟩
    rw [hNbr] at hzFilter
    exact (Finset.mem_erase.mp hz).1 (Finset.mem_singleton.mp hzFilter)
  have hRightOther (z : β) (hz : z ∈ B.erase y) :
      bipRightDegree G A z =
        bipRightDegree G (A.erase v) z := by
    unfold bipRightDegree
    rw [Finset.filter_erase]
    have hvNot : v ∉ A.filter (fun x => (x, z) ∈ G) := by
      simp [hNoOther z hz]
    simp [Finset.erase_eq_of_notMem hvNot]
  have hRight :
      (∑ z ∈ B, localPhi (bipRightDegree G A z)) =
        (∑ z ∈ B, localPhi
          (bipRightDegree G (A.erase v) z)) +
          (localPhi (bipRightDegree G A y) -
            localPhi (bipRightDegree G (A.erase v) y)) := by
    have hSumA := Finset.sum_erase_add B
      (fun z => localPhi (bipRightDegree G A z)) hy
    have hSumErase := Finset.sum_erase_add B
      (fun z => localPhi (bipRightDegree G (A.erase v) z)) hy
    have hOther :
        (∑ z ∈ B.erase y, localPhi (bipRightDegree G A z)) =
          ∑ z ∈ B.erase y,
            localPhi (bipRightDegree G (A.erase v) z) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [hRightOther z hz]
    rw [← hSumA, ← hSumErase]
    rw [hOther]
    ring
  unfold bipartitePhiTotal
  rw [hLeft, hRight]
  ring

theorem bip_right_degree_erase_left_neighbor
    (G : Finset (α × β)) (A : Finset α) (B : Finset β)
    (v : α) (y : β)
    (hv : v ∈ A)
    (hNbr : B.filter (fun z => (v, z) ∈ G) = {y}) :
    bipRightDegree G A y =
      bipRightDegree G (A.erase v) y + 1 := by
  have hEdge : (v, y) ∈ G := by
    have hyFilter : y ∈ B.filter (fun z => (v, z) ∈ G) := by
      rw [hNbr]
      simp
    exact (Finset.mem_filter.mp hyFilter).2
  have hvFilter : v ∈ A.filter (fun x => (x, y) ∈ G) :=
    Finset.mem_filter.mpr ⟨hv, hEdge⟩
  unfold bipRightDegree
  rw [Finset.filter_erase]
  exact (Finset.card_erase_add_one hvFilter).symm

/-- One added neighbor raises the actual bipartite score by at most a
quarter, the numerical input used twice in §II.A.5. -/
theorem bipartite_phi_total_erase_left_degree_one_le_quarter
    (G : Finset (α × β)) (A : Finset α) (B : Finset β)
    (v : α) (y : β)
    (hv : v ∈ A) (hy : y ∈ B)
    (hNbr : B.filter (fun z => (v, z) ∈ G) = {y}) :
    bipartitePhiTotal G A B ≤
      bipartitePhiTotal G (A.erase v) B + (1 : ℚ) / 4 := by
  rw [bipartite_phi_total_erase_left_degree_one G A B v y hv hy hNbr,
    bip_right_degree_erase_left_neighbor G A B v y hv hNbr]
  have hBound := local_phi_succ_sub_le_quarter
    (bipRightDegree G (A.erase v) y)
  linarith

theorem bipartite_phi_total_erase_left_degree_one_mono
    (G : Finset (α × β)) (A : Finset α) (B : Finset β)
    (v : α) (y : β)
    (hv : v ∈ A) (hy : y ∈ B)
    (hNbr : B.filter (fun z => (v, z) ∈ G) = {y}) :
    bipartitePhiTotal G (A.erase v) B ≤
      bipartitePhiTotal G A B := by
  rw [bipartite_phi_total_erase_left_degree_one G A B v y hv hy hNbr,
    bip_right_degree_erase_left_neighbor G A B v y hv hNbr]
  have hMono := local_phi_mono
    (Nat.le_succ (bipRightDegree G (A.erase v) y))
  linarith

/-- The two score increments caused by reinstating a mixed `A` node
are covered by the increment of its part budget.  This is (II.A.8) for
actual finite pair graphs, with the two unique neighbors explicit. -/
theorem mixed_left_two_pair_score_increment_le_budget
    (GAB : Finset (α × β)) (GAC : Finset (α × β))
    (A : Finset α) (B C : Finset β)
    (v : α) (y z : β)
    (hv : v ∈ A) (hy : y ∈ B) (hz : z ∈ C)
    (hNbrAB : B.filter (fun t => (v, t) ∈ GAB) = {y})
    (hNbrAC : C.filter (fun t => (v, t) ∈ GAC) = {z}) :
    bipartitePhiTotal GAB A B +
        bipartitePhiTotal GAC A C ≤
      bipartitePhiTotal GAB (A.erase v) B +
        bipartitePhiTotal GAC (A.erase v) C +
          (localGraphBudget A.card -
            localGraphBudget (A.erase v).card) := by
  let a := (A.erase v).card
  let d₁ := bipRightDegree GAB (A.erase v) y
  let d₂ := bipRightDegree GAC (A.erase v) z
  have hd₁ : d₁ ≤ a :=
    Finset.card_filter_le (A.erase v) (fun x => (x, y) ∈ GAB)
  have hd₂ : d₂ ≤ a :=
    Finset.card_filter_le (A.erase v) (fun x => (x, z) ∈ GAC)
  have hNum := two_neighbor_increment_le_budget_increment
    a d₁ d₂ hd₁ hd₂
  have hCard : A.card = a + 1 := by
    have h := Finset.card_erase_add_one hv
    omega
  have hAB := bipartite_phi_total_erase_left_degree_one
    GAB A B v y hv hy hNbrAB
  have hAC := bipartite_phi_total_erase_left_degree_one
    GAC A C v z hv hz hNbrAC
  rw [bip_right_degree_erase_left_neighbor GAB A B v y hv hNbrAB] at hAB
  rw [bip_right_degree_erase_left_neighbor GAC A C v z hv hNbrAC] at hAC
  rw [hAB, hAC, hCard]
  dsimp [d₁, d₂, a] at hNum ⊢
  linarith

/-- Adding a mixed node cannot create a new positive pair type among its
two incident types: each individual score grows by no more than the
new `A` budget. -/
theorem mixed_left_pair_excess_nonincreasing
    (GAB GAC : Finset (α × β))
    (A : Finset α) (B C : Finset β)
    (v : α) (y z : β)
    (hv : v ∈ A) (hy : y ∈ B) (hz : z ∈ C)
    (hNbrAB : B.filter (fun t => (v, t) ∈ GAB) = {y})
    (hNbrAC : C.filter (fun t => (v, t) ∈ GAC) = {z}) :
    bipartitePhiTotal GAB A B - localGraphBudget A.card ≤
        bipartitePhiTotal GAB (A.erase v) B -
          localGraphBudget (A.erase v).card ∧
      bipartitePhiTotal GAC A C - localGraphBudget A.card ≤
        bipartitePhiTotal GAC (A.erase v) C -
          localGraphBudget (A.erase v).card := by
  have hSum := mixed_left_two_pair_score_increment_le_budget
    GAB GAC A B C v y z hv hy hz hNbrAB hNbrAC
  have hABmono := bipartite_phi_total_erase_left_degree_one_mono
    GAB A B v y hv hy hNbrAB
  have hACmono := bipartite_phi_total_erase_left_degree_one_mono
    GAC A C v z hv hz hNbrAC
  constructor <;> linarith

/-- A positive pair graph cannot have two low-degree left vertices.
Consequently, if every left neighbor of `z` in a second graph is low in
the positive graph, then `z` has at most one such neighbor. -/
theorem positive_left_pair_limits_other_neighbor_degree
    {γ : Type*} [DecidableEq γ]
    (G₁ : Finset (α × β)) (G₂ : Finset (α × γ))
    (A : Finset α) (B : Finset β) (v : α) (z : γ)
    (hPositive :
      localGraphBudget (A.erase v).card + localGraphBudget B.card <
        bipartitePhiTotal G₁ (A.erase v) B)
    (hLow : ∀ x ∈ A.erase v, (x, z) ∈ G₂ →
      bipLeftDegree G₁ B x ≤ 1) :
    bipRightDegree G₂ (A.erase v) z ≤ 1 := by
  by_contra hNot
  have hTwo : 1 < bipRightDegree G₂ (A.erase v) z := by omega
  obtain ⟨x₁, hx₁, x₂, hx₂, hNe⟩ :=
    Finset.one_lt_card.mp hTwo
  have hx₁A : x₁ ∈ A.erase v := (Finset.mem_filter.mp hx₁).1
  have hx₂A : x₂ ∈ A.erase v := (Finset.mem_filter.mp hx₂).1
  have hx₁G : (x₁, z) ∈ G₂ := (Finset.mem_filter.mp hx₁).2
  have hx₂G : (x₂, z) ∈ G₂ := (Finset.mem_filter.mp hx₂).2
  have hEq : (Sum.inl x₁ : Sum α β) = Sum.inl x₂ :=
    positive_pair_type_at_most_one_low G₁ (A.erase v) B
      hPositive hx₁A hx₂A
      (hLow x₁ hx₁A hx₁G) (hLow x₂ hx₂A hx₂G)
  exact hNe (Sum.inl.inj hEq)

/-- equation (II.A.9) for an `AB`-positive old graph: adding a mixed `A`
node cannot raise the `AC` score. -/
theorem positive_ab_old_ac_score_unchanged
    (G : TripartitePairGraphs α)
    (A B C : Finset α) (v z : α)
    (hv : v ∈ A) (hz : z ∈ C)
    (hMixed : MixedNodeDegreeTwo G A B C)
    (hNbrAC : C.filter (fun t => (v, t) ∈ G.ac) = {z})
    (hPositiveOld :
      localGraphBudget (A.erase v).card + localGraphBudget B.card <
        bipartitePhiTotal G.ab (A.erase v) B) :
    bipartitePhiTotal G.ac A C =
      bipartitePhiTotal G.ac (A.erase v) C := by
  have hLow : ∀ x ∈ A.erase v, (x, z) ∈ G.ac →
      bipLeftDegree G.ab B x ≤ 1 := by
    intro x hx hzEdge
    have hxA : x ∈ A := (Finset.mem_erase.mp hx).2
    have hACpos : 0 < bipLeftDegree G.ac C x := by
      unfold bipLeftDegree
      exact Finset.card_pos.mpr
        ⟨z, Finset.mem_filter.mpr ⟨hz, hzEdge⟩⟩
    exact mixed_a_touching_c_has_low_ab hMixed hxA hACpos
  have hDegLe := positive_left_pair_limits_other_neighbor_degree
    G.ab G.ac A B v z hPositiveOld hLow
  have hScore := bipartite_phi_total_erase_left_degree_one
    G.ac A C v z hv hz hNbrAC
  rw [bip_right_degree_erase_left_neighbor G.ac A C v z hv hNbrAC]
    at hScore
  have hZero := local_phi_succ_sub_eq_zero_of_le_one hDegLe
  rw [hZero, add_zero] at hScore
  exact hScore

/-- The symmetric disappearance case: an old positive `AC` type makes
the `AB` score unchanged when the mixed `A` node is added. -/
theorem positive_ac_old_ab_score_unchanged
    (G : TripartitePairGraphs α)
    (A B C : Finset α) (v y : α)
    (hv : v ∈ A) (hy : y ∈ B)
    (hMixed : MixedNodeDegreeTwo G A B C)
    (hNbrAB : B.filter (fun t => (v, t) ∈ G.ab) = {y})
    (hPositiveOld :
      localGraphBudget (A.erase v).card + localGraphBudget C.card <
        bipartitePhiTotal G.ac (A.erase v) C) :
    bipartitePhiTotal G.ab A B =
      bipartitePhiTotal G.ab (A.erase v) B := by
  have hLow : ∀ x ∈ A.erase v, (x, y) ∈ G.ab →
      bipLeftDegree G.ac C x ≤ 1 := by
    intro x hx hyEdge
    have hxA : x ∈ A := (Finset.mem_erase.mp hx).2
    have hABpos : 0 < bipLeftDegree G.ab B x := by
      unfold bipLeftDegree
      exact Finset.card_pos.mpr
        ⟨y, Finset.mem_filter.mpr ⟨hy, hyEdge⟩⟩
    by_cases hACzero : bipLeftDegree G.ac C x = 0
    · omega
    · have hACpos : 0 < bipLeftDegree G.ac C x :=
        Nat.pos_of_ne_zero hACzero
      exact (hMixed.1 x hxA hABpos hACpos).2.le
  have hDegLe := positive_left_pair_limits_other_neighbor_degree
    G.ac G.ab A C v y hPositiveOld hLow
  have hScore := bipartite_phi_total_erase_left_degree_one
    G.ab A B v y hv hy hNbrAB
  rw [bip_right_degree_erase_left_neighbor G.ab A B v y hv hNbrAB]
    at hScore
  have hZero := local_phi_succ_sub_eq_zero_of_le_one hDegLe
  rw [hZero, add_zero] at hScore
  exact hScore

/-- §II.A.5's induction step when the removed mixed node lies in
part `A`.  The old local payment, the actual score increments, and the
two-low-vertex obstruction together imply the new local payment. -/
theorem mixed_left_local_payment_step
    (G : TripartitePairGraphs α)
    (A B C : Finset α) (v y z : α)
    (hv : v ∈ A) (hy : y ∈ B) (hz : z ∈ C)
    (hMixed : MixedNodeDegreeTwo G A B C)
    (hNbrAB : B.filter (fun t => (v, t) ∈ G.ab) = {y})
    (hNbrAC : C.filter (fun t => (v, t) ∈ G.ac) = {z})
    (hOld :
      localGraphBudget (A.erase v).card +
          localGraphBudget B.card + localGraphBudget C.card ≤
        localGraphPayment (A.erase v).card B.card C.card
          (bipartitePhiTotal G.ab (A.erase v) B)
          (bipartitePhiTotal G.ac (A.erase v) C)
          (bipartitePhiTotal G.bc B C)) :
    localGraphBudget A.card + localGraphBudget B.card +
        localGraphBudget C.card ≤
      localGraphPayment A.card B.card C.card
        (bipartitePhiTotal G.ab A B)
        (bipartitePhiTotal G.ac A C)
        (bipartitePhiTotal G.bc B C) := by
  let hA := localGraphBudget A.card
  let hA₀ := localGraphBudget (A.erase v).card
  let hB := localGraphBudget B.card
  let hC := localGraphBudget C.card
  let pAB := bipartitePhiTotal G.ab A B
  let pAC := bipartitePhiTotal G.ac A C
  let pBC := bipartitePhiTotal G.bc B C
  let pAB₀ := bipartitePhiTotal G.ab (A.erase v) B
  let pAC₀ := bipartitePhiTotal G.ac (A.erase v) C
  have hMixedOld : MixedNodeDegreeTwo G (A.erase v) B C :=
    mixed_node_degree_two_restrict_left G B C
      (Finset.erase_subset v A) hMixed
  have hInc : pAB + pAC ≤ pAB₀ + pAC₀ + (hA - hA₀) :=
    mixed_left_two_pair_score_increment_le_budget
      G.ab G.ac A B C v y z hv hy hz hNbrAB hNbrAC
  change hA + hB + hC ≤
    localGraphPayment A.card B.card C.card pAB pAC pBC
  by_cases hPAB : hA + hB < pAB
  · exact positive_ab_local_payment G A B C hMixed hPAB
  by_cases hPAC : hA + hC < pAC
  · exact positive_ac_local_payment G A B C hMixed hPAC
  by_cases hPBC : hB + hC < pBC
  · exact positive_bc_local_payment G A B C hMixed hPBC
  have hABBound : pAB ≤ hA + hB := le_of_not_gt hPAB
  have hACBound : pAC ≤ hA + hC := le_of_not_gt hPAC
  have hBCBound : pBC ≤ hB + hC := le_of_not_gt hPBC
  have hTotal : pAB + pAC + pBC ≤ hA + hB + hC := by
    by_cases hOldPAB : hA₀ + hB < pAB₀
    · have hOther : pAC₀ + pBC ≤ localPhi C.card :=
        positive_ab_controls_other_types G (A.erase v) B C
          hMixedOld hOldPAB
      have hACeq : pAC = pAC₀ :=
        positive_ab_old_ac_score_unchanged G A B C v z
          hv hz hMixed hNbrAC hOldPAB
      have hPhi := local_phi_le_local_graph_budget C.card
      linarith
    by_cases hOldPAC : hA₀ + hC < pAC₀
    · have hOther : pAB₀ + pBC ≤ localPhi B.card :=
        positive_ac_controls_other_types G (A.erase v) B C
          hMixedOld hOldPAC
      have hABeq : pAB = pAB₀ :=
        positive_ac_old_ab_score_unchanged G A B C v y
          hv hy hMixed hNbrAB hOldPAC
      have hPhi := local_phi_le_local_graph_budget B.card
      linarith
    · have hOldABBound : pAB₀ ≤ hA₀ + hB :=
        le_of_not_gt hOldPAB
      have hOldACBound : pAC₀ ≤ hA₀ + hC :=
        le_of_not_gt hOldPAC
      have hOldTotal : pAB₀ + pAC₀ + pBC ≤ hA₀ + hB + hC := by
        have h := (local_graph_payment_ge_iff_capped_scores
          (A.erase v).card B.card C.card pAB₀ pAC₀ pBC).mp hOld
        rw [min_eq_left hOldABBound,
          min_eq_left hOldACBound,
          min_eq_left hBCBound] at h
        exact h
      linarith
  apply (local_graph_payment_ge_iff_capped_scores
    A.card B.card C.card pAB pAC pBC).mpr
  rw [min_eq_left hABBound,
    min_eq_left hACBound,
    min_eq_left hBCBound]
  exact hTotal

/-- The unique neighbors required by the mixed-node step are supplied
by the degree-two property itself. -/
theorem mixed_first_local_payment_of_smaller
    (G : TripartitePairGraphs α)
    (A B C : Finset α) (v : α)
    (hv : v ∈ A)
    (hMixed : MixedNodeDegreeTwo G A B C)
    (hAB : 0 < bipLeftDegree G.ab B v)
    (hAC : 0 < bipLeftDegree G.ac C v)
    (hOld :
      localGraphBudget (A.erase v).card +
          localGraphBudget B.card + localGraphBudget C.card ≤
        localGraphPayment (A.erase v).card B.card C.card
          (bipartitePhiTotal G.ab (A.erase v) B)
          (bipartitePhiTotal G.ac (A.erase v) C)
          (bipartitePhiTotal G.bc B C)) :
    localGraphBudget A.card + localGraphBudget B.card +
        localGraphBudget C.card ≤
      localGraphPayment A.card B.card C.card
        (bipartitePhiTotal G.ab A B)
        (bipartitePhiTotal G.ac A C)
        (bipartitePhiTotal G.bc B C) := by
  obtain ⟨hABOne, hACOne⟩ := hMixed.1 v hv hAB hAC
  obtain ⟨y, hNbrAB⟩ := Finset.card_eq_one.mp hABOne
  obtain ⟨z, hNbrAC⟩ := Finset.card_eq_one.mp hACOne
  have hy : y ∈ B := by
    have hyFilter : y ∈ B.filter (fun t => (v, t) ∈ G.ab) := by
      rw [hNbrAB]
      simp
    exact (Finset.mem_filter.mp hyFilter).1
  have hz : z ∈ C := by
    have hzFilter : z ∈ C.filter (fun t => (v, t) ∈ G.ac) := by
      rw [hNbrAC]
      simp
    exact (Finset.mem_filter.mp hzFilter).1
  exact mixed_left_local_payment_step G A B C v y z
    hv hy hz hMixed hNbrAB hNbrAC hOld

end JSP523.Rank3
