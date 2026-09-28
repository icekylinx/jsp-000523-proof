import JSP523.Rank4.PreprocessReciprocalGraphBudget

/-! # Size of actual fixed-center parent-label pair-node graphs -/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
/-- A fixed-center link with endpoint degree at most κ has at most
κ times the ground size pair nodes. -/
theorem actual_fixed_center_link_roots_card_le
    (Q : Family α) (V : Edge α) (x : α) (κ : ℕ)
    (hUniform : Uniform 3 Q) (hx : x ∈ V)
    (hPair : ∀ P ∈ V.powersetCard 2,
      (JSP523.Rank3.containingEdges Q P).card ≤ κ) :
    (actualFixedCenterLinkRoots Q V x).card ≤ V.card * κ := by
  classical
  let L := actualFixedCenterLinkRoots Q V x
  have hMoment :
      (∑ a ∈ V, (L.filter fun P => a ∈ P).card) =
        2 * L.card := by
    calc
      _ = ∑ a ∈ V, ∑ P ∈ L, if a ∈ P then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        exact Finset.card_filter (fun P : Edge α => a ∈ P) L
      _ = ∑ P ∈ L, ∑ a ∈ V, if a ∈ P then 1 else 0 :=
        Finset.sum_comm
      _ = ∑ P ∈ L, P.card := by
        apply Finset.sum_congr rfl
        intro P hP
        have hSub : P ⊆ V :=
          (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hP).1).1
        have hFilter : V.filter (fun a => a ∈ P) = P := by
          ext a
          simp only [Finset.mem_filter]
          exact ⟨fun h => h.2, fun h => ⟨hSub h, h⟩⟩
        rw [← Finset.card_filter, hFilter]
      _ = ∑ _P ∈ L, 2 := by
        apply Finset.sum_congr rfl
        intro P hP
        exact (Finset.mem_powersetCard.mp
          (Finset.mem_filter.mp hP).1).2
      _ = 2 * L.card := by simp [mul_comm]
  have hBound :
      (∑ a ∈ V, (L.filter fun P => a ∈ P).card) ≤ V.card * κ := by
    calc
      _ ≤ ∑ _a ∈ V, κ := by
        apply Finset.sum_le_sum
        intro a ha
        exact actual_fixed_center_link_roots_endpoint_codegree_le
          Q V x a κ hUniform hx hPair
      _ = V.card * κ := by simp [mul_comm]
  change L.card ≤ V.card * κ
  omega

omit [Fintype α] in
/-- Any two color classes use at most twice the actual fixed-center
pair-node count. -/
theorem fixed_center_color_pair_vertex_card_le
    (Q : Family α) (V : Edge α) (x : α) (κ : ℕ)
    (color : fixedCenterPairNodes Q V x → Fin (2 * κ - 1))
    (i j : Fin (2 * κ - 1)) :
    Fintype.card (Sum
      {P : fixedCenterPairNodes Q V x // (color P).val = i.val}
      {P : fixedCenterPairNodes Q V x // (color P).val = j.val}) ≤
        2 * (actualFixedCenterLinkRoots Q V x).card := by
  classical
  have hi : Fintype.card
      {P : fixedCenterPairNodes Q V x // (color P).val = i.val} ≤
      Fintype.card (fixedCenterPairNodes Q V x) :=
    Fintype.card_subtype_le _
  have hj : Fintype.card
      {P : fixedCenterPairNodes Q V x // (color P).val = j.val} ≤
      Fintype.card (fixedCenterPairNodes Q V x) :=
    Fintype.card_subtype_le _
  have hNode :
      Fintype.card (fixedCenterPairNodes Q V x) =
        (actualFixedCenterLinkRoots Q V x).card := by
    exact Fintype.card_coe _
  rw [Fintype.card_sum]
  omega

omit [Fintype α] in
/-- With pair-degree κ, each colored C4 graph has at most 2κ|V|
vertices. -/
theorem fixed_center_color_pair_vertex_card_le_degree
    (Q : Family α) (V : Edge α) (x : α) (κ : ℕ)
    (color : fixedCenterPairNodes Q V x → Fin (2 * κ - 1))
    (i j : Fin (2 * κ - 1))
    (hUniform : Uniform 3 Q) (hx : x ∈ V)
    (hPair : ∀ P ∈ V.powersetCard 2,
      (JSP523.Rank3.containingEdges Q P).card ≤ κ) :
    Fintype.card (Sum
      {P : fixedCenterPairNodes Q V x // (color P).val = i.val}
      {P : fixedCenterPairNodes Q V x // (color P).val = j.val}) ≤
        2 * V.card * κ := by
  have h := fixed_center_color_pair_vertex_card_le Q V x κ color i j
  have hL := actual_fixed_center_link_roots_card_le
    Q V x κ hUniform hx hPair
  calc
    _ ≤ 2 * (actualFixedCenterLinkRoots Q V x).card := h
    _ ≤ 2 * (V.card * κ) := Nat.mul_le_mul_left 2 hL
    _ = 2 * V.card * κ := by ring

omit [Fintype α] in
/-- An explicit n times n-to-the-three-halves bound for the actual
colored C4 budget. The color-pair count depends only on κ. -/
theorem reciprocal_actual_c4_graph_budget_le_scaled
    (D : FiniteCompletionCliqueData α) (κ : ℕ)
    (color : ∀ x : α,
      fixedCenterPairNodes (reciprocalUsedParentLabelTriples D)
        D.ground x → Fin (2 * κ - 1))
    (h_pair : ∀ P ∈ D.ground.powersetCard 2,
      qPairDegree (reciprocalUsedParentLabelTriples D) P ≤ κ) :
    reciprocalActualC4GraphBudget D κ color ≤
      (D.ground.card : ℝ) *
        (Fintype.card
          (Fin (2 * κ - 1) × Fin (2 * κ - 1)) : ℝ) *
        (Real.sqrt (((2 * D.ground.card * κ : ℕ) : ℝ) ^ 3) +
          ((2 * D.ground.card * κ : ℕ) : ℝ) / 2) := by
  classical
  let Q := reciprocalUsedParentLabelTriples D
  let M : ℝ := ((2 * D.ground.card * κ : ℕ) : ℝ)
  have hLocal (x : α) (hx : x ∈ D.ground)
      (ij : Fin (2 * κ - 1) × Fin (2 * κ - 1)) :
      let N := Fintype.card (Sum
        {P : fixedCenterPairNodes Q D.ground x //
          (color x P).val = ij.1.val}
        {P : fixedCenterPairNodes Q D.ground x //
          (color x P).val = ij.2.val})
      2 * ((Real.sqrt ((N : ℝ) ^ 3) + (N : ℝ) / 2) / 2) ≤
        Real.sqrt (M ^ 3) + M / 2 := by
    dsimp
    have hN := fixed_center_color_pair_vertex_card_le_degree
      Q D.ground x κ (color x) ij.1 ij.2
      (reciprocal_used_parent_label_triples_uniform_three D)
      hx h_pair
    have hNR :
        (Fintype.card (Sum
          {P : fixedCenterPairNodes Q D.ground x //
            (color x P).val = ij.1.val}
          {P : fixedCenterPairNodes Q D.ground x //
            (color x P).val = ij.2.val}) : ℝ) ≤ M := by
      change _ ≤ ((2 * D.ground.card * κ : ℕ) : ℝ)
      exact_mod_cast hN
    have hRoot :
        Real.sqrt ((Fintype.card (Sum
          {P : fixedCenterPairNodes Q D.ground x //
            (color x P).val = ij.1.val}
          {P : fixedCenterPairNodes Q D.ground x //
            (color x P).val = ij.2.val}) : ℝ) ^ 3) ≤
          Real.sqrt (M ^ 3) := by
      gcongr
    linarith
  unfold reciprocalActualC4GraphBudget
  calc
    (∑ x ∈ D.ground,
      ∑ ij ∈ (Finset.univ : Finset
        (Fin (2 * κ - 1) × Fin (2 * κ - 1))),
        2 * ((Real.sqrt ((Fintype.card (Sum
          {P : fixedCenterPairNodes Q D.ground x //
            (color x P).val = ij.1.val}
          {P : fixedCenterPairNodes Q D.ground x //
            (color x P).val = ij.2.val}) : ℝ) ^ 3) +
          (Fintype.card (Sum
            {P : fixedCenterPairNodes Q D.ground x //
              (color x P).val = ij.1.val}
            {P : fixedCenterPairNodes Q D.ground x //
              (color x P).val = ij.2.val}) : ℝ) / 2) / 2))
      ≤ ∑ _x ∈ D.ground,
          ∑ _ij ∈ (Finset.univ : Finset
            (Fin (2 * κ - 1) × Fin (2 * κ - 1))),
            (Real.sqrt (M ^ 3) + M / 2) := by
        apply Finset.sum_le_sum
        intro x hx
        apply Finset.sum_le_sum
        intro ij hij
        exact hLocal x hx ij
    _ = (D.ground.card : ℝ) *
          (Fintype.card
            (Fin (2 * κ - 1) × Fin (2 * κ - 1)) : ℝ) *
          (Real.sqrt (M ^ 3) + M / 2) := by
        simp [mul_assoc]
        ring
    _ = _ := rfl

end JSP523.Rank4
