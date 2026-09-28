import JSP523.Rank3.LocalGraphTwoLow

/-!
# Positive pair types in the signed tripartite graph

The graph input below is the precise combinatorial property proved in
§II.A.1 for the graph built around an actual triple: a node meeting
both other parts has exactly one neighbor in each.  Combined with the
two-low-vertices lemma, it forces every pair type other than a positive
one to form a single star.
-/

namespace JSP523.Rank3

section TripartitePositive

variable {α : Type*} [DecidableEq α]

/-- The pair-type graphs of a tagged tripartite graph.  The three copies
    of a physical label are represented by their positions in `A,B,C`. -/
structure TripartitePairGraphs (α : Type*) where
  ab : Finset (α × α)
  ac : Finset (α × α)
  bc : Finset (α × α)

/-- Every node that meets both other parts has one neighbor in each. -/
def MixedNodeDegreeTwo
    (G : TripartitePairGraphs α)
    (A B C : Finset α) : Prop :=
  (∀ a ∈ A,
    0 < bipLeftDegree G.ab B a →
    0 < bipLeftDegree G.ac C a →
      bipLeftDegree G.ab B a = 1 ∧
        bipLeftDegree G.ac C a = 1) ∧
  (∀ b ∈ B,
    0 < bipRightDegree G.ab A b →
    0 < bipLeftDegree G.bc C b →
      bipRightDegree G.ab A b = 1 ∧
        bipLeftDegree G.bc C b = 1) ∧
  (∀ c ∈ C,
    0 < bipRightDegree G.ac A c →
    0 < bipRightDegree G.bc B c →
      bipRightDegree G.ac A c = 1 ∧
        bipRightDegree G.bc B c = 1)

theorem mixed_a_touching_c_has_low_ab
    {G : TripartitePairGraphs α} {A B C : Finset α}
    (hMixed : MixedNodeDegreeTwo G A B C)
    {a : α} (ha : a ∈ A)
    (hAC : 0 < bipLeftDegree G.ac C a) :
    bipLeftDegree G.ab B a ≤ 1 := by
  by_cases hAB : bipLeftDegree G.ab B a = 0
  · omega
  · have hABPos : 0 < bipLeftDegree G.ab B a := Nat.pos_of_ne_zero hAB
    exact (hMixed.1 a ha hABPos hAC).1.le

theorem mixed_b_touching_c_has_low_ab
    {G : TripartitePairGraphs α} {A B C : Finset α}
    (hMixed : MixedNodeDegreeTwo G A B C)
    {b : α} (hb : b ∈ B)
    (hBC : 0 < bipLeftDegree G.bc C b) :
    bipRightDegree G.ab A b ≤ 1 := by
  by_cases hAB : bipRightDegree G.ab A b = 0
  · omega
  · have hABPos : 0 < bipRightDegree G.ab A b := Nat.pos_of_ne_zero hAB
    exact (hMixed.2.1 b hb hABPos hBC).1.le

/-- §II.A.4: if `AB` has positive excess, the other two pair-type
    graph scores together are covered by the `C` budget. -/
theorem positive_ab_controls_other_types
    (G : TripartitePairGraphs α)
    (A B C : Finset α)
    (hMixed : MixedNodeDegreeTwo G A B C)
    (hPositive : localGraphBudget A.card + localGraphBudget B.card <
      bipartitePhiTotal G.ab A B) :
    bipartitePhiTotal G.ac A C +
      bipartitePhiTotal G.bc B C ≤
        localPhi C.card := by
  by_cases hA : ∃ a ∈ A, 0 < bipLeftDegree G.ac C a
  · obtain ⟨a, haA, haAC⟩ := hA
    have haLow : bipLeftDegree G.ab B a ≤ 1 :=
      mixed_a_touching_c_has_low_ab hMixed haA haAC
    have hOnlyA : ∀ a' ∈ A, a' ≠ a →
        bipLeftDegree G.ac C a' = 0 := by
      intro a' ha'A hNe
      by_contra hNotZero
      have ha'AC : 0 < bipLeftDegree G.ac C a' :=
        Nat.pos_of_ne_zero hNotZero
      have ha'Low : bipLeftDegree G.ab B a' ≤ 1 :=
        mixed_a_touching_c_has_low_ab hMixed ha'A ha'AC
      have hEq : (Sum.inl a' : Sum α α) = Sum.inl a :=
        positive_pair_type_at_most_one_low G.ab A B
          hPositive ha'A haA ha'Low haLow
      exact hNe (Sum.inl.inj hEq)
    have hBZero : ∀ b ∈ B, bipLeftDegree G.bc C b = 0 := by
      intro b hbB
      by_contra hNotZero
      have hbBC : 0 < bipLeftDegree G.bc C b :=
        Nat.pos_of_ne_zero hNotZero
      have hbLow : bipRightDegree G.ab A b ≤ 1 :=
        mixed_b_touching_c_has_low_ab hMixed hbB hbBC
      have hEq : (Sum.inr b : Sum α α) = Sum.inl a :=
        positive_pair_type_at_most_one_low G.ab A B
          hPositive hbB haA hbLow haLow
      cases hEq
    have hACBound := bipartite_star_score_le_phi_right
      G.ac A C haA hOnlyA
    have hBCZero := bipartite_phi_total_eq_zero_of_left_degrees_zero
      G.bc B C hBZero
    rw [hBCZero]
    simpa using hACBound
  · have hAZero : ∀ a ∈ A, bipLeftDegree G.ac C a = 0 := by
      intro a haA
      by_contra hNotZero
      exact hA ⟨a, haA, Nat.pos_of_ne_zero hNotZero⟩
    have hACZero := bipartite_phi_total_eq_zero_of_left_degrees_zero
      G.ac A C hAZero
    rw [hACZero]
    by_cases hB : ∃ b ∈ B, 0 < bipLeftDegree G.bc C b
    · obtain ⟨b, hbB, hbBC⟩ := hB
      have hbLow : bipRightDegree G.ab A b ≤ 1 :=
        mixed_b_touching_c_has_low_ab hMixed hbB hbBC
      have hOnlyB : ∀ b' ∈ B, b' ≠ b →
          bipLeftDegree G.bc C b' = 0 := by
        intro b' hb'B hNe
        by_contra hNotZero
        have hb'BC : 0 < bipLeftDegree G.bc C b' :=
          Nat.pos_of_ne_zero hNotZero
        have hb'Low : bipRightDegree G.ab A b' ≤ 1 :=
          mixed_b_touching_c_has_low_ab hMixed hb'B hb'BC
        have hEq : (Sum.inr b' : Sum α α) = Sum.inr b :=
          positive_pair_type_at_most_one_low G.ab A B
            hPositive hb'B hbB hb'Low hbLow
        exact hNe (Sum.inr.inj hEq)
      have hBCBound := bipartite_star_score_le_phi_right
        G.bc B C hbB hOnlyB
      simpa using hBCBound
    · have hBZero : ∀ b ∈ B, bipLeftDegree G.bc C b = 0 := by
        intro b hbB
        by_contra hNotZero
        exact hB ⟨b, hbB, Nat.pos_of_ne_zero hNotZero⟩
      have hBCZero := bipartite_phi_total_eq_zero_of_left_degrees_zero
        G.bc B C hBZero
      rw [hBCZero]
      simpa using local_phi_nonneg C.card

/-- A positive `AB` type satisfies the full local signed payment
    inequality (II.A.2). -/
theorem positive_ab_local_payment
    (G : TripartitePairGraphs α)
    (A B C : Finset α)
    (hMixed : MixedNodeDegreeTwo G A B C)
    (hPositive : localGraphBudget A.card + localGraphBudget B.card <
      bipartitePhiTotal G.ab A B) :
    localGraphBudget A.card + localGraphBudget B.card +
        localGraphBudget C.card ≤
      localGraphPayment A.card B.card C.card
        (bipartitePhiTotal G.ab A B)
        (bipartitePhiTotal G.ac A C)
        (bipartitePhiTotal G.bc B C) := by
  have hOther := positive_ab_controls_other_types
    G A B C hMixed hPositive
  have hPhiBudget := local_phi_le_local_graph_budget C.card
  have hACnonneg := bipartite_phi_total_nonneg G.ac A C
  have hBCnonneg := bipartite_phi_total_nonneg G.bc B C
  have hA := local_graph_budget_nonneg A.card
  have hB := local_graph_budget_nonneg B.card
  have hAC : 0 ≤ localGraphBudget A.card + localGraphBudget C.card -
      bipartitePhiTotal G.ac A C := by linarith
  have hBC : 0 ≤ localGraphBudget B.card + localGraphBudget C.card -
      bipartitePhiTotal G.bc B C := by linarith
  have hAB : localGraphBudget A.card + localGraphBudget B.card -
      bipartitePhiTotal G.ab A B ≤ 0 := by linarith
  unfold localGraphPayment
  rw [max_eq_right hAB, max_eq_left hAC, max_eq_left hBC]
  linarith

end TripartitePositive

end JSP523.Rank3
