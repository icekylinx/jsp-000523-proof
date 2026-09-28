import JSP523.Rank3.FirstMoment
import JSP523.Rank4.PreprocessBoundedLabel
import JSP523.Rank4.PreprocessGreedyColor

/-!
# Pair-root coloring for actual fixed-center links

The endpoint codegree of the actual Q-link at a center is bounded by the
ordinary pair-codegree of Q.  This supplies the hypothesis of the finite
pair-root coloring lemma without replacing link roots by abstract vertices.
-/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- The actual pair roots whose extension by `x` belongs to `Q`. -/
def actualFixedCenterLinkRoots (Q : Family α) (V : Edge α) (x : α) : Family α :=
  (V.powersetCard 2).filter fun P => insert x P ∈ Q

theorem actual_fixed_center_link_root_card
    (Q : Family α) (V : Edge α) (x : α) (P : Edge α)
    (hP : P ∈ actualFixedCenterLinkRoots Q V x) : P.card = 2 := by
  exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hP).1).2

theorem actual_fixed_center_root_avoids_center
    (Q : Family α) (V : Edge α) (x : α)
    (hUniform : Uniform 3 Q) (P : Edge α)
    (hP : P ∈ actualFixedCenterLinkRoots Q V x) : x ∉ P := by
  intro hxP
  have hQ : insert x P ∈ Q := (Finset.mem_filter.mp hP).2
  have hcardQ := hUniform hQ
  have hcardP := actual_fixed_center_link_root_card Q V x P hP
  rw [Finset.insert_eq_of_mem hxP] at hcardQ
  omega

/-- Endpoint codegree in a fixed-center link is at most the Q pair-degree. -/
theorem actual_fixed_center_link_roots_endpoint_codegree_le
    (Q : Family α) (V : Edge α) (x a : α) (κ : ℕ)
    (hUniform : Uniform 3 Q)
    (hx : x ∈ V)
    (hPair : ∀ P ∈ V.powersetCard 2,
      (JSP523.Rank3.containingEdges Q P).card ≤ κ) :
    ((actualFixedCenterLinkRoots Q V x).filter fun P => a ∈ P).card ≤ κ := by
  classical
  let L := actualFixedCenterLinkRoots Q V x
  by_cases hax : a = x
  · subst a
    have hEmpty : (L.filter fun P => x ∈ P) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro P hP
      exact actual_fixed_center_root_avoids_center Q V x hUniform P
        (Finset.mem_filter.mp hP).1 (Finset.mem_filter.mp hP).2
    simp [L, hEmpty]
  · by_cases ha : a ∈ V
    · have hxa : x ≠ a := by
        intro h
        exact hax h.symm
      let R : Edge α := {x, a}
      have hR : R ∈ V.powersetCard 2 := by
        apply Finset.mem_powersetCard.mpr
        refine ⟨?_, Finset.card_pair hxa⟩
        intro z hz
        simp only [R, Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hx
        · exact ha
      let T := JSP523.Rank3.containingEdges Q R
      let S := L.filter fun P => a ∈ P
      have hmap : ∀ P ∈ S, insert x P ∈ T := by
        intro P hP
        have hLP := (Finset.mem_filter.mp hP).1
        have hQP := (Finset.mem_filter.mp hLP).2
        have haP := (Finset.mem_filter.mp hP).2
        apply Finset.mem_filter.mpr
        refine ⟨hQP, ?_⟩
        intro z hz
        simp only [R, Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · simp
        · exact Finset.mem_insert_of_mem haP
      have hinj : (S : Set (Edge α)).InjOn (fun P => insert x P) := by
        intro P hP Q' hQ' heq
        have hxP := actual_fixed_center_root_avoids_center Q V x hUniform P
          (Finset.mem_filter.mp hP).1
        have hxQ := actual_fixed_center_root_avoids_center Q V x hUniform Q'
          (Finset.mem_filter.mp hQ').1
        have herase := congrArg (fun E : Edge α => E.erase x) heq
        rw [Finset.erase_insert hxP, Finset.erase_insert hxQ] at herase
        exact herase
      have hcard : S.card ≤ T.card :=
        Finset.card_le_card_of_injOn (fun P => insert x P) hmap hinj
      exact hcard.trans (hPair R hR)
    · have hEmpty : (L.filter fun P => a ∈ P) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro P hP
        exact ha ((Finset.mem_powersetCard.mp
          (Finset.mem_filter.mp (Finset.mem_filter.mp hP).1).1).1
          ((Finset.mem_filter.mp hP).2))
      change (L.filter fun P => a ∈ P).card ≤ κ
      rw [hEmpty]
      simp

/-- The actual fixed-center Q-link admits the `2κ-1` proper pair-root
coloring required by bounded-label separation. -/
theorem actual_fixed_center_link_roots_colorable
    (Q : Family α) (V : Edge α) (x : α) (κ : ℕ) (hκ : 1 ≤ κ)
    (hUniform : Uniform 3 Q)
    (hx : x ∈ V)
    (hPair : ∀ P ∈ V.powersetCard 2,
      (JSP523.Rank3.containingEdges Q P).card ≤ κ) :
    ∃ color : Edge α → Fin (2 * κ - 1),
      ∀ P ∈ actualFixedCenterLinkRoots Q V x,
      ∀ R ∈ actualFixedCenterLinkRoots Q V x,
        pairRootConflict P R → color P ≠ color R := by
  exact pair_roots_greedy_color (actualFixedCenterLinkRoots Q V x) κ hκ
    (actual_fixed_center_link_root_card Q V x)
    (fun a => actual_fixed_center_link_roots_endpoint_codegree_le Q V x a κ
      hUniform hx hPair)

/-- The greedy coloring, transferred to the project's subtype of actual
fixed-center pair nodes. -/
theorem fixed_center_pair_nodes_actual_coloring
    [Fintype α]
    (Q : Family α) (V : Edge α) (x : α) (κ : ℕ) (hκ : 1 ≤ κ)
    (hUniform : Uniform 3 Q) (hx : x ∈ V)
    (hPair : ∀ P ∈ V.powersetCard 2,
      (JSP523.Rank3.containingEdges Q P).card ≤ κ) :
    ∃ color : fixedCenterPairNodes Q V x → Fin (2 * κ - 1),
      ∀ P R : fixedCenterPairNodes Q V x,
        P.1 ≠ R.1 → ¬ Disjoint P.1 R.1 → color P ≠ color R := by
  obtain ⟨rootColor, hroot⟩ := actual_fixed_center_link_roots_colorable
    Q V x κ hκ hUniform hx hPair
  refine ⟨fun P => rootColor P.1, ?_⟩
  intro P R hne hnotDisj heq
  have hmemP : P.1 ∈ actualFixedCenterLinkRoots Q V x := P.2
  have hmemR : R.1 ∈ actualFixedCenterLinkRoots Q V x := R.2
  have hfin : rootColor P.1 ≠ rootColor R.1 := hroot P.1 hmemP R.1 hmemR
    ⟨hne, hnotDisj⟩
  exact hfin heq

/-- The number of represented disjoint pair-root witnesses in two fixed
color classes is at most twice the edge count of their actual bipartite
pair-node graph.  This is the ordered-adjacency form of the graph edge
count, so no injectivity of the union representation is assumed. -/
theorem fixed_center_color_pair_witnesses_le_twice_graph_edges
    [Fintype α]
    (F Q : Family α) (V : Edge α) (x : α)
    (color : fixedCenterPairNodes Q V x → ℕ) (i j : ℕ)
    (witnesses : Finset
      ({P : fixedCenterPairNodes Q V x // color P = i} ×
       {P : fixedCenterPairNodes Q V x // color P = j}))
    (hWitness : ∀ z ∈ witnesses,
      Disjoint z.1.1.1 z.2.1.1 ∧ z.1.1.1 ∪ z.2.1.1 ∈ F) :
    witnesses.card ≤ 2 *
      (fixedCenterPairNodeGraph F Q V x color i j).edgeFinset.card := by
  classical
  let G := fixedCenterPairNodeGraph F Q V x color i j
  let Node := Sum {P : fixedCenterPairNodes Q V x // color P = i}
    {P : fixedCenterPairNodes Q V x // color P = j}
  let orderedAdj : Finset (Node × Node) :=
    Finset.univ.filter fun z => G.Adj z.1 z.2
  have hmaps : Set.MapsTo
      (fun z : {P : fixedCenterPairNodes Q V x // color P = i} ×
        {P : fixedCenterPairNodes Q V x // color P = j} =>
          ((Sum.inl z.1 : Node), (Sum.inr z.2 : Node))) witnesses
      (orderedAdj : Set _) := by
    intro z hz
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change Disjoint z.1.1.1 z.2.1.1 ∧ z.1.1.1 ∪ z.2.1.1 ∈ F
    exact hWitness z hz
  have hinj : Set.InjOn
      (fun z : {P : fixedCenterPairNodes Q V x // color P = i} ×
        {P : fixedCenterPairNodes Q V x // color P = j} =>
          ((Sum.inl z.1 : Node), (Sum.inr z.2 : Node)))
      (witnesses : Set _) := by
    intro z hz z' hz' heq
    have hfst := congrArg Prod.fst heq
    have hsnd := congrArg Prod.snd heq
    exact Prod.ext (Sum.inl.inj hfst) (Sum.inr.inj hsnd)
  have hcard := Finset.card_le_card_of_injOn
    (fun z : {P : fixedCenterPairNodes Q V x // color P = i} ×
      {P : fixedCenterPairNodes Q V x // color P = j} =>
        ((Sum.inl z.1 : Node), (Sum.inr z.2 : Node))) hmaps hinj
  calc
    witnesses.card ≤ orderedAdj.card := hcard
    _ = 2 * G.edgeFinset.card := by
      simpa [orderedAdj] using (SimpleGraph.two_mul_card_edgeFinset G).symm

/-- At a fixed center, all actual represented four-edges are charged to
ordered pair-root witnesses, and those witnesses split among the colored
bipartite pair-node graphs. -/
theorem fixed_center_pair_node_deletion_card_le_graph_witness_budget
    [Fintype α]
    (F Q : Family α) (V : Edge α) (x : α) (c : ℕ)
    (color : fixedCenterPairNodes Q V x → Fin c) :
    (fixedCenterPairNodeDeletion F Q V x).card ≤
      ∑ ij ∈ (Finset.univ : Finset (Fin c × Fin c)),
        2 * (fixedCenterPairNodeGraph F Q V x
          (fun P => (color P).val) ij.1.val ij.2.val).edgeFinset.card := by
  classical
  let Node := fixedCenterPairNodes Q V x
  let nodeColor : Node → ℕ := fun P => (color P).val
  let witnesses : Finset (Node × Node) := Finset.univ.filter fun z =>
    Disjoint z.1.1 z.2.1 ∧ z.1.1 ∪ z.2.1 ∈ F
  let classWitnesses (ij : Fin c × Fin c) :=
    (Finset.univ : Finset
      ({P : Node // nodeColor P = ij.1.val} ×
       {P : Node // nodeColor P = ij.2.val})).filter fun z =>
      Disjoint z.1.1.1 z.2.1.1 ∧ z.1.1.1 ∪ z.2.1.1 ∈ F
  let represented (ij : Fin c × Fin c) :=
    (classWitnesses ij).image fun z => (z.1.1, z.2.1)
  have hwitnessSub : witnesses ⊆
      (Finset.univ : Finset (Fin c × Fin c)).biUnion represented := by
    intro z hz
    refine Finset.mem_biUnion.mpr ⟨(color z.1, color z.2), Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨(⟨z.1, rfl⟩, ⟨z.2, rfl⟩), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact (Finset.mem_filter.mp hz).2
  have hwitnessBudget : witnesses.card ≤
      ∑ ij ∈ (Finset.univ : Finset (Fin c × Fin c)),
        2 * (fixedCenterPairNodeGraph F Q V x nodeColor
          ij.1.val ij.2.val).edgeFinset.card := by
    calc
      _ ≤ ((Finset.univ : Finset (Fin c × Fin c)).biUnion represented).card :=
        Finset.card_le_card hwitnessSub
      _ ≤ ∑ ij ∈ (Finset.univ : Finset (Fin c × Fin c)),
          (represented ij).card := Finset.card_biUnion_le
      _ ≤ ∑ ij ∈ (Finset.univ : Finset (Fin c × Fin c)),
          2 * (fixedCenterPairNodeGraph F Q V x nodeColor
            ij.1.val ij.2.val).edgeFinset.card := by
        apply Finset.sum_le_sum
        intro ij hij
        calc
          _ ≤ (classWitnesses ij).card := Finset.card_image_le
          _ ≤ 2 * (fixedCenterPairNodeGraph F Q V x nodeColor
              ij.1.val ij.2.val).edgeFinset.card := by
            apply fixed_center_color_pair_witnesses_le_twice_graph_edges
            intro z hz
            exact (Finset.mem_filter.mp hz).2
  have hsurj : Set.SurjOn
      (fun z : Node × Node => z.1.1 ∪ z.2.1) witnesses
      (fixedCenterPairNodeDeletion F Q V x) := by
    intro E hE
    have hExist := (Finset.mem_filter.mp hE).2
    obtain ⟨P, R, hDisj, hUnion⟩ := hExist
    refine ⟨(P, R), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hUnion⟩
    refine ⟨hDisj, ?_⟩
    rw [hUnion]
    exact (Finset.mem_filter.mp hE).1
  have hDeleteLe := Finset.card_le_card_of_surjOn
    (fun z : Node × Node => z.1.1 ∪ z.2.1) hsurj
  exact hDeleteLe.trans hwitnessBudget

/-- The actual fixed-center bounded-label separation statement: greedy
coloring makes every pair-node graph eligible for the finite C4-free edge
bound, and all represented four-edges are charged to the sum of those graph
bounds. -/
theorem actual_fixed_center_separation_budget
    [Fintype α]
    (F Q : Family α) (V : Edge α) (x : α) (κ : ℕ) (hκ : 1 ≤ κ)
    (hUniform : Uniform 3 Q) (hx : x ∈ V)
    (hPair : ∀ P ∈ V.powersetCard 2,
      (JSP523.Rank3.containingEdges Q P).card ≤ κ)
    (hAdmissible : Admissible F) :
    ∃ color : fixedCenterPairNodes Q V x → Fin (2 * κ - 1),
      (fixedCenterPairNodeDeletion F Q V x).card ≤
        ∑ ij ∈ (Finset.univ : Finset
          (Fin (2 * κ - 1) × Fin (2 * κ - 1))),
          2 * (fixedCenterPairNodeGraph F Q V x
            (fun P => (color P).val) ij.1.val ij.2.val).edgeFinset.card ∧
      ∀ i j : Fin (2 * κ - 1),
        ((fixedCenterPairNodeGraph F Q V x
          (fun P => (color P).val) i.val j.val).edgeFinset.card : ℝ) ≤
          (Real.sqrt ((Fintype.card (Sum
            {P : fixedCenterPairNodes Q V x // (color P).val = i.val}
            {P : fixedCenterPairNodes Q V x // (color P).val = j.val}) : ℝ) ^ 3) +
            (Fintype.card (Sum
              {P : fixedCenterPairNodes Q V x // (color P).val = i.val}
              {P : fixedCenterPairNodes Q V x // (color P).val = j.val}) : ℝ) / 2) / 2 := by
  obtain ⟨color, hProper⟩ := fixed_center_pair_nodes_actual_coloring
    Q V x κ hκ hUniform hx hPair
  refine ⟨color, ?_, ?_⟩
  · exact fixed_center_pair_node_deletion_card_le_graph_witness_budget
      F Q V x (2 * κ - 1) color
  · intro i j
    apply fixed_center_pair_node_graph_edge_bound
    · intro P R hne hnotDisj heq
      apply hProper P R hne hnotDisj
      exact Fin.ext heq
    · exact hAdmissible

/-- Real-valued aggregate form of the fixed-center separation budget.  The
right side is the explicit sum of the finite C4-free graph bounds. -/
theorem actual_fixed_center_separation_explicit_bound
    [Fintype α]
    (F Q : Family α) (V : Edge α) (x : α) (κ : ℕ) (hκ : 1 ≤ κ)
    (hUniform : Uniform 3 Q) (hx : x ∈ V)
    (hPair : ∀ P ∈ V.powersetCard 2,
      (JSP523.Rank3.containingEdges Q P).card ≤ κ)
    (hAdmissible : Admissible F) :
    ∃ color : fixedCenterPairNodes Q V x → Fin (2 * κ - 1),
      ((fixedCenterPairNodeDeletion F Q V x).card : ℝ) ≤
        ∑ ij ∈ (Finset.univ : Finset
          (Fin (2 * κ - 1) × Fin (2 * κ - 1))),
          2 * ((Real.sqrt ((Fintype.card (Sum
            {P : fixedCenterPairNodes Q V x // (color P).val = ij.1.val}
            {P : fixedCenterPairNodes Q V x // (color P).val = ij.2.val}) : ℝ) ^ 3) +
            (Fintype.card (Sum
              {P : fixedCenterPairNodes Q V x // (color P).val = ij.1.val}
              {P : fixedCenterPairNodes Q V x // (color P).val = ij.2.val}) : ℝ) / 2) / 2) := by
  obtain ⟨color, hBudget, hEdge⟩ := actual_fixed_center_separation_budget
    F Q V x κ hκ hUniform hx hPair hAdmissible
  refine ⟨color, ?_⟩
  calc
    ((fixedCenterPairNodeDeletion F Q V x).card : ℝ) ≤
        ∑ ij ∈ (Finset.univ : Finset
          (Fin (2 * κ - 1) × Fin (2 * κ - 1))),
          2 * ((fixedCenterPairNodeGraph F Q V x
            (fun P => (color P).val) ij.1.val ij.2.val).edgeFinset.card : ℝ) := by
      exact_mod_cast hBudget
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro ij hij
      exact mul_le_mul_of_nonneg_left (hEdge ij.1 ij.2) (by norm_num)

end JSP523.Rank4
