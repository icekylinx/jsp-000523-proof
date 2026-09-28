import JSP523.Rank4.GraphSamplingBudget
import JSP523.Coarse.TripleLinks
import JSP523.Coarse.TripartiteColors

/-!
# Actual star-triple link edges and finite sampling

For a uniform triple family, an edge in the link at a root is exactly one
triple containing that root. Summing over roots counts each triple three
times.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
/-- Every edge of a link has endpoints in the ground set. -/
theorem triple_link_adj_supported
    (A : Family α) (U : Finset α)
    (hGround : ∀ T ∈ A, T ⊆ U)
    (x : α) (a b : α)
    (hab : (JSP523.Coarse.tripleLinkGraph A x).Adj a b) :
    a ∈ U ∧ b ∈ U := by
  have hT : ({x, a, b} : Edge α) ∈ A := hab.2
  have hTU := hGround _ hT
  exact ⟨hTU (by simp), hTU (by simp)⟩

/-- The root of an edge in a uniform triple link is outside that edge. -/
theorem triple_link_root_not_in_edge
    (A : Family α) (x : α)
    (hUniform : ∀ T ∈ A, T.card = 3)
    (e : Sym2 α)
    (he : e ∈ (JSP523.Coarse.tripleLinkGraph A x).edgeFinset) :
    x ∉ e.toFinset := by
  induction e using Sym2.inductionOn with
  | hf a b =>
      have hab : (JSP523.Coarse.tripleLinkGraph A x).Adj a b := by
        simpa [SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet] using he
      have hCard := hUniform _ hab.2
      have hne : a ≠ b := hab.1
      simp only [Sym2.toFinset_mk_eq, Finset.mem_insert,
        Finset.mem_singleton]
      intro hx
      rcases hx with rfl | rfl
      · simp [Finset.card_pair hne] at hCard
      · simp [Finset.card_pair hne] at hCard

/-- The link edge count equals the number of triples containing its root. -/
theorem triple_link_edge_count_eq_root_incidence
    (A : Family α) (x : α)
    (hUniform : ∀ T ∈ A, T.card = 3) :
    (JSP523.Coarse.tripleLinkGraph A x).edgeFinset.card =
      (A.filter fun T => x ∈ T).card := by
  classical
  let F := JSP523.Coarse.tripleLinkGraph A x
  let f : Sym2 α → Edge α := fun e => insert x e.toFinset
  apply Finset.card_bij (fun e _ => f e)
  · intro e he
    induction e using Sym2.inductionOn with
    | hf a b =>
        have hab : F.Adj a b := by
          simpa [F, SimpleGraph.mem_edgeFinset,
            SimpleGraph.mem_edgeSet] using he
        exact Finset.mem_filter.mpr
          ⟨by simpa [f, Sym2.toFinset_mk_eq] using hab.2, by simp [f]⟩
  · intro e he e' he' hEq
    have hx : x ∉ e.toFinset :=
      triple_link_root_not_in_edge A x hUniform e he
    have hx' : x ∉ e'.toFinset :=
      triple_link_root_not_in_edge A x hUniform e' he'
    have hSet : e.toFinset = e'.toFinset := by
      have hErase := congrArg (Finset.erase · x) hEq
      simpa [f, hx, hx'] using hErase
    exact JSP523.Coarse.sym2_toFinset_injective hSet
  · intro T hT
    have hTA : T ∈ A := (Finset.mem_filter.mp hT).1
    have hxT : x ∈ T := (Finset.mem_filter.mp hT).2
    have hEraseCard : (T.erase x).card = 2 := by
      rw [Finset.card_erase_of_mem hxT, hUniform T hTA]
    obtain ⟨a, b, hab, hPair⟩ :=
      Finset.card_eq_two.mp hEraseCard
    have hTpair : T = {x, a, b} := by
      have hInsert := Finset.insert_erase hxT
      rw [hPair] at hInsert
      exact hInsert.symm
    have hAdj : F.Adj a b := by
      change a ≠ b ∧ ({x, a, b} : Edge α) ∈ A
      exact ⟨hab, hTpair ▸ hTA⟩
    refine ⟨s(a, b), ?_, ?_⟩
    · simpa [F, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet] using hAdj
    · simp [f, Sym2.toFinset_mk_eq, ← hTpair]

/-- Each uniform triple contributes one edge to three rooted links. -/
theorem sum_triple_link_edge_count
    (A : Family α) (U : Finset α)
    (hGround : ∀ T ∈ A, T ⊆ U)
    (hUniform : ∀ T ∈ A, T.card = 3) :
    (∑ x ∈ U,
      (JSP523.Coarse.tripleLinkGraph A x).edgeFinset.card) =
        3 * A.card := by
  classical
  calc
    (∑ x ∈ U,
      (JSP523.Coarse.tripleLinkGraph A x).edgeFinset.card) =
        ∑ x ∈ U, (A.filter fun T => x ∈ T).card := by
          apply Finset.sum_congr rfl
          intro x _
          exact triple_link_edge_count_eq_root_incidence A x hUniform
    _ = ∑ x ∈ U, ∑ T ∈ A, if x ∈ T then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          exact Finset.card_filter _ _
    _ = ∑ T ∈ A, ∑ x ∈ U, if x ∈ T then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ T ∈ A, T.card := by
          apply Finset.sum_congr rfl
          intro T hT
          rw [← Finset.card_filter]
          have hFilter : U.filter (fun x => x ∈ T) = T := by
            ext x
            simp [hGround T hT]
          rw [hFilter]
    _ = ∑ _T ∈ A, 3 := by
          apply Finset.sum_congr rfl
          intro T hT
          exact hUniform T hT
    _ = 3 * A.card := by simp [mul_comm]

/-- Sum the finite graph sampling estimate over the actual rooted links
of a uniform triple layer. -/
theorem sum_triple_link_sampling_inequality
    (A : Family α) (U : Finset α) (m : ℕ)
    (hm : 3 ≤ m)
    (hGround : ∀ T ∈ A, T ⊆ U)
    (hUniform : ∀ T ∈ A, T.card = 3) :
    2 * ((U.card - 2).choose (m - 2) : ℚ) *
        (3 * A.card : ℚ) ≤
      ((U.card - 3).choose (m - 3) : ℚ) *
        (∑ x ∈ U,
          orderedUniquePairCount (JSP523.Coarse.tripleLinkGraph A x)) +
      ((U.card - 2).choose (m - 2) : ℚ) *
        (∑ x ∈ U,
          orderedMultiPairCount (JSP523.Coarse.tripleLinkGraph A x)) +
      (U.card : ℚ) * (m : ℚ) * (U.card.choose m) := by
  classical
  have hPoint (x : α) (_hx : x ∈ U) :=
    graph_fixed_size_sampling_inequality
      (JSP523.Coarse.tripleLinkGraph A x) U m hm
      (triple_link_adj_supported A U hGround x)
  have hSum := Finset.sum_le_sum (s := U) hPoint
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hSum
  have hEdgeQ :
      (∑ x ∈ U,
        ((JSP523.Coarse.tripleLinkGraph A x).edgeFinset.card : ℚ)) =
          (3 * A.card : ℚ) := by
    exact_mod_cast sum_triple_link_edge_count A U hGround hUniform
  rw [hEdgeQ] at hSum
  simp only [Finset.sum_const, nsmul_eq_mul] at hSum
  nlinarith

end JSP523.Rank4
