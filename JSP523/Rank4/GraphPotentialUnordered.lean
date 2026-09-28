import JSP523.Rank4.GraphActualNativeIdentity

/-!
# Converting graph potential to unordered common pairs

The established graph potential uses half an ordered common-pair count.
Here we identify that half with the unordered `q(F)` used in the actual
native representation.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A graph whose edges are the distinct vertex pairs with at least one
common neighbor in `F`. -/
def graphCommonNeighborGraph (F : SimpleGraph α)
    [DecidableRel F.Adj] : SimpleGraph α where
  Adj a b := a ≠ b ∧ 0 < graphCommonMultiplicity F a b
  symm := ⟨by
    intro a b h
    exact ⟨h.1.symm, by
      rw [graph_common_multiplicity_symm]
      exact h.2⟩⟩
  loopless := ⟨by
    intro a h
    exact h.1 rfl⟩

instance graphCommonNeighborGraphDecidableRel
    (F : SimpleGraph α) [DecidableRel F.Adj] :
    DecidableRel (graphCommonNeighborGraph F).Adj :=
  inferInstanceAs (DecidableRel (fun a b : α =>
    a ≠ b ∧ 0 < graphCommonMultiplicity F a b))

/-- The common multiplicity attached to a concrete two-element finset
is independent of the representative orientation. -/
theorem graph_common_multiplicity_at_pair_of_distinct
    (F : SimpleGraph α) [DecidableRel F.Adj]
    (a b : α) (hab : a ≠ b) :
    graphCommonMultiplicityAtPair F ({a, b} : Edge α) =
      graphCommonMultiplicity F a b := by
  classical
  have hPcard : ({a, b} : Edge α).card = 2 := Finset.card_pair hab
  let r := pairRootRep ({a, b} : Edge α) hPcard
  have hSpec := pair_root_rep_spec ({a, b} : Edge α) hPcard
  have hOrient := pair_finset_eq_oriented_eq hSpec.1 hSpec.2
  unfold graphCommonMultiplicityAtPair
  rw [dite_eq_left hPcard]
  change graphCommonMultiplicity F
    (pairRootRep ({a, b} : Edge α) hPcard).1
    (pairRootRep ({a, b} : Edge α) hPcard).2 =
      graphCommonMultiplicity F a b
  rcases hOrient with hSame | hSwap
  · rw [hSame.1, hSame.2]
  · rw [hSwap.1, hSwap.2]
    exact graph_common_multiplicity_symm F b a

omit [Fintype α] in
/-- Mapping an unordered pair to its underlying finite vertex set is
injective. -/
theorem sym2_to_finset_injective :
    Function.Injective (Sym2.toFinset : Sym2 α → Finset α) := by
  intro e f hef
  apply Sym2.ext
  intro x
  rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset, hef]

/-- The unordered common-pair set is the image of the edge set of the
common-neighbor graph under the finite-set map. -/
theorem common_pair_finset_eq_common_neighbor_edge_image
    (F : SimpleGraph α) [DecidableRel F.Adj] :
    (((Finset.univ : Finset α).powersetCard 2).filter
      (fun P => 0 < graphCommonMultiplicityAtPair F P)) =
      (graphCommonNeighborGraph F).edgeFinset.image Sym2.toFinset := by
  classical
  let G := graphCommonNeighborGraph F
  ext P
  constructor
  · intro hP
    have hP' := Finset.mem_filter.mp hP
    have hPcard : P.card = 2 :=
      (Finset.mem_powersetCard.mp hP'.1).2
    let r := pairRootRep P hPcard
    have hSpec := pair_root_rep_spec P hPcard
    have hPos : 0 < graphCommonMultiplicity F r.1 r.2 := by
      unfold graphCommonMultiplicityAtPair at hP'
      rw [dite_eq_left hPcard] at hP'
      simpa only [r] using hP'.2
    have hAdj : G.Adj r.1 r.2 := ⟨hSpec.1, hPos⟩
    have he : Sym2.mk r.1 r.2 ∈ G.edgeFinset := by
      exact (G.mem_edgeFinset).2 ((G.mem_edgeSet).2 hAdj)
    apply Finset.mem_image.mpr
    refine ⟨Sym2.mk r.1 r.2, he, ?_⟩
    simpa only [Sym2.toFinset_mk_eq] using hSpec.2.symm
  · intro hP
    obtain ⟨e, he, hImage⟩ := Finset.mem_image.mp hP
    induction e using Sym2.inductionOn with
    | hf a b =>
      have hAdj : G.Adj a b :=
        (G.mem_edgeSet).1 ((G.mem_edgeFinset).1 he)
      have hab : a ≠ b := hAdj.1
      have hPos : 0 < graphCommonMultiplicityAtPair F
          ({a, b} : Edge α) := by
        rw [graph_common_multiplicity_at_pair_of_distinct F a b hab]
        exact hAdj.2
      have hPpair : P = ({a, b} : Edge α) := by
        simpa only [Sym2.toFinset_mk_eq] using hImage.symm
      rw [hPpair]
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_powersetCard.mpr
          ⟨Finset.subset_univ _, Finset.card_pair hab⟩
      · exact hPos

/-- The unordered common-pair count is an ordinary graph edge count. -/
theorem graph_common_pair_count_eq_common_neighbor_edges
    (F : SimpleGraph α) [DecidableRel F.Adj] :
    graphCommonPairCount F =
      (graphCommonNeighborGraph F).edgeFinset.card := by
  classical
  unfold graphCommonPairCount
  rw [common_pair_finset_eq_common_neighbor_edge_image]
  exact Finset.card_image_of_injective _ sym2_to_finset_injective

/-- At each vertex, the ordered common-pair indicator count is the
degree in the common-neighbor graph. -/
theorem ordered_common_pair_count_at_vertex_eq_common_neighbor_degree
    (F : SimpleGraph α) [DecidableRel F.Adj] (x : α) :
    (∑ y ∈ Finset.univ.erase x,
      if 0 < graphCommonMultiplicity F x y then (1 : ℚ) else 0) =
      ((graphCommonNeighborGraph F).degree x : ℚ) := by
  classical
  let G := graphCommonNeighborGraph F
  have hSet : (Finset.univ.erase x).filter
      (fun y => 0 < graphCommonMultiplicity F x y) =
      G.neighborFinset x := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
      and_true, SimpleGraph.mem_neighborFinset]
    change (y ≠ x ∧ 0 < graphCommonMultiplicity F x y) ↔
      (x ≠ y ∧ 0 < graphCommonMultiplicity F x y)
    constructor
    · rintro ⟨hyx, hPos⟩
      exact ⟨hyx.symm, hPos⟩
    · rintro ⟨hxy, hPos⟩
      exact ⟨hxy.symm, hPos⟩
  have hCard :
      ((Finset.univ.erase x).filter
        (fun y => 0 < graphCommonMultiplicity F x y)).card =
      ∑ y ∈ Finset.univ.erase x,
        if 0 < graphCommonMultiplicity F x y then 1 else 0 :=
    Finset.card_filter _ _
  have hCardQ :
      (((Finset.univ.erase x).filter
        (fun y => 0 < graphCommonMultiplicity F x y)).card : ℚ) =
      ∑ y ∈ Finset.univ.erase x,
        if 0 < graphCommonMultiplicity F x y then (1 : ℚ) else 0 := by
    exact_mod_cast hCard
  rw [← hCardQ, hSet]
  rfl

/-- The ordered common-pair count is exactly twice the unordered
common-pair count. -/
theorem ordered_common_pair_count_eq_twice_unordered
    (F : SimpleGraph α) [DecidableRel F.Adj] :
    orderedCommonPairCount F =
      2 * (graphCommonPairCount F : ℚ) := by
  classical
  let G := graphCommonNeighborGraph F
  have hDegreeSum :
      (∑ x : α, (G.degree x : ℚ)) =
        2 * (G.edgeFinset.card : ℚ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  calc
    orderedCommonPairCount F =
        ∑ x : α, (G.degree x : ℚ) := by
          unfold orderedCommonPairCount
          apply Finset.sum_congr rfl
          intro x _
          exact ordered_common_pair_count_at_vertex_eq_common_neighbor_degree F x
    _ = 2 * (G.edgeFinset.card : ℚ) := hDegreeSum
    _ = 2 * (graphCommonPairCount F : ℚ) := by
          rw [graph_common_pair_count_eq_common_neighbor_edges]

/-- The rational graph potential already proved in III.B.5 is exactly
the manuscript's unordered `q-e+v/2` potential. -/
theorem graph_deficit_eq_unordered_common_potential
    (F : SimpleGraph α) [DecidableRel F.Adj] :
    graphDeficit F =
      (graphCommonPairCount F : ℚ) -
        (F.edgeFinset.card : ℚ) + activeVertexCount F / 2 := by
  rw [graphDeficit, ordered_common_pair_count_eq_twice_unordered]
  ring

end JSP523.Rank4
