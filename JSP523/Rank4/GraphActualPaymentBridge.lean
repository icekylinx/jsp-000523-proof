import JSP523.Rank4.GraphActualDeficit

/-!
# Private-facet contribution to the actual graph payment

An all-private four-edge contributes four distinct private facets. This
gives the exact `6m₀` part of the facet-side budget in (III.B.9).
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
/-- The four triple facets of distinct all-private edges are disjoint. -/
theorem all_private_edges_have_disjoint_facets
    (K : Family α) (U : Edge α)
    (hUniform : Uniform 4 K)
    (hGround : ∀ E ∈ K, E ⊆ U) :
    (↑(rankFourAllPrivateEdges K U) : Set (Edge α)).PairwiseDisjoint
      (fun E => E.powersetCard 3) := by
  classical
  intro E hE F hF hEF
  apply Finset.disjoint_left.mpr
  intro T hTE hTF
  have hPrivate :=
    (rank_four_all_private_edge_iff_degree_one K U E hUniform hGround).mp hE
  have hParentCard : (rankFourFacetParents K T).card = 1 := by
    rw [← facet_completions_card_eq_parent_edges K U T hUniform hGround
      (Finset.mem_powersetCard.mp hTE).2]
    exact hPrivate.2 T hTE
  have hParentE : E ∈ rankFourFacetParents K T :=
    Finset.mem_filter.mpr ⟨hPrivate.1,
      (Finset.mem_powersetCard.mp hTE).1⟩
  have hParentF : F ∈ rankFourFacetParents K T :=
    Finset.mem_filter.mpr
      ⟨((rank_four_all_private_edge_iff_degree_one
          K U F hUniform hGround).mp hF).1,
        (Finset.mem_powersetCard.mp hTF).1⟩
  exact hEF
    ((Finset.card_le_one.mp (by omega :
      (rankFourFacetParents K T).card ≤ 1))
      E hParentE F hParentF)

omit [Fintype α] in
/-- Every all-private four-edge contributes four different private facets. -/
theorem four_mul_all_private_edges_le_private_facets
    (K : Family α) (U : Edge α)
    (hUniform : Uniform 4 K)
    (hGround : ∀ E ∈ K, E ⊆ U) :
    4 * (rankFourAllPrivateEdges K U).card ≤
      (rankFourPrivateFacets K U).card := by
  classical
  let P := rankFourAllPrivateEdges K U
  let B := P.biUnion (fun E => E.powersetCard 3)
  have hSub : B ⊆ rankFourPrivateFacets K U := by
    intro T hT
    obtain ⟨E, hE, hTE⟩ := Finset.mem_biUnion.mp hT
    have hEdge :=
      (rank_four_all_private_edge_iff_degree_one K U E hUniform hGround).mp hE
    have hTsubU : T ⊆ U :=
      (Finset.mem_powersetCard.mp hTE).1.trans (hGround E hEdge.1)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr
        ⟨hTsubU, (Finset.mem_powersetCard.mp hTE).2⟩,
        hEdge.2 T hTE⟩
  have hCount : B.card = 4 * P.card := by
    calc
      B.card = ∑ E ∈ P, (E.powersetCard 3).card :=
        Finset.card_biUnion
          (all_private_edges_have_disjoint_facets K U hUniform hGround)
      _ = ∑ _E ∈ P, (4 : ℕ) := by
        apply Finset.sum_congr rfl
        intro E hE
        have hEK : E ∈ K :=
          ((rank_four_all_private_edge_iff_degree_one
            K U E hUniform hGround).mp hE).1
        simp [Finset.card_powersetCard, hUniform hEK]
      _ = 4 * P.card := by simp [mul_comm]
  rw [← hCount]
  exact Finset.card_le_card hSub

/-- The elementary facet coefficient check in (III.B.9). -/
private theorem facet_degree_pointwise_budget (d : ℕ) :
    9 * d + 6 * (if 2 ≤ d then 1 else 0) +
      3 * (if d = 1 then 1 else 0) ≤
    4 * d ^ 2 + 8 * (if 0 < d then 1 else 0) := by
  by_cases hZero : d = 0
  · simp [hZero]
  by_cases hOne : d = 1
  · simp [hOne]
  have hTwo : 2 ≤ d := by omega
  simp [hTwo, hOne, show 0 < d by omega]
  let e := d - 2
  have hd : d = e + 2 := by dsimp [e]; omega
  rw [hd]
  nlinarith [sq_nonneg (e : ℤ)]

/-- An indicator summed over a larger finite ground set counts its subset. -/
private theorem sum_indicator_card_of_subset {β : Type*} [DecidableEq β]
    (A B : Finset β) (hBA : B ⊆ A) :
    (∑ x ∈ A, if x ∈ B then (1 : ℕ) else 0) = B.card := by
  classical
  rw [Finset.sum_boole]
  have hFilter : A.filter (· ∈ B) = B := by
    ext x
    simp [hBA]
  rw [hFilter]
  simp

omit [Fintype α] in
/-- The facet side of the actual (III.B.9) payment, before any graph
overlap is charged, follows from completion degrees alone. -/
theorem actual_facet_base_payment
    (K : Family α) (U : Edge α)
    (hUniform : Uniform 4 K)
    (hGround : ∀ E ∈ K, E ⊆ U) :
    36 * K.card +
      6 * (rankFourNonprivateFacets K U).card +
      12 * (rankFourAllPrivateEdges K U).card ≤
    4 * (∑ T ∈ U.powersetCard 3,
      (facetCompletions K U T).card ^ 2) +
      8 * (rankFourFacetShadow K U).card := by
  classical
  let A := U.powersetCard 3
  let B := rankFourNonprivateFacets K U
  let P := rankFourPrivateFacets K U
  let S := rankFourFacetShadow K U
  let d : Edge α → ℕ := fun T => (facetCompletions K U T).card
  have hB : B ⊆ A := Finset.filter_subset _ _
  have hP : P ⊆ A := Finset.filter_subset _ _
  have hS : S ⊆ A := Finset.filter_subset _ _
  have hBsum : (∑ T ∈ A, if 2 ≤ d T then (1 : ℕ) else 0) = B.card := by
    convert sum_indicator_card_of_subset A B hB using 1
    apply Finset.sum_congr rfl
    intro T hT
    have h := Finset.mem_powersetCard.mp hT
    simp [B, d, rankFourNonprivateFacets, h.1, h.2]
  have hPsum : (∑ T ∈ A, if d T = 1 then (1 : ℕ) else 0) = P.card := by
    convert sum_indicator_card_of_subset A P hP using 1
    apply Finset.sum_congr rfl
    intro T hT
    have h := Finset.mem_powersetCard.mp hT
    simp [P, d, rankFourPrivateFacets, h.1, h.2]
  have hSsum : (∑ T ∈ A, if 0 < d T then (1 : ℕ) else 0) = S.card := by
    convert sum_indicator_card_of_subset A S hS using 1
    apply Finset.sum_congr rfl
    intro T hT
    have h := Finset.mem_powersetCard.mp hT
    simp [S, d, rankFourFacetShadow, h.1, h.2]
  have hPoint :
      (∑ T ∈ A, (9 * d T +
        6 * (if 2 ≤ d T then 1 else 0) +
        3 * (if d T = 1 then 1 else 0))) ≤
      (∑ T ∈ A, (4 * (d T)^2 +
        8 * (if 0 < d T then 1 else 0))) := by
    apply Finset.sum_le_sum
    intro T hT
    exact facet_degree_pointwise_budget (d T)
  have hDegree := rank_four_facet_completion_degree_sum
    K U hUniform hGround
  have hDegree' : (∑ T ∈ A, d T) = 4 * K.card := hDegree
  have hFour := four_mul_all_private_edges_le_private_facets
    K U hUniform hGround
  have hFour' :
      4 * (rankFourAllPrivateEdges K U).card ≤ P.card := hFour
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hPoint
  rw [hDegree', hBsum, hPsum, hSsum] at hPoint
  change 36 * K.card + 6 * B.card +
      12 * (rankFourAllPrivateEdges K U).card ≤
    4 * (∑ T ∈ A, d T ^ 2) + 8 * S.card
  omega

omit [Fintype α] in
/-- The degree-two facets supply an additional `2b` of reserve above
the coefficients in the actual graph-payment interface. -/
theorem actual_facet_strong_base_payment_rat
    (D : FiniteCompletionCliqueData α)
    (hUniform : Uniform 4 D.K)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground) :
    18 * (D.K.card : ℚ) +
      3 * ((rankFourNonprivateFacets D.K D.ground).card : ℚ) +
      6 * ((rankFourAllPrivateEdges D.K D.ground).card : ℚ) ≤
    2 * actualFacetCompletionDegreeSquareTotal D +
      4 * ((rankFourFacetShadow D.K D.ground).card : ℚ) := by
  have hNat := actual_facet_base_payment D.K D.ground hUniform hGround
  have hRat :
      36 * (D.K.card : ℚ) +
        6 * ((rankFourNonprivateFacets D.K D.ground).card : ℚ) +
        12 * ((rankFourAllPrivateEdges D.K D.ground).card : ℚ) ≤
      4 * actualFacetCompletionDegreeSquareTotal D +
        8 * ((rankFourFacetShadow D.K D.ground).card : ℚ) := by
    unfold actualFacetCompletionDegreeSquareTotal
    exact_mod_cast hNat
  linarith

omit [Fintype α] in
/-- The facet budget with the coefficients in the actual global
payment. -/
theorem actual_facet_base_payment_rat
    (D : FiniteCompletionCliqueData α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground) :
    18 * (D.K.card : ℚ) +
      ((rankFourNonprivateFacets D.K D.ground).card : ℚ) +
      6 * ((rankFourAllPrivateEdges D.K D.ground).card : ℚ) ≤
    2 * actualFacetCompletionDegreeSquareTotal D +
      4 * ((rankFourFacetShadow D.K D.ground).card : ℚ) := by
  have hStrong := actual_facet_strong_base_payment_rat
    D D.uniform_four hGround
  linarith

/-- The remaining graph payment in (III.B.9) is exactly the repeated
common-pair multiplicity `W-q`; all selected-edge and active-vertex
terms cancel. -/
theorem actual_graph_payment_iff_common_pair_overlap
    (D : FiniteCompletionCliqueData α) :
    (18 * (D.K.card : ℚ) +
        ((rankFourNonprivateFacets D.K D.ground).card : ℚ) +
        6 * ((rankFourAllPrivateEdges D.K D.ground).card : ℚ) +
        actualSelectedDegreeSquareTotal D +
        actualSelectedActiveVertexTotal D ≤
      2 * actualFacetCompletionDegreeSquareTotal D +
        4 * (actualSelectedEdgeTotal D : ℚ) +
        2 * actualSelectedPotentialTotal D +
        4 * ((rankFourFacetShadow D.K D.ground).card : ℚ)) ↔
    (18 * (D.K.card : ℚ) +
        ((rankFourNonprivateFacets D.K D.ground).card : ℚ) +
        6 * ((rankFourAllPrivateEdges D.K D.ground).card : ℚ) +
        2 * (actualSelectedDegreePairTotal D : ℚ) ≤
      2 * actualFacetCompletionDegreeSquareTotal D +
        4 * ((rankFourFacetShadow D.K D.ground).card : ℚ) +
        2 * (actualSelectedCommonPairTotal D : ℚ)) := by
  have hSquare := actual_selected_square_eq_degree_pairs_add_edges D
  have hPotential := actual_selected_common_pairs_plus_active_half D
  constructor <;> intro h <;> linarith

/-- Equivalently, the entire remaining global payment is the facet
reserve paying twice the actual common-pair multiplicity excess. -/
theorem actual_graph_payment_iff_common_excess_bound
    (D : FiniteCompletionCliqueData α) :
    (18 * (D.K.card : ℚ) +
        ((rankFourNonprivateFacets D.K D.ground).card : ℚ) +
        6 * ((rankFourAllPrivateEdges D.K D.ground).card : ℚ) +
        actualSelectedDegreeSquareTotal D +
        actualSelectedActiveVertexTotal D ≤
      2 * actualFacetCompletionDegreeSquareTotal D +
        4 * (actualSelectedEdgeTotal D : ℚ) +
        2 * actualSelectedPotentialTotal D +
        4 * ((rankFourFacetShadow D.K D.ground).card : ℚ)) ↔
    (18 * (D.K.card : ℚ) +
        ((rankFourNonprivateFacets D.K D.ground).card : ℚ) +
        6 * ((rankFourAllPrivateEdges D.K D.ground).card : ℚ) +
        2 * (actualSelectedCommonExcessTotal D : ℚ) ≤
      2 * actualFacetCompletionDegreeSquareTotal D +
        4 * ((rankFourFacetShadow D.K D.ground).card : ℚ)) := by
  have hPairs := actual_selected_degree_pairs_eq_common_pairs_add_excess D
  have hPairsRat :
      (actualSelectedDegreePairTotal D : ℚ) =
        (actualSelectedCommonPairTotal D : ℚ) +
          (actualSelectedCommonExcessTotal D : ℚ) := by
    exact_mod_cast hPairs
  rw [actual_graph_payment_iff_common_pair_overlap]
  constructor <;> intro h <;> linarith

/-- Families whose selected pair links have no repeated common pair
already satisfy the actual graph payment. -/
theorem actual_graph_payment_of_zero_common_excess
    (D : FiniteCompletionCliqueData α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground)
    (hZero : actualSelectedCommonExcessTotal D = 0) :
    18 * (D.K.card : ℚ) +
      ((rankFourNonprivateFacets D.K D.ground).card : ℚ) +
      6 * ((rankFourAllPrivateEdges D.K D.ground).card : ℚ) +
      actualSelectedDegreeSquareTotal D +
      actualSelectedActiveVertexTotal D ≤
    2 * actualFacetCompletionDegreeSquareTotal D +
      4 * (actualSelectedEdgeTotal D : ℚ) +
      2 * actualSelectedPotentialTotal D +
      4 * ((rankFourFacetShadow D.K D.ground).card : ℚ) := by
  apply (actual_graph_payment_iff_common_excess_bound D).2
  have hBase := actual_facet_base_payment_rat D hGround
  simpa [hZero] using hBase

end JSP523.Rank4
