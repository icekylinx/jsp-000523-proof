import JSP523.Rank4.NativeLabelSelection

/-!
# Native edges and actual facet completion pairs

The edge of a native tail graph is one common triple of a used completion
pair.  Reindexing pair/triple incidences shows that the total native
edge count equals the sum of choose-two completion counts over all
three-element facets.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
/-- For an actual two-element completion pair and three-element facet,
membership in the common-root cell is exactly membership of both
endpoints in the facet completion set. -/
theorem common_root_cell_iff_pair_of_facet_completions
    (K : Family α) (U P T : Edge α)
    (hUniform : Uniform 4 K)
    (hP : P ∈ U.powersetCard 2)
    (hT : T ∈ U.powersetCard 3) :
    T ∈ commonRootCell K U P ↔
      P ⊆ facetCompletions K U T := by
  classical
  have hP' := Finset.mem_powersetCard.mp hP
  let a := (pairRootRep P hP'.2).1
  let b := (pairRootRep P hP'.2).2
  have hPspec : P = ({a, b} : Edge α) :=
    (pairRootRep_spec P hP'.2).2
  have haU : a ∈ U := hP'.1 (hPspec.symm ▸ (by simp))
  have hbU : b ∈ U := hP'.1 (hPspec.symm ▸ (by simp))
  constructor
  · intro hCell
    have hCell' : T ∈ commonTripleCell K U a b := by
      simpa only [commonRootCell, dite_eq_left hP'.2] using hCell
    have hData := mem_commonTripleCell.mp hCell'
    rw [hPspec]
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨haU, hData.2.2.2.1⟩
    · exact Finset.mem_filter.mpr ⟨hbU, hData.2.2.2.2⟩
  · intro hSub
    have haC : a ∈ facetCompletions K U T :=
      hSub (hPspec.symm ▸ (by simp))
    have hbC : b ∈ facetCompletions K U T :=
      hSub (hPspec.symm ▸ (by simp))
    have hRaw : T ∈ rawCommonTripleCell K U a b :=
      Finset.mem_filter.mpr
        ⟨hT, (Finset.mem_filter.mp haC).2,
          (Finset.mem_filter.mp hbC).2⟩
    have hCell : T ∈ commonTripleCell K U a b := by
      rw [rawCommonTripleCell_eq_commonTripleCell hUniform] at hRaw
      exact hRaw
    simpa only [commonRootCell, dite_eq_left hP'.2] using hCell

omit [Fintype α] in
/-- Common-root cells over actual ground pairs reindex exactly to
completion pairs over actual ground triples. -/
theorem common_root_facet_completion_double_count
    (K : Family α) (U : Edge α)
    (hUniform : Uniform 4 K) :
    (∑ P ∈ U.powersetCard 2,
      (commonRootCell K U P).card) =
      ∑ T ∈ U.powersetCard 3,
        (facetCompletions K U T).card.choose 2 := by
  classical
  let pairs := U.powersetCard 2
  let triples := U.powersetCard 3
  have hJsub (P : Edge α) (hP : P ∈ pairs) :
      commonRootCell K U P ⊆ triples := by
    intro T hT
    have hPcard := (Finset.mem_powersetCard.mp hP).2
    have hT' : T ∈ commonTripleCell K U
        (pairRootRep P hPcard).1 (pairRootRep P hPcard).2 := by
      simpa only [commonRootCell, dite_eq_left hPcard] using hT
    have hData := mem_commonTripleCell.mp hT'
    exact Finset.mem_powersetCard.mpr ⟨hData.1, hData.2.1⟩
  have hCompletionSub (T : Edge α) :
      facetCompletions K U T ⊆ U := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  calc
    (∑ P ∈ pairs, (commonRootCell K U P).card) =
      ∑ P ∈ pairs, ∑ T ∈ triples,
        if T ∈ commonRootCell K U P then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro P hP
      rw [← Finset.card_filter]
      have hFilter : triples.filter
          (fun T => T ∈ commonRootCell K U P) =
          commonRootCell K U P := by
        ext T
        simp only [Finset.mem_filter]
        constructor
        · exact And.right
        · intro hT
          exact ⟨hJsub P hP hT, hT⟩
      exact congrArg Finset.card hFilter.symm
    _ = ∑ T ∈ triples, ∑ P ∈ pairs,
        if T ∈ commonRootCell K U P then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ T ∈ triples, ∑ P ∈ pairs,
        if P ⊆ facetCompletions K U T then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro T hT
      apply Finset.sum_congr rfl
      intro P hP
      exact if_congr
        (common_root_cell_iff_pair_of_facet_completions
          K U P T hUniform hP hT) rfl rfl
    _ = ∑ T ∈ triples,
        ((facetCompletions K U T).powersetCard 2).card := by
      apply Finset.sum_congr rfl
      intro T _
      rw [← Finset.card_filter]
      have hFilter : pairs.filter
          (fun P => P ⊆ facetCompletions K U T) =
          (facetCompletions K U T).powersetCard 2 := by
        ext P
        constructor
        · intro hP
          have hP' := Finset.mem_filter.mp hP
          exact Finset.mem_powersetCard.mpr
            ⟨hP'.2, (Finset.mem_powersetCard.mp hP'.1).2⟩
        · intro hP
          have hP' := Finset.mem_powersetCard.mp hP
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_powersetCard.mpr
              ⟨hP'.1.trans (hCompletionSub T), hP'.2⟩,
              hP'.1⟩
      exact congrArg Finset.card hFilter
    _ = ∑ T ∈ triples,
        (facetCompletions K U T).card.choose 2 := by
      apply Finset.sum_congr rfl
      intro T _
      exact Finset.card_powersetCard 2 (facetCompletions K U T)

omit [Fintype α] in
/-- Restrict the common-root side of the exact count to the pairs whose
cells are genuinely nonempty. -/
theorem used_common_root_facet_double_count
    (K : Family α) (U : Edge α)
    (hUniform : Uniform 4 K) :
    (∑ P ∈ nonemptyCommonRoots K U,
      (commonRootCell K U P).card) =
      ∑ T ∈ U.powersetCard 3,
        (facetCompletions K U T).card.choose 2 := by
  classical
  have hSub : nonemptyCommonRoots K U ⊆ U.powersetCard 2 := by
    intro P hP
    exact (Finset.mem_filter.mp hP).1
  calc
    (∑ P ∈ nonemptyCommonRoots K U,
      (commonRootCell K U P).card) =
      ∑ P ∈ U.powersetCard 2,
        (commonRootCell K U P).card := by
      apply Finset.sum_subset hSub
      intro P hP hNot
      have hNotPos : ¬ 0 < (commonRootCell K U P).card := by
        intro hPos
        exact hNot (Finset.mem_filter.mpr ⟨hP, hPos⟩)
      omega
    _ = ∑ T ∈ U.powersetCard 3,
        (facetCompletions K U T).card.choose 2 :=
      common_root_facet_completion_double_count K U hUniform

/-- The sum of edge counts of the actual centered native graphs is
exactly the second facet-completion moment.  This is the edge-count
identity used in (III.B.8). -/
theorem native_tail_edges_eq_facet_pair_count
    (K : Family α) (U : Edge α) (fallback : α)
    (hUniform : Uniform 4 K)
    (hCenters : UniqueCommonRootCenters K U) :
    (∑ P ∈ nonemptyCommonRoots K U,
      (nativeTailGraph K U P
        (chosenCommonRootLabel K U fallback hCenters P)).edgeFinset.card) =
      ∑ T ∈ U.powersetCard 3,
        (facetCompletions K U T).card.choose 2 := by
  classical
  calc
    (∑ P ∈ nonemptyCommonRoots K U,
      (nativeTailGraph K U P
        (chosenCommonRootLabel K U fallback hCenters P)).edgeFinset.card) =
      ∑ P ∈ nonemptyCommonRoots K U,
        (commonRootCell K U P).card := by
      apply Finset.sum_congr rfl
      intro P hP
      have hPcard : P.card = 2 :=
        (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hP).1).2
      exact native_tail_edge_count_eq_common_root_cell K U P
        (chosenCommonRootLabel K U fallback hCenters P) hPcard
        (fun T hT => chosen_common_root_label_center
          K U fallback hCenters P hP T hT)
    _ = ∑ T ∈ U.powersetCard 3,
        (facetCompletions K U T).card.choose 2 :=
      used_common_root_facet_double_count K U hUniform

/-- The actual excess-degree count over all native tail graphs. -/
noncomputable def nativeTailDegreeExcessTotal
    (K : Family α) (U : Edge α)
    (used : Family α) (label : Edge α → α) : ℕ :=
  ∑ P ∈ used,
    (nativeActiveVertices
      (nativeTailGraph K U P (label P))).sum
        (fun x => (nativeTailGraph K U P (label P)).degree x - 1)

/-- The graph-internal degree ledger, summed over the actual labeled
common-root cells, gives the native side of (III.B.8). -/
theorem native_tail_degree_excess_facet_ledger
    (K : Family α) (U : Edge α) (fallback : α)
    (hUniform : Uniform 4 K)
    (hCenters : UniqueCommonRootCenters K U) :
    nativeTailDegreeExcessTotal K U (nonemptyCommonRoots K U)
        (chosenCommonRootLabel K U fallback hCenters) +
      nativeTailVertexTotal K U (nonemptyCommonRoots K U)
        (chosenCommonRootLabel K U fallback hCenters) =
      2 * (∑ T ∈ U.powersetCard 3,
        (facetCompletions K U T).card.choose 2) := by
  classical
  let used := nonemptyCommonRoots K U
  let label := chosenCommonRootLabel K U fallback hCenters
  have hPoint (P : Edge α) (_hP : P ∈ used) :=
    native_degree_excess_identity (nativeTailGraph K U P (label P))
  have hSum := Finset.sum_congr rfl
    (fun P hP => hPoint P hP)
  unfold nativeTailDegreeExcessTotal nativeTailVertexTotal
  rw [Finset.sum_add_distrib] at hSum
  simp only [← Finset.mul_sum] at hSum
  rw [← native_tail_edges_eq_facet_pair_count
    K U fallback hUniform hCenters]
  simpa only [used, label] using hSum

end JSP523.Rank4
