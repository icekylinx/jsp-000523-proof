import JSP523.Rank4.GraphColoredActualRecords

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def facetLabelColor (T : Finset α) (hTcard : T.card = 3)
    (z : α) (hz : z ∈ T) : CliqueColor :=
  Fin.cast (by simpa using hTcard)
    ((Fintype.equivFin {x // x ∈ T}) ⟨z, hz⟩)

omit [Fintype α] [DecidableEq α] in
theorem facetLabelColor_injective (T : Finset α) (hTcard : T.card = 3) :
    ∀ {z w : α} (hz : z ∈ T) (hw : w ∈ T),
      facetLabelColor T hTcard z hz = facetLabelColor T hTcard w hw → z = w := by
  intro z w hz hw h
  change Fin.cast _ ((Fintype.equivFin {x // x ∈ T}) ⟨z, hz⟩) =
    Fin.cast _ ((Fintype.equivFin {x // x ∈ T}) ⟨w, hw⟩) at h
  have hfin : (Fintype.equivFin {x // x ∈ T}) ⟨z, hz⟩ =
      (Fintype.equivFin {x // x ∈ T}) ⟨w, hw⟩ := by
    apply Fin.ext
    simpa using congrArg Fin.val h
  have heq := (Fintype.equivFin {x // x ∈ T}).injective hfin
  exact congrArg Subtype.val heq

noncomputable def canonicalActualK4ColorMark (D : FiniteCompletionCliqueData α)
    (T : Edge α) (hcard : (graphFacetCompletions D.K D.ground T).card = 4)
    (i : CliqueColor) : α :=
  if i = 0 then D.label
      (completionK4Ends (canonicalK4Completion D T hcard) 0).1
      (completionK4Ends (canonicalK4Completion D T hcard) 0).2
  else if i = 1 then D.label
      (completionK4Ends (canonicalK4Completion D T hcard) 1).1
      (completionK4Ends (canonicalK4Completion D T hcard) 1).2
  else D.label
      (completionK4Ends (canonicalK4Completion D T hcard) 2).1
      (completionK4Ends (canonicalK4Completion D T hcard) 2).2

/-- The six actual labels on a canonical four-vertex completion, in the
order `01, 02, 03, 12, 13, 23`, have the proper K4 opposite-edge pattern. -/
theorem canonical_k4_labels_are_proper_pattern
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hcard : (graphFacetCompletions D.K D.ground T).card = 4)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hProper : CompletionProperlyEdgeColored D
      (graphFacetCompletions D.K D.ground T)) :
    let v := canonicalK4Completion D T hcard
    (D.label (completionK4Ends v 0).1 (completionK4Ends v 0).2 =
        D.label (completionK4Ends v 5).1 (completionK4Ends v 5).2 ∧
      D.label (completionK4Ends v 1).1 (completionK4Ends v 1).2 =
        D.label (completionK4Ends v 4).1 (completionK4Ends v 4).2 ∧
      D.label (completionK4Ends v 2).1 (completionK4Ends v 2).2 =
        D.label (completionK4Ends v 3).1 (completionK4Ends v 3).2) ∧
    (D.label (completionK4Ends v 0).1 (completionK4Ends v 0).2 ≠
        D.label (completionK4Ends v 1).1 (completionK4Ends v 1).2 ∧
      D.label (completionK4Ends v 0).1 (completionK4Ends v 0).2 ≠
        D.label (completionK4Ends v 2).1 (completionK4Ends v 2).2 ∧
      D.label (completionK4Ends v 1).1 (completionK4Ends v 1).2 ≠
        D.label (completionK4Ends v 2).1 (completionK4Ends v 2).2) := by
  let v := canonicalK4Completion D T hcard
  have hv : Function.Injective v := canonicalK4Completion_injective D T hcard
  have hmem : ∀ i, v i ∈ graphFacetCompletions D.K D.ground T := by
    intro i
    exact canonicalK4Completion_mem D T hcard i
  have hneq : ∀ {i j : Fin 4}, i ≠ j → v i ≠ v j := by
    intro i j hij heq
    exact hij (hv heq)
  have hLabel (i : Fin 6) :
      D.label (completionK4Ends v i).1 (completionK4Ends v i).2 ∈ T := by
    exact completion_pair_label_mem_facet D T hTcard hTsub _ _
      (hmem (completionK4IndexPair i).1)
      (hmem (completionK4IndexPair i).2)
      (completionK4Ends_offdiag v hv i)
  let code (i : Fin 6) : CliqueColor :=
    facetLabelColor T hTcard
      (D.label (completionK4Ends v i).1 (completionK4Ends v i).2) (hLabel i)
  have hMonoOrRainbow (i j k : Fin 4) (hij : i ≠ j)
      (hik : i ≠ k) (hjk : j ≠ k) :
      monoOrRainbow (facetLabelColor T hTcard (D.label (v i) (v j))
        (completion_pair_label_mem_facet D T hTcard hTsub _ _ (hmem i) (hmem j) (hneq hij)))
        (facetLabelColor T hTcard (D.label (v i) (v k))
          (completion_pair_label_mem_facet D T hTcard hTsub _ _ (hmem i) (hmem k) (hneq hik)))
        (facetLabelColor T hTcard (D.label (v j) (v k))
          (completion_pair_label_mem_facet D T hTcard hTsub _ _ (hmem j) (hmem k) (hneq hjk))) := by
    have h := completion_triangle_mono_or_rainbow D T (v i) (v j) (v k)
      (hmem i) (hmem j) (hmem k) (hneq hij) (hneq hik) (hneq hjk)
    rcases h with hmono | hrain
    · exact Or.inl ⟨by simp [hmono.1], by simp [hmono.1.symm, hmono.2]⟩
    · apply Or.inr
      refine ⟨?_, ?_, ?_⟩
      · intro heq
        exact hrain.1 (facetLabelColor_injective T hTcard
          (completion_pair_label_mem_facet D T hTcard hTsub _ _ (hmem i) (hmem j) (hneq hij))
          (completion_pair_label_mem_facet D T hTcard hTsub _ _ (hmem i) (hmem k) (hneq hik)) heq)
      · intro heq
        exact hrain.2.1 (facetLabelColor_injective T hTcard
          (completion_pair_label_mem_facet D T hTcard hTsub _ _ (hmem i) (hmem j) (hneq hij))
          (completion_pair_label_mem_facet D T hTcard hTsub _ _ (hmem j) (hmem k) (hneq hjk)) heq)
      · intro heq
        exact hrain.2.2 (facetLabelColor_injective T hTcard
          (completion_pair_label_mem_facet D T hTcard hTsub _ _ (hmem i) (hmem k) (hneq hik))
          (completion_pair_label_mem_facet D T hTcard hTsub _ _ (hmem j) (hmem k) (hneq hjk)) heq)
  have hTriangle012 := hMonoOrRainbow 0 1 2 (by decide) (by decide) (by decide)
  have hTriangle013 := hMonoOrRainbow 0 1 3 (by decide) (by decide) (by decide)
  have hTriangle023 := hMonoOrRainbow 0 2 3 (by decide) (by decide) (by decide)
  have hTriangle123 := hMonoOrRainbow 1 2 3 (by decide) (by decide) (by decide)
  change monoOrRainbow (code 0) (code 1) (code 3) at hTriangle012
  change monoOrRainbow (code 0) (code 2) (code 4) at hTriangle013
  change monoOrRainbow (code 1) (code 2) (code 5) at hTriangle023
  change monoOrRainbow (code 3) (code 4) (code 5) at hTriangle123
  let a := code 0
  let b := code 1
  let c := code 3
  let d := code 2
  let e := code 4
  let f := code 5
  have hK4 := k4_mono_or_proper_three_color a b c d e f
    (by simpa [a, b, c] using hTriangle012)
    (by simpa [a, d, e] using hTriangle013)
    (by simpa [b, d, f] using hTriangle023)
    (by simpa [c, e, f] using hTriangle123)
  have hOpp : a = f ∧ b = e ∧ c = d ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
    rcases hK4 with hMono | hColoring
    · have hbad := hProper (v 0) (hmem 0) (v 1) (hmem 1) (v 2) (hmem 2)
        (hneq (by decide)) (hneq (by decide)) (hneq (by decide))
      have hab : D.label (v 0) (v 1) = D.label (v 0) (v 2) :=
        facetLabelColor_injective T hTcard (hLabel 0) (hLabel 1)
          (by simpa [a, b, code, completionK4Ends, completionK4IndexPair] using hMono.1)
      exact False.elim (hbad hab)
    · exact hColoring
  have hRawOpp :
      D.label (completionK4Ends v 0).1 (completionK4Ends v 0).2 =
        D.label (completionK4Ends v 5).1 (completionK4Ends v 5).2 ∧
      D.label (completionK4Ends v 1).1 (completionK4Ends v 1).2 =
        D.label (completionK4Ends v 4).1 (completionK4Ends v 4).2 ∧
      D.label (completionK4Ends v 3).1 (completionK4Ends v 3).2 =
        D.label (completionK4Ends v 2).1 (completionK4Ends v 2).2 := by
    refine ⟨?_, ?_, ?_⟩
    · exact facetLabelColor_injective T hTcard (hLabel 0) (hLabel 5) hOpp.1
    · exact facetLabelColor_injective T hTcard (hLabel 1) (hLabel 4) hOpp.2.1
    · exact facetLabelColor_injective T hTcard (hLabel 3) (hLabel 2) hOpp.2.2.1
  have hProperRaw :
      D.label (completionK4Ends v 0).1 (completionK4Ends v 0).2 ≠
        D.label (completionK4Ends v 1).1 (completionK4Ends v 1).2 ∧
      D.label (completionK4Ends v 0).1 (completionK4Ends v 0).2 ≠
        D.label (completionK4Ends v 2).1 (completionK4Ends v 2).2 ∧
      D.label (completionK4Ends v 1).1 (completionK4Ends v 1).2 ≠
        D.label (completionK4Ends v 2).1 (completionK4Ends v 2).2 := by
    have hp01_02 := hProper (v 0) (hmem 0) (v 1) (hmem 1) (v 2) (hmem 2)
      (hneq (by decide)) (hneq (by decide)) (hneq (by decide))
    have hp01_03 := hProper (v 0) (hmem 0) (v 1) (hmem 1) (v 3) (hmem 3)
      (hneq (by decide)) (hneq (by decide)) (hneq (by decide))
    have hp02_03 := hProper (v 0) (hmem 0) (v 2) (hmem 2) (v 3) (hmem 3)
      (hneq (by decide)) (hneq (by decide)) (hneq (by decide))
    refine ⟨?_, ?_, ?_⟩
    · simpa [completionK4Ends, completionK4IndexPair] using hp01_02
    · simpa [completionK4Ends, completionK4IndexPair] using hp01_03
    · simpa [completionK4Ends, completionK4IndexPair] using hp02_03
  refine ⟨?_, ?_⟩
  · exact ⟨hRawOpp.1, hRawOpp.2.1, hRawOpp.2.2.symm⟩
  · exact hProperRaw

/-- The canonical proper completion K4 contributes at least the paper's
`2 - properFourRecordLoss k` actual undirected records at every color slot. -/
theorem canonical_actual_K4_undirected_records_card_lower_bound
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hcard : (graphFacetCompletions D.K D.ground T).card = 4)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hProper : CompletionProperlyEdgeColored D
      (graphFacetCompletions D.K D.ground T))
    (x : CliqueColor) (S : Finset (Fin 4)) (k : ℕ) (hk : k = S.card) :
    2 - properFourRecordLoss k ≤
      (selectedActualK4UndirectedColorSlotRecords D T
        (canonicalK4Completion D T hcard)
        (canonicalActualK4ColorMark D T hcard) x S).card := by
  let v := canonicalK4Completion D T hcard
  let mark := canonicalActualK4ColorMark D T hcard
  obtain ⟨hOpp, hAdj⟩ := canonical_k4_labels_are_proper_pattern
    D T hcard hTcard hTsub hProper
  have hv : Function.Injective v := canonicalK4Completion_injective D T hcard
  have hmark : Function.Injective mark := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [mark, canonicalActualK4ColorMark,
        v, completionK4Ends, completionK4IndexPair]
  have hLabelMem : ∀ i, D.label (completionK4Ends v i).1
      (completionK4Ends v i).2 ∈ T := by
    intro i
    exact completion_pair_label_mem_facet D T hTcard hTsub _ _
      (canonicalK4Completion_mem D T hcard (completionK4IndexPair i).1)
      (canonicalK4Completion_mem D T hcard (completionK4IndexPair i).2)
      (completionK4Ends_offdiag v hv i)
  have hColor : ∀ i : Fin 6,
      D.label (completionK4Ends v i).1 (completionK4Ends v i).2 =
        mark (properK4EdgeColor 0 1 2 i) := by
    intro i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · change D.label (completionK4Ends v 3).1 (completionK4Ends v 3).2 =
        D.label (completionK4Ends v 2).1 (completionK4Ends v 2).2
      simpa [v] using hOpp.2.2.symm
    · change D.label (completionK4Ends v 4).1 (completionK4Ends v 4).2 =
        D.label (completionK4Ends v 1).1 (completionK4Ends v 1).2
      simpa [v] using hOpp.2.1.symm
    · change D.label (completionK4Ends v 5).1 (completionK4Ends v 5).2 =
        D.label (completionK4Ends v 0).1 (completionK4Ends v 0).2
      simpa [v] using hOpp.1.symm
  exact selected_actual_K4_undirected_records_card_lower_bound
    D T v mark 0 1 2 x S k hk hv hmark hLabelMem hColor (by decide)

end JSP523.Rank4
