import JSP523.Rank4.GraphActualUniquePairLedger
import JSP523.Rank4.GraphCanonicalTriangleFamily
import JSP523.Rank4.GraphCanonicalK4Family

/-!
# Canonical colored-facet records in the actual unique-pair ledger

Each selected color slot uses the selected graph of its own base pair.
The family bounds reuse the facet and color disjointness proofs for the
canonical triangle and proper-K4 records.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
/-- A divergent completion facet selects each of its vertices in the
actual pair link at the opposite base pair. -/
theorem actual_colored_facet_vertex_selected
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hTsub : T ⊆ D.ground) (z : α) (hz : z ∈ T)
    (hNonprivate : 2 ≤ (graphFacetCompletions D.K D.ground T).card)
    (hColored : FacetHasDivergentLabels
      (graphFacetCompletions D.K D.ground T) D.label) :
    z ∈ actualEligiblePairSlotVertices D (T.erase z) := by
  classical
  change z ∈ D.ground.filter fun x => x ∉ T.erase z ∧
    FacetEligibleAtPair
      (graphFacetCompletions D.K D.ground (insert x (T.erase z)))
      D.label (T.erase z)
  apply Finset.mem_filter.mpr
  refine ⟨hTsub hz, by simp, ?_⟩
  rw [Finset.insert_erase hz]
  exact ⟨hNonprivate, Or.inl hColored⟩

omit [Fintype α] in
/-- Three distinct completion vertices in a proper coloring witness
divergent pair labels. -/
theorem proper_completion_facet_divergent_of_three
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hProper : CompletionProperlyEdgeColored D
      (graphFacetCompletions D.K D.ground T))
    (a b c : α)
    (ha : a ∈ graphFacetCompletions D.K D.ground T)
    (hb : b ∈ graphFacetCompletions D.K D.ground T)
    (hc : c ∈ graphFacetCompletions D.K D.ground T)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    FacetHasDivergentLabels
      (graphFacetCompletions D.K D.ground T) D.label := by
  exact ⟨a, ha, b, hb, c, hc, hab, hac, hbc,
    hProper a ha b hb c hc hab hac hbc⟩

/-- The three canonical proper-K4 color marks are vertices of the facet. -/
theorem canonical_actual_k4_color_mark_mem_facet
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hCard : (graphFacetCompletions D.K D.ground T).card = 4)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (x : CliqueColor) :
    canonicalActualK4ColorMark D T hCard x ∈ T := by
  let v := canonicalK4Completion D T hCard
  have hv : Function.Injective v :=
    canonical_k4_completion_injective D T hCard
  have hLabel (i : Fin 6) :
      D.label (completionK4Ends v i).1 (completionK4Ends v i).2 ∈ T :=
    completion_pair_label_mem_facet D T hTcard hTsub _ _
      (canonical_k4_completion_mem D T hCard (completionK4IndexPair i).1)
      (canonical_k4_completion_mem D T hCard (completionK4IndexPair i).2)
      (completion_k4_ends_offdiag v hv i)
  fin_cases x
  · simpa [canonicalActualK4ColorMark, v] using (hLabel (0 : Fin 6))
  · simpa [canonicalActualK4ColorMark, v] using (hLabel (1 : Fin 6))
  · simpa [canonicalActualK4ColorMark, v] using (hLabel (2 : Fin 6))

/-- A canonical rainbow completion triangle has divergent pair labels. -/
theorem canonical_triangle_facet_divergent
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hCard : (graphFacetCompletions D.K D.ground T).card = 3)
    (hRainbow : CompletionTriangleRainbow D
      (graphFacetCompletions D.K D.ground T)) :
    FacetHasDivergentLabels
      (graphFacetCompletions D.K D.ground T) D.label := by
  let v := canonicalTriangleCompletion D T hCard
  have hv := canonical_triangle_completion_injective D T hCard
  exact proper_completion_facet_divergent_of_three D T
    (completion_triangle_rainbow_implies_proper D _ hRainbow)
    (v 0) (v 1) (v 2)
    (canonical_triangle_completion_mem D T hCard 0)
    (canonical_triangle_completion_mem D T hCard 1)
    (canonical_triangle_completion_mem D T hCard 2)
    (by intro h; exact (by decide : (0 : Fin 3) ≠ 1) (hv h))
    (by intro h; exact (by decide : (0 : Fin 3) ≠ 2) (hv h))
    (by intro h; exact (by decide : (1 : Fin 3) ≠ 2) (hv h))

/-- Every rainbow-triangle color mark is actually selected at its
opposite base pair. -/
theorem canonical_triangle_mark_actual_selected
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hCard : (graphFacetCompletions D.K D.ground T).card = 3)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hRainbow : CompletionTriangleRainbow D
      (graphFacetCompletions D.K D.ground T))
    (x : CliqueColor) :
    let z := canonicalTriangleMark D T hCard x
    z ∈ actualEligiblePairSlotVertices D (T.erase z) := by
  exact actual_colored_facet_vertex_selected D T hTsub _
    (canonical_triangle_mark_mem_facet D T hCard hTcard hTsub x)
    (by rw [hCard]; omega)
    (canonical_triangle_facet_divergent D T hCard hRainbow)

/-- A canonical proper completion K4 has divergent pair labels. -/
theorem canonical_k4_facet_divergent
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hCard : (graphFacetCompletions D.K D.ground T).card = 4)
    (hProper : CompletionProperlyEdgeColored D
      (graphFacetCompletions D.K D.ground T)) :
    FacetHasDivergentLabels
      (graphFacetCompletions D.K D.ground T) D.label := by
  let v := canonicalK4Completion D T hCard
  have hv := canonical_k4_completion_injective D T hCard
  exact proper_completion_facet_divergent_of_three D T hProper
    (v 0) (v 1) (v 2)
    (canonical_k4_completion_mem D T hCard 0)
    (canonical_k4_completion_mem D T hCard 1)
    (canonical_k4_completion_mem D T hCard 2)
    (by intro h; exact (by decide : (0 : Fin 4) ≠ 1) (hv h))
    (by intro h; exact (by decide : (0 : Fin 4) ≠ 2) (hv h))
    (by intro h; exact (by decide : (1 : Fin 4) ≠ 2) (hv h))

/-- Every proper-K4 color mark is actually selected at its opposite
base pair. -/
theorem canonical_k4_mark_actual_selected
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hCard : (graphFacetCompletions D.K D.ground T).card = 4)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hProper : CompletionProperlyEdgeColored D
      (graphFacetCompletions D.K D.ground T))
    (x : CliqueColor) :
    let z := canonicalActualK4ColorMark D T hCard x
    z ∈ actualEligiblePairSlotVertices D (T.erase z) := by
  exact actual_colored_facet_vertex_selected D T hTsub _
    (canonical_actual_k4_color_mark_mem_facet D T hCard hTcard hTsub x)
    (by rw [hCard]; omega)
    (canonical_k4_facet_divergent D T hCard hProper)

/-- Rainbow-triangle color records, with each color using the graph of
its own actual base pair, are paid by the single actual unique ledger. -/
theorem canonical_triangle_family_actual_unique_records
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : FiniteCompletionCliqueData α) (C : Finset ι)
    (T : ι → Edge α) (hTInjective : Function.Injective T)
    (hCard : ∀ t ∈ C,
      (graphFacetCompletions D.K D.ground (T t)).card = 3)
    (hTCard : ∀ t ∈ C, (T t).card = 3)
    (hTSub : ∀ t ∈ C, T t ⊆ D.ground)
    (hRainbow : ∀ t ∈ C, CompletionTriangleRainbow D
      (graphFacetCompletions D.K D.ground (T t)))
    (S₀ : ι → CliqueColor → Finset (Fin 3))
    (hVerticesSelected : ∀ (t : ι) (ht : t ∈ C) (x : CliqueColor) (i : Fin 3),
      i ∈ S₀ t x →
        let z := canonicalTriangleMark D (T t) (hCard t ht) x
        canonicalTriangleCompletion D (T t) (hCard t ht) i ∈
          actualEligiblePairSlotVertices D ((T t).erase z)) :
    (∑ t ∈ C, (coloredFacetRecords 3 -
      ∑ x : CliqueColor, coloredSlotLoss 3 (S₀ t x).card)) ≤
        ((actualUniquePairRecordKeys D).card : ℚ) := by
  apply canonical_triangle_family_actual_h_records_into
    D C T hTInjective hCard hTCard hTSub hRainbow S₀
      (actualUniquePairRecordKeys D)
  intro t ht x
  let z := canonicalTriangleMark D (T t) (hCard t ht) x
  let Q := (T t).erase z
  have hv : Function.Injective
      (canonicalTriangleCompletion D (T t) (hCard t ht)) :=
    canonical_triangle_completion_injective D (T t) (hCard t ht)
  have hMark : z ∈ actualEligiblePairSlotVertices D Q :=
    canonical_triangle_mark_actual_selected D (T t) (hCard t ht)
      (hTCard t ht) (hTSub t ht) (hRainbow t ht) x
  exact selected_triangle_color_records_subset_actual_unique
    D (T t) Q
      (canonicalTriangleCompletion D (T t) (hCard t ht))
      (canonicalTriangleMark D (T t) (hCard t ht)) x (S₀ t x)
      (facet_erase_vertex_mem_ground_pairs D (T t)
        (hTCard t ht) (hTSub t ht) z
        (canonical_triangle_mark_mem_facet D (T t) (hCard t ht)
          (hTCard t ht) (hTSub t ht) x))
      rfl hMark (hVerticesSelected t ht x)
      (hTCard t ht) (hTSub t ht)
      (fun i => canonical_triangle_completion_mem D (T t) (hCard t ht) i)
      hv

/-- Proper-K4 color records use the same actual base-dependent ledger. -/
theorem canonical_k4_family_actual_unique_records
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : FiniteCompletionCliqueData α) (C : Finset ι)
    (T : ι → Edge α) (hTInjective : Function.Injective T)
    (hCard : ∀ t ∈ C,
      (graphFacetCompletions D.K D.ground (T t)).card = 4)
    (hTCard : ∀ t ∈ C, (T t).card = 3)
    (hTSub : ∀ t ∈ C, T t ⊆ D.ground)
    (hProper : ∀ t ∈ C, CompletionProperlyEdgeColored D
      (graphFacetCompletions D.K D.ground (T t)))
    (S₀ : ι → CliqueColor → Finset (Fin 4))
    (hVerticesSelected : ∀ (t : ι) (ht : t ∈ C) (x : CliqueColor) (i : Fin 4),
      i ∈ S₀ t x →
        let z := canonicalActualK4ColorMark D (T t) (hCard t ht) x
        canonicalK4Completion D (T t) (hCard t ht) i ∈
          actualEligiblePairSlotVertices D ((T t).erase z)) :
    (∑ t ∈ C, (coloredFacetRecords 4 -
      ∑ x : CliqueColor, coloredSlotLoss 4 (S₀ t x).card)) ≤
        ((actualUniquePairRecordKeys D).card : ℚ) := by
  apply canonical_k4_family_actual_h_records_into
    D C T hTInjective hCard hTCard hTSub hProper S₀
      (actualUniquePairRecordKeys D)
  intro t ht x
  let z := canonicalActualK4ColorMark D (T t) (hCard t ht) x
  let Q := (T t).erase z
  have hv : Function.Injective
      (canonicalK4Completion D (T t) (hCard t ht)) :=
    canonical_k4_completion_injective D (T t) (hCard t ht)
  have hMark : z ∈ actualEligiblePairSlotVertices D Q :=
    canonical_k4_mark_actual_selected D (T t) (hCard t ht)
      (hTCard t ht) (hTSub t ht) (hProper t ht) x
  exact selected_k4_color_records_subset_actual_unique
    D (T t) Q
      (canonicalK4Completion D (T t) (hCard t ht))
      (canonicalActualK4ColorMark D (T t) (hCard t ht)) x (S₀ t x)
      (facet_erase_vertex_mem_ground_pairs D (T t)
        (hTCard t ht) (hTSub t ht) z
        (canonical_actual_k4_color_mark_mem_facet D (T t) (hCard t ht)
          (hTCard t ht) (hTSub t ht) x))
      rfl hMark (hVerticesSelected t ht x)
      (hTCard t ht) (hTSub t ht)
      (fun i => canonical_k4_completion_mem D (T t) (hCard t ht) i)
      hv

end JSP523.Rank4
