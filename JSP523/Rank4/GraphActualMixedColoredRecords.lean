import JSP523.Rank4.GraphActualColoredMarks

/-!
# Mixed colored-facet records in one actual pair-link ledger

Rainbow-triangle and proper-K4 records are disjoint even across the two
facet types. This permits one common unique-pair ledger in (III.B.10).
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Both canonical colored-facet types share the actual unique-pair
record ledger, with no double counting between types. -/
theorem canonical_mixed_actual_unique_records
    {ι₃ ι₄ : Type*} [Fintype ι₃] [DecidableEq ι₃]
    [Fintype ι₄] [DecidableEq ι₄]
    (D : FiniteCompletionCliqueData α)
    (T₃ : ι₃ → Edge α) (hT₃Injective : Function.Injective T₃)
    (hCard₃ : ∀ t,
      (graphFacetCompletions D.K D.ground (T₃ t)).card = 3)
    (hT₃Card : ∀ t, (T₃ t).card = 3)
    (hT₃Sub : ∀ t, T₃ t ⊆ D.ground)
    (hRainbow : ∀ t, CompletionTriangleRainbow D
      (graphFacetCompletions D.K D.ground (T₃ t)))
    (T₄ : ι₄ → Edge α) (hT₄Injective : Function.Injective T₄)
    (hCard₄ : ∀ t,
      (graphFacetCompletions D.K D.ground (T₄ t)).card = 4)
    (hT₄Card : ∀ t, (T₄ t).card = 3)
    (hT₄Sub : ∀ t, T₄ t ⊆ D.ground)
    (hProper : ∀ t, CompletionProperlyEdgeColored D
      (graphFacetCompletions D.K D.ground (T₄ t))) :
    (∑ t : ι₃, (coloredFacetRecords 3 -
      ∑ x : CliqueColor, coloredSlotLoss 3
        (canonicalTriangleActualSelectedIndices D (T₃ t) (hCard₃ t) x).card)) +
    (∑ t : ι₄, (coloredFacetRecords 4 -
      ∑ x : CliqueColor, coloredSlotLoss 4
        (canonicalK4ActualSelectedIndices D (T₄ t) (hCard₄ t) x).card)) ≤
      ((actualUniquePairRecordKeys D).card : ℚ) := by
  classical
  let R₃ (t : ι₃) (x : CliqueColor) : Finset (Edge α × Edge α) :=
    selectedActualTriangleUndirectedColorSlotRecords D (T₃ t)
      (canonicalTriangleCompletion D (T₃ t) (hCard₃ t))
      (canonicalTriangleMark D (T₃ t) (hCard₃ t)) x
      (canonicalTriangleActualSelectedIndices D (T₃ t) (hCard₃ t) x)
  let R₄ (t : ι₄) (x : CliqueColor) : Finset (Edge α × Edge α) :=
    selectedActualK4UndirectedColorSlotRecords D (T₄ t)
      (canonicalK4Completion D (T₄ t) (hCard₄ t))
      (canonicalActualK4ColorMark D (T₄ t) (hCard₄ t)) x
      (canonicalK4ActualSelectedIndices D (T₄ t) (hCard₄ t) x)
  let U₃ : Finset (Edge α × Edge α) :=
    (Finset.univ : Finset ι₃).biUnion fun t =>
      (Finset.univ : Finset CliqueColor).biUnion fun x => R₃ t x
  let U₄ : Finset (Edge α × Edge α) :=
    (Finset.univ : Finset ι₄).biUnion fun t =>
      (Finset.univ : Finset CliqueColor).biUnion fun x => R₄ t x
  have h₃Bound :
      (∑ t : ι₃, (coloredFacetRecords 3 -
        ∑ x : CliqueColor, coloredSlotLoss 3
          (canonicalTriangleActualSelectedIndices D (T₃ t)
            (hCard₃ t) x).card)) ≤ (U₃.card : ℚ) := by
    apply canonical_triangle_family_actual_h_records_into
      D (Finset.univ : Finset ι₃) T₃ hT₃Injective
      (by intro t _; exact hCard₃ t)
      (by intro t _; exact hT₃Card t)
      (by intro t _; exact hT₃Sub t)
      (by intro t _; exact hRainbow t)
      (fun t x => canonicalTriangleActualSelectedIndices D (T₃ t) (hCard₃ t) x)
      U₃
    intro t _ x
    change R₃ t x ⊆ U₃
    intro key hkey
    exact Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ t,
      Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ x, hkey⟩⟩
  have h₄Bound :
      (∑ t : ι₄, (coloredFacetRecords 4 -
        ∑ x : CliqueColor, coloredSlotLoss 4
          (canonicalK4ActualSelectedIndices D (T₄ t)
            (hCard₄ t) x).card)) ≤ (U₄.card : ℚ) := by
    apply canonical_k4_family_actual_h_records_into
      D (Finset.univ : Finset ι₄) T₄ hT₄Injective
      (by intro t _; exact hCard₄ t)
      (by intro t _; exact hT₄Card t)
      (by intro t _; exact hT₄Sub t)
      (by intro t _; exact hProper t)
      (fun t x => canonicalK4ActualSelectedIndices D (T₄ t) (hCard₄ t) x)
      U₄
    intro t _ x
    change R₄ t x ⊆ U₄
    intro key hkey
    exact Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ t,
      Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ x, hkey⟩⟩
  have h₃Sub : U₃ ⊆ actualUniquePairRecordKeys D := by
    intro key hkey
    rcases Finset.mem_biUnion.mp hkey with ⟨t, _, h⟩
    rcases Finset.mem_biUnion.mp h with ⟨x, _, hR⟩
    exact selected_triangle_color_records_subset_actual_unique
      D (T₃ t) ((T₃ t).erase (canonicalTriangleMark D (T₃ t) (hCard₃ t) x))
      (canonicalTriangleCompletion D (T₃ t) (hCard₃ t))
      (canonicalTriangleMark D (T₃ t) (hCard₃ t)) x
      (canonicalTriangleActualSelectedIndices D (T₃ t) (hCard₃ t) x)
      (facet_erase_vertex_mem_ground_pairs D (T₃ t)
        (hT₃Card t) (hT₃Sub t) _
        (canonical_triangle_mark_mem_facet D (T₃ t) (hCard₃ t)
          (hT₃Card t) (hT₃Sub t) x))
      rfl
      (canonical_triangle_mark_actual_selected D (T₃ t) (hCard₃ t)
        (hT₃Card t) (hT₃Sub t) (hRainbow t) x)
      (by intro i hi; exact (Finset.mem_filter.mp hi).2)
      (hT₃Card t) (hT₃Sub t)
      (fun i => canonical_triangle_completion_mem D (T₃ t) (hCard₃ t) i)
      (canonical_triangle_completion_injective D (T₃ t) (hCard₃ t)) hR
  have h₄Sub : U₄ ⊆ actualUniquePairRecordKeys D := by
    intro key hkey
    rcases Finset.mem_biUnion.mp hkey with ⟨t, _, h⟩
    rcases Finset.mem_biUnion.mp h with ⟨x, _, hR⟩
    exact selected_k4_color_records_subset_actual_unique
      D (T₄ t) ((T₄ t).erase (canonicalActualK4ColorMark D (T₄ t) (hCard₄ t) x))
      (canonicalK4Completion D (T₄ t) (hCard₄ t))
      (canonicalActualK4ColorMark D (T₄ t) (hCard₄ t)) x
      (canonicalK4ActualSelectedIndices D (T₄ t) (hCard₄ t) x)
      (facet_erase_vertex_mem_ground_pairs D (T₄ t)
        (hT₄Card t) (hT₄Sub t) _
        (canonical_actual_k4_color_mark_mem_facet D (T₄ t) (hCard₄ t)
          (hT₄Card t) (hT₄Sub t) x))
      rfl
      (canonical_k4_mark_actual_selected D (T₄ t) (hCard₄ t)
        (hT₄Card t) (hT₄Sub t) (hProper t) x)
      (by intro i hi; exact (Finset.mem_filter.mp hi).2)
      (hT₄Card t) (hT₄Sub t)
      (fun i => canonical_k4_completion_mem D (T₄ t) (hCard₄ t) i)
      (canonical_k4_completion_injective D (T₄ t) (hCard₄ t)) hR
  have hDisjoint : Disjoint U₃ U₄ := by
    apply Finset.disjoint_left.mpr
    intro key hkey3 hkey4
    rcases Finset.mem_biUnion.mp hkey3 with ⟨t, _, htx⟩
    rcases Finset.mem_biUnion.mp htx with ⟨x, _, hR3⟩
    rcases Finset.mem_biUnion.mp hkey4 with ⟨u, _, huy⟩
    rcases Finset.mem_biUnion.mp huy with ⟨y, _, hR4⟩
    have hTT' : T₃ t ≠ T₄ u := by
      intro h
      have h3 := hCard₃ t
      rw [h, hCard₄ u] at h3
      omega
    have hDis := selected_triangle_k4_undirected_records_disjoint_across_facets
      D (T₃ t) (T₄ u)
      (canonicalTriangleCompletion D (T₃ t) (hCard₃ t))
      (canonicalK4Completion D (T₄ u) (hCard₄ u))
      (canonicalTriangleMark D (T₃ t) (hCard₃ t))
      (canonicalActualK4ColorMark D (T₄ u) (hCard₄ u)) x y
      (canonicalTriangleActualSelectedIndices D (T₃ t) (hCard₃ t) x)
      (canonicalK4ActualSelectedIndices D (T₄ u) (hCard₄ u) y)
      hTT' (hT₃Card t) (hT₃Sub t)
      (fun i => canonical_triangle_completion_mem D (T₃ t) (hCard₃ t) i)
      (canonical_triangle_completion_injective D (T₃ t) (hCard₃ t))
      (hT₄Card u) (hT₄Sub u)
      (fun i => canonical_k4_completion_mem D (T₄ u) (hCard₄ u) i)
      (canonical_k4_completion_injective D (T₄ u) (hCard₄ u))
    exact (Finset.disjoint_left.mp hDis) hR3 hR4
  have hUnionSub : U₃ ∪ U₄ ⊆ actualUniquePairRecordKeys D :=
    Finset.union_subset h₃Sub h₄Sub
  have hCardBound : U₃.card + U₄.card ≤
      (actualUniquePairRecordKeys D).card := by
    rw [← Finset.card_union_of_disjoint hDisjoint]
    exact Finset.card_le_card hUnionSub
  have hCast : (U₃.card : ℚ) + (U₄.card : ℚ) ≤
      ((actualUniquePairRecordKeys D).card : ℚ) := by
    exact_mod_cast hCardBound
  linarith

/-- The full-mark budget for a finite rainbow family indexed directly
by a finite type. -/
theorem canonical_triangle_mark_sum_le_actual_fintype
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : FiniteCompletionCliqueData α)
    (T : ι → Edge α) (hTInjective : Function.Injective T)
    (hCard : ∀ t,
      (graphFacetCompletions D.K D.ground (T t)).card = 3)
    (hTCard : ∀ t, (T t).card = 3)
    (hTSub : ∀ t, T t ⊆ D.ground)
    (hRainbow : ∀ t, CompletionTriangleRainbow D
      (graphFacetCompletions D.K D.ground (T t))) :
    (∑ t : ι, ∑ x : CliqueColor,
      coloredSlotMark 3
        (canonicalTriangleActualSelectedIndices D (T t)
          (hCard t) x).card) ≤
      (∑ Q ∈ D.ground.powersetCard 2,
        ((actualColoredMarkedThreeSlots D Q).card : ℚ)) / 2 := by
  have h := canonical_triangle_mark_sum_le_actual D
    (Finset.univ : Finset ι) T hTInjective
    (by intro t _; exact hCard t)
    (by intro t _; exact hTCard t)
    (by intro t _; exact hTSub t)
    (by intro t _; exact hRainbow t)
  simpa using h

/-- The full-mark budget for a finite proper-K4 family. -/
theorem canonical_k4_mark_sum_le_actual_fintype
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : FiniteCompletionCliqueData α)
    (T : ι → Edge α) (hTInjective : Function.Injective T)
    (hCard : ∀ t,
      (graphFacetCompletions D.K D.ground (T t)).card = 4)
    (hTCard : ∀ t, (T t).card = 3)
    (hTSub : ∀ t, T t ⊆ D.ground)
    (hProper : ∀ t, CompletionProperlyEdgeColored D
      (graphFacetCompletions D.K D.ground (T t))) :
    (∑ t : ι, ∑ x : CliqueColor,
      coloredSlotMark 4
        (canonicalK4ActualSelectedIndices D (T t)
          (hCard t) x).card) ≤
      ∑ Q ∈ D.ground.powersetCard 2,
        ((actualColoredMarkedFourSlots D Q).card : ℚ) := by
  have h := canonical_k4_mark_sum_le_actual D
    (Finset.univ : Finset ι) T hTInjective
    (by intro t _; exact hCard t)
    (by intro t _; exact hTCard t)
    (by intro t _; exact hTSub t)
    (by intro t _; exact hProper t)
  simpa using h

/-- The actual selected graph potential and slot slacks pay all
rainbow-triangle and proper-K4 colored facets together. -/
theorem canonical_mixed_actual_colored_payment
    {ι₃ ι₄ : Type*} [Fintype ι₃] [DecidableEq ι₃]
    [Fintype ι₄] [DecidableEq ι₄]
    (D : FiniteCompletionCliqueData α)
    (T₃ : ι₃ → Edge α) (hT₃Injective : Function.Injective T₃)
    (hCard₃ : ∀ t,
      (graphFacetCompletions D.K D.ground (T₃ t)).card = 3)
    (hT₃Card : ∀ t, (T₃ t).card = 3)
    (hT₃Sub : ∀ t, T₃ t ⊆ D.ground)
    (hRainbow : ∀ t, CompletionTriangleRainbow D
      (graphFacetCompletions D.K D.ground (T₃ t)))
    (T₄ : ι₄ → Edge α) (hT₄Injective : Function.Injective T₄)
    (hCard₄ : ∀ t,
      (graphFacetCompletions D.K D.ground (T₄ t)).card = 4)
    (hT₄Card : ∀ t, (T₄ t).card = 3)
    (hT₄Sub : ∀ t, T₄ t ⊆ D.ground)
    (hProper : ∀ t, CompletionProperlyEdgeColored D
      (graphFacetCompletions D.K D.ground (T₄ t))) :
    (∑ _t : ι₃, coloredFacetRecords 3) +
      (∑ _t : ι₄, coloredFacetRecords 4) ≤
      actualSelectedPotentialTotal D +
      ((∑ t : ι₃, ∑ x : CliqueColor,
          slotSlack 3
            (canonicalTriangleActualSelectedIndices D (T₃ t)
              (hCard₃ t) x).card) +
        (∑ t : ι₄, ∑ x : CliqueColor,
          slotSlack 4
            (canonicalK4ActualSelectedIndices D (T₄ t)
              (hCard₄ t) x).card)) / 2 := by
  classical
  let d : Sum ι₃ ι₄ → ℕ := fun t =>
    match t with
    | .inl _ => 3
    | .inr _ => 4
  let k : Sum ι₃ ι₄ → CliqueColor → ℕ := fun t x =>
    match t with
    | .inl a =>
        (canonicalTriangleActualSelectedIndices D (T₃ a)
          (hCard₃ a) x).card
    | .inr b =>
        (canonicalK4ActualSelectedIndices D (T₄ b)
          (hCard₄ b) x).card
  have hd : ∀ t ∈ (Finset.univ : Finset (Sum ι₃ ι₄)),
      d t = 3 ∨ d t = 4 := by
    intro t _
    cases t <;> simp [d]
  have hk : ∀ t ∈ (Finset.univ : Finset (Sum ι₃ ι₄)),
      ∀ x : CliqueColor, k t x ≤ d t := by
    intro t _ x
    cases t with
    | inl a =>
        have h := Finset.card_le_card
          (Finset.subset_univ (canonicalTriangleActualSelectedIndices
            D (T₃ a) (hCard₃ a) x))
        simpa [d, k] using h
    | inr b =>
        have h := Finset.card_le_card
          (Finset.subset_univ (canonicalK4ActualSelectedIndices
            D (T₄ b) (hCard₄ b) x))
        simpa [d, k] using h
  have hRecords :
      (∑ t ∈ (Finset.univ : Finset (Sum ι₃ ι₄)),
        (coloredFacetRecords (d t) -
          ∑ x : CliqueColor, coloredSlotLoss (d t) (k t x))) ≤
        ((actualUniquePairRecordKeys D).card : ℚ) := by
    have h := canonical_mixed_actual_unique_records D T₃ hT₃Injective
        hCard₃ hT₃Card hT₃Sub hRainbow
        T₄ hT₄Injective hCard₄ hT₄Card hT₄Sub hProper
    simp only [Fintype.sum_sum_type,
      Finset.sum_sub_distrib] at h ⊢
    dsimp [d, k]
    linarith
  have hMarks :
      (∑ t ∈ (Finset.univ : Finset (Sum ι₃ ι₄)),
        ∑ x : CliqueColor, coloredSlotMark (d t) (k t x)) ≤
      (∑ Q ∈ D.ground.powersetCard 2,
        ((actualColoredMarkedThreeSlots D Q).card : ℚ)) / 2 +
      (∑ Q ∈ D.ground.powersetCard 2,
        ((actualColoredMarkedFourSlots D Q).card : ℚ)) := by
    have h3 := canonical_triangle_mark_sum_le_actual_fintype
      D T₃ hT₃Injective hCard₃ hT₃Card hT₃Sub hRainbow
    have h4 := canonical_k4_mark_sum_le_actual_fintype
      D T₄ hT₄Injective hCard₄ hT₄Card hT₄Sub hProper
    simpa [d, k, Fintype.sum_sum_type] using add_le_add h3 h4
  have hPayment := actual_colored_facet_family_payment D
    (Finset.univ : Finset (Sum ι₃ ι₄)) d k hd hk hRecords hMarks
  simpa [d, k, Fintype.sum_sum_type] using hPayment

end JSP523.Rank4
