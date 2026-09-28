import JSP523.Rank4.GraphColoredActualRecords

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem canonical_triangle_family_actual_h_records
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : FiniteCompletionCliqueData α) (C : Finset ι)
    (T : ι → Edge α) (hTInjective : Function.Injective T)
    (hCard : ∀ t ∈ C,
      (graphFacetCompletions D.K D.ground (T t)).card = 3)
    (hTCard : ∀ t ∈ C, (T t).card = 3)
    (hTSub : ∀ t ∈ C, T t ⊆ D.ground)
    (hRainbow : ∀ t ∈ C, CompletionTriangleRainbow D
      (graphFacetCompletions D.K D.ground (T t)))
    (S : Finset α) (S₀ : ι → CliqueColor → Finset (Fin 3))
    (hMarkSelected : ∀ (t : ι) (ht : t ∈ C) (x : CliqueColor),
      canonicalTriangleMark D (T t) (hCard t ht) x ∈ S)
    (hVerticesSelected : ∀ (t : ι) (ht : t ∈ C) (x : CliqueColor) (i : Fin 3),
      i ∈ S₀ t x →
        canonicalTriangleCompletion D (T t) (hCard t ht) i ∈ S) :
    (∑ t ∈ C, (coloredFacetRecords 3 -
      ∑ x : CliqueColor, coloredSlotLoss 3 (S₀ t x).card)) ≤
        (selectedUndirectedCompletionRecordKeys D S).card := by
  classical
  let v (t : ι) (ht : t ∈ C) : Fin 3 → α :=
    canonicalTriangleCompletion D (T t) (hCard t ht)
  let mark (t : ι) (ht : t ∈ C) : CliqueColor → α :=
    canonicalTriangleMark D (T t) (hCard t ht)
  let R (t : ι) (x : CliqueColor) : Finset (Edge α × Edge α) :=
    if ht : t ∈ C then
      selectedActualTriangleUndirectedColorSlotRecords D (T t)
        (v t ht) (mark t ht) x (S₀ t x)
    else ∅
  let k (t : ι) (x : CliqueColor) : ℕ := (S₀ t x).card
  have hSlot : ∀ t ∈ C, ∀ x : CliqueColor,
      actualColoredSlotBase 3 ≤ (R t x).card + actualColoredSlotLoss 3 (k t x) := by
    intro t ht x
    have h := canonical_actual_triangle_undirected_records_card_lower_bound
      D (T t) (hCard t ht) (hTCard t ht) (hTSub t ht) (hRainbow t ht)
      x (S₀ t x) (k t x) rfl
    simpa [R, k, v, mark, ht, actualColoredSlotBase,
      actualColoredSlotLoss, rainbowRecordLoss] using h
  have hSub : ∀ t ∈ C, ∀ x, R t x ⊆ selectedUndirectedCompletionRecordKeys D S := by
    intro t ht x
    simp only [R, dite_eq_left ht]
    have hv : Function.Injective (v t ht) := by
      simpa [v] using canonical_triangle_completion_injective D (T t) (hCard t ht)
    exact selected_actual_triangle_undirected_records_subset_global
      D (T t) (v t ht) (mark t ht) x S (S₀ t x)
      (hMarkSelected t ht x) (hVerticesSelected t ht x)
      (hTCard t ht) (hTSub t ht)
      (fun i => canonical_triangle_completion_mem D (T t) (hCard t ht) i)
      hv
  have hDisjoint : ∀ t ∈ C, ∀ x, ∀ t' ∈ C, ∀ x',
      (t, x) ≠ (t', x') → Disjoint (R t x) (R t' x') := by
    intro t ht x t' ht' x' hne
    simp only [R, dite_eq_left ht, dite_eq_left ht']
    by_cases hsame : t = t'
    · subst t'
      have hxy : x ≠ x' := by
        intro h
        apply hne
        exact Prod.ext rfl h
      have hv : Function.Injective (v t ht) := by
        simpa [v] using canonical_triangle_completion_injective D (T t) (hCard t ht)
      have hmark : Function.Injective (mark t ht) := by
        simpa [mark] using canonical_triangle_mark_injective D (T t)
          (hCard t ht) (hRainbow t ht)
      exact selected_actual_triangle_undirected_color_slots_disjoint
        D (T t) (v t ht) (mark t ht) hxy (S₀ t x) (S₀ t x')
        hv hmark
    · have hTT' : T t ≠ T t' := by
        intro heq
        exact hsame (hTInjective heq)
      have hv : Function.Injective (v t ht) := by
        simpa [v] using canonical_triangle_completion_injective D (T t) (hCard t ht)
      have hw : Function.Injective (v t' ht') := by
        simpa [v] using canonical_triangle_completion_injective D (T t') (hCard t' ht')
      exact selected_triangle_undirected_records_disjoint_across_facets
        D (T t) (T t') (v t ht) (v t' ht') (mark t ht) (mark t' ht')
        x x' (S₀ t x) (S₀ t' x') hTT' (hTCard t ht) (hTSub t ht)
        (fun i => canonical_triangle_completion_mem D (T t) (hCard t ht) i)
        hv
        (hTCard t' ht') (hTSub t' ht')
        (fun i => canonical_triangle_completion_mem D (T t') (hCard t' ht') i)
        hw
  simpa [R, k, actualColoredRecordBase, actualColoredSlotLoss,
    coloredFacetRecords, coloredSlotLoss] using
    actual_colored_records_loss_le_ledger_rat C (fun _ => 3) k R
      (selectedUndirectedCompletionRecordKeys D S)
      (by intro t ht; exact Or.inl rfl) hSlot hSub hDisjoint

theorem canonical_triangle_family_colored_payment
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : FiniteCompletionCliqueData α) (C : Finset ι)
    (T : ι → Edge α) (hTInjective : Function.Injective T)
    (hCard : ∀ t ∈ C,
      (graphFacetCompletions D.K D.ground (T t)).card = 3)
    (hTCard : ∀ t ∈ C, (T t).card = 3)
    (hTSub : ∀ t ∈ C, T t ⊆ D.ground)
    (hRainbow : ∀ t ∈ C, CompletionTriangleRainbow D
      (graphFacetCompletions D.K D.ground (T t)))
    (S : Finset α) (S₀ : ι → CliqueColor → Finset (Fin 3))
    (hMarkSelected : ∀ (t : ι) (ht : t ∈ C) (x : CliqueColor),
      canonicalTriangleMark D (T t) (hCard t ht) x ∈ S)
    (hVerticesSelected : ∀ (t : ι) (ht : t ∈ C) (x : CliqueColor) (i : Fin 3),
      i ∈ S₀ t x →
        canonicalTriangleCompletion D (T t) (hCard t ht) i ∈ S) :
    (∑ _t ∈ C, coloredFacetRecords 3) ≤
      ((selectedUndirectedCompletionRecordKeys D S).card : ℚ) / 2 +
        (∑ t ∈ C, ∑ x : CliqueColor,
          slotSlack 3 (S₀ t x).card) / 2 +
        ∑ t ∈ C, ∑ x : CliqueColor,
          coloredSlotMark 3 (S₀ t x).card := by
  have hRecords := canonical_triangle_family_actual_h_records
    D C T hTInjective hCard hTCard hTSub hRainbow S S₀
    hMarkSelected hVerticesSelected
  have hk : ∀ t ∈ C, ∀ x : CliqueColor, (S₀ t x).card ≤ 3 := by
    intro t ht x
    calc
      (S₀ t x).card ≤ (Finset.univ : Finset (Fin 3)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = 3 := by simp
  simpa using colored_family_payment C (fun _ => 3)
    (fun t x => (S₀ t x).card)
    ((selectedUndirectedCompletionRecordKeys D S).card : ℚ)
    (by intro t ht; exact Or.inl rfl) hk (by simpa using hRecords)

end JSP523.Rank4
