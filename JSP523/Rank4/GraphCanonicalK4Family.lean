import JSP523.Rank4.GraphCanonicalK4Actual

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Aggregate the canonical proper-K4 records of a finite divergent-facet
family into the global actual record ledger. -/
theorem canonical_K4_family_actual_hRecords
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : FiniteCompletionCliqueData α) (C : Finset ι)
    (T : ι → Edge α) (hTInjective : Function.Injective T)
    (hCard : ∀ t ∈ C,
      (graphFacetCompletions D.K D.ground (T t)).card = 4)
    (hTCard : ∀ t ∈ C, (T t).card = 3)
    (hTSub : ∀ t ∈ C, T t ⊆ D.ground)
    (hProper : ∀ t ∈ C, CompletionProperlyEdgeColored D
      (graphFacetCompletions D.K D.ground (T t)))
    (S : Finset α) (S₀ : ι → CliqueColor → Finset (Fin 4))
    (hMarkSelected : ∀ (t : ι) (ht : t ∈ C) (x : CliqueColor),
      canonicalActualK4ColorMark D (T t) (hCard t ht) x ∈ S)
    (hVerticesSelected : ∀ (t : ι) (ht : t ∈ C) (x : CliqueColor) (i : Fin 4),
      i ∈ S₀ t x →
        canonicalK4Completion D (T t) (hCard t ht) i ∈ S) :
    (∑ t ∈ C, (coloredFacetRecords 4 -
      ∑ x : CliqueColor, coloredSlotLoss 4 (S₀ t x).card)) ≤
        (selectedUndirectedCompletionRecordKeys D S).card := by
  classical
  let v (t : ι) (ht : t ∈ C) : Fin 4 → α :=
    canonicalK4Completion D (T t) (hCard t ht)
  let mark (t : ι) (ht : t ∈ C) : CliqueColor → α :=
    canonicalActualK4ColorMark D (T t) (hCard t ht)
  let R (t : ι) (x : CliqueColor) : Finset (Edge α × Edge α) :=
    if ht : t ∈ C then
      selectedActualK4UndirectedColorSlotRecords D (T t)
        (v t ht) (mark t ht) x (S₀ t x)
    else ∅
  let k (t : ι) (x : CliqueColor) : ℕ := (S₀ t x).card
  have hSlot : ∀ t ∈ C, ∀ x : CliqueColor,
      actualColoredSlotBase 4 ≤ (R t x).card + actualColoredSlotLoss 4 (k t x) := by
    intro t ht x
    have h := canonical_actual_K4_undirected_records_card_lower_bound
      D (T t) (hCard t ht) (hTCard t ht) (hTSub t ht) (hProper t ht)
      x (S₀ t x) (k t x) rfl
    simpa [R, k, v, mark, ht, actualColoredSlotBase,
      actualColoredSlotLoss, properFourRecordLoss] using h
  have hSub : ∀ t ∈ C, ∀ x, R t x ⊆ selectedUndirectedCompletionRecordKeys D S := by
    intro t ht x
    simp only [R, dite_eq_left ht]
    have hv : Function.Injective (v t ht) := by
      simpa [v] using canonicalK4Completion_injective D (T t) (hCard t ht)
    exact selected_actual_K4_undirected_records_subset_global
      D (T t) (v t ht) (mark t ht) x S (S₀ t x)
      (hMarkSelected t ht x) (hVerticesSelected t ht x)
      (hTCard t ht) (hTSub t ht)
      (fun i => canonicalK4Completion_mem D (T t) (hCard t ht) i)
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
        simpa [v] using canonicalK4Completion_injective D (T t) (hCard t ht)
      obtain ⟨_, hAdj⟩ := canonical_k4_labels_are_proper_pattern
        D (T t) (hCard t ht) (hTCard t ht) (hTSub t ht) (hProper t ht)
      have hmark : Function.Injective (mark t ht) := by
        intro i j hij
        fin_cases i <;> fin_cases j <;>
          simp_all [mark, canonicalActualK4ColorMark,
            v, completionK4Ends, completionK4IndexPair]
      exact selected_actual_K4_undirected_color_slots_disjoint
        D (T t) (v t ht) (mark t ht) hxy (S₀ t x) (S₀ t x')
        hv hmark
    · have hTT' : T t ≠ T t' := by
        intro heq
        exact hsame (hTInjective heq)
      have hv : Function.Injective (v t ht) := by
        simpa [v] using canonicalK4Completion_injective D (T t) (hCard t ht)
      have hw : Function.Injective (v t' ht') := by
        simpa [v] using canonicalK4Completion_injective D (T t') (hCard t' ht')
      exact selected_K4_undirected_records_disjoint_across_facets
        D (T t) (T t') (v t ht) (v t' ht') (mark t ht) (mark t' ht')
        x x' (S₀ t x) (S₀ t' x') hTT' (hTCard t ht) (hTSub t ht)
        (fun i => canonicalK4Completion_mem D (T t) (hCard t ht) i) hv
        (hTCard t' ht') (hTSub t' ht')
        (fun i => canonicalK4Completion_mem D (T t') (hCard t' ht') i) hw
  simpa [R, k, actualColoredRecordBase, actualColoredSlotLoss,
    coloredFacetRecords, coloredSlotLoss] using
    actual_colored_records_loss_le_ledger_rat C (fun _ => 4) k R
      (selectedUndirectedCompletionRecordKeys D S)
      (by intro t ht; exact Or.inr rfl) hSlot hSub hDisjoint

/-- The family record ledger is precisely the record premise needed by the
colored-slot payment inequality for proper completion K4 facets. -/
theorem canonical_K4_family_colored_payment
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : FiniteCompletionCliqueData α) (C : Finset ι)
    (T : ι → Edge α) (hTInjective : Function.Injective T)
    (hCard : ∀ t ∈ C,
      (graphFacetCompletions D.K D.ground (T t)).card = 4)
    (hTCard : ∀ t ∈ C, (T t).card = 3)
    (hTSub : ∀ t ∈ C, T t ⊆ D.ground)
    (hProper : ∀ t ∈ C, CompletionProperlyEdgeColored D
      (graphFacetCompletions D.K D.ground (T t)))
    (S : Finset α) (S₀ : ι → CliqueColor → Finset (Fin 4))
    (hMarkSelected : ∀ (t : ι) (ht : t ∈ C) (x : CliqueColor),
      canonicalActualK4ColorMark D (T t) (hCard t ht) x ∈ S)
    (hVerticesSelected : ∀ (t : ι) (ht : t ∈ C) (x : CliqueColor) (i : Fin 4),
      i ∈ S₀ t x →
        canonicalK4Completion D (T t) (hCard t ht) i ∈ S) :
    (∑ _t ∈ C, coloredFacetRecords 4) ≤
      ((selectedUndirectedCompletionRecordKeys D S).card : ℚ) / 2 +
        (∑ t ∈ C, ∑ x : CliqueColor,
          slotSlack 4 (S₀ t x).card) / 2 +
        ∑ t ∈ C, ∑ x : CliqueColor,
          coloredSlotMark 4 (S₀ t x).card := by
  have hRecords := canonical_K4_family_actual_hRecords
    D C T hTInjective hCard hTCard hTSub hProper S S₀
    hMarkSelected hVerticesSelected
  have hk : ∀ t ∈ C, ∀ x : CliqueColor, (S₀ t x).card ≤ 4 := by
    intro t ht x
    calc
      (S₀ t x).card ≤ (Finset.univ : Finset (Fin 4)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = 4 := by simp
  simpa using colored_family_payment C (fun _ => 4)
    (fun t x => (S₀ t x).card)
    ((selectedUndirectedCompletionRecordKeys D S).card : ℚ)
    (by intro t ht; exact Or.inr rfl) hk (by simpa using hRecords)

end JSP523.Rank4
