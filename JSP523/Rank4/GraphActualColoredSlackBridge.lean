import JSP523.Rank4.GraphActualFacetSlotReindex
import JSP523.Rank4.GraphActualMixedColoredRecords

/-!
# Canonical colored slots and actual facet slack

The three canonical color marks of a rainbow triangle or proper K4
enumerate the three vertices of its actual facet. Their canonical
selected-index counts are the actual selected pair-link degrees.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Every actual eligible slot selects at most all completions of its facet. -/
theorem actual_facet_slot_degree_le_completion_degree
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hT : T ∈ D.ground.powersetCard 3) (x : α)
    (hx : x ∈ actualFacetEligibleVertices D T) :
    actualFacetSlotDegree D T x ≤
      (facetCompletions D.K D.ground T).card := by
  classical
  obtain ⟨hxT, hxS⟩ := Finset.mem_filter.mp hx
  have hTC := (Finset.mem_powersetCard.mp hT).2
  have hTS := (Finset.mem_powersetCard.mp hT).1
  rw [actualFacetSlotDegree,
    selected_facet_degree_eq_selected_completions D T hTC hTS x hxT
      (actualEligiblePairSlotVertices D (T.erase x)) hxS]
  change ((facetCompletions D.K D.ground T).filter
    (· ∈ actualEligiblePairSlotVertices D (T.erase x))).card ≤
      (facetCompletions D.K D.ground T).card
  exact Finset.card_filter_le _ _

/-- Every nonprivate actual facet has nonnegative total slot slack. -/
theorem actual_facet_slot_slack_sum_nonneg
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hT : T ∈ D.ground.powersetCard 3)
    (hDegree : 2 ≤ (facetCompletions D.K D.ground T).card) :
    0 ≤ actualFacetSlotSlackSum D T := by
  unfold actualFacetSlotSlackSum
  apply Finset.sum_nonneg
  intro x hx
  exact slot_slack_nonneg_of_nonprivate _ _ hDegree
    (actual_facet_slot_degree_le_completion_degree D T hT x hx)

/-- The monochromatic part of the actual slot slack is nonnegative. -/
theorem actual_monochromatic_facet_slack_sum_nonneg
    (D : FiniteCompletionCliqueData α) :
    0 ≤ ∑ T ∈ actualMonochromaticFacets D,
      actualFacetSlotSlackSum D T := by
  classical
  apply Finset.sum_nonneg
  intro T hT
  have h := Finset.mem_filter.mp hT
  exact actual_facet_slot_slack_sum_nonneg D T h.1 h.2.1

omit [Fintype α] in
/-- An injective three-color marking into a three-vertex facet
reindexes any slot sum exactly. -/
theorem sum_clique_color_marks_eq_facet_sum
    (T : Edge α) (mark : CliqueColor → α)
    (hTcard : T.card = 3)
    (hMem : ∀ x, mark x ∈ T)
    (hInjective : Function.Injective mark)
    (f : α → ℚ) :
    (∑ x : CliqueColor, f (mark x)) = ∑ z ∈ T, f z := by
  classical
  let I : Finset CliqueColor := Finset.univ
  have hImageSub : I.image mark ⊆ T := by
    intro z hz
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
    exact hMem x
  have hImageCard : (I.image mark).card = T.card := by
    rw [Finset.card_image_of_injective _ hInjective, hTcard]
    simp [I, CliqueColor]
  have hImage : I.image mark = T :=
    Finset.eq_of_subset_of_card_le hImageSub hImageCard.ge
  rw [← hImage]
  exact (Finset.sum_image (s := I) (f := f)
    (by intro x _ y _ hxy; exact hInjective hxy)).symm

/-- The three canonical rainbow slots account for exactly the actual
selected slack of their colored facet. -/
theorem actual_triangle_facet_slack_eq_canonical
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hCard : (graphFacetCompletions D.K D.ground T).card = 3)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hRainbow : CompletionTriangleRainbow D
      (graphFacetCompletions D.K D.ground T)) :
    (∑ x : CliqueColor,
      slotSlack 3
        (canonicalTriangleActualSelectedIndices D T hCard x).card) =
      actualFacetSlotSlackSum D T := by
  classical
  have hFacetCard : (facetCompletions D.K D.ground T).card = 3 := hCard
  have hEligible := actual_colored_facet_eligible_vertices_eq D T
    hTsub (by rw [hFacetCard]; omega)
    (canonical_triangle_facet_divergent D T hCard hRainbow)
  have hMark := sum_clique_color_marks_eq_facet_sum T
    (canonicalTriangleMark D T hCard) hTcard
    (canonical_triangle_mark_mem_facet D T hCard hTcard hTsub)
    (canonical_triangle_mark_injective D T hCard hRainbow)
    (fun z => slotSlack 3 (actualFacetSlotDegree D T z))
  calc
    (∑ x : CliqueColor,
      slotSlack 3
        (canonicalTriangleActualSelectedIndices D T hCard x).card) =
        ∑ x : CliqueColor,
          slotSlack 3 (actualFacetSlotDegree D T
            (canonicalTriangleMark D T hCard x)) := by
              apply Finset.sum_congr rfl
              intro x _
              have hDegree := canonical_triangle_actual_selected_degree_eq
                D T hCard hTcard hTsub hRainbow x
              exact congrArg (slotSlack 3) hDegree.symm
    _ = ∑ z ∈ T, slotSlack 3 (actualFacetSlotDegree D T z) := hMark
    _ = actualFacetSlotSlackSum D T := by
          unfold actualFacetSlotSlackSum
          rw [hEligible]
          simp [hFacetCard]

/-- The three canonical proper-K4 color slots account for exactly the
actual selected slack of their colored facet. -/
theorem actual_k4_facet_slack_eq_canonical
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hCard : (graphFacetCompletions D.K D.ground T).card = 4)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hProper : CompletionProperlyEdgeColored D
      (graphFacetCompletions D.K D.ground T)) :
    (∑ x : CliqueColor,
      slotSlack 4
        (canonicalK4ActualSelectedIndices D T hCard x).card) =
      actualFacetSlotSlackSum D T := by
  classical
  have hFacetCard : (facetCompletions D.K D.ground T).card = 4 := hCard
  have hEligible := actual_colored_facet_eligible_vertices_eq D T
    hTsub (by rw [hFacetCard]; omega)
    (canonical_k4_facet_divergent D T hCard hProper)
  have hMarkInjective : Function.Injective
      (canonicalActualK4ColorMark D T hCard) := by
    intro x y hxy
    obtain ⟨_, hAdj⟩ := canonical_k4_labels_are_proper_pattern
      D T hCard hTcard hTsub hProper
    fin_cases x <;> fin_cases y <;>
      simp_all [canonicalActualK4ColorMark,
        completionK4Ends, completionK4IndexPair]
  have hMark := sum_clique_color_marks_eq_facet_sum T
    (canonicalActualK4ColorMark D T hCard) hTcard
    (canonical_actual_k4_color_mark_mem_facet
      D T hCard hTcard hTsub)
    hMarkInjective
    (fun z => slotSlack 4 (actualFacetSlotDegree D T z))
  calc
    (∑ x : CliqueColor,
      slotSlack 4
        (canonicalK4ActualSelectedIndices D T hCard x).card) =
        ∑ x : CliqueColor,
          slotSlack 4 (actualFacetSlotDegree D T
            (canonicalActualK4ColorMark D T hCard x)) := by
              apply Finset.sum_congr rfl
              intro x _
              have hDegree := canonical_k4_actual_selected_degree_eq
                D T hCard hTcard hTsub hProper x
              exact congrArg (slotSlack 4) hDegree.symm
    _ = ∑ z ∈ T, slotSlack 4 (actualFacetSlotDegree D T z) := hMark
    _ = actualFacetSlotSlackSum D T := by
          unfold actualFacetSlotSlackSum
          rw [hEligible]
          simp [hFacetCard]

/-- The mixed canonical colored payment, instantiated on exactly the
actual rainbow and proper-K4 facet families, uses the same slot slack
sum as the signed facet accounting. -/
theorem actual_mixed_colored_payment_on_facet_families
    (D : FiniteCompletionCliqueData α) :
    3 * ((actualColoredThreeFacets D).card : ℚ) +
      6 * ((actualColoredFourFacets D).card : ℚ) ≤
      actualSelectedPotentialTotal D +
      (∑ T ∈ actualColoredFacets D,
        actualFacetSlotSlackSum D T) / 2 := by
  classical
  let I₃ := {T : Edge α // T ∈ actualColoredThreeFacets D}
  let I₄ := {T : Edge α // T ∈ actualColoredFourFacets D}
  let T₃ : I₃ → Edge α := Subtype.val
  let T₄ : I₄ → Edge α := Subtype.val
  have hCard₃ (t : I₃) :
      (graphFacetCompletions D.K D.ground (T₃ t)).card = 3 :=
    (Finset.mem_filter.mp t.property).2
  have hCard₄ (t : I₄) :
      (graphFacetCompletions D.K D.ground (T₄ t)).card = 4 :=
    (Finset.mem_filter.mp t.property).2
  have hT₃ (t : I₃) :
      (T₃ t).card = 3 ∧ T₃ t ⊆ D.ground := by
    have h := (Finset.mem_filter.mp
      (Finset.mem_filter.mp t.property).1).1
    exact ⟨(Finset.mem_powersetCard.mp h).2,
      (Finset.mem_powersetCard.mp h).1⟩
  have hT₄ (t : I₄) :
      (T₄ t).card = 3 ∧ T₄ t ⊆ D.ground := by
    have h := (Finset.mem_filter.mp
      (Finset.mem_filter.mp t.property).1).1
    exact ⟨(Finset.mem_powersetCard.mp h).2,
      (Finset.mem_powersetCard.mp h).1⟩
  have hRainbow (t : I₃) : CompletionTriangleRainbow D
      (graphFacetCompletions D.K D.ground (T₃ t)) := by
    have hColored := (Finset.mem_filter.mp t.property).1
    rcases actual_colored_facet_completion_classification
      D (T₃ t) hColored with hThree | hFour
    · exact hThree.2
    · have h3 := hCard₃ t
      omega
  have hProper (t : I₄) : CompletionProperlyEdgeColored D
      (graphFacetCompletions D.K D.ground (T₄ t)) := by
    have hColored := (Finset.mem_filter.mp t.property).1
    rcases actual_colored_facet_completion_classification
      D (T₄ t) hColored with hThree | hFour
    · have h4 := hCard₄ t
      omega
    · exact hFour.2
  have hMixed := canonical_mixed_actual_colored_payment D
    T₃ (by intro t u h; exact Subtype.ext h)
    hCard₃ (fun t => (hT₃ t).1) (fun t => (hT₃ t).2) hRainbow
    T₄ (by intro t u h; exact Subtype.ext h)
    hCard₄ (fun t => (hT₄ t).1) (fun t => (hT₄ t).2) hProper
  have hRecord₃ :
      (∑ _t : I₃, coloredFacetRecords 3) =
      3 * ((actualColoredThreeFacets D).card : ℚ) := by
    have hSum : (∑ _t : I₃, coloredFacetRecords 3) =
        ∑ _T ∈ actualColoredThreeFacets D, coloredFacetRecords 3 := by
      exact (Finset.sum_subtype (actualColoredThreeFacets D)
        (by intro T; rfl) (fun _ => coloredFacetRecords 3)).symm
    simp [I₃, coloredFacetRecords, mul_comm] at hSum ⊢
  have hRecord₄ :
      (∑ _t : I₄, coloredFacetRecords 4) =
      6 * ((actualColoredFourFacets D).card : ℚ) := by
    have hSum : (∑ _t : I₄, coloredFacetRecords 4) =
        ∑ _T ∈ actualColoredFourFacets D, coloredFacetRecords 4 := by
      exact (Finset.sum_subtype (actualColoredFourFacets D)
        (by intro T; rfl) (fun _ => coloredFacetRecords 4)).symm
    simp [I₄, coloredFacetRecords, mul_comm] at hSum ⊢
  have hSlack₃ :
      (∑ t : I₃, ∑ x : CliqueColor,
        slotSlack 3
          (canonicalTriangleActualSelectedIndices D (T₃ t)
            (hCard₃ t) x).card) =
      ∑ T ∈ actualColoredThreeFacets D,
        actualFacetSlotSlackSum D T := by
    calc
      _ = ∑ t : I₃, actualFacetSlotSlackSum D (T₃ t) := by
        apply Finset.sum_congr rfl
        intro t _
        exact actual_triangle_facet_slack_eq_canonical
          D (T₃ t) (hCard₃ t) (hT₃ t).1 (hT₃ t).2 (hRainbow t)
      _ = _ := by
        exact (Finset.sum_subtype (actualColoredThreeFacets D)
          (by intro T; rfl) (actualFacetSlotSlackSum D)).symm
  have hSlack₄ :
      (∑ t : I₄, ∑ x : CliqueColor,
        slotSlack 4
          (canonicalK4ActualSelectedIndices D (T₄ t)
            (hCard₄ t) x).card) =
      ∑ T ∈ actualColoredFourFacets D,
        actualFacetSlotSlackSum D T := by
    calc
      _ = ∑ t : I₄, actualFacetSlotSlackSum D (T₄ t) := by
        apply Finset.sum_congr rfl
        intro t _
        exact actual_k4_facet_slack_eq_canonical
          D (T₄ t) (hCard₄ t) (hT₄ t).1 (hT₄ t).2 (hProper t)
      _ = _ := by
        exact (Finset.sum_subtype (actualColoredFourFacets D)
          (by intro T; rfl) (actualFacetSlotSlackSum D)).symm
  rw [hRecord₃, hRecord₄, hSlack₃, hSlack₄] at hMixed
  rw [actual_colored_facets_eq_three_union_four,
    Finset.sum_union (actual_colored_three_four_disjoint D)]
  exact hMixed

end JSP523.Rank4
