import JSP523.Rank4.GraphActualEdgeOccurrence
import JSP523.Rank4.GraphActualFacetSlotReindex
import JSP523.Rank3.RootedWeightSum

/-! # Actual four-edge slack and opposite-facet classification -/

namespace JSP523.Rank4

attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Opposite rows whose completion facets are colored. -/
noncomputable def actualEdgeColoredRows
    (D : FiniteCompletionCliqueData α) (E : Edge α) : Finset α := by
  classical
  exact (actualEdgeNonprivateRows D E).filter fun a =>
    FacetHasDivergentLabels
      (graphFacetCompletions D.K D.ground (E.erase a)) D.label

/-- Opposite rows whose completion facets are monochromatic. -/
noncomputable def actualEdgeMonochromaticRows
    (D : FiniteCompletionCliqueData α) (E : Edge α) : Finset α := by
  classical
  exact (actualEdgeNonprivateRows D E).filter fun a =>
    ¬ FacetHasDivergentLabels
      (graphFacetCompletions D.K D.ground (E.erase a)) D.label

omit [Fintype α] in
/-- Every nonprivate opposite row is classified exactly once. -/
theorem actual_edge_rows_colored_mono_partition
    (D : FiniteCompletionCliqueData α) (E : Edge α) :
    actualEdgeColoredRows D E ∪ actualEdgeMonochromaticRows D E =
      actualEdgeNonprivateRows D E ∧
    Disjoint (actualEdgeColoredRows D E)
      (actualEdgeMonochromaticRows D E) := by
  classical
  constructor
  · ext a
    simp only [actualEdgeColoredRows, actualEdgeMonochromaticRows,
      Finset.mem_union, Finset.mem_filter]
    tauto
  · apply Finset.disjoint_left.mpr
    intro a ha hb
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    exact hb' ha'

omit [Fintype α] in
/-- The colored and monochromatic opposite rows count all nonprivate
rows, including the full four-row case. -/
theorem actual_edge_rows_colored_mono_card
    (D : FiniteCompletionCliqueData α) (E : Edge α) :
    (actualEdgeColoredRows D E).card +
      (actualEdgeMonochromaticRows D E).card =
      (actualEdgeNonprivateRows D E).card := by
  have h := actual_edge_rows_colored_mono_partition D E
  rw [← h.1, Finset.card_union_of_disjoint h.2]

omit [Fintype α] in
/-- If all four opposite rows are nonprivate, then every vertex of
the edge is an eligible row. -/
theorem actual_edge_nonprivate_rows_eq_edge_of_card_four
    (D : FiniteCompletionCliqueData α) (E : Edge α)
    (hE : E ∈ D.K)
    (hFull : (actualEdgeNonprivateRows D E).card = 4) :
    actualEdgeNonprivateRows D E = E := by
  have hSub : actualEdgeNonprivateRows D E ⊆ E :=
    Finset.filter_subset _ _
  have hCard := D.uniform_four hE
  exact Finset.eq_of_subset_of_card_le hSub (by omega)

omit [Fintype α] in
/-- A monochromatic nonprivate opposite facet supplies a unique
target vertex in that facet. -/
theorem actual_edge_mono_row_has_target
    (D : FiniteCompletionCliqueData α) (E : Edge α)
    (hE : E ∈ D.K) (hGround : E ⊆ D.ground)
    (a : α) (ha : a ∈ actualEdgeMonochromaticRows D E) :
    ∃! b : α, b ∈ E.erase a ∧
      actualEdgeMonochromaticArrow D E a b := by
  classical
  have haRow := (Finset.mem_filter.mp ha).1
  have haE := (Finset.mem_filter.mp haRow).1
  have hd := (Finset.mem_filter.mp haRow).2
  have hNoDiv := (Finset.mem_filter.mp ha).2
  have hCard : (E.erase a).card = 3 := by
    rw [Finset.card_erase_of_mem haE, D.uniform_four hE]
  have hSub : E.erase a ⊆ D.ground :=
    (Finset.erase_subset _ _).trans hGround
  obtain ⟨b, hb, hMono⟩ :=
    actual_nonprivate_nondivergent_facet_has_center
      D (E.erase a) hCard hSub hd hNoDiv
  refine ⟨b, ⟨hb, hMono⟩, ?_⟩
  intro c hc
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hd
  have hb' := hMono u hu v hv huv
  have hc' := hc.2 u hu v hv huv
  exact hc'.symm.trans hb'

omit [Fintype α] in
/-- A colored opposite facet contributes no monochromatic arrow. -/
theorem actual_edge_colored_row_no_arrow
    (D : FiniteCompletionCliqueData α) (E : Edge α)
    (a b : α) (ha : a ∈ actualEdgeColoredRows D E) :
    ¬ actualEdgeMonochromaticArrow D E a b := by
  classical
  intro hArrow
  obtain ⟨u, hu, v, hv, w, hw, huv, huw, hvw, hDiv⟩ :=
    (Finset.mem_filter.mp ha).2
  exact hDiv ((hArrow u hu v hv huv).trans
    (hArrow u hu w hw huw).symm)



omit [Fintype α] in
private theorem unordered_directed_sum (V : Finset α) (g : α → α → ℚ) :
    (∑ P ∈ V.powersetCard 2,
      if hP : P.card = 2 then
        g (pairRootRep P hP).1 (pairRootRep P hP).2 +
          g (pairRootRep P hP).2 (pairRootRep P hP).1 else 0) =
      ∑ a ∈ V, ∑ b ∈ V.erase a, g a b := by
  classical
  let F : Edge α → ℚ := fun P => if hP : P.card = 2 then
    g (pairRootRep P hP).1 (pairRootRep P hP).2 +
      g (pairRootRep P hP).2 (pairRootRep P hP).1 else 0
  have hPair (a b : α) (hab : a ≠ b) : F {a, b} = g a b + g b a := by
    have hcard : ({a, b} : Edge α).card = 2 := Finset.card_pair hab
    simp only [F, dite_eq_left hcard]
    have hspec := (pair_root_rep_spec ({a, b} : Edge α) hcard).2
    rcases pair_finset_eq_oriented_eq hab hspec.symm with h | h
    · exact congrArg₂ (fun x y : ℚ => x + y)
        (congrArg₂ g h.1.symm h.2.symm) (congrArg₂ g h.2.symm h.1.symm)
    · exact (congrArg₂ (fun x y : ℚ => x + y)
        (congrArg₂ g h.2.symm h.1.symm) (congrArg₂ g h.1.symm h.2.symm)).trans (add_comm _ _)
  have hTwice := JSP523.Rank3.ordered_pair_sum_eq_twice_unordered V F
  have hOrdered : (∑ a ∈ V, ∑ b ∈ V.erase a, F {a, b}) =
      (∑ a ∈ V, ∑ b ∈ V.erase a, g a b) +
        (∑ a ∈ V, ∑ b ∈ V.erase a, g b a) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    exact hPair a b (Finset.mem_erase.mp hb).1.symm
  have hSwap : (∑ a ∈ V, ∑ b ∈ V.erase a, g b a) =
      ∑ a ∈ V, ∑ b ∈ V.erase a, g a b := by
    apply Finset.sum_comm'
    intro a b
    simp only [Finset.mem_erase]
    tauto
  rw [hOrdered, hSwap] at hTwice
  change (∑ P ∈ V.powersetCard 2, F P) = _
  linarith

omit [Fintype α] in
/-- Reindex unordered row pairs by their directed source. -/
theorem actual_edge_arrow_count_eq_directed_sum
    (D : FiniteCompletionCliqueData α) (E : Edge α) :
    (actualEdgeMonochromaticArrowCount D E : ℚ) =
      ∑ a ∈ actualEdgeNonprivateRows D E,
        ∑ b ∈ (actualEdgeNonprivateRows D E).erase a,
          if actualEdgeMonochromaticArrow D E a b then (1 : ℚ) else 0 := by
  classical
  unfold actualEdgeMonochromaticArrowCount
  push_cast
  convert unordered_directed_sum (actualEdgeNonprivateRows D E)
    (fun a b => if actualEdgeMonochromaticArrow D E a b then (1 : ℚ) else 0) using 1
  apply Finset.sum_congr rfl
  intro P hP
  have hc := (Finset.mem_powersetCard.mp hP).2
  simp only [dite_eq_left hc, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  exact add_comm _ _



omit [Fintype α] in
/-- With four nonprivate rows, every monochromatic row contributes one arrow. -/
theorem actual_edge_excluded_slots_full
    (D : FiniteCompletionCliqueData α) (E : Edge α)
    (hE : E ∈ D.K) (hGround : E ⊆ D.ground)
    (hFull : (actualEdgeNonprivateRows D E).card = 4) :
    actualEdgeExcludedSlots D E = (actualEdgeMonochromaticRows D E).card := by
  classical
  rw [actual_edge_excluded_slots_eq_monochromatic_arrow_sum D E hE hGround]
  have hRows := actual_edge_nonprivate_rows_eq_edge_of_card_four D E hE hFull
  have hCount := actual_edge_arrow_count_eq_directed_sum D E
  have hInner (a : α) (ha : a ∈ actualEdgeNonprivateRows D E) :
      (∑ b ∈ (actualEdgeNonprivateRows D E).erase a,
        if actualEdgeMonochromaticArrow D E a b then (1 : ℚ) else 0) =
      if a ∈ actualEdgeMonochromaticRows D E then 1 else 0 := by
    by_cases hm : a ∈ actualEdgeMonochromaticRows D E
    · obtain ⟨b, hb, hUnique⟩ := actual_edge_mono_row_has_target D E hE hGround a hm
      rw [ite_eq_left hm, hRows]
      rw [Finset.sum_eq_single b]
      · simp [hb.2]
      · intro c hc hcb
        rw [ite_eq_right]
        intro hArrow
        exact hcb (hUnique c ⟨hc, hArrow⟩)
      · intro hnot
        exact False.elim (hnot hb.1)
    · have hc : a ∈ actualEdgeColoredRows D E := by
        have hp := (actual_edge_rows_colored_mono_partition D E).1
        rw [← hp] at ha
        exact (Finset.mem_union.mp ha).resolve_right hm
      rw [ite_eq_right hm]
      apply Finset.sum_eq_zero
      intro b hb
      exact ite_eq_right (actual_edge_colored_row_no_arrow D E a b hc)
  have hRhs : (∑ a ∈ actualEdgeNonprivateRows D E,
      ∑ b ∈ (actualEdgeNonprivateRows D E).erase a,
        if actualEdgeMonochromaticArrow D E a b then (1 : ℚ) else 0) =
      ((actualEdgeMonochromaticRows D E).card : ℚ) := by
    calc
      _ = ∑ a ∈ actualEdgeNonprivateRows D E,
          if a ∈ actualEdgeMonochromaticRows D E then (1 : ℚ) else 0 :=
        Finset.sum_congr rfl hInner
      _ = _ := by
        rw [← Finset.sum_filter]
        have hf : (actualEdgeNonprivateRows D E).filter
            (fun a => a ∈ actualEdgeMonochromaticRows D E) =
            actualEdgeMonochromaticRows D E := by
          ext a
          simp only [actualEdgeMonochromaticRows, Finset.mem_filter, and_self_left]
        rw [hf]
        simp
  exact_mod_cast hCount.trans hRhs

/-- Private opposite rows of an edge. -/
def actualEdgePrivateRows
    (D : FiniteCompletionCliqueData α) (E : Edge α) : Finset α :=
  E.filter fun a =>
    (graphFacetCompletions D.K D.ground (E.erase a)).card = 1

/-- The exact signed reserve in the edge occurrence balance. -/
noncomputable def actualEdgeSlack
    (D : FiniteCompletionCliqueData α) (E : Edge α) : ℤ :=
  2 + (actualEdgeColoredRows D E).card -
    (actualEdgeSelectedOccurrences D E).card +
    (actualEdgePrivateRows D E).card +
    (actualEdgeReciprocalExclusions D E).card



omit [Fintype α] in
/-- Opposite facets of an actual edge split into private and nonprivate rows. -/
theorem actual_edge_nonprivate_private_card
    (D : FiniteCompletionCliqueData α) (E : Edge α)
    (hE : E ∈ D.K) (hGround : E ⊆ D.ground) :
    (actualEdgeNonprivateRows D E).card + (actualEdgePrivateRows D E).card = 4 := by
  classical
  have hPos (a : α) (ha : a ∈ E) :
      0 < (graphFacetCompletions D.K D.ground (E.erase a)).card := by
    apply Finset.card_pos.mpr
    refine ⟨a, Finset.mem_filter.mpr ⟨hGround ha, ?_⟩⟩
    simpa [Finset.insert_erase ha] using hE
  have hUnion : actualEdgeNonprivateRows D E ∪ actualEdgePrivateRows D E = E := by
    ext a
    simp only [actualEdgeNonprivateRows, actualEdgePrivateRows,
      Finset.mem_union, Finset.mem_filter]
    constructor
    · tauto
    · intro ha
      have hp := hPos a ha
      by_cases hn : 2 ≤ (graphFacetCompletions D.K D.ground (E.erase a)).card
      · exact Or.inl ⟨ha, hn⟩
      · exact Or.inr ⟨ha, by omega⟩
  have hDis : Disjoint (actualEdgeNonprivateRows D E) (actualEdgePrivateRows D E) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    have h1 := (Finset.mem_filter.mp ha).2
    have h2 := (Finset.mem_filter.mp hb).2
    omega
  rw [← Finset.card_union_of_disjoint hDis, hUnion, D.uniform_four hE]

omit [Fintype α] in
/-- Every actual four-edge has a nonnegative reserve. -/
theorem actual_edge_slack_nonneg
    (D : FiniteCompletionCliqueData α) (E : Edge α)
    (hE : E ∈ D.K) (hGround : E ⊆ D.ground) :
    0 ≤ actualEdgeSlack D E := by
  have hp := actual_edge_nonprivate_private_card D E hE hGround
  have hk := actual_edge_selected_occurrence_identity D E
  have hEq := original_edge_slack_eq
    (actualEdgeNonprivateRows D E).card (actualEdgePrivateRows D E).card
    (actualEdgeColoredRows D E).card (actualEdgeExcludedSlots D E)
    (actualEdgeReciprocalExclusions D E).card
    (actualEdgeSelectedOccurrences D E).card hp hk
  change 0 ≤ (2 : ℤ) + _ - _ + _ + _
  rw [hEq]
  apply edge_slack_nonneg
  · omega
  · intro hFull
    rw [actual_edge_excluded_slots_full D E hE hGround hFull,
      actual_edge_rows_colored_mono_card D E, hFull]



omit [Fintype α] in
/-- An all-private edge has no nonprivate opposite rows. -/
theorem actual_edge_all_private_rows_empty
    (D : FiniteCompletionCliqueData α) (E : Edge α)
    (hE : E ∈ rankFourAllPrivateEdges D.K D.ground) :
    actualEdgeNonprivateRows D E = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have haE := (Finset.mem_filter.mp ha).1
  have hd := (Finset.mem_filter.mp ha).2
  have hParts := Finset.mem_filter.mp hE
  have hFacet : E.erase a ∈ E.powersetCard 3 := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.erase_subset _ _, ?_⟩
    rw [Finset.card_erase_of_mem haE, D.uniform_four hParts.1]
  have hSmall := hParts.2 (E.erase a) hFacet
  change (graphFacetCompletions D.K D.ground (E.erase a)).card < 2 at hSmall
  omega

omit [Fintype α] in
/-- An all-private edge supplies exactly six units of reserve. -/
theorem actual_edge_slack_all_private
    (D : FiniteCompletionCliqueData α) (E : Edge α)
    (hE : E ∈ rankFourAllPrivateEdges D.K D.ground)
    (hGround : E ⊆ D.ground) :
    actualEdgeSlack D E = 6 := by
  have hEmpty := actual_edge_all_private_rows_empty D E hE
  have hp := actual_edge_nonprivate_private_card D E
    (Finset.mem_filter.mp hE).1 hGround
  have hk := actual_edge_selected_occurrence_identity D E
  have hc : actualEdgeColoredRows D E = ∅ := by
    simp [actualEdgeColoredRows, hEmpty]
  have hl : actualEdgeExcludedSlots D E = 0 := by
    simp [actualEdgeExcludedSlots, hEmpty]
  have hEq := original_edge_slack_eq
    (actualEdgeNonprivateRows D E).card (actualEdgePrivateRows D E).card
    (actualEdgeColoredRows D E).card (actualEdgeExcludedSlots D E)
    (actualEdgeReciprocalExclusions D E).card
    (actualEdgeSelectedOccurrences D E).card hp hk
  change (2 : ℤ) + _ - _ + _ + _ = 6
  rw [hEq, hEmpty, hc, hl]
  exact edge_slack_all_private



omit [Fintype α] in
/-- Summed edge reserves pay six units for each all-private edge. -/
theorem actual_edge_slack_sum_ge_all_private
    (D : FiniteCompletionCliqueData α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground) :
    6 * ((rankFourAllPrivateEdges D.K D.ground).card : ℚ) ≤
      ∑ E ∈ D.K, (actualEdgeSlack D E : ℚ) := by
  classical
  have hSub : rankFourAllPrivateEdges D.K D.ground ⊆ D.K :=
    Finset.filter_subset _ _
  calc
    _ = ∑ E ∈ rankFourAllPrivateEdges D.K D.ground,
        (actualEdgeSlack D E : ℚ) := by
      have hEq : (∑ E ∈ rankFourAllPrivateEdges D.K D.ground,
          (actualEdgeSlack D E : ℚ)) =
          ∑ _E ∈ rankFourAllPrivateEdges D.K D.ground, (6 : ℚ) := by
        apply Finset.sum_congr rfl
        intro E hE
        rw [actual_edge_slack_all_private D E hE (hGround E (hSub hE))]
        norm_num
      rw [hEq]
      simp [mul_comm]
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hSub
      intro E hE _
      exact_mod_cast actual_edge_slack_nonneg D E hE (hGround E hE)

end JSP523.Rank4
