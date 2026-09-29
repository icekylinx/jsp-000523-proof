import JSP523.Rank4.GraphActualFacetBracket
import JSP523.Rank4.GraphActualAlgebra
import JSP523.Rank4.GraphActualDeficit
import JSP523.Rank4.GraphColoredFacetClassification

/-!
# Reindexing actual selected links by triple-facet slots

The map `(Q,x) ↦ (insert x Q,x)` identifies a base pair with a vertex
outside it and a triple facet with a vertex in it. This is the exact
index change needed for the facet bracket in (III.B.9).
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

private theorem sum_if_mem_subset
    {β : Type*} [DecidableEq β] (A B : Finset β)
    (f : β → ℚ) (hBA : B ⊆ A) :
    (∑ x ∈ A, if x ∈ B then f x else 0) = ∑ x ∈ B, f x := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp [hBA]

/-- All base-pair and exterior-vertex slots on a finite ground set. -/
def actualBasePairSlots (U : Edge α) : Finset (Edge α × α) :=
  ((U.powersetCard 2).product U).filter fun p => p.2 ∉ p.1

/-- All triple-facet slots on a finite ground set. -/
def actualTripleFacetSlots (U : Edge α) : Finset (Edge α × α) :=
  ((U.powersetCard 3).product U).filter fun p => p.2 ∈ p.1

omit [Fintype α] in
/-- The two finite slot sets are exactly reindexed by insertion and
erasure of the distinguished vertex. -/
theorem actual_base_pair_slot_sum_eq_facet_slot_sum
    (U : Edge α) (f : Edge α → α → ℚ) :
    (∑ p ∈ actualBasePairSlots U, f p.1 p.2) =
      ∑ p ∈ actualTripleFacetSlots U, f (p.1.erase p.2) p.2 := by
  classical
  refine Finset.sum_bij'
    (fun p _ => (insert p.2 p.1, p.2))
    (fun p _ => (p.1.erase p.2, p.2)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rcases p with ⟨Q, x⟩
    obtain ⟨hProd, hxQ⟩ := Finset.mem_filter.mp hp
    obtain ⟨hQ, hxU⟩ := Finset.mem_product.mp hProd
    obtain ⟨hQU, hQcard⟩ := Finset.mem_powersetCard.mp hQ
    have hCard : (insert x Q).card = 3 := by
      rw [Finset.card_insert_of_notMem hxQ, hQcard]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr
      ⟨?_, hCard⟩, hxU⟩, Finset.mem_insert_self _ _⟩
    exact Finset.insert_subset hxU hQU
  · intro p hp
    rcases p with ⟨T, x⟩
    obtain ⟨hProd, hxT⟩ := Finset.mem_filter.mp hp
    obtain ⟨hT, hxU⟩ := Finset.mem_product.mp hProd
    obtain ⟨hTU, hTcard⟩ := Finset.mem_powersetCard.mp hT
    have hCard : (T.erase x).card = 2 := by
      rw [Finset.card_erase_of_mem hxT, hTcard]
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_powersetCard.mpr
        ⟨(Finset.erase_subset x T).trans hTU, hCard⟩, hxU⟩,
      Finset.notMem_erase x T⟩
  · intro p hp
    rcases p with ⟨Q, x⟩
    have hx : x ∉ Q := (Finset.mem_filter.mp hp).2
    simp [Finset.erase_insert hx]
  · intro p hp
    rcases p with ⟨T, x⟩
    have hx : x ∈ T := (Finset.mem_filter.mp hp).2
    simp [Finset.insert_erase hx]
  · intro p hp
    rcases p with ⟨Q, x⟩
    have hx : x ∉ Q := (Finset.mem_filter.mp hp).2
    simp [Finset.erase_insert hx]

omit [Fintype α] in
/-- Rewriting the triple-facet slot set as a sum over supported
triple facets and their three vertices. -/
theorem actual_facet_slot_sum_eq_facet_sum
    (U : Edge α) (f : Edge α → α → ℚ) :
    (∑ p ∈ actualTripleFacetSlots U, f p.1 p.2) =
      ∑ T ∈ U.powersetCard 3, ∑ x ∈ T, f T x := by
  classical
  have hProd :
      (∑ p ∈ actualTripleFacetSlots U, f p.1 p.2) =
      ∑ T ∈ U.powersetCard 3,
        ∑ x ∈ U, if x ∈ T then f T x else 0 := by
    change (∑ p ∈ ((U.powersetCard 3).product U).filter
        (fun p => p.2 ∈ p.1), f p.1 p.2) = _
    rw [Finset.sum_filter]
    exact Finset.sum_product (s := U.powersetCard 3) (t := U)
      (f := fun p : Edge α × α =>
        if p.2 ∈ p.1 then f p.1 p.2 else 0)
  rw [hProd]
  apply Finset.sum_congr rfl
  intro T hT
  have hTU := (Finset.mem_powersetCard.mp hT).1
  have hFilter : U.filter (· ∈ T) = T := by
    ext x
    simp [hTU]
  rw [← Finset.sum_filter, hFilter]

/-- Any function supported on the actual selected slot vertices can
be reindexed from base pairs to triple-facet vertices. -/
theorem actual_selected_supported_sum_eq_facet_sum
    (D : FiniteCompletionCliqueData α)
    (f : Edge α → α → ℚ)
    (hSupport : ∀ Q x,
      x ∉ actualEligiblePairSlotVertices D Q → f Q x = 0) :
    (∑ Q ∈ D.ground.powersetCard 2, ∑ x : α, f Q x) =
      ∑ T ∈ D.ground.powersetCard 3,
        ∑ x ∈ T, f (T.erase x) x := by
  classical
  have hPerBase (Q : Edge α) :
      (∑ x : α, f Q x) =
      ∑ x ∈ D.ground.filter (· ∉ Q), f Q x := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    apply hSupport
    intro hxSlot
    have hParts := Finset.mem_filter.mp hxSlot
    exact hx (Finset.mem_filter.mpr ⟨hParts.1, hParts.2.1⟩)
  simp_rw [hPerBase]
  have hBase :
      (∑ Q ∈ D.ground.powersetCard 2,
        ∑ x ∈ D.ground.filter (· ∉ Q), f Q x) =
      ∑ p ∈ actualBasePairSlots D.ground, f p.1 p.2 := by
    simp only [actualBasePairSlots, Finset.sum_filter]
    change (∑ Q ∈ D.ground.powersetCard 2,
      ∑ x ∈ D.ground,
        (fun p : Edge α × α =>
          if p.2 ∉ p.1 then f p.1 p.2 else 0) (Q, x)) =
      ∑ p ∈ (D.ground.powersetCard 2).product D.ground,
        if p.2 ∉ p.1 then f p.1 p.2 else 0
    exact (Finset.sum_product
      (s := D.ground.powersetCard 2) (t := D.ground)
      (f := fun p : Edge α × α =>
        if p.2 ∉ p.1 then f p.1 p.2 else 0)).symm
  rw [hBase, actual_base_pair_slot_sum_eq_facet_slot_sum]
  exact actual_facet_slot_sum_eq_facet_sum D.ground
    (fun T x => f (T.erase x) x)

/-- Vertices outside the actual selected slot set are isolated in the
selected pair link. -/
theorem actual_selected_degree_zero_of_not_slot
    (D : FiniteCompletionCliqueData α) (Q : Edge α) (x : α)
    (hx : x ∉ actualEligiblePairSlotVertices D Q) :
    (selectedCompletionPairGraph D
      (actualEligiblePairSlotVertices D Q) Q).degree x = 0 := by
  apply (SimpleGraph.degree_eq_zero _ _).2
  intro y hxy
  exact hx hxy.2.1

/-- Squared selected degrees can be summed over genuine exterior
base-pair slots, with every other vertex contributing zero. -/
theorem actual_selected_square_eq_base_slot_sum
    (D : FiniteCompletionCliqueData α) :
    actualSelectedDegreeSquareTotal D =
      ∑ p ∈ actualBasePairSlots D.ground,
        ((selectedCompletionPairGraph D
          (actualEligiblePairSlotVertices D p.1) p.1).degree p.2 : ℚ) ^ 2 := by
  classical
  unfold actualSelectedDegreeSquareTotal
  have hPerBase (Q : Edge α) :
      (∑ x : α,
        ((selectedCompletionPairGraph D
          (actualEligiblePairSlotVertices D Q) Q).degree x : ℚ) ^ 2) =
      ∑ x ∈ D.ground.filter (· ∉ Q),
        ((selectedCompletionPairGraph D
          (actualEligiblePairSlotVertices D Q) Q).degree x : ℚ) ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    have hxNotSlot : x ∉ actualEligiblePairSlotVertices D Q := by
      intro hxSlot
      have hParts := Finset.mem_filter.mp hxSlot
      have hxU : x ∈ D.ground := hParts.1
      have hxQ : x ∉ Q := hParts.2.1
      exact hx (Finset.mem_filter.mpr ⟨hxU, hxQ⟩)
    simp [actual_selected_degree_zero_of_not_slot D Q x hxNotSlot]
  simp_rw [hPerBase]
  simp only [actualBasePairSlots, Finset.sum_filter]
  change (∑ Q ∈ D.ground.powersetCard 2,
      ∑ x ∈ D.ground,
        (fun p : Edge α × α =>
          if p.2 ∉ p.1 then
            ((selectedCompletionPairGraph D
              (actualEligiblePairSlotVertices D p.1) p.1).degree p.2 : ℚ) ^ 2
          else 0) (Q, x)) =
    ∑ p ∈ (D.ground.powersetCard 2).product D.ground,
      if p.2 ∉ p.1 then
        ((selectedCompletionPairGraph D
          (actualEligiblePairSlotVertices D p.1) p.1).degree p.2 : ℚ) ^ 2
      else 0
  exact (Finset.sum_product
    (s := D.ground.powersetCard 2) (t := D.ground)
    (f := fun p : Edge α × α =>
      if p.2 ∉ p.1 then
        ((selectedCompletionPairGraph D
          (actualEligiblePairSlotVertices D p.1) p.1).degree p.2 : ℚ) ^ 2
      else 0)).symm

/-- Selected degree at the base pair opposite a vertex of a triple
facet. -/
noncomputable def actualFacetSlotDegree
    (D : FiniteCompletionCliqueData α) (T : Edge α) (x : α) : ℕ :=
  (selectedCompletionPairGraph D
    (actualEligiblePairSlotVertices D (T.erase x))
      (T.erase x)).degree x

/-- The actual selected degree-square total is a sum over triple-facet
slots. -/
theorem actual_selected_square_eq_facet_slot_sum
    (D : FiniteCompletionCliqueData α) :
    actualSelectedDegreeSquareTotal D =
      ∑ p ∈ actualTripleFacetSlots D.ground,
        (actualFacetSlotDegree D p.1 p.2 : ℚ) ^ 2 := by
  rw [actual_selected_square_eq_base_slot_sum]
  exact actual_base_pair_slot_sum_eq_facet_slot_sum D.ground
    (fun Q x =>
      ((selectedCompletionPairGraph D
        (actualEligiblePairSlotVertices D Q) Q).degree x : ℚ) ^ 2)

/-- The squared-degree total grouped by each actual triple facet. -/
theorem actual_selected_square_eq_facet_sum
    (D : FiniteCompletionCliqueData α) :
    actualSelectedDegreeSquareTotal D =
      ∑ T ∈ D.ground.powersetCard 3,
        ∑ x ∈ T, (actualFacetSlotDegree D T x : ℚ) ^ 2 := by
  rw [actual_selected_square_eq_facet_slot_sum]
  exact actual_facet_slot_sum_eq_facet_sum D.ground
    (fun T x => (actualFacetSlotDegree D T x : ℚ) ^ 2)

/-- Active selected vertices can be summed over genuine exterior
base-pair slots, with every other vertex contributing zero. -/
theorem actual_selected_active_eq_base_slot_sum
    (D : FiniteCompletionCliqueData α) :
    actualSelectedActiveVertexTotal D =
      ∑ p ∈ actualBasePairSlots D.ground,
        if 0 < (selectedCompletionPairGraph D
          (actualEligiblePairSlotVertices D p.1) p.1).degree p.2
        then (1 : ℚ) else 0 := by
  classical
  unfold actualSelectedActiveVertexTotal activeVertexCount
  have hPerBase (Q : Edge α) :
      (∑ x : α, if 0 < (selectedCompletionPairGraph D
          (actualEligiblePairSlotVertices D Q) Q).degree x
        then (1 : ℚ) else 0) =
      ∑ x ∈ D.ground.filter (· ∉ Q),
        if 0 < (selectedCompletionPairGraph D
          (actualEligiblePairSlotVertices D Q) Q).degree x
        then (1 : ℚ) else 0 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    have hxNotSlot : x ∉ actualEligiblePairSlotVertices D Q := by
      intro hxSlot
      have hParts := Finset.mem_filter.mp hxSlot
      exact hx (Finset.mem_filter.mpr ⟨hParts.1, hParts.2.1⟩)
    simp [actual_selected_degree_zero_of_not_slot D Q x hxNotSlot]
  simp_rw [hPerBase]
  simp only [actualBasePairSlots, Finset.sum_filter]
  exact (Finset.sum_product
    (s := D.ground.powersetCard 2) (t := D.ground)
    (f := fun p : Edge α × α =>
      if p.2 ∉ p.1 then
        if 0 < (selectedCompletionPairGraph D
          (actualEligiblePairSlotVertices D p.1) p.1).degree p.2
        then (1 : ℚ) else 0
      else 0)).symm

/-- The actual active-vertex total is a sum over triple-facet slots. -/
theorem actual_selected_active_eq_facet_slot_sum
    (D : FiniteCompletionCliqueData α) :
    actualSelectedActiveVertexTotal D =
      ∑ p ∈ actualTripleFacetSlots D.ground,
        if 0 < actualFacetSlotDegree D p.1 p.2
        then (1 : ℚ) else 0 := by
  rw [actual_selected_active_eq_base_slot_sum]
  exact actual_base_pair_slot_sum_eq_facet_slot_sum D.ground
    (fun Q x =>
      if 0 < (selectedCompletionPairGraph D
        (actualEligiblePairSlotVertices D Q) Q).degree x
      then (1 : ℚ) else 0)

/-- The positive selected-slot count grouped by actual triple facets. -/
theorem actual_selected_active_eq_facet_sum
    (D : FiniteCompletionCliqueData α) :
    actualSelectedActiveVertexTotal D =
      ∑ T ∈ D.ground.powersetCard 3,
        ∑ x ∈ T,
          if 0 < actualFacetSlotDegree D T x then (1 : ℚ) else 0 := by
  rw [actual_selected_active_eq_facet_slot_sum]
  exact actual_facet_slot_sum_eq_facet_sum D.ground
    (fun T x =>
      if 0 < actualFacetSlotDegree D T x then (1 : ℚ) else 0)

/-- Exactly the eligible vertices of a triple facet, viewed at their
opposite base pairs. -/
noncomputable def actualFacetEligibleVertices
    (D : FiniteCompletionCliqueData α) (T : Edge α) : Finset α :=
  T.filter fun x => x ∈ actualEligiblePairSlotVertices D (T.erase x)

omit [Fintype α] in
/-- A private facet offers no selected base-pair slot. -/
theorem actual_private_facet_eligible_vertices_empty
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hPrivate : (facetCompletions D.K D.ground T).card = 1) :
    actualFacetEligibleVertices D T = ∅ := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨hxT, hxSlot⟩ := Finset.mem_filter.mp hx
    have hEligible := (Finset.mem_filter.mp hxSlot).2.2
    have hC : graphFacetCompletions D.K D.ground
        (insert x (T.erase x)) = facetCompletions D.K D.ground T := by
      rw [Finset.insert_erase hxT]
      rfl
    have hCount := hEligible.1
    rw [hC, hPrivate] at hCount
    omega
  · simp

omit [Fintype α] in
/-- A triple with no completion has no eligible selected slot. -/
theorem actual_zero_facet_eligible_vertices_empty
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hZero : (facetCompletions D.K D.ground T).card = 0) :
    actualFacetEligibleVertices D T = ∅ := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨hxT, hxSlot⟩ := Finset.mem_filter.mp hx
    have hEligible := (Finset.mem_filter.mp hxSlot).2.2
    have hCount := hEligible.1
    rw [Finset.insert_erase hxT] at hCount
    change 2 ≤ (facetCompletions D.K D.ground T).card at hCount
    omega
  · simp

omit [Fintype α] in
/-- Every vertex of a colored facet is an eligible selected slot. -/
theorem actual_colored_facet_eligible_vertices_eq
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hTSub : T ⊆ D.ground)
    (hNonprivate : 2 ≤ (facetCompletions D.K D.ground T).card)
    (hColored : FacetHasDivergentLabels
      (graphFacetCompletions D.K D.ground T) D.label) :
    actualFacetEligibleVertices D T = T := by
  classical
  ext x
  constructor
  · intro hx
    exact (Finset.mem_filter.mp hx).1
  · intro hxT
    apply Finset.mem_filter.mpr
    refine ⟨hxT, Finset.mem_filter.mpr ⟨hTSub hxT,
      Finset.notMem_erase x T, ?_⟩⟩
    rw [Finset.insert_erase hxT]
    exact ⟨hNonprivate, Or.inl hColored⟩

omit [Fintype α] in
/-- A monochromatic nonprivate facet offers exactly the two slots
opposite vertices other than its center. -/
theorem actual_monochromatic_facet_eligible_vertices_eq
    (D : FiniteCompletionCliqueData α) (T : Edge α) (z : α)
    (hTSub : T ⊆ D.ground)
    (hzT : z ∈ T)
    (hNonprivate : 2 ≤ (facetCompletions D.K D.ground T).card)
    (hNotColored : ¬ FacetHasDivergentLabels
      (graphFacetCompletions D.K D.ground T) D.label)
    (hMono : ∀ a ∈ graphFacetCompletions D.K D.ground T,
      ∀ b ∈ graphFacetCompletions D.K D.ground T,
        a ≠ b → D.label a b = z) :
    actualFacetEligibleVertices D T = T.erase z := by
  classical
  have hPair : ∃ a ∈ graphFacetCompletions D.K D.ground T,
      ∃ b ∈ graphFacetCompletions D.K D.ground T, a ≠ b :=
    Finset.one_lt_card.mp hNonprivate
  ext x
  constructor
  · intro hx
    obtain ⟨hxT, hxSlot⟩ := Finset.mem_filter.mp hx
    have hEligible := (Finset.mem_filter.mp hxSlot).2.2
    rw [Finset.insert_erase hxT] at hEligible
    rcases hEligible.2 with hColored | ⟨w, hwQ, hAll⟩
    · exact False.elim (hNotColored hColored)
    · obtain ⟨a, ha, b, hb, hab⟩ := hPair
      have hwz : w = z := (hAll a ha b hb hab).symm.trans
        (hMono a ha b hb hab)
      have hxne : x ≠ z := by
        intro h
        subst x
        exact (Finset.notMem_erase z T) (hwz ▸ hwQ)
      exact Finset.mem_erase.mpr ⟨hxne, hxT⟩
  · intro hx
    obtain ⟨hxne, hxT⟩ := Finset.mem_erase.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨hxT, Finset.mem_filter.mpr ⟨hTSub hxT,
      Finset.notMem_erase x T, ?_⟩⟩
    rw [Finset.insert_erase hxT]
    exact ⟨hNonprivate, Or.inr ⟨z,
      Finset.mem_erase.mpr ⟨Ne.symm hxne, hzT⟩, hMono⟩⟩

omit [Fintype α] in
/-- The monochromatic center of any nonprivate facet without
divergent labels is an actual vertex of the facet. -/
theorem actual_nonprivate_nondivergent_facet_has_center
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hTcard : T.card = 3) (hTSub : T ⊆ D.ground)
    (hNonprivate : 2 ≤ (facetCompletions D.K D.ground T).card)
    (hNotColored : ¬ FacetHasDivergentLabels
      (graphFacetCompletions D.K D.ground T) D.label) :
    ∃ z ∈ T,
      ∀ a ∈ graphFacetCompletions D.K D.ground T,
      ∀ b ∈ graphFacetCompletions D.K D.ground T,
        a ≠ b → D.label a b = z := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hNonprivate
  let z := D.label a b
  have hzT := completion_pair_label_mem_facet
    D T hTcard hTSub a b ha hb hab
  refine ⟨z, hzT, ?_⟩
  exact facet_pair_labels_constant_of_no_divergence
    _ D.label D.label_symm hNotColored a b ha hb hab

/-- Nonprivate facets with a monochromatic completion clique. -/
noncomputable def actualMonochromaticFacets
    (D : FiniteCompletionCliqueData α) : Family α := by
  classical
  exact (D.ground.powersetCard 3).filter fun T =>
    2 ≤ (facetCompletions D.K D.ground T).card ∧
      ¬ FacetHasDivergentLabels
        (graphFacetCompletions D.K D.ground T) D.label

/-- Nonprivate facets with divergent completion labels. -/
noncomputable def actualColoredFacets
    (D : FiniteCompletionCliqueData α) : Family α := by
  classical
  exact (D.ground.powersetCard 3).filter fun T =>
    2 ≤ (facetCompletions D.K D.ground T).card ∧
      FacetHasDivergentLabels
        (graphFacetCompletions D.K D.ground T) D.label

omit [Fintype α] in
/-- Every actual colored facet is one of the manuscript's two
canonical types: a rainbow completion triangle or a properly colored
completion K4. -/
theorem actual_colored_facet_completion_classification
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hColored : T ∈ actualColoredFacets D) :
    ((graphFacetCompletions D.K D.ground T).card = 3 ∧
      CompletionTriangleRainbow D
        (graphFacetCompletions D.K D.ground T)) ∨
    ((graphFacetCompletions D.K D.ground T).card = 4 ∧
      CompletionProperlyEdgeColored D
        (graphFacetCompletions D.K D.ground T)) := by
  classical
  obtain ⟨hT, _, hDivergent⟩ := Finset.mem_filter.mp hColored
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hDiff⟩ := hDivergent
  let C := graphFacetCompletions D.K D.ground T
  have hSub : ({a, b, c} : Finset α) ⊆ C := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have hCard : ({a, b, c} : Finset α).card = 3 := by
    simp [hab, hac, hbc]
  have hLarge : 3 ≤ C.card := by
    have hLe := Finset.card_le_card hSub
    rw [hCard] at hLe
    exact hLe
  have hClass := divergent_completion_facet_classification D T
    (Finset.mem_powersetCard.mp hT).2
    (Finset.mem_powersetCard.mp hT).1
    ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hDiff⟩
    hLarge
  rcases hClass with hThree | hFour
  · exact Or.inl hThree
  · exact Or.inr ⟨hFour.1, hFour.2.1⟩

/-- Actual colored facets with three completions. -/
noncomputable def actualColoredThreeFacets
    (D : FiniteCompletionCliqueData α) : Family α :=
  (actualColoredFacets D).filter fun T =>
    (facetCompletions D.K D.ground T).card = 3

/-- Actual colored facets with four completions. -/
noncomputable def actualColoredFourFacets
    (D : FiniteCompletionCliqueData α) : Family α :=
  (actualColoredFacets D).filter fun T =>
    (facetCompletions D.K D.ground T).card = 4

omit [Fintype α] in
/-- The actual colored facet family is the disjoint union of the two
canonical completion sizes. -/
theorem actual_colored_facets_eq_three_union_four
    (D : FiniteCompletionCliqueData α) :
    actualColoredFacets D =
      actualColoredThreeFacets D ∪ actualColoredFourFacets D := by
  classical
  ext T
  constructor
  · intro hT
    rcases actual_colored_facet_completion_classification D T hT with
      hThree | hFour
    · exact Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_filter.mpr ⟨hT, hThree.1⟩
    · exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_filter.mpr ⟨hT, hFour.1⟩
  · intro hT
    rcases Finset.mem_union.mp hT with hThree | hFour
    · exact (Finset.mem_filter.mp hThree).1
    · exact (Finset.mem_filter.mp hFour).1

omit [Fintype α] in
/-- The two canonical colored facet sizes cannot overlap. -/
theorem actual_colored_three_four_disjoint
    (D : FiniteCompletionCliqueData α) :
    Disjoint (actualColoredThreeFacets D)
      (actualColoredFourFacets D) := by
  classical
  apply Finset.disjoint_left.mpr
  intro T hThree hFour
  have h3 := (Finset.mem_filter.mp hThree).2
  have h4 := (Finset.mem_filter.mp hFour).2
  omega

omit [Fintype α] in
/-- The completion-degree sum over actual colored facets is `3r₃+4r₄`. -/
theorem actual_colored_facet_degree_sum
    (D : FiniteCompletionCliqueData α) :
    (∑ T ∈ actualColoredFacets D,
      ((facetCompletions D.K D.ground T).card : ℚ)) =
      3 * ((actualColoredThreeFacets D).card : ℚ) +
      4 * ((actualColoredFourFacets D).card : ℚ) := by
  classical
  rw [actual_colored_facets_eq_three_union_four,
    Finset.sum_union (actual_colored_three_four_disjoint D)]
  have h3 :
      (∑ T ∈ actualColoredThreeFacets D,
        ((facetCompletions D.K D.ground T).card : ℚ)) =
      3 * ((actualColoredThreeFacets D).card : ℚ) := by
    calc
      _ = ∑ _T ∈ actualColoredThreeFacets D, (3 : ℚ) := by
        apply Finset.sum_congr rfl
        intro T hT
        simp [(Finset.mem_filter.mp hT).2]
      _ = _ := by simp [mul_comm]
  have h4 :
      (∑ T ∈ actualColoredFourFacets D,
        ((facetCompletions D.K D.ground T).card : ℚ)) =
      4 * ((actualColoredFourFacets D).card : ℚ) := by
    calc
      _ = ∑ _T ∈ actualColoredFourFacets D, (4 : ℚ) := by
        apply Finset.sum_congr rfl
        intro T hT
        simp [(Finset.mem_filter.mp hT).2]
      _ = _ := by simp [mul_comm]
  rw [h3, h4]

omit [Fintype α] in
/-- Completion degrees over actual facets split into private,
monochromatic, and colored contributions. -/
theorem actual_facet_completion_degree_sum_by_type
    (D : FiniteCompletionCliqueData α) :
    (∑ T ∈ D.ground.powersetCard 3,
      ((facetCompletions D.K D.ground T).card : ℚ)) =
      ((rankFourPrivateFacets D.K D.ground).card : ℚ) +
      (∑ T ∈ actualMonochromaticFacets D,
        ((facetCompletions D.K D.ground T).card : ℚ)) +
      (∑ T ∈ actualColoredFacets D,
        ((facetCompletions D.K D.ground T).card : ℚ)) := by
  classical
  let A := D.ground.powersetCard 3
  let P := rankFourPrivateFacets D.K D.ground
  let M := actualMonochromaticFacets D
  let C := actualColoredFacets D
  have hP : P ⊆ A := Finset.filter_subset _ _
  have hM : M ⊆ A := Finset.filter_subset _ _
  have hC : C ⊆ A := Finset.filter_subset _ _
  have hPoint (T : Edge α) (hT : T ∈ A) :
      ((facetCompletions D.K D.ground T).card : ℚ) =
      (if T ∈ P then (1 : ℚ) else 0) +
      (if T ∈ M then
        ((facetCompletions D.K D.ground T).card : ℚ) else 0) +
      (if T ∈ C then
        ((facetCompletions D.K D.ground T).card : ℚ) else 0) := by
    let d := (facetCompletions D.K D.ground T).card
    change T ∈ D.ground.powersetCard 3 at hT
    by_cases hZero : d = 0
    · simp [P, M, C, rankFourPrivateFacets,
        actualMonochromaticFacets, actualColoredFacets, hT, hZero, d]
    by_cases hOne : d = 1
    · simp [P, M, C, rankFourPrivateFacets,
        actualMonochromaticFacets, actualColoredFacets, hT, hOne, d]
    have hTwo : 2 ≤ d := by omega
    by_cases hColored : FacetHasDivergentLabels
        (graphFacetCompletions D.K D.ground T) D.label
    · simp [P, M, C, rankFourPrivateFacets,
        actualMonochromaticFacets, actualColoredFacets,
        hT, hOne, hTwo, hColored, d]
    · simp [P, M, C, rankFourPrivateFacets,
        actualMonochromaticFacets, actualColoredFacets,
        hT, hOne, hTwo, hColored, d]
  calc
    (∑ T ∈ A, ((facetCompletions D.K D.ground T).card : ℚ)) =
        ∑ T ∈ A,
          ((if T ∈ P then (1 : ℚ) else 0) +
          (if T ∈ M then
            ((facetCompletions D.K D.ground T).card : ℚ) else 0) +
          (if T ∈ C then
            ((facetCompletions D.K D.ground T).card : ℚ) else 0)) := by
            apply Finset.sum_congr rfl
            intro T hT
            exact hPoint T hT
    _ = (∑ T ∈ A, if T ∈ P then (1 : ℚ) else 0) +
        (∑ T ∈ A, if T ∈ M then
          ((facetCompletions D.K D.ground T).card : ℚ) else 0) +
        (∑ T ∈ A, if T ∈ C then
          ((facetCompletions D.K D.ground T).card : ℚ) else 0) := by
            simp only [Finset.sum_add_distrib]
    _ = (P.card : ℚ) +
        (∑ T ∈ M, ((facetCompletions D.K D.ground T).card : ℚ)) +
        ∑ T ∈ C, ((facetCompletions D.K D.ground T).card : ℚ) := by
          rw [sum_if_mem_subset A P (fun _ => 1) hP,
            sum_if_mem_subset A M _ hM,
            sum_if_mem_subset A C _ hC]
          simp

omit [Fintype α] in
/-- The colored facet's scalar bracket contributes `21/2` for a
rainbow triangle and `11` for a proper K4. -/
theorem actual_colored_facet_base_sum
    (D : FiniteCompletionCliqueData α) :
    (∑ T ∈ actualColoredFacets D,
      (-((facetCompletions D.K D.ground T).card : ℚ) ^ 2 +
        (15 / 2) * ((facetCompletions D.K D.ground T).card : ℚ) - 3)) =
      (21 / 2) * ((actualColoredThreeFacets D).card : ℚ) +
      11 * ((actualColoredFourFacets D).card : ℚ) := by
  classical
  rw [actual_colored_facets_eq_three_union_four,
    Finset.sum_union (actual_colored_three_four_disjoint D)]
  have h3 :
      (∑ T ∈ actualColoredThreeFacets D,
        (-((facetCompletions D.K D.ground T).card : ℚ) ^ 2 +
          (15 / 2) * ((facetCompletions D.K D.ground T).card : ℚ) - 3)) =
      (21 / 2) * ((actualColoredThreeFacets D).card : ℚ) := by
    calc
      _ = ∑ _T ∈ actualColoredThreeFacets D, (21 / 2 : ℚ) := by
        apply Finset.sum_congr rfl
        intro T hT
        simp [(Finset.mem_filter.mp hT).2]
        norm_num
      _ = _ := by simp [mul_comm]
  have h4 :
      (∑ T ∈ actualColoredFourFacets D,
        (-((facetCompletions D.K D.ground T).card : ℚ) ^ 2 +
          (15 / 2) * ((facetCompletions D.K D.ground T).card : ℚ) - 3)) =
      11 * ((actualColoredFourFacets D).card : ℚ) := by
    calc
      _ = ∑ _T ∈ actualColoredFourFacets D, (11 : ℚ) := by
        apply Finset.sum_congr rfl
        intro T hT
        simp [(Finset.mem_filter.mp hT).2]
        norm_num
      _ = _ := by simp [mul_comm]
  rw [h3, h4]

omit [Fintype α] in
/-- The global facet-completion degree count expressed in the
private/monochromatic/rainbow/proper-K4 classes. -/
theorem actual_facet_degree_count_by_colored_type
    (D : FiniteCompletionCliqueData α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground) :
    ((rankFourPrivateFacets D.K D.ground).card : ℚ) +
      (∑ T ∈ actualMonochromaticFacets D,
        ((facetCompletions D.K D.ground T).card : ℚ)) +
      3 * ((actualColoredThreeFacets D).card : ℚ) +
      4 * ((actualColoredFourFacets D).card : ℚ) =
      4 * (D.K.card : ℚ) := by
  have hDegree := rank_four_facet_completion_degree_sum
    D.K D.ground D.uniform_four hGround
  have hDegreeRat :
      (∑ T ∈ D.ground.powersetCard 3,
        ((facetCompletions D.K D.ground T).card : ℚ)) =
      4 * (D.K.card : ℚ) := by
    exact_mod_cast hDegree
  have hTypes := actual_facet_completion_degree_sum_by_type D
  have hColors := actual_colored_facet_degree_sum D
  linarith

/-- Sum of selected degrees at one facet's eligible slots. -/
noncomputable def actualFacetSelectedDegreeSum
    (D : FiniteCompletionCliqueData α) (T : Edge α) : ℚ :=
  ∑ x ∈ actualFacetEligibleVertices D T,
    (actualFacetSlotDegree D T x : ℚ)

/-- The selected-degree sum over actual eligible facet slots is
exactly twice the selected pair-link edge total. -/
theorem actual_facet_selected_degree_sum_eq_twice_edges
    (D : FiniteCompletionCliqueData α) :
    (∑ T ∈ D.ground.powersetCard 3,
      actualFacetSelectedDegreeSum D T) =
      2 * (actualSelectedEdgeTotal D : ℚ) := by
  classical
  have hReindex := actual_selected_supported_sum_eq_facet_sum D
    (fun Q x =>
      ((selectedCompletionPairGraph D
        (actualEligiblePairSlotVertices D Q) Q).degree x : ℚ))
    (by
      intro Q x hx
      simp [actual_selected_degree_zero_of_not_slot D Q x hx])
  have hFacet :
      (∑ T ∈ D.ground.powersetCard 3,
        ∑ x ∈ T, (actualFacetSlotDegree D T x : ℚ)) =
      ∑ T ∈ D.ground.powersetCard 3,
        actualFacetSelectedDegreeSum D T := by
    apply Finset.sum_congr rfl
    intro T _
    unfold actualFacetSelectedDegreeSum
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro x hxT hxNot
    have hxNotSlot :
        x ∉ actualEligiblePairSlotVertices D (T.erase x) := by
      intro hxSlot
      exact hxNot (Finset.mem_filter.mpr ⟨hxT, hxSlot⟩)
    simp [actualFacetSlotDegree,
      actual_selected_degree_zero_of_not_slot D (T.erase x) x hxNotSlot]
  have hHand :
      (∑ Q ∈ D.ground.powersetCard 2,
        ∑ x : α,
          ((selectedCompletionPairGraph D
            (actualEligiblePairSlotVertices D Q) Q).degree x : ℚ)) =
      2 * (actualSelectedEdgeTotal D : ℚ) := by
    unfold actualSelectedEdgeTotal
    rw [Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro Q _
    exact_mod_cast
      (selectedCompletionPairGraph D
        (actualEligiblePairSlotVertices D Q) Q).sum_degrees_eq_twice_card_edges
  change (∑ Q ∈ D.ground.powersetCard 2,
      ∑ x : α,
        ((selectedCompletionPairGraph D
          (actualEligiblePairSlotVertices D Q) Q).degree x : ℚ)) =
      ∑ T ∈ D.ground.powersetCard 3,
        ∑ x ∈ T, (actualFacetSlotDegree D T x : ℚ) at hReindex
  rw [hFacet] at hReindex
  exact hReindex.symm.trans hHand

/-- Sum of the manuscript's nonnegative slot slack at one facet. -/
noncomputable def actualFacetSlotSlackSum
    (D : FiniteCompletionCliqueData α) (T : Edge α) : ℚ :=
  ∑ x ∈ actualFacetEligibleVertices D T,
    slotSlack (facetCompletions D.K D.ground T).card
      (actualFacetSlotDegree D T x)

/-- The monochromatic contribution to the actual facet bracket. -/
noncomputable def actualMonochromaticBracketTerm
    (D : FiniteCompletionCliqueData α) (T : Edge α) : ℚ :=
  5 * ((facetCompletions D.K D.ground T).card : ℚ) - 2 -
    (5 / 2) * actualFacetSelectedDegreeSum D T +
    actualFacetSlotSlackSum D T

/-- The colored contribution to the actual facet bracket. -/
noncomputable def actualColoredBracketTerm
    (D : FiniteCompletionCliqueData α) (T : Edge α) : ℚ :=
  -((facetCompletions D.K D.ground T).card : ℚ) ^ 2 +
    (15 / 2) * ((facetCompletions D.K D.ground T).card : ℚ) - 3 -
    (5 / 2) * actualFacetSelectedDegreeSum D T +
    actualFacetSlotSlackSum D T

/-- The actual facet bracket after inactive slots have been removed. -/
noncomputable def actualFacetSlotBracket
    (D : FiniteCompletionCliqueData α) (T : Edge α) : ℚ :=
  2 * ((facetCompletions D.K D.ground T).card : ℚ) ^ 2 -
    ∑ x ∈ actualFacetEligibleVertices D T,
      ((actualFacetSlotDegree D T x : ℚ) ^ 2 +
        (if 0 < actualFacetSlotDegree D T x then (1 : ℚ) else 0))

/-- An ineligible facet vertex has selected degree zero at the
opposite base pair. -/
theorem actual_facet_slot_degree_zero_of_not_eligible
    (D : FiniteCompletionCliqueData α) (T : Edge α) (x : α)
    (hxT : x ∈ T)
    (hx : x ∉ actualFacetEligibleVertices D T) :
    actualFacetSlotDegree D T x = 0 := by
  have hxNotSlot :
      x ∉ actualEligiblePairSlotVertices D (T.erase x) := by
    intro hxSlot
    exact hx (Finset.mem_filter.mpr ⟨hxT, hxSlot⟩)
  exact actual_selected_degree_zero_of_not_slot
    D (T.erase x) x hxNotSlot

/-- The actual squared-degree identity is a sum of the exact local
facet brackets, with only eligible slots retained. -/
theorem actual_global_facet_slot_bracket_identity
    (D : FiniteCompletionCliqueData α) :
    2 * actualFacetCompletionDegreeSquareTotal D -
      actualSelectedDegreeSquareTotal D -
      actualSelectedActiveVertexTotal D =
    ∑ T ∈ D.ground.powersetCard 3,
      actualFacetSlotBracket D T := by
  classical
  rw [actual_selected_square_eq_facet_sum,
    actual_selected_active_eq_facet_sum]
  unfold actualFacetCompletionDegreeSquareTotal actualFacetSlotBracket
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro T _
  have hEligible : actualFacetEligibleVertices D T ⊆ T :=
    Finset.filter_subset _ _
  have hSum :
      (∑ x ∈ actualFacetEligibleVertices D T,
        ((actualFacetSlotDegree D T x : ℚ) ^ 2 +
          (if 0 < actualFacetSlotDegree D T x then (1 : ℚ) else 0))) =
      ∑ x ∈ T,
        ((actualFacetSlotDegree D T x : ℚ) ^ 2 +
          (if 0 < actualFacetSlotDegree D T x then (1 : ℚ) else 0)) := by
    apply Finset.sum_subset hEligible
    intro x hxT hxNot
    have hxZero := actual_facet_slot_degree_zero_of_not_eligible
      D T x hxT hxNot
    simp [hxZero]
  rw [hSum, Finset.sum_add_distrib]
  ring

/-- The signed facet-side contribution in (III.B.9), expressed using
actual completion degrees, actual eligible-slot counts, and actual
selected slot slack. -/
theorem actual_facet_slot_bracket_polynomial
    (D : FiniteCompletionCliqueData α) (T : Edge α) :
    actualFacetSlotBracket D T =
      (2 - (actualFacetEligibleVertices D T).card : ℚ) *
        ((facetCompletions D.K D.ground T).card : ℚ) ^ 2 +
      (5 / 2) * (actualFacetEligibleVertices D T).card *
        ((facetCompletions D.K D.ground T).card : ℚ) -
      (actualFacetEligibleVertices D T).card -
      (5 / 2) * (∑ x ∈ actualFacetEligibleVertices D T,
        (actualFacetSlotDegree D T x : ℚ)) +
      ∑ x ∈ actualFacetEligibleVertices D T,
        slotSlack (facetCompletions D.K D.ground T).card
          (actualFacetSlotDegree D T x) := by
  exact facet_slot_bracket_identity
    (actualFacetEligibleVertices D T)
    (facetCompletions D.K D.ground T).card
    (actualFacetSlotDegree D T)

/-- The actual private-facet bracket equals two. -/
theorem actual_private_facet_bracket_eq_two
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hPrivate : (facetCompletions D.K D.ground T).card = 1) :
    actualFacetSlotBracket D T = 2 := by
  rw [actualFacetSlotBracket,
    actual_private_facet_eligible_vertices_empty D T hPrivate]
  simp [hPrivate]

/-- The actual monochromatic-facet bracket has the manuscript's
`5d−2` coefficient and two selected slot degrees. -/
theorem actual_monochromatic_facet_bracket_identity
    (D : FiniteCompletionCliqueData α) (T : Edge α) (z : α)
    (hTcard : T.card = 3) (hTSub : T ⊆ D.ground)
    (hzT : z ∈ T)
    (hNonprivate : 2 ≤ (facetCompletions D.K D.ground T).card)
    (hNotColored : ¬ FacetHasDivergentLabels
      (graphFacetCompletions D.K D.ground T) D.label)
    (hMono : ∀ a ∈ graphFacetCompletions D.K D.ground T,
      ∀ b ∈ graphFacetCompletions D.K D.ground T,
        a ≠ b → D.label a b = z) :
    actualFacetSlotBracket D T =
      5 * ((facetCompletions D.K D.ground T).card : ℚ) - 2 -
        (5 / 2) * (∑ x ∈ actualFacetEligibleVertices D T,
          (actualFacetSlotDegree D T x : ℚ)) +
        ∑ x ∈ actualFacetEligibleVertices D T,
          slotSlack (facetCompletions D.K D.ground T).card
            (actualFacetSlotDegree D T x) := by
  have hSlots := actual_monochromatic_facet_eligible_vertices_eq
    D T z hTSub hzT hNonprivate hNotColored hMono
  have hCard : (actualFacetEligibleVertices D T).card = 2 := by
    rw [hSlots, Finset.card_erase_of_mem hzT, hTcard]
  exact monochromatic_facet_slot_bracket_identity
    (actualFacetEligibleVertices D T)
    (facetCompletions D.K D.ground T).card
    (actualFacetSlotDegree D T) hCard

/-- The actual colored-facet bracket has the manuscript's
`−d²+15d/2−3` coefficient and three selected slot degrees. -/
theorem actual_colored_facet_bracket_identity
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hTcard : T.card = 3) (hTSub : T ⊆ D.ground)
    (hNonprivate : 2 ≤ (facetCompletions D.K D.ground T).card)
    (hColored : FacetHasDivergentLabels
      (graphFacetCompletions D.K D.ground T) D.label) :
    actualFacetSlotBracket D T =
      -((facetCompletions D.K D.ground T).card : ℚ) ^ 2 +
        (15 / 2) * ((facetCompletions D.K D.ground T).card : ℚ) - 3 -
        (5 / 2) * (∑ x ∈ actualFacetEligibleVertices D T,
          (actualFacetSlotDegree D T x : ℚ)) +
        ∑ x ∈ actualFacetEligibleVertices D T,
          slotSlack (facetCompletions D.K D.ground T).card
            (actualFacetSlotDegree D T x) := by
  have hSlots := actual_colored_facet_eligible_vertices_eq
    D T hTSub hNonprivate hColored
  have hCard : (actualFacetEligibleVertices D T).card = 3 := by
    rw [hSlots, hTcard]
  exact colored_facet_slot_bracket_identity
    (actualFacetEligibleVertices D T)
    (facetCompletions D.K D.ground T).card
    (actualFacetSlotDegree D T) hCard

/-- Every actual triple facet contributes precisely its private,
monochromatic, or colored bracket term. Unsupported triples contribute
zero. This is the facet-side classification in (III.B.9). -/
theorem actual_facet_bracket_typewise
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hT : T ∈ D.ground.powersetCard 3) :
    actualFacetSlotBracket D T =
      (if T ∈ rankFourPrivateFacets D.K D.ground then (2 : ℚ) else 0) +
      (if T ∈ actualMonochromaticFacets D then
        actualMonochromaticBracketTerm D T else 0) +
      (if T ∈ actualColoredFacets D then
        actualColoredBracketTerm D T else 0) := by
  classical
  have hTcard := (Finset.mem_powersetCard.mp hT).2
  have hTSub := (Finset.mem_powersetCard.mp hT).1
  let d := (facetCompletions D.K D.ground T).card
  by_cases hZero : d = 0
  · have hSlots := actual_zero_facet_eligible_vertices_empty D T hZero
    have hBracket : actualFacetSlotBracket D T = 0 := by
      change (facetCompletions D.K D.ground T).card = 0 at hZero
      simp [actualFacetSlotBracket, hSlots, hZero]
    simp [hBracket, rankFourPrivateFacets,
      actualMonochromaticFacets, actualColoredFacets,
      hT, hZero, d]
  by_cases hPrivate : d = 1
  · have hBracket := actual_private_facet_bracket_eq_two D T hPrivate
    simp [hBracket, rankFourPrivateFacets,
      actualMonochromaticFacets, actualColoredFacets,
      hT, hPrivate, d]
  have hNonprivate : 2 ≤ d := by omega
  by_cases hColored : FacetHasDivergentLabels
      (graphFacetCompletions D.K D.ground T) D.label
  · have hBracket := actual_colored_facet_bracket_identity
      D T hTcard hTSub hNonprivate hColored
    simpa [rankFourPrivateFacets, actualMonochromaticFacets,
      actualColoredFacets, actualColoredBracketTerm,
      actualFacetSelectedDegreeSum, actualFacetSlotSlackSum,
      hT, hNonprivate, hColored, hPrivate, d] using hBracket
  · obtain ⟨z, hzT, hMono⟩ :=
      actual_nonprivate_nondivergent_facet_has_center
        D T hTcard hTSub hNonprivate hColored
    have hBracket := actual_monochromatic_facet_bracket_identity
      D T z hTcard hTSub hzT hNonprivate hColored hMono
    simpa [rankFourPrivateFacets, actualMonochromaticFacets,
      actualColoredFacets, actualMonochromaticBracketTerm,
      actualFacetSelectedDegreeSum, actualFacetSlotSlackSum,
      hT, hNonprivate, hColored, hPrivate, d] using hBracket

omit [Fintype α] in
/-- The nonprivate facet set is exactly the disjoint union of the
monochromatic and colored facet sets. -/
theorem actual_nonprivate_facets_eq_mono_union_colored
    (D : FiniteCompletionCliqueData α) :
    rankFourNonprivateFacets D.K D.ground =
      actualMonochromaticFacets D ∪ actualColoredFacets D := by
  classical
  ext T
  simp only [rankFourNonprivateFacets, actualMonochromaticFacets,
    actualColoredFacets, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hT, hNonprivate⟩
    by_cases hColored : FacetHasDivergentLabels
        (graphFacetCompletions D.K D.ground T) D.label
    · exact Or.inr ⟨hT, hNonprivate, hColored⟩
    · exact Or.inl ⟨hT, hNonprivate, hColored⟩
  · rintro (⟨hT, hNonprivate, _⟩ | ⟨hT, hNonprivate, _⟩)
    · exact ⟨hT, hNonprivate⟩
    · exact ⟨hT, hNonprivate⟩

omit [Fintype α] in
/-- The actual monochromatic and colored facet classes are disjoint. -/
theorem actual_mono_colored_facets_disjoint
    (D : FiniteCompletionCliqueData α) :
    Disjoint (actualMonochromaticFacets D)
      (actualColoredFacets D) := by
  classical
  apply Finset.disjoint_left.mpr
  intro T hM hC
  exact (Finset.mem_filter.mp hM).2.2
    (Finset.mem_filter.mp hC).2.2

omit [Fintype α] in
/-- The nonprivate facet count splits into monochromatic and the two
colored completion types. -/
theorem actual_nonprivate_facet_card_by_type
    (D : FiniteCompletionCliqueData α) :
    (rankFourNonprivateFacets D.K D.ground).card =
      (actualMonochromaticFacets D).card +
      (actualColoredThreeFacets D).card +
      (actualColoredFourFacets D).card := by
  rw [actual_nonprivate_facets_eq_mono_union_colored,
    Finset.card_union_of_disjoint (actual_mono_colored_facets_disjoint D),
    actual_colored_facets_eq_three_union_four,
    Finset.card_union_of_disjoint (actual_colored_three_four_disjoint D)]
  omega

omit [Fintype α] in
/-- The actual facet shadow count splits into private,
monochromatic, rainbow, and proper-K4 facets. -/
theorem actual_facet_shadow_card_by_type
    (D : FiniteCompletionCliqueData α) :
    (rankFourFacetShadow D.K D.ground).card =
      (rankFourPrivateFacets D.K D.ground).card +
      (actualMonochromaticFacets D).card +
      (actualColoredThreeFacets D).card +
      (actualColoredFourFacets D).card := by
  have hShadow := rank_four_facet_shadow_private_nonprivate
    D.K D.ground
  have hNonprivate := actual_nonprivate_facet_card_by_type D
  omega

/-- The sum of actual selected degrees is supported exactly on the
nonprivate facets, hence splits across the two facet classes. -/
theorem actual_facet_selected_degree_sum_by_type
    (D : FiniteCompletionCliqueData α) :
    (∑ T ∈ D.ground.powersetCard 3,
      actualFacetSelectedDegreeSum D T) =
      (∑ T ∈ actualMonochromaticFacets D,
        actualFacetSelectedDegreeSum D T) +
      ∑ T ∈ actualColoredFacets D,
        actualFacetSelectedDegreeSum D T := by
  classical
  let A := D.ground.powersetCard 3
  let B := rankFourNonprivateFacets D.K D.ground
  have hBA : B ⊆ A := Finset.filter_subset _ _
  have hRestricted :
      (∑ T ∈ A, actualFacetSelectedDegreeSum D T) =
        ∑ T ∈ B, actualFacetSelectedDegreeSum D T := by
    symm
    apply Finset.sum_subset hBA
    intro T hTA hNotB
    have hNotTwo : ¬ 2 ≤ (facetCompletions D.K D.ground T).card := by
      intro hTwo
      exact hNotB (Finset.mem_filter.mpr ⟨hTA, hTwo⟩)
    have hDegree : (facetCompletions D.K D.ground T).card = 0 ∨
        (facetCompletions D.K D.ground T).card = 1 := by omega
    rcases hDegree with hZero | hOne
    · simp [actualFacetSelectedDegreeSum,
        actual_zero_facet_eligible_vertices_empty D T hZero]
    · simp [actualFacetSelectedDegreeSum,
        actual_private_facet_eligible_vertices_empty D T hOne]
  rw [hRestricted]
  change (∑ T ∈ rankFourNonprivateFacets D.K D.ground,
    actualFacetSelectedDegreeSum D T) = _
  rw [actual_nonprivate_facets_eq_mono_union_colored,
    Finset.sum_union (actual_mono_colored_facets_disjoint D)]

/-- The full actual facet bracket splits into its private,
monochromatic, and colored facet contributions. This is the
classification step before the edge-occurrence identity in (III.B.9). -/
theorem actual_global_facet_bracket_by_type
    (D : FiniteCompletionCliqueData α) :
    (∑ T ∈ D.ground.powersetCard 3,
      actualFacetSlotBracket D T) =
      2 * ((rankFourPrivateFacets D.K D.ground).card : ℚ) +
      (∑ T ∈ actualMonochromaticFacets D,
        actualMonochromaticBracketTerm D T) +
      ∑ T ∈ actualColoredFacets D,
        actualColoredBracketTerm D T := by
  classical
  let A := D.ground.powersetCard 3
  let P := rankFourPrivateFacets D.K D.ground
  let M := actualMonochromaticFacets D
  let C := actualColoredFacets D
  have hP : P ⊆ A := Finset.filter_subset _ _
  have hM : M ⊆ A := Finset.filter_subset _ _
  have hC : C ⊆ A := Finset.filter_subset _ _
  calc
    (∑ T ∈ A, actualFacetSlotBracket D T) =
        ∑ T ∈ A, ((if T ∈ P then (2 : ℚ) else 0) +
          (if T ∈ M then actualMonochromaticBracketTerm D T else 0) +
          (if T ∈ C then actualColoredBracketTerm D T else 0)) := by
            apply Finset.sum_congr rfl
            intro T hT
            exact actual_facet_bracket_typewise D T hT
    _ = (∑ T ∈ A, if T ∈ P then (2 : ℚ) else 0) +
        (∑ T ∈ A,
          if T ∈ M then actualMonochromaticBracketTerm D T else 0) +
        (∑ T ∈ A,
          if T ∈ C then actualColoredBracketTerm D T else 0) := by
            simp only [Finset.sum_add_distrib]
    _ = 2 * (P.card : ℚ) +
        (∑ T ∈ M, actualMonochromaticBracketTerm D T) +
        ∑ T ∈ C, actualColoredBracketTerm D T := by
          rw [sum_if_mem_subset A P (fun _ => 2) hP,
            sum_if_mem_subset A M _ hM,
            sum_if_mem_subset A C _ hC]
          simp [mul_comm]

/-- The exact actual-link accounting equation immediately preceding
(III.B.9), now with every square and positive-slot count grouped by
its triple facet. -/
theorem actual_native_facet_slot_accounting
    (D : FiniteCompletionCliqueData α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground)
    (fallback : α)
    (hCenters : UniqueCommonRootCenters D.K D.ground) :
    2 * (nativeTailVertexTotal D.K D.ground
      (nonemptyCommonRoots D.K D.ground)
        (chosenCommonRootLabel D.K D.ground fallback hCenters) : ℚ) =
      (∑ T ∈ D.ground.powersetCard 3,
        actualFacetSlotBracket D T) -
      8 * (D.K.card : ℚ) +
      4 * (actualSelectedEdgeTotal D : ℚ) +
      2 * actualSelectedPotentialTotal D := by
  have hGraph := actual_graph_squared_accounting_identity
    D hGround fallback hCenters
  have hBracket := actual_global_facet_slot_bracket_identity D
  linarith

/-- The exact actual facet-side accounting after classifying private,
monochromatic, and colored facets and using the selected graph
handshake. The only graph edge term left is `-e_*`. -/
theorem actual_native_classified_facet_accounting
    (D : FiniteCompletionCliqueData α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground)
    (fallback : α)
    (hCenters : UniqueCommonRootCenters D.K D.ground) :
    2 * (nativeTailVertexTotal D.K D.ground
      (nonemptyCommonRoots D.K D.ground)
        (chosenCommonRootLabel D.K D.ground fallback hCenters) : ℚ) =
      2 * ((rankFourPrivateFacets D.K D.ground).card : ℚ) +
      5 * (∑ T ∈ actualMonochromaticFacets D,
        ((facetCompletions D.K D.ground T).card : ℚ)) -
      2 * ((actualMonochromaticFacets D).card : ℚ) +
      (∑ T ∈ actualColoredFacets D,
        (-((facetCompletions D.K D.ground T).card : ℚ) ^ 2 +
          (15 / 2) * ((facetCompletions D.K D.ground T).card : ℚ) - 3)) +
      (∑ T ∈ actualMonochromaticFacets D,
        actualFacetSlotSlackSum D T) +
      (∑ T ∈ actualColoredFacets D,
        actualFacetSlotSlackSum D T) -
      8 * (D.K.card : ℚ) -
      (actualSelectedEdgeTotal D : ℚ) +
      2 * actualSelectedPotentialTotal D := by
  have hNative := actual_native_facet_slot_accounting
    D hGround fallback hCenters
  rw [actual_global_facet_bracket_by_type] at hNative
  have hDegrees := actual_facet_selected_degree_sum_eq_twice_edges D
  rw [actual_facet_selected_degree_sum_by_type] at hDegrees
  unfold actualMonochromaticBracketTerm actualColoredBracketTerm at hNative
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hNative ⊢
  linarith

/-- The complete actual facet-side signed balance for `2S`, before
the retained-edge occurrence count is exchanged for `Z` and `R`.
All colored coefficients are actual rainbow/proper-K4 facet counts. -/
theorem actual_facet_side_signed_balance
    (D : FiniteCompletionCliqueData α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground)
    (fallback : α)
    (hCenters : UniqueCommonRootCenters D.K D.ground) :
    2 * (nativeTailVertexTotal D.K D.ground
      (nonemptyCommonRoots D.K D.ground)
        (chosenCommonRootLabel D.K D.ground fallback hCenters) : ℚ) +
      4 * ((rankFourFacetShadow D.K D.ground).card : ℚ) -
      10 * (D.K.card : ℚ) =
    2 * (D.K.card : ℚ) +
      ((rankFourPrivateFacets D.K D.ground).card : ℚ) +
      2 * ((actualMonochromaticFacets D).card : ℚ) -
      (1 / 2) * ((actualColoredThreeFacets D).card : ℚ) -
      5 * ((actualColoredFourFacets D).card : ℚ) +
      (∑ T ∈ actualMonochromaticFacets D,
        actualFacetSlotSlackSum D T) +
      (∑ T ∈ actualColoredFacets D,
        actualFacetSlotSlackSum D T) -
      (actualSelectedEdgeTotal D : ℚ) +
      2 * actualSelectedPotentialTotal D := by
  have hNative := actual_native_classified_facet_accounting
    D hGround fallback hCenters
  have hColorBase := actual_colored_facet_base_sum D
  have hDegree := actual_facet_degree_count_by_colored_type D hGround
  have hShadow := actual_facet_shadow_card_by_type D
  have hShadowRat :
      ((rankFourFacetShadow D.K D.ground).card : ℚ) =
      ((rankFourPrivateFacets D.K D.ground).card : ℚ) +
      ((actualMonochromaticFacets D).card : ℚ) +
      ((actualColoredThreeFacets D).card : ℚ) +
      ((actualColoredFourFacets D).card : ℚ) := by
    exact_mod_cast hShadow
  linarith

end JSP523.Rank4
