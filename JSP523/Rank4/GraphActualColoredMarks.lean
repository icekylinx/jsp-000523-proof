import JSP523.Rank4.GraphActualColoredFamilyPayment

/-!
# Selected facet degrees and marked colored slots

The degree of a facet vertex in its actual selected pair link is the
number of surviving completion vertices of that facet.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Neighbors of a selected facet vertex are exactly its selected
completion vertices. -/
theorem selected_facet_neighbor_finset_eq
    (D : FiniteCompletionCliqueData α)
    (T : Edge α) (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (z : α) (hzT : z ∈ T) (S : Finset α) (hzS : z ∈ S)
    [DecidableRel (selectedCompletionPairGraph D S (T.erase z)).Adj] :
    (selectedCompletionPairGraph D S (T.erase z)).neighborFinset z =
      (graphFacetCompletions D.K D.ground T).filter (· ∈ S) := by
  classical
  let Q := T.erase z
  have hTdecomp : insert z Q = T := Finset.insert_erase hzT
  have hzQ : z ∉ Q := Finset.notMem_erase z T
  ext a
  rw [SimpleGraph.mem_neighborFinset]
  simp only [Finset.mem_filter]
  constructor
  · intro h
    have hAdj : (completionPairLinkGraph D Q).Adj z a := h.1
    change z ∉ Q ∧ a ∉ Q ∧ z ∈ D.ground ∧ a ∈ D.ground ∧
      z ≠ a ∧ insert z (insert a Q) ∈ D.K at hAdj
    refine ⟨Finset.mem_filter.mpr ⟨hAdj.2.2.2.1, ?_⟩, h.2.2⟩
    have hEdge := hAdj.2.2.2.2.2
    simpa [graphFacetCompletions, ← hTdecomp, Finset.insert_comm] using hEdge
  · intro h
    have haC := (Finset.mem_filter.mp h.1)
    have haT : a ∉ T := by
      intro ha
      have hFour := D.uniform_four haC.2
      change (insert a T).card = 4 at hFour
      rw [Finset.insert_eq_of_mem ha, hTcard] at hFour
      omega
    have haQ : a ∉ Q := fun ha => haT (Finset.mem_of_mem_erase ha)
    have hza : z ≠ a := by
      intro hEq
      exact haT (hEq ▸ hzT)
    have hEdge : insert z (insert a Q) ∈ D.K := by
      simpa [← hTdecomp, Finset.insert_comm] using haC.2
    change (completionPairLinkGraph D Q).Adj z a ∧ z ∈ S ∧ a ∈ S
    exact ⟨⟨hzQ, haQ, hTsub hzT, haC.1, hza, hEdge⟩, hzS, h.2⟩

/-- The selected degree of a colored facet vertex is its surviving
completion count. -/
theorem selected_facet_degree_eq_selected_completions
    (D : FiniteCompletionCliqueData α)
    (T : Edge α) (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (z : α) (hzT : z ∈ T) (S : Finset α) (hzS : z ∈ S)
    [DecidableRel (selectedCompletionPairGraph D S (T.erase z)).Adj] :
    (selectedCompletionPairGraph D S (T.erase z)).degree z =
      ((graphFacetCompletions D.K D.ground T).filter (· ∈ S)).card := by
  change ((selectedCompletionPairGraph D S (T.erase z)).neighborFinset z).card =
    ((graphFacetCompletions D.K D.ground T).filter (· ∈ S)).card
  rw [selected_facet_neighbor_finset_eq D T hTcard hTsub z hzT S hzS]

omit [Fintype α] in
/-- A facet and one of its three color marks are recovered from the
opposite base pair and marked vertex. This is the finite injectivity
behind the full-degree mark budget. -/
theorem facet_color_base_mark_eq_implies_same
    {ι : Type*} (T : ι → Edge α) (hTInjective : Function.Injective T)
    (mark : ι → CliqueColor → α)
    (t u : ι) (x y : CliqueColor)
    (hMarkInjective : Function.Injective (mark t))
    (hxt : mark t x ∈ T t) (hyu : mark u y ∈ T u)
    (hKey : ((T t).erase (mark t x), mark t x) =
      ((T u).erase (mark u y), mark u y)) :
    t = u ∧ x = y := by
  have hQ : (T t).erase (mark t x) =
      (T u).erase (mark u y) := congrArg Prod.fst hKey
  have hz : mark t x = mark u y := congrArg Prod.snd hKey
  have hFacet : T t = T u := by
    calc
      T t = insert (mark t x) ((T t).erase (mark t x)) :=
        (Finset.insert_erase hxt).symm
      _ = insert (mark u y) ((T u).erase (mark u y)) :=
        congrArg₂ (fun z s => insert z s) hz hQ
      _ = T u := Finset.insert_erase hyu
  have htu := hTInjective hFacet
  subst u
  exact ⟨rfl, hMarkInjective hz⟩

omit [Fintype α] in
/-- Injective full-slot marks are bounded by the actual marked vertices,
summed over their base pairs. -/
theorem finite_full_slot_mark_count_le
    {ι : Type*} [DecidableEq ι]
    (D : FiniteCompletionCliqueData α)
    (C : Finset ι) (F : Finset (ι × CliqueColor))
    (T : ι → Edge α) (hTInjective : Function.Injective T)
    (mark : ι → CliqueColor → α)
    (M : Edge α → Finset α)
    (hOwner : ∀ p ∈ F, p.1 ∈ C)
    (hMarkMem : ∀ t ∈ C, ∀ x : CliqueColor, mark t x ∈ T t)
    (hMarkInjective : ∀ t ∈ C, Function.Injective (mark t))
    (hQ : ∀ p ∈ F,
      (T p.1).erase (mark p.1 p.2) ∈ D.ground.powersetCard 2)
    (hMarked : ∀ p ∈ F,
      mark p.1 p.2 ∈ M ((T p.1).erase (mark p.1 p.2))) :
    F.card ≤ ∑ Q ∈ D.ground.powersetCard 2, (M Q).card := by
  classical
  let key : ι × CliqueColor → Edge α × α := fun p =>
    ((T p.1).erase (mark p.1 p.2), mark p.1 p.2)
  let U : Finset (Edge α × α) :=
    (D.ground.powersetCard 2).biUnion fun Q =>
      (M Q).image fun z => (Q, z)
  have hInj : Set.InjOn key F := by
    intro p hp q hq heq
    obtain ⟨t, x⟩ := p
    obtain ⟨u, y⟩ := q
    have hpOwner : t ∈ C := hOwner (t, x) hp
    have hqOwner : u ∈ C := hOwner (u, y) hq
    obtain ⟨htu, hxy⟩ := facet_color_base_mark_eq_implies_same
      T hTInjective mark t u x y
      (hMarkInjective t hpOwner)
      (hMarkMem t hpOwner x) (hMarkMem u hqOwner y) heq
    exact Prod.ext htu hxy
  have hImageSub : F.image key ⊆ U := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    apply Finset.mem_biUnion.mpr
    refine ⟨(T q.1).erase (mark q.1 q.2), hQ q hq, ?_⟩
    exact Finset.mem_image.mpr ⟨mark q.1 q.2, hMarked q hq, rfl⟩
  have hUcard : U.card ≤
      ∑ Q ∈ D.ground.powersetCard 2, (M Q).card := by
    calc
      U.card ≤ ∑ Q ∈ D.ground.powersetCard 2,
          ((M Q).image fun z => (Q, z)).card := Finset.card_biUnion_le
      _ ≤ ∑ Q ∈ D.ground.powersetCard 2, (M Q).card :=
        Finset.sum_le_sum (fun Q _ => Finset.card_image_le)
  calc
    F.card = (F.image key).card := (Finset.card_image_iff.mpr hInj).symm
    _ ≤ U.card := Finset.card_le_card hImageSub
    _ ≤ ∑ Q ∈ D.ground.powersetCard 2, (M Q).card := hUcard

omit [Fintype α] in
/-- Filtering a finite set through a bijective indexing map preserves
its cardinality. -/
theorem indexed_filter_card_eq
    {β : Type*} [Fintype β] [DecidableEq β]
    (C S : Finset α) (v : β → α)
    (hv : Function.Injective v)
    (hImage : (Finset.univ : Finset β).image v = C) :
    ((Finset.univ : Finset β).filter fun i => v i ∈ S).card =
      (C.filter (· ∈ S)).card := by
  classical
  have hFilterImage :
      ((Finset.univ : Finset β).filter fun i => v i ∈ S).image v =
        C.filter (· ∈ S) := by
    ext a
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨hImage ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hi⟩
    · rintro ⟨haC, haS⟩
      have haImage : a ∈ (Finset.univ : Finset β).image v := hImage.symm ▸ haC
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp haImage
      exact ⟨i, haS, rfl⟩
  calc
    ((Finset.univ : Finset β).filter fun i => v i ∈ S).card =
        (((Finset.univ : Finset β).filter fun i => v i ∈ S).image v).card :=
      (Finset.card_image_of_injective _ hv).symm
    _ = (C.filter (· ∈ S)).card := by rw [hFilterImage]

/-- The canonical completion enumeration exhausts the facet. -/
theorem canonical_triangle_completion_image_univ
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hCard : (graphFacetCompletions D.K D.ground T).card = 3) :
    (Finset.univ : Finset (Fin 3)).image
      (canonicalTriangleCompletion D T hCard) =
        graphFacetCompletions D.K D.ground T := by
  apply Finset.eq_of_subset_of_card_le
  · intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact canonical_triangle_completion_mem D T hCard i
  · rw [Finset.card_image_of_injective _
      (canonical_triangle_completion_injective D T hCard), hCard]
    simp

/-- The canonical four-completion enumeration also exhausts its facet. -/
theorem canonical_k4_completion_image_univ
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hCard : (graphFacetCompletions D.K D.ground T).card = 4) :
    (Finset.univ : Finset (Fin 4)).image
      (canonicalK4Completion D T hCard) =
        graphFacetCompletions D.K D.ground T := by
  apply Finset.eq_of_subset_of_card_le
  · intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact canonical_k4_completion_mem D T hCard i
  · rw [Finset.card_image_of_injective _
      (canonical_k4_completion_injective D T hCard), hCard]
    simp

/-- Surviving completion indices for one actual rainbow-triangle color
slot. -/
noncomputable def canonicalTriangleActualSelectedIndices
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hCard : (graphFacetCompletions D.K D.ground T).card = 3)
    (x : CliqueColor) : Finset (Fin 3) := by
  classical
  exact Finset.univ.filter fun i =>
    canonicalTriangleCompletion D T hCard i ∈
      actualEligiblePairSlotVertices D
        (T.erase (canonicalTriangleMark D T hCard x))

/-- Surviving completion indices for one actual proper-K4 color slot. -/
noncomputable def canonicalK4ActualSelectedIndices
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hCard : (graphFacetCompletions D.K D.ground T).card = 4)
    (x : CliqueColor) : Finset (Fin 4) := by
  classical
  exact Finset.univ.filter fun i =>
    canonicalK4Completion D T hCard i ∈
      actualEligiblePairSlotVertices D
        (T.erase (canonicalActualK4ColorMark D T hCard x))

/-- The canonical rainbow slot's selected index count is exactly the
degree of its marked vertex in the actual selected pair link. -/
theorem canonical_triangle_actual_selected_degree_eq
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hCard : (graphFacetCompletions D.K D.ground T).card = 3)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hRainbow : CompletionTriangleRainbow D
      (graphFacetCompletions D.K D.ground T))
    (x : CliqueColor) :
    let z := canonicalTriangleMark D T hCard x
    let S := actualEligiblePairSlotVertices D (T.erase z)
    (selectedCompletionPairGraph D S (T.erase z)).degree z =
      (canonicalTriangleActualSelectedIndices D T hCard x).card := by
  let z := canonicalTriangleMark D T hCard x
  let S := actualEligiblePairSlotVertices D (T.erase z)
  have hzT := canonical_triangle_mark_mem_facet D T hCard hTcard hTsub x
  have hzS := canonical_triangle_mark_actual_selected D T hCard
    hTcard hTsub hRainbow x
  change z ∈ S at hzS
  change (selectedCompletionPairGraph D S (T.erase z)).degree z =
    (canonicalTriangleActualSelectedIndices D T hCard x).card
  rw [selected_facet_degree_eq_selected_completions
    D T hTcard hTsub z hzT S hzS]
  simpa [canonicalTriangleActualSelectedIndices, z, S] using
    (indexed_filter_card_eq
    (graphFacetCompletions D.K D.ground T) S
    (canonicalTriangleCompletion D T hCard)
    (canonical_triangle_completion_injective D T hCard)
    (canonical_triangle_completion_image_univ D T hCard)).symm

/-- The analogous actual selected degree identity for a proper K4. -/
theorem canonical_k4_actual_selected_degree_eq
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hCard : (graphFacetCompletions D.K D.ground T).card = 4)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hProper : CompletionProperlyEdgeColored D
      (graphFacetCompletions D.K D.ground T))
    (x : CliqueColor) :
    let z := canonicalActualK4ColorMark D T hCard x
    let S := actualEligiblePairSlotVertices D (T.erase z)
    (selectedCompletionPairGraph D S (T.erase z)).degree z =
      (canonicalK4ActualSelectedIndices D T hCard x).card := by
  let z := canonicalActualK4ColorMark D T hCard x
  let S := actualEligiblePairSlotVertices D (T.erase z)
  have hzT := canonical_actual_k4_color_mark_mem_facet D T hCard hTcard hTsub x
  have hzS := canonical_k4_mark_actual_selected D T hCard
    hTcard hTsub hProper x
  change z ∈ S at hzS
  change (selectedCompletionPairGraph D S (T.erase z)).degree z =
    (canonicalK4ActualSelectedIndices D T hCard x).card
  rw [selected_facet_degree_eq_selected_completions
    D T hTcard hTsub z hzT S hzS]
  simpa [canonicalK4ActualSelectedIndices, z, S] using
    (indexed_filter_card_eq
    (graphFacetCompletions D.K D.ground T) S
    (canonicalK4Completion D T hCard)
    (canonical_k4_completion_injective D T hCard)
    (canonical_k4_completion_image_univ D T hCard)).symm

/-- A full canonical rainbow slot is one of the actual marked
degree-three pair-link vertices. -/
theorem canonical_triangle_full_slot_mem_actual_marked
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hCard : (graphFacetCompletions D.K D.ground T).card = 3)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hRainbow : CompletionTriangleRainbow D
      (graphFacetCompletions D.K D.ground T))
    (x : CliqueColor)
    (hFull : (canonicalTriangleActualSelectedIndices D T hCard x).card = 3) :
    let z := canonicalTriangleMark D T hCard x
    z ∈ actualColoredMarkedThreeSlots D (T.erase z) := by
  classical
  let z := canonicalTriangleMark D T hCard x
  have hzT := canonical_triangle_mark_mem_facet D T hCard hTcard hTsub x
  have hTdecomp : insert z (T.erase z) = T := Finset.insert_erase hzT
  have hDegree := canonical_triangle_actual_selected_degree_eq
    D T hCard hTcard hTsub hRainbow x
  change (selectedCompletionPairGraph D
    (actualEligiblePairSlotVertices D (T.erase z)) (T.erase z)).degree z =
      (canonicalTriangleActualSelectedIndices D T hCard x).card at hDegree
  change z ∈ D.ground.filter fun y =>
    y ∉ T.erase z ∧
      (graphFacetCompletions D.K D.ground (insert y (T.erase z))).card = 3 ∧
      FacetHasDivergentLabels
        (graphFacetCompletions D.K D.ground (insert y (T.erase z)))
        D.label ∧
      (selectedCompletionPairGraph D
        (actualEligiblePairSlotVertices D (T.erase z))
        (T.erase z)).degree y = 3
  apply Finset.mem_filter.mpr
  refine ⟨hTsub hzT, by simp, ?_, ?_, ?_⟩
  · simpa [hTdecomp] using hCard
  · simpa [hTdecomp] using
      canonical_triangle_facet_divergent D T hCard hRainbow
  · exact hDegree.trans hFull

/-- A full canonical proper-K4 slot is one of the actual marked
degree-four pair-link vertices. -/
theorem canonical_k4_full_slot_mem_actual_marked
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hCard : (graphFacetCompletions D.K D.ground T).card = 4)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hProper : CompletionProperlyEdgeColored D
      (graphFacetCompletions D.K D.ground T))
    (x : CliqueColor)
    (hFull : (canonicalK4ActualSelectedIndices D T hCard x).card = 4) :
    let z := canonicalActualK4ColorMark D T hCard x
    z ∈ actualColoredMarkedFourSlots D (T.erase z) := by
  classical
  let z := canonicalActualK4ColorMark D T hCard x
  have hzT := canonical_actual_k4_color_mark_mem_facet
    D T hCard hTcard hTsub x
  have hTdecomp : insert z (T.erase z) = T := Finset.insert_erase hzT
  have hDegree := canonical_k4_actual_selected_degree_eq
    D T hCard hTcard hTsub hProper x
  change (selectedCompletionPairGraph D
    (actualEligiblePairSlotVertices D (T.erase z)) (T.erase z)).degree z =
      (canonicalK4ActualSelectedIndices D T hCard x).card at hDegree
  change z ∈ D.ground.filter fun y =>
    y ∉ T.erase z ∧
      (graphFacetCompletions D.K D.ground (insert y (T.erase z))).card = 4 ∧
      FacetHasDivergentLabels
        (graphFacetCompletions D.K D.ground (insert y (T.erase z)))
        D.label ∧
      (selectedCompletionPairGraph D
        (actualEligiblePairSlotVertices D (T.erase z))
        (T.erase z)).degree y = 4
  apply Finset.mem_filter.mpr
  refine ⟨hTsub hzT, by simp, ?_, ?_, ?_⟩
  · simpa [hTdecomp] using hCard
  · simpa [hTdecomp] using
      canonical_k4_facet_divergent D T hCard hProper
  · exact hDegree.trans hFull

/-- Canonical rainbow slots for a finite family, using the actual
selected pair link belonging to each color. -/
noncomputable def canonicalTriangleFamilyActualSlots
    {ι : Type*} [DecidableEq ι]
    (D : FiniteCompletionCliqueData α) (C : Finset ι)
    (T : ι → Edge α)
    (hCard : ∀ t ∈ C,
      (graphFacetCompletions D.K D.ground (T t)).card = 3)
    (t : ι) (x : CliqueColor) : Finset (Fin 3) :=
  if ht : t ∈ C then
    canonicalTriangleActualSelectedIndices D (T t) (hCard t ht) x
  else ∅

/-- Canonical proper-K4 slots with their actual selected pair links. -/
noncomputable def canonicalK4FamilyActualSlots
    {ι : Type*} [DecidableEq ι]
    (D : FiniteCompletionCliqueData α) (C : Finset ι)
    (T : ι → Edge α)
    (hCard : ∀ t ∈ C,
      (graphFacetCompletions D.K D.ground (T t)).card = 4)
    (t : ι) (x : CliqueColor) : Finset (Fin 4) :=
  if ht : t ∈ C then
    canonicalK4ActualSelectedIndices D (T t) (hCard t ht) x
  else ∅

/-- The actual rainbow family needs no extra selected-vertex premise:
its canonical slots are defined by the actual pair links. -/
theorem canonical_triangle_family_actual_unique_records_selected
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : FiniteCompletionCliqueData α) (C : Finset ι)
    (T : ι → Edge α) (hTInjective : Function.Injective T)
    (hCard : ∀ t ∈ C,
      (graphFacetCompletions D.K D.ground (T t)).card = 3)
    (hTCard : ∀ t ∈ C, (T t).card = 3)
    (hTSub : ∀ t ∈ C, T t ⊆ D.ground)
    (hRainbow : ∀ t ∈ C, CompletionTriangleRainbow D
      (graphFacetCompletions D.K D.ground (T t))) :
    (∑ t ∈ C, (coloredFacetRecords 3 -
      ∑ x : CliqueColor, coloredSlotLoss 3
        (canonicalTriangleFamilyActualSlots D C T hCard t x).card)) ≤
      ((actualUniquePairRecordKeys D).card : ℚ) := by
  apply canonical_triangle_family_actual_unique_records D C T
    hTInjective hCard hTCard hTSub hRainbow
    (canonicalTriangleFamilyActualSlots D C T hCard)
  intro t ht x i hi
  have hi' : i ∈ canonicalTriangleActualSelectedIndices D (T t)
      (hCard t ht) x := by
    simpa [canonicalTriangleFamilyActualSlots, ht] using hi
  exact (Finset.mem_filter.mp hi').2

/-- The same closed actual record bound for proper-K4 facets. -/
theorem canonical_k4_family_actual_unique_records_selected
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : FiniteCompletionCliqueData α) (C : Finset ι)
    (T : ι → Edge α) (hTInjective : Function.Injective T)
    (hCard : ∀ t ∈ C,
      (graphFacetCompletions D.K D.ground (T t)).card = 4)
    (hTCard : ∀ t ∈ C, (T t).card = 3)
    (hTSub : ∀ t ∈ C, T t ⊆ D.ground)
    (hProper : ∀ t ∈ C, CompletionProperlyEdgeColored D
      (graphFacetCompletions D.K D.ground (T t))) :
    (∑ t ∈ C, (coloredFacetRecords 4 -
      ∑ x : CliqueColor, coloredSlotLoss 4
        (canonicalK4FamilyActualSlots D C T hCard t x).card)) ≤
      ((actualUniquePairRecordKeys D).card : ℚ) := by
  apply canonical_k4_family_actual_unique_records D C T
    hTInjective hCard hTCard hTSub hProper
    (canonicalK4FamilyActualSlots D C T hCard)
  intro t ht x i hi
  have hi' : i ∈ canonicalK4ActualSelectedIndices D (T t)
      (hCard t ht) x := by
    simpa [canonicalK4FamilyActualSlots, ht] using hi
  exact (Finset.mem_filter.mp hi').2

/-- Full rainbow color slots in a finite canonical facet family. -/
noncomputable def canonicalTriangleFullSlots
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : FiniteCompletionCliqueData α) (C : Finset ι)
    (T : ι → Edge α)
    (hCard : ∀ t ∈ C,
      (graphFacetCompletions D.K D.ground (T t)).card = 3) :
    Finset ({t : ι // t ∈ C} × CliqueColor) := by
  classical
  exact Finset.univ.filter fun p =>
    (canonicalTriangleActualSelectedIndices D (T p.1.1)
      (hCard p.1.1 p.1.2) p.2).card = 3

/-- Full proper-K4 color slots in a finite canonical facet family. -/
noncomputable def canonicalK4FullSlots
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : FiniteCompletionCliqueData α) (C : Finset ι)
    (T : ι → Edge α)
    (hCard : ∀ t ∈ C,
      (graphFacetCompletions D.K D.ground (T t)).card = 4) :
    Finset ({t : ι // t ∈ C} × CliqueColor) := by
  classical
  exact Finset.univ.filter fun p =>
    (canonicalK4ActualSelectedIndices D (T p.1.1)
      (hCard p.1.1 p.1.2) p.2).card = 4

/-- Full rainbow slots inject into the actual degree-three marked
vertices, paired with their base pairs. -/
theorem canonical_triangle_full_slots_card_le_actual_marks
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : FiniteCompletionCliqueData α) (C : Finset ι)
    (T : ι → Edge α) (hTInjective : Function.Injective T)
    (hCard : ∀ t ∈ C,
      (graphFacetCompletions D.K D.ground (T t)).card = 3)
    (hTCard : ∀ t ∈ C, (T t).card = 3)
    (hTSub : ∀ t ∈ C, T t ⊆ D.ground)
    (hRainbow : ∀ t ∈ C, CompletionTriangleRainbow D
      (graphFacetCompletions D.K D.ground (T t))) :
    (canonicalTriangleFullSlots D C T hCard).card ≤
      ∑ Q ∈ D.ground.powersetCard 2,
        (actualColoredMarkedThreeSlots D Q).card := by
  classical
  let β := {t : ι // t ∈ C}
  let T' : β → Edge α := fun t => T t.1
  let mark : β → CliqueColor → α := fun t =>
    canonicalTriangleMark D (T t.1) (hCard t.1 t.2)
  apply finite_full_slot_mark_count_le D
    (Finset.univ : Finset β) (canonicalTriangleFullSlots D C T hCard)
    T' (by
      intro t u h
      apply Subtype.ext
      exact hTInjective h)
    mark (actualColoredMarkedThreeSlots D)
  · intro p _
    exact Finset.mem_univ p.1
  · intro t _ x
    exact canonical_triangle_mark_mem_facet D (T t.1)
      (hCard t.1 t.2) (hTCard t.1 t.2) (hTSub t.1 t.2) x
  · intro t _
    exact canonical_triangle_mark_injective D (T t.1)
      (hCard t.1 t.2) (hRainbow t.1 t.2)
  · intro p hp
    exact facet_erase_vertex_mem_ground_pairs D (T p.1.1)
      (hTCard p.1.1 p.1.2) (hTSub p.1.1 p.1.2) (mark p.1 p.2)
      (canonical_triangle_mark_mem_facet D (T p.1.1)
        (hCard p.1.1 p.1.2) (hTCard p.1.1 p.1.2)
        (hTSub p.1.1 p.1.2) p.2)
  · intro p hp
    have hFull := (Finset.mem_filter.mp hp).2
    exact canonical_triangle_full_slot_mem_actual_marked D (T p.1.1)
      (hCard p.1.1 p.1.2) (hTCard p.1.1 p.1.2)
      (hTSub p.1.1 p.1.2) (hRainbow p.1.1 p.1.2) p.2 hFull

/-- Full proper-K4 slots inject into the actual degree-four marked
vertices, paired with their base pairs. -/
theorem canonical_k4_full_slots_card_le_actual_marks
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : FiniteCompletionCliqueData α) (C : Finset ι)
    (T : ι → Edge α) (hTInjective : Function.Injective T)
    (hCard : ∀ t ∈ C,
      (graphFacetCompletions D.K D.ground (T t)).card = 4)
    (hTCard : ∀ t ∈ C, (T t).card = 3)
    (hTSub : ∀ t ∈ C, T t ⊆ D.ground)
    (hProper : ∀ t ∈ C, CompletionProperlyEdgeColored D
      (graphFacetCompletions D.K D.ground (T t))) :
    (canonicalK4FullSlots D C T hCard).card ≤
      ∑ Q ∈ D.ground.powersetCard 2,
        (actualColoredMarkedFourSlots D Q).card := by
  classical
  let β := {t : ι // t ∈ C}
  let T' : β → Edge α := fun t => T t.1
  let mark : β → CliqueColor → α := fun t =>
    canonicalActualK4ColorMark D (T t.1) (hCard t.1 t.2)
  apply finite_full_slot_mark_count_le D
    (Finset.univ : Finset β) (canonicalK4FullSlots D C T hCard)
    T' (by
      intro t u h
      apply Subtype.ext
      exact hTInjective h)
    mark (actualColoredMarkedFourSlots D)
  · intro p _
    exact Finset.mem_univ p.1
  · intro t _ x
    exact canonical_actual_k4_color_mark_mem_facet D (T t.1)
      (hCard t.1 t.2) (hTCard t.1 t.2) (hTSub t.1 t.2) x
  · intro t _
    have hmark : Function.Injective (mark t) := by
      intro x y hxy
      obtain ⟨_, hAdj⟩ := canonical_k4_labels_are_proper_pattern
        D (T t.1) (hCard t.1 t.2) (hTCard t.1 t.2)
        (hTSub t.1 t.2) (hProper t.1 t.2)
      fin_cases x <;> fin_cases y <;>
        simp_all [mark, canonicalActualK4ColorMark,
          completionK4Ends, completionK4IndexPair]
    exact hmark
  · intro p hp
    exact facet_erase_vertex_mem_ground_pairs D (T p.1.1)
      (hTCard p.1.1 p.1.2) (hTSub p.1.1 p.1.2) (mark p.1 p.2)
      (canonical_actual_k4_color_mark_mem_facet D (T p.1.1)
        (hCard p.1.1 p.1.2) (hTCard p.1.1 p.1.2)
        (hTSub p.1.1 p.1.2) p.2)
  · intro p hp
    have hFull := (Finset.mem_filter.mp hp).2
    exact canonical_k4_full_slot_mem_actual_marked D (T p.1.1)
      (hCard p.1.1 p.1.2) (hTCard p.1.1 p.1.2)
      (hTSub p.1.1 p.1.2) (hProper p.1.1 p.1.2) p.2 hFull

/-- Count full slots by summing their indicator over facets and colors. -/
theorem full_slot_indicator_sum_eq_card
    {β : Type*} [Fintype β]
    (P : β × CliqueColor → Prop) [DecidablePred P] :
    (∑ t : β, ∑ x : CliqueColor,
      if P (t, x) then (1 : ℚ) else 0) =
      (((Finset.univ : Finset (β × CliqueColor)).filter P).card : ℚ) := by
  calc
    (∑ t : β, ∑ x : CliqueColor,
      if P (t, x) then (1 : ℚ) else 0) =
        ∑ p : β × CliqueColor, if P p then (1 : ℚ) else 0 := by
      simpa using (Finset.sum_product
        (Finset.univ : Finset β) (Finset.univ : Finset CliqueColor)
        (fun p => if P p then (1 : ℚ) else 0)).symm
    _ = (((Finset.univ : Finset (β × CliqueColor)).filter P).card : ℚ) := by
      rw [← Finset.sum_filter]
      simp

/-- The scalar rainbow mark sum is exactly half the full-slot count. -/
theorem canonical_triangle_full_slot_mark_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : FiniteCompletionCliqueData α) (C : Finset ι)
    (T : ι → Edge α)
    (hCard : ∀ t ∈ C,
      (graphFacetCompletions D.K D.ground (T t)).card = 3) :
    (∑ t : {t : ι // t ∈ C}, ∑ x : CliqueColor,
      coloredSlotMark 3
        (canonicalTriangleActualSelectedIndices D (T t.1)
          (hCard t.1 t.2) x).card) =
      ((canonicalTriangleFullSlots D C T hCard).card : ℚ) / 2 := by
  classical
  have hIndicator := full_slot_indicator_sum_eq_card
    (fun p : {t : ι // t ∈ C} × CliqueColor =>
      (canonicalTriangleActualSelectedIndices D (T p.1.1)
        (hCard p.1.1 p.1.2) p.2).card = 3)
  change (∑ t : {t : ι // t ∈ C}, ∑ x : CliqueColor,
      if (canonicalTriangleActualSelectedIndices D (T t.1)
        (hCard t.1 t.2) x).card = 3 then (1 : ℚ) else 0) =
      ((canonicalTriangleFullSlots D C T hCard).card : ℚ) at hIndicator
  calc
    (∑ t : {t : ι // t ∈ C}, ∑ x : CliqueColor,
      coloredSlotMark 3
        (canonicalTriangleActualSelectedIndices D (T t.1)
          (hCard t.1 t.2) x).card) =
        (∑ t : {t : ι // t ∈ C}, ∑ x : CliqueColor,
          if (canonicalTriangleActualSelectedIndices D (T t.1)
            (hCard t.1 t.2) x).card = 3 then (1 : ℚ) else 0) / 2 := by
      have hEach (k : ℕ) : coloredSlotMark 3 k =
          (if k = 3 then (1 : ℚ) else 0) / 2 := by
        by_cases hk : k = 3 <;> simp [coloredSlotMark, hk]
      simp_rw [hEach, Finset.sum_div]
    _ = ((canonicalTriangleFullSlots D C T hCard).card : ℚ) / 2 := by
      rw [hIndicator]

/-- The scalar proper-K4 mark sum is its full-slot count. -/
theorem canonical_k4_full_slot_mark_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : FiniteCompletionCliqueData α) (C : Finset ι)
    (T : ι → Edge α)
    (hCard : ∀ t ∈ C,
      (graphFacetCompletions D.K D.ground (T t)).card = 4) :
    (∑ t : {t : ι // t ∈ C}, ∑ x : CliqueColor,
      coloredSlotMark 4
        (canonicalK4ActualSelectedIndices D (T t.1)
          (hCard t.1 t.2) x).card) =
      ((canonicalK4FullSlots D C T hCard).card : ℚ) := by
  classical
  have hIndicator := full_slot_indicator_sum_eq_card
    (fun p : {t : ι // t ∈ C} × CliqueColor =>
      (canonicalK4ActualSelectedIndices D (T p.1.1)
        (hCard p.1.1 p.1.2) p.2).card = 4)
  simpa [coloredSlotMark, canonicalK4FullSlots] using hIndicator

/-- All full rainbow marks are paid by the actual degree-three marked
vertices with the coefficient in (III.B.10). -/
theorem canonical_triangle_mark_sum_le_actual
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : FiniteCompletionCliqueData α) (C : Finset ι)
    (T : ι → Edge α) (hTInjective : Function.Injective T)
    (hCard : ∀ t ∈ C,
      (graphFacetCompletions D.K D.ground (T t)).card = 3)
    (hTCard : ∀ t ∈ C, (T t).card = 3)
    (hTSub : ∀ t ∈ C, T t ⊆ D.ground)
    (hRainbow : ∀ t ∈ C, CompletionTriangleRainbow D
      (graphFacetCompletions D.K D.ground (T t))) :
    (∑ t : {t : ι // t ∈ C}, ∑ x : CliqueColor,
      coloredSlotMark 3
        (canonicalTriangleActualSelectedIndices D (T t.1)
          (hCard t.1 t.2) x).card) ≤
      (∑ Q ∈ D.ground.powersetCard 2,
        ((actualColoredMarkedThreeSlots D Q).card : ℚ)) / 2 := by
  rw [canonical_triangle_full_slot_mark_sum D C T hCard]
  have hCardBound := canonical_triangle_full_slots_card_le_actual_marks
    D C T hTInjective hCard hTCard hTSub hRainbow
  have hCast : ((canonicalTriangleFullSlots D C T hCard).card : ℚ) ≤
      ∑ Q ∈ D.ground.powersetCard 2,
        ((actualColoredMarkedThreeSlots D Q).card : ℚ) := by
    exact_mod_cast hCardBound
  linarith

/-- All full proper-K4 marks are paid by the actual degree-four marked
vertices. -/
theorem canonical_k4_mark_sum_le_actual
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : FiniteCompletionCliqueData α) (C : Finset ι)
    (T : ι → Edge α) (hTInjective : Function.Injective T)
    (hCard : ∀ t ∈ C,
      (graphFacetCompletions D.K D.ground (T t)).card = 4)
    (hTCard : ∀ t ∈ C, (T t).card = 3)
    (hTSub : ∀ t ∈ C, T t ⊆ D.ground)
    (hProper : ∀ t ∈ C, CompletionProperlyEdgeColored D
      (graphFacetCompletions D.K D.ground (T t))) :
    (∑ t : {t : ι // t ∈ C}, ∑ x : CliqueColor,
      coloredSlotMark 4
        (canonicalK4ActualSelectedIndices D (T t.1)
          (hCard t.1 t.2) x).card) ≤
      ∑ Q ∈ D.ground.powersetCard 2,
        ((actualColoredMarkedFourSlots D Q).card : ℚ) := by
  rw [canonical_k4_full_slot_mark_sum D C T hCard]
  have hCardBound := canonical_k4_full_slots_card_le_actual_marks
    D C T hTInjective hCard hTCard hTSub hProper
  exact_mod_cast hCardBound

end JSP523.Rank4
