import JSP523.Rank4.PreprocessBicoloredCompletionData

/-! # The actual repeated-color wedge budget for bad triple facets -/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- Used label fibers before the bicolored deletion. No clique-coloring
condition is required to define these actual parent fibers. -/
noncomputable def rawUsedCompletionLabelFiber
    (K : Family α) (U : Edge α) (label : α → α → α) (x a : α) : Finset α := by
  classical
  exact (U.filter fun y => x ≠ y ∧ label x y = a).filter fun y =>
    (commonTripleCell K U x y).Nonempty

/-- Triple facets supporting one oriented repeated-color wedge. -/
noncomputable def repeatedColorCompletionFacets
    (K : Family α) (U : Edge α) (label : α → α → α) (x y z : α) : Family α := by
  classical
  exact (U.powersetCard 3).filter fun T =>
    x ∈ graphFacetCompletions K U T ∧ y ∈ graphFacetCompletions K U T ∧
    z ∈ graphFacetCompletions K U T ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
    label x y = label x z ∧ label x y ≠ label y z

/-- Two distinct completion vertices give an actual common triple. -/
theorem completion_pair_common_triple_of_uniform
    (K : Family α) (U T : Edge α) (hUniform : Uniform 4 K)
    (hT : T ∈ U.powersetCard 3) (x y : α)
    (hx : x ∈ graphFacetCompletions K U T)
    (hy : y ∈ graphFacetCompletions K U T) :
    T ∈ commonTripleCell K U x y := by
  have hParts := Finset.mem_powersetCard.mp hT
  have hxNot := four_facet_completion_not_in_facet K hUniform T hParts.2 x
    (Finset.mem_filter.mp hx).2
  have hyNot := four_facet_completion_not_in_facet K hUniform T hParts.2 y
    (Finset.mem_filter.mp hy).2
  apply mem_common_triple_cell.mpr
  refine ⟨hParts.1, hParts.2, ?_, (Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2⟩
  apply Finset.disjoint_left.mpr
  intro a ha hab
  rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hab : a = x ∨ a = y) with rfl | rfl
  · exact hxNot ha
  · exact hyNot ha

/-- The two distinct labels and the fixed wedge root pin a triple in
each parent edge, leaving at most the facet-cap many supporting facets. -/
theorem repeated_color_completion_facets_card_le
    (K : Family α) (U : Edge α) (label : α → α → α) (d : ℕ)
    (hUniform : Uniform 4 K) (hGround : ∀ E ∈ K, E ⊆ U)
    (hCenter : ∀ x y, x ≠ y → ∀ T ∈ commonTripleCell K U x y, label x y ∈ T)
    (hCap : ∀ T : Edge α, T.card = 3 → (facetCompletions K U T).card ≤ d)
    (x y z : α) :
    (repeatedColorCompletionFacets K U label x y z).card ≤ d := by
  classical
  let S := repeatedColorCompletionFacets K U label x y z
  by_cases hEmpty : S = ∅
  · simp [show repeatedColorCompletionFacets K U label x y z = ∅ from hEmpty]
  have hGeometry (T : Edge α) (hT : T ∈ S) :
      x ∉ T ∧ label x y ∈ T ∧ label y z ∈ T ∧ label x y ≠ label y z := by
    obtain ⟨hTU, hx, hy, hz, hxy, _hxz, hyz, _hSame, hDiff⟩ := Finset.mem_filter.mp hT
    exact ⟨four_facet_completion_not_in_facet K hUniform T
      (Finset.mem_powersetCard.mp hTU).2 x (Finset.mem_filter.mp hx).2,
      hCenter x y hxy T (completion_pair_common_triple_of_uniform K U T hUniform hTU x y hx hy),
      hCenter y z hyz T (completion_pair_common_triple_of_uniform K U T hUniform hTU y z hy hz), hDiff⟩
  obtain ⟨T₀, hT₀⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
  obtain ⟨hxT, haT, hbT, hab⟩ := hGeometry T₀ hT₀
  let A : Edge α := {x, label x y, label y z}
  have hxa : x ≠ label x y := fun h => hxT (h ▸ haT)
  have hxb : x ≠ label y z := fun h => hxT (h ▸ hbT)
  have hAcard : A.card = 3 := by simp [A, hxa, hxb, hab]
  have hMap : ∀ T ∈ S, insert x T ∈ rankFourFacetParents K A := by
    intro T hT
    have hG := hGeometry T hT
    have hx := (Finset.mem_filter.mp hT).2.1
    apply Finset.mem_filter.mpr
    refine ⟨(Finset.mem_filter.mp hx).2, ?_⟩
    simp only [A, Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hG.2.1,
      Finset.mem_insert_of_mem hG.2.2.1⟩
  have hInj : Set.InjOn (fun T : Edge α => insert x T) S := by
    intro T hT R hR hEq
    have hTNot := (hGeometry T hT).1
    have hRNot := (hGeometry R hR).1
    have hErase := congrArg (fun E : Edge α => E.erase x) hEq
    simpa only [Finset.erase_insert hTNot, Finset.erase_insert hRNot] using hErase
  have hCard := Finset.card_le_card_of_injOn (fun T : Edge α => insert x T) hMap hInj
  have hParents := facet_completions_card_eq_parent_edges K U A hUniform hGround hAcard
  exact hCard.trans (hParents ▸ hCap A hAcard)

/-- Every bicolored triangle has an orientation with its repeated color
at the first vertex. -/
theorem bicolored_completion_facet_has_repeated_wedge
    (K : Family α) (U : Edge α) (label : α → α → α)
    (hSymm : ∀ x y, label x y = label y x)
    (T : Edge α) (hT : T ∈ bicoloredCompletionFacets K U label) :
    ∃ x y z, T ∈ repeatedColorCompletionFacets K U label x y z := by
  classical
  obtain ⟨hTU, x, hx, y, hy, z, hz, hxy, hxz, hyz, hColor⟩ := Finset.mem_filter.mp hT
  rcases hColor with ⟨hSame, hDiff⟩ | ⟨hSame, hDiff⟩ | ⟨hSame, hDiff⟩
  · exact ⟨x, y, z, Finset.mem_filter.mpr ⟨hTU, hx, hy, hz, hxy, hxz, hyz, hSame, hDiff⟩⟩
  · refine ⟨y, x, z, Finset.mem_filter.mpr ⟨hTU, hy, hx, hz, hxy.symm, hyz, hxz, ?_, ?_⟩⟩
    · exact (hSymm y x).trans hSame
    · simpa only [hSymm y x] using hDiff
  · refine ⟨z, x, y, Finset.mem_filter.mpr ⟨hTU, hz, hx, hy, hxz.symm, hyz.symm, hxy, ?_, ?_⟩⟩
    · exact (hSymm z x).trans (hSame.trans (hSymm y z))
    · simpa only [hSymm z x] using hDiff



/-- The supporting triple facets cost at most one facet-cap per ordered
repeated-color wedge. -/
theorem bicolored_completion_facets_card_le_wedge_budget
    (K : Family α) (U : Edge α) (label : α → α → α) (d κ : ℕ)
    (hUniform : Uniform 4 K) (hGround : ∀ E ∈ K, E ⊆ U)
    (hSymm : ∀ x y, label x y = label y x)
    (hCenter : ∀ x y, x ≠ y → ∀ T ∈ commonTripleCell K U x y, label x y ∈ T)
    (hCap : ∀ T : Edge α, T.card = 3 → (facetCompletions K U T).card ≤ d)
    (hFiber : ∀ x a, (rawUsedCompletionLabelFiber K U label x a).card ≤ κ) :
    (bicoloredCompletionFacets K U label).card ≤ d * U.card ^ 2 * κ ^ 2 := by
  classical
  let fiber := rawUsedCompletionLabelFiber K U label
  let support := repeatedColorCompletionFacets K U label
  let cover := U.biUnion fun x => U.biUnion fun a =>
    (fiber x a).biUnion fun y => (fiber x a).biUnion fun z => support x y z
  have hCover : bicoloredCompletionFacets K U label ⊆ cover := by
    intro T hT
    obtain ⟨x, y, z, hRep⟩ := bicolored_completion_facet_has_repeated_wedge K U label hSymm T hT
    obtain ⟨hTU, hx, hy, hz, hxy, hxz, _hyz, hSame, _hDiff⟩ := Finset.mem_filter.mp hRep
    have hXY := completion_pair_common_triple_of_uniform K U T hUniform hTU x y hx hy
    have hXZ := completion_pair_common_triple_of_uniform K U T hUniform hTU x z hx hz
    have hLabelT := hCenter x y hxy T hXY
    have hLabelU := (Finset.mem_powersetCard.mp hTU).1 hLabelT
    have hyFiber : y ∈ fiber x (label x y) :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1, hxy, rfl⟩, T, hXY⟩
    have hzFiber : z ∈ fiber x (label x y) :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1, hxz, hSame.symm⟩, T, hXZ⟩
    exact Finset.mem_biUnion.mpr ⟨x, (Finset.mem_filter.mp hx).1,
      Finset.mem_biUnion.mpr ⟨label x y, hLabelU,
        Finset.mem_biUnion.mpr ⟨y, hyFiber, Finset.mem_biUnion.mpr ⟨z, hzFiber, hRep⟩⟩⟩⟩
  have hCoverCard : cover.card ≤ ∑ x ∈ U, ∑ a ∈ U,
      ∑ y ∈ fiber x a, ∑ z ∈ fiber x a, (support x y z).card := by
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro x hx
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro y hy
    exact Finset.card_biUnion_le
  calc
    _ ≤ cover.card := Finset.card_le_card hCover
    _ ≤ ∑ x ∈ U, ∑ a ∈ U, ∑ y ∈ fiber x a, ∑ z ∈ fiber x a,
        (support x y z).card := hCoverCard
    _ ≤ ∑ _x ∈ U, ∑ _a ∈ U, d * κ ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro a ha
      have hSupports : (∑ y ∈ fiber x a, ∑ z ∈ fiber x a, (support x y z).card) ≤
          ∑ _y ∈ fiber x a, ∑ _z ∈ fiber x a, d := by
        apply Finset.sum_le_sum
        intro y hy
        apply Finset.sum_le_sum
        intro z hz
        exact repeated_color_completion_facets_card_le K U label d hUniform hGround hCenter hCap x y z
      have hBound := Nat.mul_le_mul_left d (Nat.mul_self_le_mul_self (hFiber x a))
      simp only [Finset.sum_const, nsmul_eq_mul] at hSupports
      dsimp only [fiber] at hSupports
      nlinarith
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]; ring

/-- The manuscript's actual bad-facet deletion bound, with an explicit
constant one for the ordered repeated-color wedge cover. -/
theorem bicolored_completion_deletion_card_le_wedge_budget
    (K : Family α) (U : Edge α) (label : α → α → α) (d κ : ℕ)
    (hUniform : Uniform 4 K) (hGround : ∀ E ∈ K, E ⊆ U)
    (hSymm : ∀ x y, label x y = label y x)
    (hCenter : ∀ x y, x ≠ y → ∀ T ∈ commonTripleCell K U x y, label x y ∈ T)
    (hCap : ∀ T : Edge α, T.card = 3 → (facetCompletions K U T).card ≤ d)
    (hFiber : ∀ x a, (rawUsedCompletionLabelFiber K U label x a).card ≤ κ) :
    (bicoloredCompletionDeletionEdges K U label).card ≤ d ^ 2 * U.card ^ 2 * κ ^ 2 := by
  have h1 := bicolored_completion_deletion_card_le K U label d hUniform hGround hCap
  have h2 := bicolored_completion_facets_card_le_wedge_budget K U label d κ
    hUniform hGround hSymm hCenter hCap hFiber
  calc
    _ ≤ d * (bicoloredCompletionFacets K U label).card := h1
    _ ≤ d * (d * U.card ^ 2 * κ ^ 2) := Nat.mul_le_mul_left d h2
    _ = _ := by ring

end JSP523.Rank4
