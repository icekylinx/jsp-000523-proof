import JSP523.Rank4.PreprocessUsedParentWedgeBudget
import JSP523.Rank4.PreprocessParentTails

/-! # Pair-degree of the corrected used-parent label system -/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- The ordered used completion pairs whose parent label triple contains
the fixed unordered pair of vertices. -/
noncomputable def usedParentSourcesThroughPair
    (D : FiniteCompletionCliqueData α) (a b : α) : Finset (α × α) := by
  classical
  exact (D.ground.product D.ground).filter fun xy =>
    xy.1 ≠ xy.2 ∧
    (commonTripleCell D.K D.ground xy.1 xy.2).Nonempty ∧
    ({a, b} : Edge α) ⊆
      insert (D.label xy.1 xy.2) ({xy.1, xy.2} : Edge α)

/-- The source-pair count dominates the actual parent-label pair-degree. -/
theorem used_parent_pair_degree_le_source_count
    (D : FiniteCompletionCliqueData α) (a b : α) :
    qPairDegree (reciprocalUsedParentLabelTriples D) {a, b} ≤
      (usedParentSourcesThroughPair D a b).card := by
  classical
  let source := usedParentSourcesThroughPair D a b
  let f : α × α → Edge α := fun xy =>
    insert (D.label xy.1 xy.2) ({xy.1, xy.2} : Edge α)
  have hSub : JSP523.Rank3.containingEdges
      (reciprocalUsedParentLabelTriples D) ({a, b} : Edge α) ⊆
      source.image f := by
    intro T hT
    have hParts := Finset.mem_filter.mp hT
    obtain ⟨xy, hxy, rfl⟩ := Finset.mem_image.mp hParts.1
    apply Finset.mem_image.mpr
    refine ⟨xy, ?_, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hxy).1,
        (Finset.mem_filter.mp hxy).2.1,
        (Finset.mem_filter.mp hxy).2.2,
        hParts.2⟩
  exact (Finset.card_le_card hSub).trans Finset.card_image_le

/-- Six possible orientations of a source pair through a fixed target
pair: two direct sources and four labeled-fiber sources. -/
noncomputable def usedParentSourceCandidates
    (D : FiniteCompletionCliqueData α) (a b : α) :
    Finset (α × α) := by
  classical
  exact ({(a, b), (b, a)} : Finset (α × α)) ∪
    ((reciprocalUsedLabelFiber D a b).image fun c => (a, c)) ∪
    ((reciprocalUsedLabelFiber D a b).image fun c => (c, a)) ∪
    ((reciprocalUsedLabelFiber D b a).image fun c => (b, c)) ∪
    ((reciprocalUsedLabelFiber D b a).image fun c => (c, b))

theorem used_parent_source_candidates_card_le
    (D : FiniteCompletionCliqueData α) (a b : α) (Kstar : ℕ)
    (h_label : ∀ x y : α,
      (reciprocalUsedLabelFiber D x y).card ≤ Kstar) :
    (usedParentSourceCandidates D a b).card ≤ 2 + 4 * Kstar := by
  classical
  unfold usedParentSourceCandidates
  have hbase : ({(a, b), (b, a)} : Finset (α × α)).card ≤ 2 := by
    exact (Finset.card_insert_le _ _).trans
      (by simp)
  have h1 := Finset.card_union_le
    ({(a, b), (b, a)} : Finset (α × α))
    ((reciprocalUsedLabelFiber D a b).image fun c => (a, c))
  have h2 := Finset.card_union_le
    (({(a, b), (b, a)} : Finset (α × α)) ∪
      ((reciprocalUsedLabelFiber D a b).image fun c => (a, c)))
    ((reciprocalUsedLabelFiber D a b).image fun c => (c, a))
  have h3 := Finset.card_union_le
    ((({(a, b), (b, a)} : Finset (α × α)) ∪
      ((reciprocalUsedLabelFiber D a b).image fun c => (a, c))) ∪
      ((reciprocalUsedLabelFiber D a b).image fun c => (c, a)))
    ((reciprocalUsedLabelFiber D b a).image fun c => (b, c))
  have h4 := Finset.card_union_le
    (((({(a, b), (b, a)} : Finset (α × α)) ∪
      ((reciprocalUsedLabelFiber D a b).image fun c => (a, c))) ∪
      ((reciprocalUsedLabelFiber D a b).image fun c => (c, a))) ∪
      ((reciprocalUsedLabelFiber D b a).image fun c => (b, c)))
    ((reciprocalUsedLabelFiber D b a).image fun c => (c, b))
  have hIab : ((reciprocalUsedLabelFiber D a b).image fun c => (a, c)).card ≤ Kstar :=
    (Finset.card_image_le).trans (h_label a b)
  have hIba : ((reciprocalUsedLabelFiber D a b).image fun c => (c, a)).card ≤ Kstar :=
    (Finset.card_image_le).trans (h_label a b)
  have hJab : ((reciprocalUsedLabelFiber D b a).image fun c => (b, c)).card ≤ Kstar :=
    (Finset.card_image_le).trans (h_label b a)
  have hJba : ((reciprocalUsedLabelFiber D b a).image fun c => (c, b)).card ≤ Kstar :=
    (Finset.card_image_le).trans (h_label b a)
  omega

private theorem source_candidate_direct
    (D : FiniteCompletionCliqueData α) (a b : α) :
    (a, b) ∈ usedParentSourceCandidates D a b ∧
      (b, a) ∈ usedParentSourceCandidates D a b := by
  constructor <;> simp [usedParentSourceCandidates]

private theorem source_candidate_fiber_left
    (D : FiniteCompletionCliqueData α) (a b c : α)
    (hc : c ∈ reciprocalUsedLabelFiber D a b) :
    (a, c) ∈ usedParentSourceCandidates D a b ∧
      (c, a) ∈ usedParentSourceCandidates D a b := by
  constructor <;> simp [usedParentSourceCandidates, hc]

private theorem source_candidate_fiber_right
    (D : FiniteCompletionCliqueData α) (a b c : α)
    (hc : c ∈ reciprocalUsedLabelFiber D b a) :
    (b, c) ∈ usedParentSourceCandidates D a b ∧
      (c, b) ∈ usedParentSourceCandidates D a b := by
  constructor <;> simp [usedParentSourceCandidates, hc]

theorem used_parent_sources_subset_candidates
    (D : FiniteCompletionCliqueData α) (a b : α)
    (hab : a ≠ b) :
    usedParentSourcesThroughPair D a b ⊆
      usedParentSourceCandidates D a b := by
  classical
  rintro ⟨u, v⟩ hsrc
  have hParts := Finset.mem_filter.mp hsrc
  have hu : u ∈ D.ground := (Finset.mem_product.mp hParts.1).1
  have hv : v ∈ D.ground := (Finset.mem_product.mp hParts.1).2
  have huv : u ≠ v := hParts.2.1
  have hUsed : (commonTripleCell D.K D.ground u v).Nonempty :=
    hParts.2.2.1
  have hUsedSwap : (commonTripleCell D.K D.ground v u).Nonempty := by
    rw [← common_triple_cell_swap D.K D.ground u v]
    exact hUsed
  have hsub := hParts.2.2.2
  have ha : a = D.label u v ∨ a = u ∨ a = v := by
    have h := hsub (by simp : a ∈ ({a, b} : Edge α))
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h
  have hb : b = D.label u v ∨ b = u ∨ b = v := by
    have h := hsub (by simp : b ∈ ({a, b} : Edge α))
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h
  rcases ha with ha | ha | ha
  · rcases hb with hb | hb | hb
    · exact (hab (ha.trans hb.symm)).elim
    · have hFiber : v ∈ reciprocalUsedLabelFiber D b a := by
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_filter.mpr
          refine ⟨hv, ?_, ?_⟩
          · simpa [hb] using huv
          · simpa [hb] using ha.symm
        · simpa [hb] using hUsed
      simpa only [hb] using
        (source_candidate_fiber_right D a b v hFiber).1
    · have hFiber : u ∈ reciprocalUsedLabelFiber D b a := by
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_filter.mpr
          refine ⟨hu, ?_, ?_⟩
          · simpa [hb] using huv.symm
          · have hlabel : D.label v u = a := by
              simpa [D.label_symm] using ha.symm
            simpa [hb] using hlabel
        · simpa [hb] using hUsedSwap
      simpa only [hb] using
        (source_candidate_fiber_right D a b u hFiber).2
  · rcases hb with hb | hb | hb
    · have hFiber : v ∈ reciprocalUsedLabelFiber D a b := by
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_filter.mpr
          refine ⟨hv, ?_, ?_⟩
          · simpa [ha] using huv
          · simpa [ha] using hb.symm
        · simpa [ha] using hUsed
      simpa only [ha] using
        (source_candidate_fiber_left D a b v hFiber).1
    · exact (hab (ha.trans hb.symm)).elim
    · simpa only [ha, hb] using (source_candidate_direct D a b).1
  · rcases hb with hb | hb | hb
    · have hFiber : u ∈ reciprocalUsedLabelFiber D a b := by
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_filter.mpr
          refine ⟨hu, ?_, ?_⟩
          · simpa [ha] using huv.symm
          · have hlabel : D.label v u = b := by
              simpa [D.label_symm] using hb.symm
            simpa [ha] using hlabel
        · simpa [ha] using hUsedSwap
      simpa only [ha] using
        (source_candidate_fiber_left D a b u hFiber).2
    · simpa only [ha, hb] using (source_candidate_direct D a b).2
    · exact (hab (ha.trans hb.symm)).elim

theorem reciprocal_used_parent_pair_degree_le_label_fibers
    (D : FiniteCompletionCliqueData α) (a b : α) (Kstar : ℕ)
    (hab : a ≠ b)
    (h_label : ∀ x y : α,
      (reciprocalUsedLabelFiber D x y).card ≤ Kstar) :
    qPairDegree (reciprocalUsedParentLabelTriples D) {a, b} ≤
      2 + 4 * Kstar := by
  calc
    _ ≤ (usedParentSourcesThroughPair D a b).card :=
      used_parent_pair_degree_le_source_count D a b
    _ ≤ (usedParentSourceCandidates D a b).card :=
      Finset.card_le_card
        (used_parent_sources_subset_candidates D a b hab)
    _ ≤ 2 + 4 * Kstar :=
      used_parent_source_candidates_card_le D a b Kstar h_label

theorem reciprocal_used_parent_pair_degree_cap_of_label_fibers
    (D : FiniteCompletionCliqueData α) (Kstar : ℕ)
    (h_label : ∀ x y : α,
      (reciprocalUsedLabelFiber D x y).card ≤ Kstar) :
    ∀ P ∈ D.ground.powersetCard 2,
      qPairDegree (reciprocalUsedParentLabelTriples D) P ≤
        2 + 4 * Kstar := by
  intro P hP
  obtain ⟨a, b, hab, rfl⟩ :=
    Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hP).2
  exact reciprocal_used_parent_pair_degree_le_label_fibers
    D a b Kstar hab h_label

end JSP523.Rank4
