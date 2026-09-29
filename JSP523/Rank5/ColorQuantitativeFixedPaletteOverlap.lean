import JSP523.Rank5.ColorQuantitativeFixedPaletteCleanup

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α]

noncomputable def fixedPaletteOverlappingPartners
    (H : Family α) (V B R : Edge α) (s : ℕ) : Family α := by
  classical
  exact (actualCoreLink H V B s).filter fun T => ¬ Disjoint R T

/-- Roots in a core parent link containing one specified vertex inject
    into the actual parent edges through the resulting extended core. -/
theorem fixed_palette_roots_containing_vertex_le_codegree
    (H : Family α) (V B : Edge α) (s : ℕ) (a : α) :
    ((actualCoreLink H V B s).filter fun T => a ∈ T).card ≤
      (H.filter fun E => B ∪ {a} ⊆ E).card := by
  classical
  let f : Edge α → Edge α := fun T => B ∪ T
  apply Finset.card_le_card_of_injOn f
  · intro T hT
    obtain ⟨hLink, haT⟩ := Finset.mem_filter.mp hT
    have hParts := mem_actual_core_link.mp hLink
    apply Finset.mem_filter.mpr
    refine ⟨hParts.2.2.2, ?_⟩
    intro x hx
    rcases Finset.mem_union.mp hx with hxB | hxA
    · exact Finset.mem_union_left T hxB
    · have hxa : x = a := Finset.mem_singleton.mp hxA
      exact Finset.mem_union_right B (hxa ▸ haT)
  · intro T hT U hU hEq
    have hTdisj : Disjoint B T :=
      (mem_actual_core_link.mp (Finset.mem_filter.mp hT).1).2.2.1.symm
    have hUdisj : Disjoint B U :=
      (mem_actual_core_link.mp (Finset.mem_filter.mp hU).1).2.2.1.symm
    calc
      T = (B ∪ T) \ B := (Finset.union_sdiff_cancel_left hTdisj).symm
      _ = (B ∪ U) \ B := congrArg (· \ B) hEq
      _ = U := Finset.union_sdiff_cancel_left hUdisj

/-- Overlapping partners are covered by the roots containing each vertex of
    `R`, and hence by the sum of the corresponding actual codegrees. -/
theorem fixed_palette_overlapping_partners_card_le_codegree_sum
    (H : Family α) (V B R : Edge α) (s : ℕ) :
    (fixedPaletteOverlappingPartners H V B R s).card ≤
      ∑ a ∈ R, (H.filter fun E => B ∪ {a} ⊆ E).card := by
  classical
  let L : α → Family α := fun a =>
    (actualCoreLink H V B s).filter fun T => a ∈ T
  have hCover : fixedPaletteOverlappingPartners H V B R s ⊆ R.biUnion L := by
    intro T hT
    have hParts := Finset.mem_filter.mp hT
    obtain ⟨a, haR, haT⟩ := Finset.not_disjoint_iff.mp hParts.2
    exact Finset.mem_biUnion.mpr
      ⟨a, haR, Finset.mem_filter.mpr ⟨hParts.1, haT⟩⟩
  calc
    (fixedPaletteOverlappingPartners H V B R s).card ≤ (R.biUnion L).card :=
      Finset.card_le_card hCover
    _ ≤ ∑ a ∈ R, (L a).card := Finset.card_biUnion_le
    _ ≤ ∑ a ∈ R, (H.filter fun E => B ∪ {a} ⊆ E).card := by
      apply Finset.sum_le_sum
      intro a ha
      exact fixed_palette_roots_containing_vertex_le_codegree H V B s a

/-- The concrete facet case: a pair root has at most the root size times the extended-core codegree
    cap many overlapping partners in its core parent link. -/
theorem fixed_palette_overlapping_partners_card_le_codegree
    (H : Family α) (V B R : Edge α) (s : ℕ) (D₄ : ℕ)
    (hRcard : R.card = s)
    (hD₄ : ∀ a ∈ R, (H.filter fun E => B ∪ {a} ⊆ E).card ≤ D₄) :
    (fixedPaletteOverlappingPartners H V B R s).card ≤ s * D₄ := by
  have hOverlap := fixed_palette_overlapping_partners_card_le_codegree_sum H V B R s
  have hSum : (∑ a ∈ R, (H.filter fun E => B ∪ {a} ⊆ E).card) ≤
      ∑ _a ∈ R, D₄ := Finset.sum_le_sum hD₄
  simpa [hRcard, mul_comm] using hOverlap.trans hSum

theorem fixed_palette_overlap_incidence_sum_budget
    (H : Family α) (V : Edge α) (r s k D₄ : ℕ)
    (hUniform : Uniform r H)
    (hAmbient : ∀ E ∈ H, E ⊆ V)
    (hD₄ : ∀ S : Edge α, S.card = k + 1 →
      (H.filter fun E => S ⊆ E).card ≤ D₄) :
    (∑ B ∈ V.powersetCard k,
      ∑ R ∈ actualCoreLink H V B s,
        (fixedPaletteOverlappingPartners H V B R s).card) ≤
      s * r.choose k * D₄ * H.card := by
  classical
  have hLocal : ∀ B ∈ V.powersetCard k,
      ∀ R ∈ actualCoreLink H V B s,
        (fixedPaletteOverlappingPartners H V B R s).card ≤ s * D₄ := by
    intro B hB R hR
    have hBcard := (Finset.mem_powersetCard.mp hB).2
    have hParts := mem_actual_core_link.mp hR
    have hCap : ∀ a ∈ R,
        (H.filter fun E => B ∪ {a} ⊆ E).card ≤ D₄ := by
      intro a haR
      have haNotB : a ∉ B := by
        intro haB
        exact (Finset.disjoint_left.mp hParts.2.2.1) haR haB
      have hCard : (B ∪ {a}).card = k + 1 := by
        have hDisj : Disjoint B ({a} : Edge α) :=
          Finset.disjoint_singleton_right.mpr haNotB
        rw [Finset.card_union_of_disjoint hDisj]
        simp [hBcard]
      exact hD₄ (B ∪ {a}) hCard
    exact fixed_palette_overlapping_partners_card_le_codegree
      H V B R s D₄ hParts.2.1 hCap
  have hCount := total_fixed_palette_core_links_le_edges
    H V r s k hUniform hAmbient
  calc
    (∑ B ∈ V.powersetCard k,
        ∑ R ∈ actualCoreLink H V B s,
          (fixedPaletteOverlappingPartners H V B R s).card) ≤
        ∑ B ∈ V.powersetCard k,
          (s * D₄) * (actualCoreLink H V B s).card := by
      apply Finset.sum_le_sum
      intro B hB
      calc
        (∑ R ∈ actualCoreLink H V B s,
            (fixedPaletteOverlappingPartners H V B R s).card) ≤
            ∑ _R ∈ actualCoreLink H V B s, s * D₄ :=
          Finset.sum_le_sum (fun R hR => hLocal B hB R hR)
        _ = (s * D₄) * (actualCoreLink H V B s).card := by
          simp [mul_comm]
    _ = (s * D₄) *
          (∑ B ∈ V.powersetCard k, (actualCoreLink H V B s).card) := by
      rw [Finset.mul_sum]
    _ ≤ (s * D₄) * (r.choose k * H.card) := Nat.mul_le_mul_left _ hCount
    _ = s * r.choose k * D₄ * H.card := by ring

end JSP523.Rank5
