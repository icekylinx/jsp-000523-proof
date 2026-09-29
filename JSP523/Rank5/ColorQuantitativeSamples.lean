import JSP523.Rank5.ColorCleanSamples

/-! # Quantitative color rigidity by actual sample incidences

Discordant ordered edge pairs force bad samples. Extending each union to
a four-set yields a uniform lower incidence count, sufficient for the
quantitative coloring estimate at every fixed palette size.
-/

namespace JSP523.Rank5

variable {α κ : Type*} [DecidableEq α] [DecidableEq κ]

noncomputable def badPartialColorSamples
    (V : Finset α) (h : ℕ) (edgeColor : Finset α → Option κ) : Finset (Finset α) := by
  classical
  exact (V.powersetCard h).filter fun A =>
    (∃ e ∈ uncoloredEdgeSupports V edgeColor, e ⊆ A) ∨
    (∃ T ∈ bicoloredTriangleSupports V edgeColor, T ⊆ A)

/-- Every large sample containing a discordant pair contains an actual
    uncolored edge or an actual bicolored triangle. -/
theorem sample_containing_discordant_pair_is_bad
    [Fintype κ] [Nonempty κ]
    (V : Finset α) (h : ℕ) (edgeColor : Finset α → Option κ)
    (hq : 2 ≤ Fintype.card κ)
    (hSize : max 4 ((Fintype.card κ - 1) ^ 2 + 1) ≤ h)
    {p : Finset α × Finset α}
    (hp : p ∈ discordantColorPairs (V.powersetCard 2) edgeColor)
    {A : Finset α} (hA : A ∈ V.powersetCard h) (hUnion : p.1 ∪ p.2 ⊆ A) :
    A ∈ badPartialColorSamples V h edgeColor := by
  classical
  have hAV := (Finset.mem_powersetCard.mp hA).1
  have hAc := (Finset.mem_powersetCard.mp hA).2
  have hpParts := Finset.mem_filter.mp hp
  have hpEdges := Finset.mem_product.mp hpParts.1
  apply Finset.mem_filter.mpr
  refine ⟨hA, ?_⟩
  by_contra hClean
  have hTotal : ∀ e ∈ A.powersetCard 2, edgeColor e ≠ none := by
    intro e he hNone
    have heParts := Finset.mem_powersetCard.mp he
    apply hClean
    exact Or.inl ⟨e, Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨heParts.1.trans hAV, heParts.2⟩, hNone⟩,
      heParts.1⟩
  have hNoBi : ∀ T ∈ A.powersetCard 3, ¬ IsBicoloredTriangleSupport edgeColor T := by
    intro T hT hBi
    have hTParts := Finset.mem_powersetCard.mp hT
    apply hClean
    exact Or.inr ⟨T, Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨hTParts.1.trans hAV, hTParts.2⟩, hBi⟩,
      hTParts.1⟩
  obtain ⟨c, hc⟩ := clean_partial_coloring_sample_monochromatic A edgeColor
    hq (by omega) hTotal hNoBi
  have hFirst : p.1 ∈ A.powersetCard 2 := Finset.mem_powersetCard.mpr
    ⟨Finset.subset_union_left.trans hUnion, (Finset.mem_powersetCard.mp hpEdges.1).2⟩
  have hSecond : p.2 ∈ A.powersetCard 2 := Finset.mem_powersetCard.mpr
    ⟨Finset.subset_union_right.trans hUnion, (Finset.mem_powersetCard.mp hpEdges.2).2⟩
  exact hpParts.2 ⟨c, hc _ hFirst, hc _ hSecond⟩

/-- The actual discordant-pair count is charged to actual bad samples.
    The common four-set extension degree keeps the estimate integral. -/
theorem discordant_pairs_mul_extensions_le_bad_samples
    [Fintype κ] [Nonempty κ]
    (V : Finset α) (h : ℕ) (edgeColor : Finset α → Option κ)
    (hq : 2 ≤ Fintype.card κ)
    (hSize : max 4 ((Fintype.card κ - 1) ^ 2 + 1) ≤ h)
    (hh : h ≤ V.card) :
    (discordantColorPairs (V.powersetCard 2) edgeColor).card *
      (V.card - 4).choose (h - 4) ≤
        (badPartialColorSamples V h edgeColor).card * (h.choose 2) ^ 2 := by
  classical
  let D := discordantColorPairs (V.powersetCard 2) edgeColor
  let B := badPartialColorSamples V h edgeColor
  have h4 : 4 ≤ h := (le_max_left _ _).trans hSize
  have hLower : ∀ p ∈ D, (V.card - 4).choose (h - 4) ≤
      (B.filter fun A => p.1 ∪ p.2 ⊆ A).card := by
    intro p hp
    have hpParts := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    have he := Finset.mem_powersetCard.mp hpParts.1
    have hf := Finset.mem_powersetCard.mp hpParts.2
    have hUnionV : p.1 ∪ p.2 ⊆ V := Finset.union_subset he.1 hf.1
    have hUnionC : (p.1 ∪ p.2).card ≤ 4 := by
      have := Finset.card_union_le p.1 p.2
      omega
    obtain ⟨T,hUT,hTV,hTc⟩ := Finset.exists_subsuperset_card_eq
      hUnionV hUnionC (by omega : 4 ≤ V.card)
    have hCount : ((V.powersetCard h).filter fun A => T ⊆ A).card =
        (V.card - 4).choose (h - 4) := by
      rw [Finset.card_filter_powersetCard_subset T V h hTV (by omega), hTc]
    rw [← hCount]
    apply Finset.card_le_card
    intro A hA
    have hAParts := Finset.mem_filter.mp hA
    have hUA := hUT.trans hAParts.2
    exact Finset.mem_filter.mpr
      ⟨sample_containing_discordant_pair_is_bad V h edgeColor hq hSize hp hAParts.1 hUA, hUA⟩
  have hUpper : ∀ A ∈ B,
      (D.filter fun p => p.1 ∪ p.2 ⊆ A).card ≤ (h.choose 2) ^ 2 := by
    intro A hA
    have hAc := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hA).1).2
    have hSub : (D.filter fun p => p.1 ∪ p.2 ⊆ A) ⊆
        A.powersetCard 2 ×ˢ A.powersetCard 2 := by
      intro p hp
      have hpFilter := Finset.mem_filter.mp hp
      have hpParts := Finset.mem_product.mp (Finset.mem_filter.mp hpFilter.1).1
      apply Finset.mem_product.mpr
      exact ⟨Finset.mem_powersetCard.mpr
        ⟨Finset.subset_union_left.trans hpFilter.2, (Finset.mem_powersetCard.mp hpParts.1).2⟩,
        Finset.mem_powersetCard.mpr
        ⟨Finset.subset_union_right.trans hpFilter.2, (Finset.mem_powersetCard.mp hpParts.2).2⟩⟩
    have hc := Finset.card_le_card hSub
    simpa only [Finset.card_product, Finset.card_powersetCard, hAc, pow_two] using hc
  have hCount : (∑ p ∈ D, (B.filter fun A => p.1 ∪ p.2 ⊆ A).card) =
      ∑ A ∈ B, (D.filter fun p => p.1 ∪ p.2 ⊆ A).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
  calc
    D.card * (V.card - 4).choose (h - 4) = ∑ _p ∈ D, (V.card - 4).choose (h - 4) := by simp
    _ ≤ ∑ p ∈ D, (B.filter fun A => p.1 ∪ p.2 ⊆ A).card := Finset.sum_le_sum hLower
    _ = ∑ A ∈ B, (D.filter fun p => p.1 ∪ p.2 ⊆ A).card := hCount
    _ ≤ ∑ _A ∈ B, (h.choose 2) ^ 2 := Finset.sum_le_sum hUpper
    _ = B.card * (h.choose 2) ^ 2 := by simp

/-- Quantitative color rigidity, in a denominator-free finite form. This
    directly bounds the exceptions to an actually chosen majority color
    by uncolored edges and fully colored bicolored triangles. -/
theorem exists_majority_color_scaled_exception_bound
    [Fintype κ] [Nonempty κ]
    (V : Finset α) (h : ℕ) (edgeColor : Finset α → Option κ)
    (hq : 2 ≤ Fintype.card κ)
    (hSize : max 4 ((Fintype.card κ - 1) ^ 2 + 1) ≤ h)
    (hh : h ≤ V.card) :
    ∃ c : κ,
      ((V.powersetCard 2).filter fun e => edgeColor e ≠ some c).card *
        V.card.choose 2 * (V.card - 4).choose (h - 4) ≤
      (h.choose 2) ^ 2 *
        ((uncoloredEdgeSupports V edgeColor).card * (V.card - 2).choose (h - 2) +
          (bicoloredTriangleSupports V edgeColor).card * (V.card - 3).choose (h - 3)) := by
  classical
  obtain ⟨c, _, hc⟩ := exists_color_exception_mul_card_le_discordant
    (V.powersetCard 2) Finset.univ edgeColor Finset.univ_nonempty
    (by intro e he c hc; exact Finset.mem_univ c)
  refine ⟨c, ?_⟩
  rw [Finset.card_powersetCard] at hc
  have hInc := discordant_pairs_mul_extensions_le_bad_samples V h edgeColor hq hSize hh
  have h4 : 4 ≤ h := (le_max_left _ _).trans hSize
  have hBad := bad_coloring_samples_card_le V h edgeColor (by omega) (by omega)
  change (badPartialColorSamples V h edgeColor).card ≤ _ at hBad
  calc
    _ ≤ (discordantColorPairs (V.powersetCard 2) edgeColor).card *
        (V.card - 4).choose (h - 4) := Nat.mul_le_mul_right _ hc
    _ ≤ (badPartialColorSamples V h edgeColor).card * (h.choose 2) ^ 2 := hInc
    _ ≤ _ := by nlinarith [Nat.mul_le_mul_right ((h.choose 2) ^ 2) hBad]

end JSP523.Rank5
