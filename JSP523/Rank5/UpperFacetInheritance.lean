import JSP523.Rank5.InheritanceLowRetention

/-!
# Facet inheritance after the actual upper color cleanup

The IV.8 pair and triangle deletion set supplies the upper strong-partner
condition used by the IV.9 witness count.  This bridge keeps that condition
attached to the center selected by the surviving facet completions.
-/

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α] [Nonempty α]

/-- The IV.9.3 high-retention witness estimate for the center actually
    selected by IV.8 color cleanup. -/
theorem facet_high_retention_weighted_bound_of_color_cleanup
    (K H : Family α) (V : Edge α) (C : Family α)
    (P Q L₃ tLower tUpper u q D₃ D₄ : ℕ)
    (tripleLabel : Edge α → α)
    (hKH : K ⊆ H) (hUniformK : Uniform 5 K)
    (hAmbientK : ∀ E ∈ K, E ⊆ V)
    (hUpperSurvive : Disjoint K
      (upperFacetColorCleanupEdges H V tUpper))
    (hQ : 0 < Q)
    (hScale : Q * L₃ ≤ P * u) (hq : 4 * q ≤ L₃)
    (hC : ∀ i ∈ highRetentionBadIncidences K H V P Q
      (upperFacetColorCenter K H V tUpper hKH hUniformK hAmbientK hUpperSurvive)
      tripleLabel, facetWitnessCore i ∈ C)
    (hLowerSurvive : Disjoint K
      (multilevelDeletedEdges H V C 2 u q
        (fun B R T => ¬ ActualStrongPartner H V R T 2 3 tLower
          (tripleLabel B))))
    (hTripleLabels : ActualTripleLabels K tripleLabel)
    (ht : 1 ≤ tLower)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D₃)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄) :
    tLower * (∑ i ∈ highRetentionBadIncidences K H V P Q
      (upperFacetColorCenter K H V tUpper hKH hUniformK hAmbientK hUpperSurvive)
      tripleLabel,
        (facetParents K i.1.2).card *
          (parentPairLink K V (facetWitnessCore i)).card) ≤
      8 * (V.powersetCard 2).card ^ 2 * D₃ * D₄ * D₄ := by
  let center := upperFacetColorCenter K H V tUpper
    hKH hUniformK hAmbientK hUpperSurvive
  let I := highRetentionBadIncidences K H V P Q center tripleLabel
  have hI : I ⊆ facetBadIncidences K V center tripleLabel :=
    high_retention_bad_incidence_subset K H V P Q center tripleLabel
  have hCenter : ∀ A ∈ sharedFourShadow K, center A ∈ A := by
    intro A hA
    exact (upper_facet_color_center_spec K H V tUpper
      hKH hUniformK hAmbientK hUpperSurvive hA).1
  have hStrong := facet_upper_strong_of_actual_facet_color_cleanup
    I K H V tUpper tripleLabel hKH hUniformK hAmbientK hUpperSurvive hI
  have hParent : ∀ i ∈ I,
      u ≤ (actualCoreLink H V (facetWitnessCore i) 2).card := by
    intro i hi
    exact retained_pair_root_parent_degree_ge K H V C u q
      (fun B R T => ¬ ActualStrongPartner H V R T 2 3 tLower
        (tripleLabel B)) hKH hLowerSurvive (hC i hi)
      (facet_bad_incidence_first_root_mem_pair_link K V center tripleLabel
        hUniformK hAmbientK (hI hi))
  have hMinTriple : ∀ i ∈ I,
      Q * L₃ ≤ P * (H.filter fun E => facetWitnessCore i ⊆ E).card := by
    intro i hi
    have hLink := hParent i hi
    rw [actual_core_link_two_eq_parent_pair_link] at hLink
    have hLinkCount : (parentPairLink H V (facetWitnessCore i)).card ≤
        (H.filter fun E => facetWitnessCore i ⊆ E).card := by
      exact JSP523.Counting.parent_pair_link_card_le_codegree H V (facetWitnessCore i)
    exact hScale.trans (Nat.mul_le_mul_left P (hLink.trans hLinkCount))
  have hRetained := (high_retention_bad_incidence_degrees K H V P Q
    0 L₃ center tripleLabel hQ hUniformK hAmbientK
    (by intro i hi; simp) hMinTriple).2
  have hDegree : ∀ i ∈ I,
      u ≤ (actualCoreLink H V (facetWitnessCore i) 2).card ∧
      4 * q ≤ (parentPairLink K V (facetWitnessCore i)).card := by
    intro i hi
    exact ⟨hParent i hi, hq.trans (hRetained i hi)⟩
  exact facet_inheritance_weighted_incidence_bound_of_cleanup
    I K H V C tLower tUpper u q D₃ D₄ center tripleLabel
    hI hKH hUniformK hAmbientK hCenter hTripleLabels
    hStrong hDegree hC hLowerSurvive ht hD₃ hD₄

/-- The full facet inheritance incidence budget, with both IV.9
    low-retention classes and the IV.8 center chosen from the actual
    surviving completion colors. -/
theorem facet_bad_incidence_budget_of_color_cleanup
    (K H : Family α) (V : Edge α) (C : Family α)
    (P Q L₃ tLower tUpper u q D₃ D₄ : ℕ)
    (tripleLabel : Edge α → α)
    (hKH : K ⊆ H) (hUniformK : Uniform 5 K)
    (hUniformH : Uniform 5 H)
    (hAmbientH : ∀ E ∈ H, E ⊆ V)
    (hUpperSurvive : Disjoint K
      (upperFacetColorCleanupEdges H V tUpper))
    (hQ : 0 < Q)
    (hScale : Q * L₃ ≤ P * u) (hq : 4 * q ≤ L₃)
    (hC : ∀ i ∈ highRetentionBadIncidences K H V P Q
      (upperFacetColorCenter K H V tUpper hKH hUniformK
        (fun E hE => hAmbientH E (hKH hE)) hUpperSurvive)
      tripleLabel, facetWitnessCore i ∈ C)
    (hLowerSurvive : Disjoint K
      (multilevelDeletedEdges H V C 2 u q
        (fun B R T => ¬ ActualStrongPartner H V R T 2 3 tLower
          (tripleLabel B))))
    (hTripleLabels : ActualTripleLabels K tripleLabel)
    (ht : 1 ≤ tLower)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D₃)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄) :
    Q * (tLower * (2 * L₃) *
      (facetBadIncidences K V
        (upperFacetColorCenter K H V tUpper hKH hUniformK
          (fun E hE => hAmbientH E (hKH hE)) hUpperSurvive)
        tripleLabel).card) ≤
      tLower * (2 * L₃) * (40 * P * H.card) +
        Q * (8 * (V.powersetCard 2).card ^ 2 * D₃ * D₄ * D₄) := by
  let hAmbientK : ∀ E ∈ K, E ⊆ V :=
    fun E hE => hAmbientH E (hKH hE)
  let center := upperFacetColorCenter K H V tUpper
    hKH hUniformK hAmbientK hUpperSurvive
  have hDegreeFacet : ∀ i ∈ highRetentionBadIncidences K H V P Q
      center tripleLabel, 2 ≤ (facetParents K i.1.2).card := by
    intro i hi
    have hBad := high_retention_bad_incidence_subset K H V P Q center tripleLabel hi
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hBad).2.2.1).2
  have hMinTriple : ∀ i ∈ highRetentionBadIncidences K H V P Q
      center tripleLabel,
      Q * L₃ ≤ P * (H.filter fun E => facetWitnessCore i ⊆ E).card := by
    intro i hi
    have hBad := high_retention_bad_incidence_subset K H V P Q center tripleLabel hi
    have hRoot := facet_bad_incidence_first_root_mem_pair_link K V center tripleLabel
      hUniformK hAmbientK hBad
    have hDegree := retained_pair_root_parent_degree_ge K H V C u q
      (fun B R T => ¬ ActualStrongPartner H V R T 2 3 tLower
        (tripleLabel B)) hKH hLowerSurvive (hC i hi) hRoot
    rw [actual_core_link_two_eq_parent_pair_link] at hDegree
    exact hScale.trans (Nat.mul_le_mul_left P (hDegree.trans
      (JSP523.Counting.parent_pair_link_card_le_codegree H V (facetWitnessCore i))))
  have hDegreeTriple := (high_retention_bad_incidence_degrees K H V P Q
    0 L₃ center tripleLabel hQ hUniformK hAmbientK
    (by intro i hi; simp) hMinTriple).2
  have hWeighted := facet_high_retention_weighted_bound_of_color_cleanup
    K H V C P Q L₃ tLower tUpper u q D₃ D₄ tripleLabel
    hKH hUniformK hAmbientK hUpperSurvive hQ hScale hq
    hC hLowerSurvive hTripleLabels ht hD₃ hD₄
  exact facet_bad_incidence_combined_budget K H V P Q tLower
    2 L₃ D₃ D₄ center tripleLabel hKH hUniformK hUniformH
    hAmbientH hDegreeFacet hDegreeTriple hWeighted

/-- With the actual triple-core cleanup, every structural and label
    premise of the facet incidence budget follows from survival. -/
theorem facet_bad_incidence_budget_of_actual_cleanups
    (K H : Family α) (V : Edge α)
    (P Q L₃ tLower tUpper u q D₃ D₄ : ℕ)
    (tripleLabel : Edge α → α)
    (hKH : K ⊆ H) (hUniformK : Uniform 5 K)
    (hUniformH : Uniform 5 H)
    (hAmbientH : ∀ E ∈ H, E ⊆ V)
    (hUpperSurvive : Disjoint K
      (upperFacetColorCleanupEdges H V tUpper))
    (hQ : 0 < Q)
    (hScale : Q * L₃ ≤ P * u) (hq : 4 * q ≤ L₃)
    (hLowerSurvive : Disjoint K
      (multilevelDeletedEdges H V (V.powersetCard 3) 2 u q
        (fun B R T => ¬ ActualStrongPartner H V R T 2 3 tLower
          (tripleLabel B))))
    (hqu : q < u)
    (ht : 1 ≤ tLower)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D₃)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄) :
    Q * (tLower * (2 * L₃) *
      (facetBadIncidences K V
        (upperFacetColorCenter K H V tUpper hKH hUniformK
          (fun E hE => hAmbientH E (hKH hE)) hUpperSurvive)
        tripleLabel).card) ≤
      tLower * (2 * L₃) * (40 * P * H.card) +
        Q * (8 * (V.powersetCard 2).card ^ 2 * D₃ * D₄ * D₄) := by
  let hAmbientK : ∀ E ∈ K, E ⊆ V := fun E hE => hAmbientH E (hKH hE)
  let center := upperFacetColorCenter K H V tUpper
    hKH hUniformK hAmbientK hUpperSurvive
  have hLabels := actual_triple_labels_of_multilevel_cleanup K H V
    tLower u q tripleLabel hKH hUniformK hAmbientK hqu hLowerSurvive
  have hC : ∀ i ∈ highRetentionBadIncidences K H V P Q center tripleLabel,
      facetWitnessCore i ∈ V.powersetCard 3 := by
    intro i hi
    have hBad := high_retention_bad_incidence_subset K H V P Q center tripleLabel hi
    have hSource := (Finset.mem_filter.mp hBad).1
    have hFace := Finset.mem_powersetCard.mp
      (Finset.mem_product.mp (Finset.mem_product.mp hSource).1).2
    have ha := (Finset.mem_filter.mp hBad).2.2.2.1
    apply Finset.mem_powersetCard.mpr
    refine ⟨(Finset.erase_subset _ _).trans hFace.1, ?_⟩
    have hErase := Finset.card_erase_add_one ha
    change (i.1.2.erase i.2).card = 3
    omega
  exact facet_bad_incidence_budget_of_color_cleanup K H V (V.powersetCard 3)
    P Q L₃ tLower tUpper u q D₃ D₄ tripleLabel
    hKH hUniformK hUniformH hAmbientH hUpperSurvive
    hQ hScale hq hC hLowerSurvive hLabels ht hD₃ hD₄


omit [Nonempty α] in
/-- Every edge removed in the shared-facet inheritance repair is the first
    projection of an actual bad incidence. -/
theorem bad_facet_parent_edges_subset_incidence_projection
    (K : Family α) (V : Edge α)
    (facetCenter tripleLabel : Edge α → α)
    (hAmbient : ∀ E ∈ K, E ⊆ V) :
    badFacetParentEdges K facetCenter tripleLabel ⊆
      (facetBadIncidences K V facetCenter tripleLabel).image
        (fun i : (Edge α × Edge α) × α => i.1.1) := by
  classical
  intro E hE
  obtain ⟨hEK, A, hAE, hShared, a, ha, haCenter, hMismatch⟩ :=
    Finset.mem_filter.mp hE
  obtain ⟨_, _, _, hAcard⟩ :=
    (mem_four_shadow_iff_parent K A).mp
      (Finset.mem_filter.mp hShared).1
  have hAV : A ⊆ V := hAE.trans (hAmbient E hEK)
  have haV : a ∈ V := hAV ha
  apply Finset.mem_image.mpr
  refine ⟨((E, A), a), ?_, rfl⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr
    ⟨hEK, Finset.mem_powersetCard.mpr ⟨hAV, hAcard⟩⟩,
    haV⟩, hAE, hShared, ha, haCenter, ?_⟩
  exact hMismatch

omit [Nonempty α] in
/-- Counting incidences also pays for every parent edge removed by the
    exact IV.9 shared-facet inheritance repair. -/
theorem bad_facet_parent_edges_card_le_incidences
    (K : Family α) (V : Edge α)
    (facetCenter tripleLabel : Edge α → α)
    (hAmbient : ∀ E ∈ K, E ⊆ V) :
    (badFacetParentEdges K facetCenter tripleLabel).card ≤
      (facetBadIncidences K V facetCenter tripleLabel).card := by
  calc
    _ ≤ ((facetBadIncidences K V facetCenter tripleLabel).image
          (fun i : (Edge α × Edge α) × α => i.1.1)).card :=
      Finset.card_le_card
        (bad_facet_parent_edges_subset_incidence_projection
          K V facetCenter tripleLabel hAmbient)
    _ ≤ _ := Finset.card_image_le

end JSP523.Rank5
