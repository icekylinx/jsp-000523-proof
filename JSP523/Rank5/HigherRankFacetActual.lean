import JSP523.Rank5.HigherRankFacetWitness
import JSP523.Rank5.HigherRankPartnerRetention

/-! # Actual cleanup interfaces for arbitrary-rank facet witnesses -/
namespace JSP523.Rank5.HigherRankUpper
variable {α : Type*} [DecidableEq α] (n : ℕ)

theorem facet_bad_incidence_first_root_mem_pair_link
    (K : Family α) (V : Edge α)
    (facetCenter tripleLabel : Edge α → α)
    (hUniformK : Uniform (n + 2) K)
    (hAmbientK : ∀ E ∈ K, E ⊆ V)
    {i : (Edge α × Edge α) × α}
    (hi : i ∈ facetBadIncidences K V (n + 1) facetCenter tripleLabel) :
    facetWitnessRoot i ∈ parentPairLink K V (facetWitnessCore i) := by
  classical
  have hSource := (Finset.mem_filter.mp hi).1
  have hE : i.1.1 ∈ K :=
    (Finset.mem_product.mp (Finset.mem_product.mp hSource).1).1
  have hAcard : i.1.2.card = n + 1 :=
    (Finset.mem_powersetCard.mp
      (Finset.mem_product.mp (Finset.mem_product.mp hSource).1).2).2
  have hAE : i.1.2 ⊆ i.1.1 := (Finset.mem_filter.mp hi).2.1
  have ha : i.2 ∈ i.1.2 := (Finset.mem_filter.mp hi).2.2.2.1
  have hBE : facetWitnessCore i ⊆ i.1.1 :=
    (Finset.erase_subset i.2 i.1.2).trans hAE
  have hBcard : (facetWitnessCore i).card = n := by
    have hErase := Finset.card_erase_add_one ha
    change (i.1.2.erase i.2).card = n
    omega
  have hRcard : (facetWitnessRoot i).card = 2 := by
    change (i.1.1 \ facetWitnessCore i).card = 2
    rw [Finset.card_sdiff_of_subset hBE, hUniformK hE]
    omega
  have hRecon : facetWitnessCore i ∪ facetWitnessRoot i = i.1.1 :=
    Finset.union_sdiff_of_subset hBE
  exact mem_parent_pair_link.mpr
    ⟨Finset.sdiff_subset.trans (hAmbientK i.1.1 hE),
      hRcard, Finset.sdiff_disjoint, hRecon.symm ▸ hE⟩

theorem facet_bad_incidence_roots_survive_multilevel_cleanup
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (C : Family α)
    (u q : ℕ) (bad : Edge α → Edge α → Edge α → Prop)
    (facetCenter tripleLabel : Edge α → α)
    (hI : I ⊆ facetBadIncidences K V (n + 1) facetCenter tripleLabel)
    (hKH : K ⊆ H) (hUniformK : Uniform (n + 2) K)
    (hAmbientK : ∀ E ∈ K, E ⊆ V)
    (hC : ∀ i ∈ I, facetWitnessCore i ∈ C)
    (hSurvive : Disjoint K (multilevelDeletedEdges H V C 2 u q bad)) :
    ∀ i ∈ I,
      ∀ R ∈ insert (facetWitnessRoot i) (facetWitnessSecondRoots K V i),
        R ∈ actualCoreLink H V (facetWitnessCore i) 2 ∧
          R ∉ cleanupTails H V (facetWitnessCore i) 2 u q bad := by
  intro i hi R hR
  have hRoot : R ∈ parentPairLink K V (facetWitnessCore i) := by
    rcases Finset.mem_insert.mp hR with rfl | hSecond
    · exact facet_bad_incidence_first_root_mem_pair_link n K V
        facetCenter tripleLabel hUniformK hAmbientK (hI hi)
    · exact (Finset.mem_filter.mp hSecond).1
  exact retained_pair_root_survives_multilevel_cleanup K H V C
    u q bad hKH hSurvive (hC i hi) hRoot

theorem facet_second_root_upper_completion_vertices
    (K : Family α) (V : Edge α)
    (facetCenter tripleLabel : Edge α → α)
    (hUniformK : Uniform (n + 2) K)
    (hAmbientK : ∀ E ∈ K, E ⊆ V)
    {i : (Edge α × Edge α) × α}
    (hi : i ∈ facetBadIncidences K V (n + 1) facetCenter tripleLabel)
    {R₁ : Edge α} (hR₁ : R₁ ∈ facetWitnessSecondRoots K V i) :
    ∃ x y : α,
      x ≠ y ∧
      (facetWitnessRoot i).erase i.2 = {x} ∧
      R₁.erase i.2 = {y} ∧
      x ∈ V.filter (fun w => w ∉ i.1.2 ∧ insert w i.1.2 ∈ K) ∧
      y ∈ V.filter (fun w => w ∉ i.1.2 ∧ insert w i.1.2 ∈ K) := by
  classical
  let A := i.1.2
  let a := i.2
  let B := facetWitnessCore i
  let R₀ := facetWitnessRoot i
  have hSource := (Finset.mem_filter.mp hi).1
  have hE : i.1.1 ∈ K :=
    (Finset.mem_product.mp (Finset.mem_product.mp hSource).1).1
  have haA : a ∈ A := (Finset.mem_filter.mp hi).2.2.2.1
  have hAeq : A = B ∪ {a} := by
    change i.1.2 = (i.1.2.erase a) ∪ {a}
    simpa [Finset.union_singleton] using (Finset.insert_erase haA).symm
  have hBE : B ⊆ i.1.1 :=
    (Finset.erase_subset a i.1.2).trans (Finset.mem_filter.mp hi).2.1
  have hEeq : i.1.1 = B ∪ R₀ :=
    (Finset.union_sdiff_of_subset hBE).symm
  have hR₀link := facet_bad_incidence_first_root_mem_pair_link n K V
    facetCenter tripleLabel hUniformK hAmbientK hi
  have hR₁link : R₁ ∈ parentPairLink K V B :=
    (Finset.mem_filter.mp hR₁).1
  have hR₀parts := mem_parent_pair_link.mp hR₀link
  have hR₁parts := mem_parent_pair_link.mp hR₁link
  have hInter : R₀ ∩ R₁ = {a} := (Finset.mem_filter.mp hR₁).2
  have haR₀ : a ∈ R₀ := by
    have h : a ∈ R₀ ∩ R₁ := by rw [hInter]; simp
    exact (Finset.mem_inter.mp h).1
  have haR₁ : a ∈ R₁ := by
    have h : a ∈ R₀ ∩ R₁ := by rw [hInter]; simp
    exact (Finset.mem_inter.mp h).2
  have hR₀erase : (R₀.erase a).card = 1 := by
    have hCard := Finset.card_erase_add_one haR₀
    have hTwo : R₀.card = 2 := hR₀parts.2.1
    omega
  have hR₁erase : (R₁.erase a).card = 1 := by
    have hCard := Finset.card_erase_add_one haR₁
    have hTwo : R₁.card = 2 := hR₁parts.2.1
    omega
  obtain ⟨x, hxEq⟩ := Finset.card_eq_one.mp hR₀erase
  obtain ⟨y, hyEq⟩ := Finset.card_eq_one.mp hR₁erase
  have hxR₀ : x ∈ R₀ := by
    have hx : x ∈ R₀.erase a := by rw [hxEq]; simp
    exact Finset.mem_of_mem_erase hx
  have hyR₁ : y ∈ R₁ := by
    have hy : y ∈ R₁.erase a := by rw [hyEq]; simp
    exact Finset.mem_of_mem_erase hy
  have hxa : x ≠ a := by
    have hx : x ∈ R₀.erase a := by rw [hxEq]; simp
    exact (Finset.mem_erase.mp hx).1
  have hya : y ≠ a := by
    have hy : y ∈ R₁.erase a := by rw [hyEq]; simp
    exact (Finset.mem_erase.mp hy).1
  have hxy : x ≠ y := by
    intro h
    have hxInter : x ∈ R₀ ∩ R₁ :=
      Finset.mem_inter.mpr ⟨hxR₀, h ▸ hyR₁⟩
    have hxa' : x = a := by
      rw [hInter] at hxInter
      exact Finset.mem_singleton.mp hxInter
    exact hxa hxa'
  have hxNotA : x ∉ A := by
    rw [hAeq]
    intro hx
    rcases Finset.mem_union.mp hx with hxB | hxa'
    · exact (Finset.disjoint_left.mp hR₀parts.2.2.1) hxR₀ hxB
    · exact hxa (Finset.mem_singleton.mp hxa')
  have hyNotA : y ∉ A := by
    rw [hAeq]
    intro hy
    rcases Finset.mem_union.mp hy with hyB | hya'
    · exact (Finset.disjoint_left.mp hR₁parts.2.2.1) hyR₁ hyB
    · exact hya (Finset.mem_singleton.mp hya')
  have hR₀eq : R₀ = {a, x} := by
    have hIns := Finset.insert_erase haR₀
    rw [hxEq] at hIns
    simpa [Finset.insert_comm] using hIns.symm
  have hR₁eq : R₁ = {a, y} := by
    have hIns := Finset.insert_erase haR₁
    rw [hyEq] at hIns
    simpa [Finset.insert_comm] using hIns.symm
  have hEx : insert x A ∈ K := by
    have hRecon : insert x A = i.1.1 := by
      rw [hAeq, hEeq, hR₀eq]
      ext v
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
      tauto
    exact hRecon.symm ▸ hE
  have hEy : insert y A ∈ K := by
    have hRecon : insert y A = B ∪ R₁ := by
      rw [hAeq, hR₁eq]
      ext v
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
      tauto
    exact hRecon.symm ▸ hR₁parts.2.2.2
  refine ⟨x, y, hxy, hxEq, hyEq, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨hR₀parts.1 hxR₀, hxNotA, hEx⟩
  · exact Finset.mem_filter.mpr ⟨hR₁parts.1 hyR₁, hyNotA, hEy⟩

theorem facet_upper_strong_of_actual_facet_color_cleanup
    [Nonempty α]
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (tUpper : ℕ)
    (tripleLabel : Edge α → α)
    (hKH : K ⊆ H) (hUniformK : Uniform (n + 2) K)
    (hAmbientK : ∀ E ∈ K, E ⊆ V)
    (hSurvive : Disjoint K
      (upperFacetColorCleanupEdges (n + 1) H V tUpper))
    (hI : I ⊆ facetBadIncidences K V (n + 1)
      (facetColorCenter K H V (n + 1) tUpper hKH hSurvive)
      tripleLabel) :
    ∀ i ∈ I,
      ∀ R₁ ∈ facetWitnessSecondRoots K V i,
        ActualStrongPartner H V
          ((facetWitnessRoot i).erase i.2) (R₁.erase i.2)
          1 (n + 1) tUpper
            (facetColorCenter K H V (n + 1) tUpper hKH hSurvive i.1.2) := by
  classical
  intro i hi R₁ hR₁
  let center := facetColorCenter K H V (n + 1) tUpper hKH hSurvive
  have hBad := hI hi
  have hShared : i.1.2 ∈ sharedFacets K V (n + 1) :=
    (Finset.mem_filter.mp hBad).2.2.1
  obtain ⟨x, y, hxy, hxEq, hyEq, hxS, hyS⟩ :=
    facet_second_root_upper_completion_vertices n K V center
      tripleLabel hUniformK hAmbientK hBad hR₁
  have hCenter := facet_color_center_spec K H V (n + 1) tUpper hKH hSurvive hShared
  have hColor := hCenter.2 x hxS y hyS hxy
  have hxV : x ∈ V := (Finset.mem_filter.mp hxS).1
  have hyV : y ∈ V := (Finset.mem_filter.mp hyS).1
  have hStrong := (upper_singleton_pair_color_eq_some_iff_strong
    (n + 1) H V tUpper hxV hyV hxy).mp hColor
  simpa [hxEq, hyEq, center] using hStrong

theorem facet_bad_incidence_core_mem_powerset
    (K : Family α) (V : Edge α) (center lower : Edge α → α)
    {i : (Edge α × Edge α) × α}
    (hi : i ∈ facetBadIncidences K V (n + 1) center lower) :
    facetWitnessCore i ∈ V.powersetCard n := by
  have hSource := (Finset.mem_filter.mp hi).1
  have hA := Finset.mem_powersetCard.mp
    (Finset.mem_product.mp (Finset.mem_product.mp hSource).1).2
  have ha := (Finset.mem_filter.mp hi).2.2.2.1
  apply Finset.mem_powersetCard.mpr
  refine ⟨(Finset.erase_subset i.2 i.1.2).trans hA.1, ?_⟩
  have hErase := Finset.card_erase_add_one ha
  change (i.1.2.erase i.2).card = n
  omega

/-- The complete arbitrary-rank s=2 weighted incidence estimate after
    actual color and lower-partner cleanup. Retention is the only
    remaining incidence-dependent numerical premise. -/
theorem facet_weighted_bound_of_actual_cleanups [Nonempty α]
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (tLower tUpper u q D₃ D₄ Dₙ : ℕ)
    (lower : Edge α → α)
    (hKH : K ⊆ H) (hUniformK : Uniform (n + 2) K)
    (hAmbientK : ∀ E ∈ K, E ⊆ V)
    (hUpper : Disjoint K (upperFacetColorCleanupEdges (n + 1) H V tUpper))
    (hI : I ⊆ facetBadIncidences K V (n + 1)
      (facetColorCenter K H V (n + 1) tUpper hKH hUpper) lower)
    (hLower : Disjoint K
      (multilevelDeletedEdges H V (V.powersetCard n) 2 u q
        (fun B R T => ¬ ActualStrongPartner H V R T 2 n tLower (lower B))))
    (hqu : q < u) (ht : 1 ≤ tLower)
    (hRetained : ∀ i ∈ I,
      4 * q ≤ (parentPairLink K V (facetWitnessCore i)).card)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D₃)
    (hDₙ : ∀ S : Edge α, S.card = n + 1 →
      (H.filter fun E => S ⊆ E).card ≤ Dₙ)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄) :
    tLower * (∑ i ∈ I,
      (facetParents K i.1.2).card *
        (parentPairLink K V (facetWitnessCore i)).card) ≤
      8 * (V.powersetCard 2).card ^ 2 * D₃ * Dₙ * D₄ := by
  let center := facetColorCenter K H V (n + 1) tUpper hKH hUpper
  let bad := fun B R T => ¬ ActualStrongPartner H V R T 2 n tLower (lower B)
  have hC : ∀ i ∈ I, facetWitnessCore i ∈ V.powersetCard n := by
    intro i hi
    exact facet_bad_incidence_core_mem_powerset n K V center lower (hI hi)
  have hKeep := facet_bad_incidence_roots_survive_multilevel_cleanup n
    I K H V (V.powersetCard n) u q bad center lower hI hKH hUniformK
    hAmbientK hC hLower
  have hDegree : ∀ i ∈ I,
      u ≤ (actualCoreLink H V (facetWitnessCore i) 2).card ∧
      4 * q ≤ (parentPairLink K V (facetWitnessCore i)).card := by
    intro i hi
    refine ⟨?_, hRetained i hi⟩
    exact retained_pair_root_parent_degree_ge K H V (V.powersetCard n) u q bad
      hKH hLower (hC i hi)
      (facet_bad_incidence_first_root_mem_pair_link n K V center lower
        hUniformK hAmbientK (hI hi))
  have hLabels : ActualRankLabels K n lower := by
    have h := higher_actual_rank_labels_of_multilevel_cleanup K H V (n + 2)
      tLower u q (by omega) lower hKH hUniformK hAmbientK hqu
      (by simpa only [show n + 2 - 2 = n by omega] using hLower)
    simpa only [show n + 2 - 2 = n by omega] using h
  have hStrong := facet_upper_strong_of_actual_facet_color_cleanup n
    I K H V tUpper lower hKH hUniformK hAmbientK hUpper hI
  exact facet_inheritance_weighted_incidence_bound n I K H V
    tLower tUpper u q D₃ D₄ Dₙ center lower hI hKH hUniformK hAmbientK
    (fun A hA => (facet_color_center_spec K H V (n + 1) tUpper hKH hUpper hA).1)
    hLabels hStrong hDegree hKeep ht hD₃ hDₙ hD₄

end JSP523.Rank5.HigherRankUpper
