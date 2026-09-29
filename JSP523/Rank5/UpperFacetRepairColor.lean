import JSP523.Rank5.RootedPrefixPairLabel

/-! # Parent pair colors after rank-five inheritance repair -/

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α] [Nonempty α]

omit [Nonempty α] in
theorem shared_four_shadow_mono
    {K L : Family α} (hLK : L ⊆ K) :
    sharedFourShadow L ⊆ sharedFourShadow K := by
  classical
  intro A hA
  have hShadow : A ∈ fourShadow K :=
    four_shadow_mono hLK (Finset.mem_filter.mp hA).1
  have hParents : facetParents L A ⊆ facetParents K A := by
    intro E hE
    have h := Finset.mem_filter.mp hE
    exact Finset.mem_filter.mpr ⟨hLK h.1, h.2⟩
  have hMany : 2 ≤ (facetParents K A).card :=
    (Finset.mem_filter.mp hA).2 |>.trans (Finset.card_le_card hParents)
  exact Finset.mem_filter.mpr ⟨hShadow, hMany⟩

/-- Every shared facet left by IV.9 retains the parent IV.8 color on each
    pair of its surviving completions. -/
theorem upper_facet_pair_color_after_inheritance_repair
    (K H : Family α) (V : Edge α) (tUpper : ℕ)
    (tripleLabel : Edge α → α)
    (hKH : K ⊆ H) (hUniformK : Uniform 5 K)
    (hAmbientK : ∀ E ∈ K, E ⊆ V)
    (hSurvive : Disjoint K (upperFacetColorCleanupEdges H V tUpper))
    {A : Edge α} {x y : α}
    (hA : A ∈ sharedFourShadow
      (repairSharedFacetInheritance K
        (upperFacetColorCenter K H V tUpper hKH hUniformK hAmbientK hSurvive)
        tripleLabel))
    (hxy : x ≠ y)
    (hx : insert x A ∈ repairSharedFacetInheritance K
      (upperFacetColorCenter K H V tUpper hKH hUniformK hAmbientK hSurvive)
      tripleLabel)
    (hy : insert y A ∈ repairSharedFacetInheritance K
      (upperFacetColorCenter K H V tUpper hKH hUniformK hAmbientK hSurvive)
      tripleLabel) :
    upperSingletonPairColor H V tUpper x y =
      some (upperFacetColorCenter K H V tUpper
        hKH hUniformK hAmbientK hSurvive A) := by
  classical
  let center := upperFacetColorCenter K H V tUpper
    hKH hUniformK hAmbientK hSurvive
  let L := repairSharedFacetInheritance K center tripleLabel
  have hLK : L ⊆ K := Finset.filter_subset _ _
  have hAK : A ∈ sharedFourShadow K := shared_four_shadow_mono hLK hA
  have hxK : insert x A ∈ K := hLK hx
  have hyK : insert y A ∈ K := hLK hy
  have hxV : x ∈ V := hAmbientK (insert x A) hxK
    (Finset.mem_insert_self x A)
  have hyV : y ∈ V := hAmbientK (insert y A) hyK
    (Finset.mem_insert_self y A)
  have hAc : A.card = 4 := by
    obtain ⟨_, _, _, hCard⟩ :=
      (mem_four_shadow_iff_parent K A).mp (Finset.mem_filter.mp hAK).1
    exact hCard
  have hxNotA : x ∉ A := by
    intro hxA
    have hEq : insert x A = A := Finset.insert_eq_of_mem hxA
    have hFive := hUniformK hxK
    rw [hEq] at hFive
    omega
  have hyNotA : y ∉ A := by
    intro hyA
    have hEq : insert y A = A := Finset.insert_eq_of_mem hyA
    have hFive := hUniformK hyK
    rw [hEq] at hFive
    omega
  have hxC : x ∈ V.filter (fun x => x ∉ A ∧ insert x A ∈ K) :=
    Finset.mem_filter.mpr ⟨hxV, hxNotA, hxK⟩
  have hyC : y ∈ V.filter (fun x => x ∉ A ∧ insert x A ∈ K) :=
    Finset.mem_filter.mpr ⟨hyV, hyNotA, hyK⟩
  exact (upper_facet_color_center_spec K H V tUpper
    hKH hUniformK hAmbientK hSurvive hAK).2 x hxC y hyC hxy

end JSP523.Rank5
