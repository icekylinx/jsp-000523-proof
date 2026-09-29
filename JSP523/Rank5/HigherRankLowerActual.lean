import JSP523.Rank5.HigherRankLowerWeighted

/-! # The s=3 weighted bound from both actual core cleanups -/
namespace JSP523.Rank5.HigherRankLower
variable {α : Type*} [DecidableEq α]

theorem bad_incidence_core_mem_powerset
    (K : Family α) (V : Edge α) (n : ℕ) (upper lower : Edge α → α)
    {i : (Edge α × Edge α) × α}
    (hi : i ∈ badIncidences K V (n + 1) upper lower) :
    lowerWitnessCore i ∈ V.powersetCard n := by
  have hA := Finset.mem_powersetCard.mp (Finset.mem_filter.mp hi).2.2.1
  have ha := (Finset.mem_filter.mp hi).2.2.2.1
  refine Finset.mem_powersetCard.mpr
    ⟨(Finset.erase_subset i.2 i.1.2).trans hA.1, ?_⟩
  have hErase := Finset.card_erase_add_one ha
  change (i.1.2.erase i.2).card = n
  omega

theorem bad_incidence_first_root_mem_triple_link
    (K : Family α) (V : Edge α) (n : ℕ) (upper lower : Edge α → α)
    (hUniform : Uniform (n + 3) K) (hAmbient : ∀ E ∈ K, E ⊆ V)
    {i : (Edge α × Edge α) × α}
    (hi : i ∈ badIncidences K V (n + 1) upper lower) :
    lowerWitnessRoot i ∈ parentTripleLink K V (lowerWitnessCore i) := by
  have hSource := (Finset.mem_filter.mp hi).1
  have hE : i.1.1 ∈ K :=
    (Finset.mem_product.mp (Finset.mem_product.mp hSource).1).1
  have hBE : lowerWitnessCore i ⊆ i.1.1 :=
    (Finset.erase_subset i.2 i.1.2).trans (Finset.mem_filter.mp hi).2.1
  have hBc := (Finset.mem_powersetCard.mp
    (bad_incidence_core_mem_powerset K V n upper lower hi)).2
  apply mem_parent_triple_link.mpr
  refine ⟨Finset.sdiff_subset.trans (hAmbient _ hE), ?_, Finset.sdiff_disjoint, ?_⟩
  · change (i.1.1 \ lowerWitnessCore i).card = 3
    rw [Finset.card_sdiff_of_subset hBE, hUniform hE, hBc]
    omega
  · change lowerWitnessCore i ∪ (i.1.1 \ lowerWitnessCore i) ∈ K
    rw [Finset.union_sdiff_of_subset hBE]
    exact hE

theorem bad_incidence_upper_root_mem_pair_link
    (K : Family α) (V : Edge α) (n : ℕ) (upper lower : Edge α → α)
    (hUniform : Uniform (n + 3) K) (hAmbient : ∀ E ∈ K, E ⊆ V)
    {i : (Edge α × Edge α) × α}
    (hi : i ∈ badIncidences K V (n + 1) upper lower) :
    i.1.1 \ i.1.2 ∈ parentPairLink K V i.1.2 := by
  have hSource := (Finset.mem_filter.mp hi).1
  have hE : i.1.1 ∈ K :=
    (Finset.mem_product.mp (Finset.mem_product.mp hSource).1).1
  have hAE := (Finset.mem_filter.mp hi).2.1
  have hAc := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hi).2.2.1).2
  apply mem_parent_pair_link.mpr
  refine ⟨Finset.sdiff_subset.trans (hAmbient _ hE), ?_, Finset.sdiff_disjoint, ?_⟩
  · rw [Finset.card_sdiff_of_subset hAE, hUniform hE, hAc]
    omega
  · rw [Finset.union_sdiff_of_subset hAE]
    exact hE

theorem retained_bad_triple_partners_le
    (K H : Family α) (V : Edge α) (n t u q : ℕ) (lower : Edge α → α)
    (hKH : K ⊆ H)
    (hSurvive : Disjoint K
      (multilevelDeletedEdges H V (V.powersetCard n) 3 u q
        (fun B R T => ¬ ActualStrongPartner H V R T 3 n t (lower B))))
    {B R : Edge α} (hBC : B ∈ V.powersetCard n)
    (hR : R ∈ parentTripleLink K V B) :
    (badTriplePartners H V B R
      (fun B R T => ActualStrongPartner H V R T 3 n t (lower B))).card ≤ q := by
  classical
  let bad := fun B R T => ¬ ActualStrongPartner H V R T 3 n t (lower B)
  have hKeep := retained_core_root_survives_multilevel_cleanup K H V
    (V.powersetCard n) 3 u q bad hKH hSurvive hBC hR
  have hDegree := retained_core_root_parent_degree_ge K H V
    (V.powersetCard n) 3 u q bad hKH hSurvive hBC hR
  have h := retained_tail_exception_degree_le H V B R 3 u q bad
    hKeep.1 hDegree hKeep.2
  simpa only [actualBadPartnerDegree, badTriplePartners, parentTripleLink, bad] using h

/-- Actual upper and lower multilevel cleanup supplies every center and
    partner input of the s=3 witness count. -/
theorem lower_weighted_bound_of_actual_cleanups
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α)
    (n tLower tUpper uLower qLower uUpper qUpper D₄ D₅ Dₙ : ℕ)
    (upper lower : Edge α → α)
    (hI : I ⊆ badIncidences K V (n + 1) upper lower)
    (hKH : K ⊆ H) (hUniform : Uniform (n + 3) K)
    (hAmbient : ∀ E ∈ K, E ⊆ V)
    (hUpper : Disjoint K
      (multilevelDeletedEdges H V (V.powersetCard (n + 1)) 2 uUpper qUpper
        (fun A R T => ¬ ActualStrongPartner H V R T 2 (n + 1) tUpper (upper A))))
    (hLower : Disjoint K
      (multilevelDeletedEdges H V (V.powersetCard n) 3 uLower qLower
        (fun B R T => ¬ ActualStrongPartner H V R T 3 n tLower (lower B))))
    (hUpperGap : qUpper < uUpper) (hLowerGap : qLower < uLower)
    (hRetainUpper : ∀ i ∈ I, 2 * qUpper ≤ (facetParents K i.1.2).card)
    (hRetainLower : ∀ i ∈ I,
      4 * qLower ≤ (parentTripleLink K V (lowerWitnessCore i)).card)
    (ht : 1 ≤ tLower)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄)
    (hDₙ : ∀ S : Edge α, S.card = n + 1 →
      (H.filter fun E => S ⊆ E).card ≤ Dₙ)
    (hD₅ : ∀ S : Edge α, S.card = 5 →
      (H.filter fun E => S ⊆ E).card ≤ D₅) :
    tLower * (∑ i ∈ I, (facetParents K i.1.2).card *
      (parentTripleLink K V (lowerWitnessCore i)).card) ≤
      12 * (V.powersetCard 3).card ^ 2 * D₄ * Dₙ * D₅ := by
  classical
  have hUpperLabels := actual_rank_labels_of_core_cleanup K H V (n + 1) 2
    tUpper uUpper qUpper upper hKH
    (by simpa only [Nat.add_assoc] using hUniform) hAmbient hUpperGap hUpper
  have hLowerLabels := actual_rank_labels_of_core_cleanup K H V n 3
    tLower uLower qLower lower hKH hUniform hAmbient hLowerGap hLower
  apply lower_inheritance_weighted_incidence_bound I K H V n tLower tUpper
    D₄ D₅ Dₙ upper lower hI hKH hUniform hAmbient hUpperLabels hLowerLabels
    ht hD₄ hDₙ hD₅
  · intro i hi
    apply strong_second_roots_half_of_bad_partner_bound K H V n tUpper qUpper
      upper lower hKH hUniform hAmbient (hI hi) (hRetainUpper i hi)
    exact higher_retained_pair_bad_partners_le K H V (V.powersetCard (n + 1))
      uUpper qUpper
      (fun A R T => ActualStrongPartner H V R T 2 (n + 1) tUpper (upper A))
      hKH hUpper (Finset.mem_filter.mp (hI hi)).2.2.1
      (bad_incidence_upper_root_mem_pair_link K V n upper lower hUniform hAmbient (hI hi))
  · intro i hi R hR
    have hBC := bad_incidence_core_mem_powerset K V n upper lower (hI hi)
    have hRoot := bad_incidence_first_root_mem_triple_link K V n upper lower
      hUniform hAmbient (hI hi)
    have hRlink := (Finset.mem_filter.mp (Finset.mem_filter.mp hR).1).1
    exact lower_third_roots_half_of_retained_partner_bounds n K H V tLower qLower
      lower hKH i R (hRetainLower i hi)
      (retained_bad_triple_partners_le K H V n tLower uLower qLower lower hKH hLower hBC hRoot)
      (retained_bad_triple_partners_le K H V n tLower uLower qLower lower hKH hLower hBC hRlink)

end JSP523.Rank5.HigherRankLower
