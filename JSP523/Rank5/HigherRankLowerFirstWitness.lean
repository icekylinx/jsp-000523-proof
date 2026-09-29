import JSP523.Rank5.HigherRankLowerWitness
import JSP523.Rank5.HigherRankFacetRetention
import JSP523.Rank5.HigherRankCoreRetention

/-! # First lower-deletion witnesses from upper-core partners -/
namespace JSP523.Rank5.HigherRankLower
variable {α : Type*} [DecidableEq α]

noncomputable def strongSecondRoots
    (K H : Family α) (V : Edge α) (n tUpper : ℕ)
    (upper : Edge α → α) (i : (Edge α × Edge α) × α) : Family α := by
  classical
  exact (lowerWitnessSecondRoots K V i).filter fun R =>
    ActualStrongPartner H V ((lowerWitnessRoot i).erase i.2)
      (R.erase i.2) 2 (n + 1) tUpper (upper i.1.2)

theorem lower_first_root_erase_eq_upper_root
    (i : (Edge α × Edge α) × α) (ha : i.2 ∈ i.1.2) :
    (lowerWitnessRoot i).erase i.2 = i.1.1 \ i.1.2 := by
  ext x
  by_cases hx : x = i.2
  · subst x
    simp [lowerWitnessRoot, lowerWitnessCore, ha]
  · simp [lowerWitnessRoot, lowerWitnessCore, hx]

noncomputable def upperGoodRetainedPartners
    (K H : Family α) (V : Edge α) (n tUpper : ℕ)
    (upper : Edge α → α) (i : (Edge α × Edge α) × α) : Family α := by
  classical
  exact (parentPairLink K V i.1.2).filter fun Q =>
    ActualStrongPartner H V (i.1.1 \ i.1.2) Q 2 (n + 1) tUpper (upper i.1.2)

/-- Every retained good upper-core partner gives a distinct valid second
    three-root, carrying the different upper label required by IV.9.2. -/
theorem good_upper_partners_inject_into_second_roots
    (K H : Family α) (V : Edge α) (n tUpper : ℕ)
    (upper lower : Edge α → α) (hAmbient : ∀ E ∈ K, E ⊆ V)
    {i : (Edge α × Edge α) × α}
    (hi : i ∈ badIncidences K V (n + 1) upper lower) :
    (upperGoodRetainedPartners K H V n tUpper upper i).card ≤
      (strongSecondRoots K H V n tUpper upper i).card := by
  classical
  have hSource := (Finset.mem_filter.mp hi).1
  have hE : i.1.1 ∈ K :=
    (Finset.mem_product.mp (Finset.mem_product.mp hSource).1).1
  have hAE := (Finset.mem_filter.mp hi).2.1
  have ha := (Finset.mem_filter.mp hi).2.2.2.1
  have haV := hAmbient _ hE (hAE ha)
  have haR : i.2 ∈ lowerWitnessRoot i :=
    Finset.mem_sdiff.mpr ⟨hAE ha, by simp [lowerWitnessCore]⟩
  have hFirstEq := lower_first_root_erase_eq_upper_root i ha
  apply Finset.card_le_card_of_injOn (fun Q => insert i.2 Q)
  · intro Q hQ
    have hQparts := Finset.mem_filter.mp hQ
    have hp := mem_parent_pair_link.mp hQparts.1
    have haQ : i.2 ∉ Q := fun h => (Finset.disjoint_left.mp hp.2.2.1) h ha
    have hLink : insert i.2 Q ∈ parentTripleLink K V (lowerWitnessCore i) := by
      apply mem_parent_triple_link.mpr
      refine ⟨Finset.insert_subset_iff.mpr ⟨haV, hp.1⟩, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem haQ, hp.2.1]
      · apply Finset.disjoint_left.mpr
        intro x hx hxB
        rcases Finset.mem_insert.mp hx with rfl | hxQ
        · exact (Finset.mem_erase.mp hxB).1 rfl
        · exact (Finset.disjoint_left.mp hp.2.2.1) hxQ (Finset.mem_of_mem_erase hxB)
      · have hEq : lowerWitnessCore i ∪ insert i.2 Q = i.1.2 ∪ Q := by
          simp only [lowerWitnessCore, Finset.union_insert, ← Finset.insert_union,
            Finset.insert_erase ha]
        rw [hEq]
        exact hp.2.2.2
    have hInter : lowerWitnessRoot i ∩ insert i.2 Q = {i.2} := by
      ext x
      constructor
      · intro hx
        have hp := Finset.mem_inter.mp hx
        rcases Finset.mem_insert.mp hp.2 with hxa | hxQ
        · exact Finset.mem_singleton.mpr hxa
        · by_cases hxa : x = i.2
          · exact Finset.mem_singleton.mpr hxa
          · have hxRoot : x ∈ i.1.1 \ i.1.2 := by
              rw [← hFirstEq]
              exact Finset.mem_erase.mpr ⟨hxa, hp.1⟩
            exact False.elim ((Finset.disjoint_left.mp hQparts.2.2.1) hxRoot hxQ)
      · intro hx
        rw [Finset.mem_singleton.mp hx]
        exact Finset.mem_inter.mpr ⟨haR, Finset.mem_insert_self _ _⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨hLink, hInter⟩, ?_⟩
    simpa only [hFirstEq, Finset.erase_insert haQ] using hQparts.2
  · intro Q hQ R hR hEq
    have haQ : i.2 ∉ Q := by
      have hp := mem_parent_pair_link.mp (Finset.mem_filter.mp hQ).1
      exact fun h => (Finset.disjoint_left.mp hp.2.2.1) h ha
    have haR : i.2 ∉ R := by
      have hp := mem_parent_pair_link.mp (Finset.mem_filter.mp hR).1
      exact fun h => (Finset.disjoint_left.mp hp.2.2.1) h ha
    have h := congrArg (fun S : Edge α => S.erase i.2) hEq
    simpa only [Finset.erase_insert haQ, Finset.erase_insert haR] using h

/-- The upper-core exception guarantee leaves half of the retained upper
    parents as valid second witnesses. -/
theorem strong_second_roots_half_of_bad_partner_bound
    (K H : Family α) (V : Edge α) (n tUpper q : ℕ)
    (upper lower : Edge α → α) (hKH : K ⊆ H)
    (hUniform : Uniform (n + 3) K) (hAmbient : ∀ E ∈ K, E ⊆ V)
    {i : (Edge α × Edge α) × α}
    (hi : i ∈ badIncidences K V (n + 1) upper lower)
    (hRetained : 2 * q ≤ (facetParents K i.1.2).card)
    (hBad : (badParentPartners H V i.1.2 (i.1.1 \ i.1.2)
      (fun A P Q => ActualStrongPartner H V P Q 2 (n + 1) tUpper
        (upper A))).card ≤ q) :
    (facetParents K i.1.2).card ≤
      2 * (strongSecondRoots K H V n tUpper upper i).card := by
  classical
  let link := parentPairLink K V i.1.2
  let good := fun Q => ActualStrongPartner H V (i.1.1 \ i.1.2) Q
    2 (n + 1) tUpper (upper i.1.2)
  have hBadSub : link.filter (fun Q => ¬ good Q) ⊆
      badParentPartners H V i.1.2 (i.1.1 \ i.1.2)
        (fun A P Q => ActualStrongPartner H V P Q 2 (n + 1) tUpper (upper A)) := by
    intro Q hQ
    have hp := Finset.mem_filter.mp hQ
    have hLink := mem_parent_pair_link.mp hp.1
    exact Finset.mem_filter.mpr ⟨mem_parent_pair_link.mpr
      ⟨hLink.1, hLink.2.1, hLink.2.2.1, hKH hLink.2.2.2⟩, hp.2⟩
  have hB := (Finset.card_le_card hBadSub).trans hBad
  have hPart := Finset.card_filter_add_card_filter_not (s := link) good
  have hAc := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hi).2.2.1).2
  have hEq : link.card = (facetParents K i.1.2).card := by
    exact HigherRankUpper.triple_parent_pair_link_card_eq_codegree (n + 1)
      K V i.1.2 (by simpa only [Nat.add_assoc] using hUniform) hAmbient hAc
  have hGood := good_upper_partners_inject_into_second_roots K H V n tUpper
    upper lower hAmbient hi
  change (link.filter good).card ≤ _ at hGood
  omega

end JSP523.Rank5.HigherRankLower
