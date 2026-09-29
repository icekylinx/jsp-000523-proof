import JSP523.Rank5.UpperFacetPairLabel
import JSP523.Rank5.LowerPartnerRetention
import JSP523.Counting.AssignedPrefixGeometry

/-!
# The actual rank-five rooted prefix inequality

The pair-prefix geometry and its parent pair labels are now constructed
from the IV.8 color cleanup and IV.9 repaired family. Only the lower-core
partner guarantee and ordinary codegree caps enter as numerical inputs.
-/

namespace JSP523.Rank5

open JSP523.Counting

variable {α : Type*} [DecidableEq α] [Nonempty α]

theorem rooted_prefix_bound_after_color_inheritance_repair
    (K H : Family α) (V : Edge α) (tUpper D D₄ : ℕ) (ε : ℝ)
    (tripleLabel : Edge α → α)
    (hAdmH : Admissible H)
    (hKH : K ⊆ H) (hUniformK : Uniform 5 K)
    (hAmbientK : ∀ E ∈ K, E ⊆ V)
    (hUpperSurvive : Disjoint K
      (upperFacetColorCleanupEdges H V tUpper))
    (hD₄pos : 1 ≤ D₄) (hε : 0 ≤ ε)
    (good : Edge α → Edge α → Edge α → Prop)
    (label : Edge α → Edge α → α)
    (hGoodCenter : ∀ A S T, good A S T →
      label S T = tripleLabel A)
    (hLabel : GoodPairLabelValid H V good label)
    (hBad : ∀ P ∈ V.powersetCard 3,
      ∀ Y ∈ chosenPrefixesAt
        (rootedEdges
          (repairSharedFacetInheritance K
            (upperFacetColorCenter K H V tUpper hKH hUniformK
              hAmbientK hUpperSurvive) tripleLabel)
          tripleLabel)
        V 2 (rootedChosenPairPrefix tripleLabel) P,
      ∀ x ∈ P,
        ((badParentPartners H V (Y ∪ {x}) (P.erase x) good).card : ℝ) ≤
          ε * ((parentPairLink H V (Y ∪ {x})).card : ℝ))
    (hD : ∀ A : Edge α, A.card = 3 →
      (H.filter (fun E => A ⊆ E)).card ≤ D)
    (hD₄ : ∀ Q : Edge α, Q.card = 4 →
      ((repairSharedFacetInheritance K
        (upperFacetColorCenter K H V tUpper hKH hUniformK
          hAmbientK hUpperSurvive) tripleLabel).filter
        (fun E => Q ⊆ E)).card ≤ D₄) :
    let L := repairSharedFacetInheritance K
      (upperFacetColorCenter K H V tUpper hKH hUniformK
        hAmbientK hUpperSurvive) tripleLabel
    ((rootedEdges L tripleLabel).card : ℝ) ^ 2 ≤
      (V.card.choose 3 : ℝ) *
        (((1 + 2 * (D₄ - 1) : ℕ) : ℝ) *
          ((rootedEdges L tripleLabel).card : ℝ) +
          ((V.card.choose 2 * (V.card - 2).choose 2 : ℕ) : ℝ) *
            max 7 (1 + ε * (D : ℝ))) := by
  classical
  let center := upperFacetColorCenter K H V tUpper
    hKH hUniformK hAmbientK hUpperSurvive
  let L := repairSharedFacetInheritance K center tripleLabel
  let R := rootedEdges L tripleLabel
  have hLK : L ⊆ K := Finset.filter_subset _ _
  have hRL : R ⊆ L := rooted_edges_subset L tripleLabel
  have hRH : R ⊆ H := hRL.trans (hLK.trans hKH)
  have hUniformR : Uniform 5 R := by
    intro E hE
    exact hUniformK (hLK (hRL hE))
  have hGroundR : ∀ E ∈ R, E ⊆ V := by
    intro E hE
    exact hAmbientK E (hLK (hRL hE))
  have hPrefix := rooted_chosen_pair_prefix_sub_card L tripleLabel
    (by intro E hE; exact hUniformK (hLK hE))
  have hPair : ∀ Y ∈ V.powersetCard (5 - 3),
      PairCompletionLabelInPrefix
        (R.filter (fun E => rootedChosenPairPrefix tripleLabel E = Y))
        (upperUnorderedPairLabel H V tUpper) Y := by
    intro Y hY
    exact rooted_pair_label_in_prefix_after_color_repair
      K H V tUpper tripleLabel Y hKH hUniformK hAmbientK hUpperSurvive
  have hCenter := rooted_chosen_pair_prefix_triple_centers
    L V tripleLabel (by intro E hE; exact hUniformK (hLK hE))
  have hCenter' : ∀ P ∈ V.powersetCard 3,
      ∀ Y ∈ chosenPrefixesAt R V (5 - 3)
        (rootedChosenPairPrefix tripleLabel) P,
      ∀ x ∈ P, tripleLabel (Y ∪ {x}) ∈ Y := by
    simpa only [show 5 - 3 = 2 by omega] using hCenter
  have hD₄R : ∀ Q : Edge α, Q.card = 4 →
      (R.filter fun E => Q ⊆ E).card ≤ D₄ := by
    intro Q hQc
    have hSub : (R.filter fun E => Q ⊆ E) ⊆
        (L.filter fun E => Q ⊆ E) := by
      intro E hE
      exact Finset.mem_filter.mpr
        ⟨hRL (Finset.mem_filter.mp hE).1,
          (Finset.mem_filter.mp hE).2⟩
    exact (Finset.card_le_card hSub).trans (hD₄ Q hQc)
  have hBound := actual_prefix_bound_from_parent_structure
    R H V 5 D D₄ ε (rootedChosenPairPrefix tripleLabel)
    (by omega) hD₄pos hε hAdmH hRH hUniformR hGroundR
    hPrefix.1 (by intro E hE; simpa using hPrefix.2 E hE)
    (upperUnorderedPairLabel H V tUpper) hPair
    tripleLabel hCenter'
    good label hGoodCenter hLabel hBad hD hD₄R
  simpa only [show 5 - 3 = 2 by omega] using hBound

/-- IV.B.1 for the actual rooted part of the IV.9 repaired family. Both
    upper pair labels and lower strong-pair labels are constructed from
    their parent cells; the lower bad-partner bound follows from the IV.7
    edge deletion set. -/
theorem rooted_prefix_bound_of_actual_cleanups
    (K H : Family α) (V : Edge α)
    (tLower tUpper u q D D₄ : ℕ) (ε : ℝ)
    (tripleLabel : Edge α → α)
    (hAdmH : Admissible H)
    (hKH : K ⊆ H) (hUniformK : Uniform 5 K)
    (hUniformH : Uniform 5 H)
    (hAmbientH : ∀ E ∈ H, E ⊆ V)
    (hUpperSurvive : Disjoint K
      (upperFacetColorCleanupEdges H V tUpper))
    (hLowerSurvive : Disjoint K
      (multilevelDeletedEdges H V (V.powersetCard 3) 2 u q
        (fun B R T => ¬ ActualStrongPartner H V R T 2 3 tLower
          (tripleLabel B))))
    (hScale : (q : ℝ) ≤ ε * (u : ℝ))
    (hD₄pos : 1 ≤ D₄) (hε : 0 ≤ ε)
    (hD : ∀ A : Edge α, A.card = 3 →
      (H.filter (fun E => A ⊆ E)).card ≤ D)
    (hD₄ : ∀ Q : Edge α, Q.card = 4 →
      ((repairSharedFacetInheritance K
        (upperFacetColorCenter K H V tUpper hKH hUniformK
          (fun E hE => hAmbientH E (hKH hE)) hUpperSurvive)
        tripleLabel).filter (fun E => Q ⊆ E)).card ≤ D₄) :
    let L := repairSharedFacetInheritance K
      (upperFacetColorCenter K H V tUpper hKH hUniformK
        (fun E hE => hAmbientH E (hKH hE)) hUpperSurvive)
      tripleLabel
    ((rootedEdges L tripleLabel).card : ℝ) ^ 2 ≤
      (V.card.choose 3 : ℝ) *
        (((1 + 2 * (D₄ - 1) : ℕ) : ℝ) *
          ((rootedEdges L tripleLabel).card : ℝ) +
          ((V.card.choose 2 * (V.card - 2).choose 2 : ℕ) : ℝ) *
            max 7 (1 + ε * (D : ℝ))) := by
  classical
  let hAmbientK : ∀ E ∈ K, E ⊆ V :=
    fun E hE => hAmbientH E (hKH hE)
  let center := upperFacetColorCenter K H V tUpper
    hKH hUniformK hAmbientK hUpperSurvive
  let L := repairSharedFacetInheritance K center tripleLabel
  let R := rootedEdges L tripleLabel
  have hRL : R ⊆ L := rooted_edges_subset L tripleLabel
  have hLK : L ⊆ K := Finset.filter_subset _ _
  have hRK : R ⊆ K := hRL.trans hLK
  have hUniformL : Uniform 5 L := by
    intro E hE
    exact hUniformK (hLK hE)
  have hPrefix := rooted_chosen_pair_prefix_sub_card
    L tripleLabel hUniformL
  have hBadNat := assigned_prefix_bad_partners_le_of_cleanup
    R K H V (rootedChosenPairPrefix tripleLabel)
    tLower u q tripleLabel hRK hKH hPrefix.2
    hLowerSurvive
  have hBad : ∀ P ∈ V.powersetCard 3,
      ∀ Y ∈ chosenPrefixesAt R V 2
        (rootedChosenPairPrefix tripleLabel) P,
      ∀ x ∈ P,
        ((badParentPartners H V (Y ∪ {x}) (P.erase x)
          (fun B R T => ActualStrongPartner H V R T 2 3 tLower
            (tripleLabel B))).card : ℝ) ≤
          ε * ((parentPairLink H V (Y ∪ {x})).card : ℝ) := by
    intro P hP Y hY x hx
    have hCount := hBadNat P hP Y hY x hx
    have hYparts := mem_chosen_prefixes_at.mp hY
    have hYV := (Finset.mem_powersetCard.mp hYparts.1).1
    have hYcard := (Finset.mem_powersetCard.mp hYparts.1).2
    have hPV := (Finset.mem_powersetCard.mp hP).1
    have hxY : x ∉ Y := by
      intro hxY
      exact (Finset.disjoint_left.mp hYparts.2.1) hxY hx
    have hBcard : (Y ∪ {x}).card = 3 := by
      rw [Finset.union_singleton, Finset.card_insert_of_notMem hxY]
      omega
    have hBV : Y ∪ {x} ⊆ V := by
      intro a ha
      rcases Finset.mem_union.mp ha with haY | hax
      · exact hYV haY
      · exact hPV ((Finset.mem_singleton.mp hax) ▸ hx)
    have hBC : Y ∪ {x} ∈ V.powersetCard 3 :=
      Finset.mem_powersetCard.mpr ⟨hBV, hBcard⟩
    have hCountReal :
        ((badParentPartners H V (Y ∪ {x}) (P.erase x)
          (fun B R T => ActualStrongPartner H V R T 2 3 tLower
            (tripleLabel B))).card : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast hCount
    have hR := assigned_prefix_tail_mem_retained_pair_link
      R K V (rootedChosenPairPrefix tripleLabel) hRK hP hY hx
    have hDegree := retained_pair_root_parent_degree_ge
      K H V (V.powersetCard 3) u q
      (fun B R T => ¬ ActualStrongPartner H V R T 2 3 tLower
        (tripleLabel B)) hKH hLowerSurvive hBC hR
    rw [actual_core_link_two_eq_parent_pair_link] at hDegree
    have hDegreeReal : (u : ℝ) ≤ (parentPairLink H V (Y ∪ {x})).card :=
      by exact_mod_cast hDegree
    exact hCountReal.trans (hScale.trans (mul_le_mul_of_nonneg_left hDegreeReal hε))
  have hLabels := lower_strong_pair_label_interfaces
    H V tLower tripleLabel hUniformH hAmbientH
  exact rooted_prefix_bound_after_color_inheritance_repair
    K H V tUpper D D₄ ε tripleLabel hAdmH hKH hUniformK
    hAmbientK hUpperSurvive hD₄pos hε
    (fun B R T => ActualStrongPartner H V R T 2 3 tLower
      (tripleLabel B))
    (lowerStrongPairLabel H V tLower)
    hLabels.1 hLabels.2 hBad hD hD₄

end JSP523.Rank5
