import JSP523.Rank5.HigherRankPartnerRetention
import JSP523.Rank5.HigherRankFacetPrefix

/-! # Assigned-prefix bound from higher-rank inheritance and actual cleanup -/
namespace JSP523.Rank5
open JSP523.Counting
variable {α : Type*} [DecidableEq α] [Nonempty α]

/-- Parent strong labels and the partner estimate are supplied by their
    actual cells and deletion sets. The remaining pair-completion premise
    records the upper-color inheritance input. -/
theorem higher_rank_prefix_bound_of_actual_cleanup
    (K H : Family α) (V : Edge α) (r t u q D D₄ : ℕ) (ε : ℝ)
    (chosen : Edge α → Edge α) (center pairLabel : Edge α → α)
    (hr : 6 ≤ r) (hD₄pos : 1 ≤ D₄) (hε : 0 ≤ ε)
    (hAdm : Admissible H) (hKH : K ⊆ H)
    (hUniformK : Uniform r K) (hUniformH : Uniform r H)
    (hAmbient : ∀ E ∈ H, E ⊆ V)
    (hSub : ∀ E ∈ K, chosen E ⊆ E)
    (hCard : ∀ E ∈ K, (chosen E).card = r - 3)
    (hPair : ∀ Y ∈ V.powersetCard (r - 3),
      PairCompletionLabelInPrefix
        (K.filter (fun E => chosen E = Y)) pairLabel Y)
    (hCenter : ∀ P ∈ V.powersetCard 3,
      ∀ Y ∈ chosenPrefixesAt K V (r - 3) chosen P,
      ∀ x ∈ P, center (Y ∪ {x}) ∈ Y)
    (hSurvive : Disjoint K
      (multilevelDeletedEdges H V (V.powersetCard (r - 2)) 2 u q
        (fun B P T => ¬ ActualStrongPartner H V P T 2 (r - 2) t
          (center B))))
    (hScale : (q : ℝ) ≤ ε * (u : ℝ))
    (hD : ∀ A : Edge α, A.card = r - 2 →
      (H.filter (fun E => A ⊆ E)).card ≤ D)
    (hD₄ : ∀ Q : Edge α, Q.card = 4 →
      (K.filter (fun E => Q ⊆ E)).card ≤ D₄) :
    (K.card : ℝ) ^ 2 ≤ (V.card.choose 3 : ℝ) *
      (((1 + (r - 3) * (D₄ - 1) : ℕ) : ℝ) * (K.card : ℝ) +
        ((V.card.choose (r - 3) *
          (V.card - (r - 3)).choose (r - 3) : ℕ) : ℝ) *
            max 7 (1 + ε * (D : ℝ))) := by
  have hLabels := higher_strong_pair_label_interfaces H V r t center
    hUniformH hAmbient
  have hBad := higher_assigned_prefix_bad_partners_relative
    K K H V r u q ε chosen
    (fun B P T => ActualStrongPartner H V P T 2 (r - 2) t (center B))
    (by omega) Finset.Subset.rfl hKH hSurvive hε hScale
  exact actual_prefix_bound_from_parent_structure K H V r D D₄ ε chosen
    (by omega) hD₄pos hε hAdm hKH hUniformK
    (fun E hE => hAmbient E (hKH hE)) hSub hCard pairLabel hPair
    center hCenter
    (fun B P T => ActualStrongPartner H V P T 2 (r - 2) t (center B))
    (higherStrongPairLabel H V r t) hLabels.1 hLabels.2 hBad hD hD₄

/-- Construct the prefix assignment from inheritance; only actual upper
    pair colors still need to agree with the inherited facet centers. -/
theorem higher_rank_prefix_bound_of_inherited_facet_colors
    (K H : Family α) (V : Edge α) (r t u q D D₄ : ℕ) (ε : ℝ)
    (center facet pairLabel : Edge α → α)
    (hr : 6 ≤ r) (hD₄pos : 1 ≤ D₄) (hε : 0 ≤ ε)
    (hAdm : Admissible H) (hKH : K ⊆ H)
    (hUniformK : Uniform r K) (hUniformH : Uniform r H)
    (hAmbient : ∀ E ∈ H, E ⊆ V)
    (hBase : FamilyRankCenterInheritance K (r - 2) center)
    (hFacet : FamilyRankCenterInheritance K (r - 1) facet)
    (hPreserve : ∀ B : Edge α, B.card = r - 2 → facet B = center B)
    (hPairCenter : ∀ A : Edge α, A.card = r - 1 → ∀ x y : α,
      x ≠ y → insert x A ∈ K → insert y A ∈ K →
        pairLabel {x, y} = facet A)
    (hSurvive : Disjoint K
      (multilevelDeletedEdges H V (V.powersetCard (r - 2)) 2 u q
        (fun B P T => ¬ ActualStrongPartner H V P T 2 (r - 2) t
          (center B))))
    (hScale : (q : ℝ) ≤ ε * (u : ℝ))
    (hD : ∀ A : Edge α, A.card = r - 2 →
      (H.filter (fun E => A ⊆ E)).card ≤ D)
    (hD₄ : ∀ Q : Edge α, Q.card = 4 →
      (K.filter (fun E => Q ⊆ E)).card ≤ D₄) :
    (K.card : ℝ) ^ 2 ≤ (V.card.choose 3 : ℝ) *
      (((1 + (r - 3) * (D₄ - 1) : ℕ) : ℝ) * (K.card : ℝ) +
        ((V.card.choose (r - 3) *
          (V.card - (r - 3)).choose (r - 3) : ℕ) : ℝ) *
            max 7 (1 + ε * (D : ℝ))) := by
  obtain ⟨chosen, hChosen⟩ :=
    exists_occurring_rooted_prefix_assignment hr hUniformK hBase
  have hSub : ∀ E ∈ K, chosen E ⊆ E := fun E hE => (hChosen E hE).1
  have hCard : ∀ E ∈ K, (chosen E).card = r - 3 :=
    fun E hE => (hChosen E hE).2.1
  have hPrefix : ∀ E ∈ K, ∀ x ∈ E \ chosen E,
      center (chosen E ∪ {x}) ∈ chosen E :=
    fun E hE => (hChosen E hE).2.2
  have hPair : ∀ Y ∈ V.powersetCard (r - 3),
      PairCompletionLabelInPrefix
        (K.filter (fun E => chosen E = Y)) pairLabel Y := by
    intro Y _
    exact higher_rank_pair_completion_label_in_prefix K r chosen center facet
      pairLabel Y (by omega) hUniformK hCard hPrefix hFacet hPreserve hPairCenter
  have hCenter : ∀ P ∈ V.powersetCard 3,
      ∀ Y ∈ chosenPrefixesAt K V (r - 3) chosen P,
      ∀ x ∈ P, center (Y ∪ {x}) ∈ Y := by
    intro P _ Y hY x hx
    exact assigned_prefix_center_of_edge_prefix_law center chosen hPrefix hY hx
  exact higher_rank_prefix_bound_of_actual_cleanup K H V r t u q D D₄ ε
    chosen center pairLabel hr hD₄pos hε hAdm hKH hUniformK hUniformH hAmbient
    hSub hCard hPair hCenter hSurvive hScale hD hD₄

end JSP523.Rank5
