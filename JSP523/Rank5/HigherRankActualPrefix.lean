import JSP523.Rank5.HigherRankUpperRepair
import JSP523.Rank5.HigherRankPrefixBound

/-! # Higher-rank prefix inequality after actual shared-facet repair

The lower inheritance rank is `n`, and the parent uniformity is `n+2`.
The actual upper coloring supplies all completion-pair labels; no abstract
pair-label agreement remains in this bound.
-/
namespace JSP523.Rank5.HigherRankUpper
open JSP523.Counting
variable {α : Type*} [DecidableEq α] [Nonempty α]

theorem prefix_bound_after_actual_facet_repair
    (K H : Family α) (V : Edge α) (n tLower tUpper u q D D₄ : ℕ) (ε : ℝ)
    (lower : Edge α → α)
    (hn : 4 ≤ n) (hD₄pos : 1 ≤ D₄) (hε : 0 ≤ ε)
    (hAdm : Admissible H) (hKH : K ⊆ H)
    (hUniformK : Uniform (n + 2) K) (hUniformH : Uniform (n + 2) H)
    (hAmbient : ∀ E ∈ H, E ⊆ V)
    (hUpper : Disjoint K (upperFacetColorCleanupEdges (n + 1) H V tUpper))
    (hBase : FamilyRankCenterInheritance K n lower)
    (hLower : Disjoint K
      (multilevelDeletedEdges H V (V.powersetCard n) 2 u q
        (fun B P T => ¬ ActualStrongPartner H V P T 2 n tLower (lower B))))
    (hScale : (q : ℝ) ≤ ε * (u : ℝ))
    (hD : ∀ A : Edge α, A.card = n →
      (H.filter (fun E => A ⊆ E)).card ≤ D)
    (hD₄ : ∀ Q : Edge α, Q.card = 4 →
      (K.filter (fun E => Q ⊆ E)).card ≤ D₄) :
    let L := repairSharedFacet K V (n + 1)
      (facetColorCenter K H V (n + 1) tUpper hKH hUpper) lower
    (L.card : ℝ) ^ 2 ≤ (V.card.choose 3 : ℝ) *
      (((1 + (n - 1) * (D₄ - 1) : ℕ) : ℝ) * (L.card : ℝ) +
        ((V.card.choose (n - 1) *
          (V.card - (n - 1)).choose (n - 1) : ℕ) : ℝ) *
            max 7 (1 + ε * (D : ℝ))) := by
  classical
  let parentCenter := facetColorCenter K H V (n + 1) tUpper hKH hUpper
  let L := repairSharedFacet K V (n + 1) parentCenter lower
  have hLK : L ⊆ K := repair_shared_facet_subset K V (n + 1) parentCenter lower
  have hBaseL := family_rank_center_inheritance_mono hLK hBase
  let facet := extendFamilyRankCenter L n lower hBaseL (by omega)
  have hFacet : FamilyRankCenterInheritance L (n + 1) facet :=
    extend_family_rank_center_inheritance hBaseL (by omega)
  have hPreserve : ∀ B : Edge α, B.card = n → facet B = lower B := by
    intro B hBc
    exact extend_family_rank_center_eq_of_card_ne hBaseL (by omega) (by omega)
  have hPair : ∀ A : Edge α, A.card = n + 1 → ∀ x y : α,
      x ≠ y → insert x A ∈ L → insert y A ∈ L →
        upperUnorderedPairLabel (n + 1) H V tUpper {x, y} = facet A := by
    intro A hAc x y hxy hx hy
    have hBase' : FamilyRankCenterInheritance K ((n + 1) - 1) lower := by
      simpa only [Nat.add_sub_cancel_right] using hBase
    have hUniform' : Uniform ((n + 1) + 1) K := by
      simpa only [Nat.add_assoc] using hUniformK
    have h := upper_pair_label_eq_extended_facet_center K H V (n + 1) tUpper
      hKH hUniform' (fun E hE => hAmbient E (hKH hE)) hUpper lower
      (by omega) hBase' hAc hxy hx hy
    simpa only [Nat.add_sub_cancel_right] using h
  have hLowerL := Finset.disjoint_of_subset_left hLK hLower
  have hD₄L : ∀ Q : Edge α, Q.card = 4 →
      (L.filter fun E => Q ⊆ E).card ≤ D₄ := by
    intro Q hQc
    apply (Finset.card_le_card (Finset.filter_subset_filter _ hLK)).trans
    exact hD₄ Q hQc
  have hBound := higher_rank_prefix_bound_of_inherited_facet_colors
    L H V (n + 2) tLower u q D D₄ ε lower facet
    (upperUnorderedPairLabel (n + 1) H V tUpper)
    (by omega) hD₄pos hε hAdm (hLK.trans hKH)
    (fun E hE => hUniformK (hLK hE)) hUniformH hAmbient
    (by simpa only [show n + 2 - 2 = n by omega] using hBaseL)
    (by simpa only [show n + 2 - 1 = n + 1 by omega] using hFacet)
    (by simpa only [show n + 2 - 2 = n by omega] using hPreserve)
    (by simpa only [show n + 2 - 1 = n + 1 by omega] using hPair)
    (by simpa only [show n + 2 - 2 = n by omega] using hLowerL)
    hScale (by simpa only [show n + 2 - 2 = n by omega] using hD) hD₄L
  simpa only [show n + 2 - 3 = n - 1 by omega] using hBound

end JSP523.Rank5.HigherRankUpper
