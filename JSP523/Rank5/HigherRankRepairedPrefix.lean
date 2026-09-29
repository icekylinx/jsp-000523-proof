import JSP523.Rank5.HigherRankActualPrefix
import JSP523.Rank5.HigherRankLowerBudget
import JSP523.Rank5.HigherRankFacetBudget

/-! # The actual two-stage higher-rank repaired family

For parent uniformity n+3, repair lower-core deletion at rank n+1,
then repair the actual shared-facet centers at rank n+2. Both losses
are charged to the incidence sets bounded by IV.9.1–IV.9.3.
-/
namespace JSP523.Rank5
open JSP523.Counting
variable {α : Type*} [DecidableEq α] [Nonempty α]

noncomputable def repairedHigherRankFamily
    (K H : Family α) (V : Edge α) (n tSingleton : ℕ) (z : Edge α → α)
    (hKH : K ⊆ H)
    (hSingleton : Disjoint K
      (HigherRankUpper.upperFacetColorCleanupEdges (n + 2) H V tSingleton)) : Family α :=
  let B := repairRankInheritance K (n + 1) z
  let hBK := repair_rank_inheritance_subset K (n + 1) z
  HigherRankUpper.repairSharedFacet B V (n + 2)
    (HigherRankUpper.facetColorCenter B H V (n + 2) tSingleton
      (hBK.trans hKH) (Finset.disjoint_of_subset_left hBK hSingleton)) z

theorem repaired_higher_rank_family_subset
    (K H : Family α) (V : Edge α) (n tSingleton : ℕ) (z : Edge α → α)
    (hKH : K ⊆ H)
    (hSingleton : Disjoint K
      (HigherRankUpper.upperFacetColorCleanupEdges (n + 2) H V tSingleton)) :
    repairedHigherRankFamily K H V n tSingleton z hKH hSingleton ⊆ K :=
  (HigherRankUpper.repair_shared_facet_subset _ _ _ _ _).trans
    (repair_rank_inheritance_subset K (n + 1) z)

/-- The complete actual-family prefix inequality at every r=n+3≥6.
    All centers, upper pair labels and assigned prefixes are constructed. -/
theorem repaired_higher_rank_prefix_bound
    (K H : Family α) (V : Edge α) (n tPair tSingleton u q D D₄ : ℕ) (ε : ℝ)
    (z : Edge α → α)
    (hn : 3 ≤ n) (hD₄pos : 1 ≤ D₄) (hε : 0 ≤ ε)
    (hAdm : Admissible H) (hKH : K ⊆ H)
    (hUniformK : Uniform (n + 3) K) (hUniformH : Uniform (n + 3) H)
    (hAmbient : ∀ E ∈ H, E ⊆ V)
    (hSingleton : Disjoint K
      (HigherRankUpper.upperFacetColorCleanupEdges (n + 2) H V tSingleton))
    (hPair : Disjoint K
      (multilevelDeletedEdges H V (V.powersetCard (n + 1)) 2 u q
        (fun A R T => ¬ ActualStrongPartner H V R T 2 (n + 1) tPair (z A))))
    (hGap : q < u) (hScale : (q : ℝ) ≤ ε * (u : ℝ))
    (hD : ∀ A : Edge α, A.card = n + 1 →
      (H.filter (fun E => A ⊆ E)).card ≤ D)
    (hD₄ : ∀ Q : Edge α, Q.card = 4 →
      (K.filter (fun E => Q ⊆ E)).card ≤ D₄) :
    let L := repairedHigherRankFamily K H V n tSingleton z hKH hSingleton
    (L.card : ℝ) ^ 2 ≤ (V.card.choose 3 : ℝ) *
      (((1 + n * (D₄ - 1) : ℕ) : ℝ) * (L.card : ℝ) +
        ((V.card.choose n * (V.card - n).choose n : ℕ) : ℝ) *
          max 7 (1 + ε * (D : ℝ))) := by
  classical
  let B := repairRankInheritance K (n + 1) z
  have hBK : B ⊆ K := repair_rank_inheritance_subset K (n + 1) z
  have hLabels : ActualRankLabels K (n + 1) z :=
    actual_rank_labels_of_core_cleanup K H V (n + 1) 2 tPair u q z hKH
      (by simpa only [Nat.add_assoc] using hUniformK)
      (fun E hE => hAmbient E (hKH hE)) hGap hPair
  have hBase : FamilyRankCenterInheritance B (n + 1) z :=
    repaired_family_rank_center_inheritance hLabels
  have hUniformB : Uniform ((n + 1) + 2) B := by
    intro E hE
    simpa only [Nat.add_assoc] using hUniformK (hBK hE)
  have hD₄B : ∀ Q : Edge α, Q.card = 4 →
      (B.filter fun E => Q ⊆ E).card ≤ D₄ := by
    intro Q hQc
    exact (Finset.card_le_card (Finset.filter_subset_filter _ hBK)).trans (hD₄ Q hQc)
  have hUpperB := Finset.disjoint_of_subset_left hBK hSingleton
  have hLowerB := Finset.disjoint_of_subset_left hBK hPair
  have hBound := HigherRankUpper.prefix_bound_after_actual_facet_repair
    B H V (n + 1) tPair tSingleton u q D D₄ ε z (by omega) hD₄pos hε hAdm
    (hBK.trans hKH) hUniformB (by simpa only [Nat.add_assoc] using hUniformH)
    hAmbient (by simpa only [Nat.add_assoc] using hUpperB) hBase
    hLowerB hScale hD hD₄B
  simpa [repairedHigherRankFamily, B, Nat.add_assoc] using hBound

/-- Exact finite loss charge for both actual inheritance repairs. -/
theorem repaired_higher_rank_loss_le_actual_incidences
    (K H : Family α) (V : Edge α) (n tSingleton : ℕ) (z : Edge α → α)
    (hKH : K ⊆ H) (hAmbientK : ∀ E ∈ K, E ⊆ V)
    (hSingleton : Disjoint K
      (HigherRankUpper.upperFacetColorCleanupEdges (n + 2) H V tSingleton)) :
    let B := repairRankInheritance K (n + 1) z
    let hBK := repair_rank_inheritance_subset K (n + 1) z
    K.card - (repairedHigherRankFamily K H V n tSingleton z hKH hSingleton).card ≤
      (HigherRankLower.badIncidences K V (n + 1) z z).card +
      (HigherRankUpper.facetBadIncidences B V (n + 2)
        (HigherRankUpper.facetColorCenter B H V (n + 2) tSingleton
          (hBK.trans hKH) (Finset.disjoint_of_subset_left hBK hSingleton)) z).card := by
  let B := repairRankInheritance K (n + 1) z
  have hBK := repair_rank_inheritance_subset K (n + 1) z
  let center := HigherRankUpper.facetColorCenter B H V (n + 2) tSingleton
    (hBK.trans hKH) (Finset.disjoint_of_subset_left hBK hSingleton)
  have hBase := HigherRankLower.rank_repair_loss_le_lower_bad_incidences
    K V (n + 1) z hAmbientK
  have hFacet := HigherRankUpper.shared_facet_repair_loss_le_bad_incidences
    B V (n + 2) center z
  have hBcard := Finset.card_le_card hBK
  have hLcard := Finset.card_le_card
    (HigherRankUpper.repair_shared_facet_subset B V (n + 2) center z)
  change K.card - B.card ≤ _ at hBase
  change B.card ≤ K.card at hBcard
  change K.card - (HigherRankUpper.repairSharedFacet B V (n + 2) center z).card ≤
    (HigherRankLower.badIncidences K V (n + 1) z z).card +
      (HigherRankUpper.facetBadIncidences B V (n + 2) center z).card
  omega

end JSP523.Rank5
