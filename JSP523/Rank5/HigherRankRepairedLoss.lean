import JSP523.Rank5.HigherRankRepairedPrefix

/-! # Combined finite loss for both higher-rank inheritance repairs -/
namespace JSP523.Rank5
variable {α : Type*} [DecidableEq α] [Nonempty α]

theorem repaired_higher_rank_loss_budget
    (K H : Family α) (V : Edge α)
    (n P Q LPair LTriple tSingleton tPair tTriple uPair qPair uTriple qTriple
      D₃ D₄ D₅ DBase DFacet : ℕ)
    (z : Edge α → α)
    (hKH : K ⊆ H) (hUniformK : Uniform (n + 3) K)
    (hUniformH : Uniform (n + 3) H) (hAmbientH : ∀ E ∈ H, E ⊆ V)
    (hSingleton : Disjoint K
      (HigherRankUpper.upperFacetColorCleanupEdges (n + 2) H V tSingleton))
    (hPair : Disjoint K
      (multilevelDeletedEdges H V (V.powersetCard (n + 1)) 2 uPair qPair
        (fun A R T => ¬ ActualStrongPartner H V R T 2 (n + 1) tPair (z A))))
    (hTriple : Disjoint K
      (multilevelDeletedEdges H V (V.powersetCard n) 3 uTriple qTriple
        (fun B R T => ¬ ActualStrongPartner H V R T 3 n tTriple (z B))))
    (hQ : 0 < Q)
    (hScalePair : Q * LPair ≤ P * uPair)
    (hScaleTriple : Q * LTriple ≤ P * uTriple)
    (hqPair : 4 * qPair ≤ LPair) (hqTriple : 4 * qTriple ≤ LTriple)
    (hGapPair : qPair < uPair) (hGapTriple : qTriple < uTriple)
    (htPair : 1 ≤ tPair) (htTriple : 1 ≤ tTriple)
    (hD₃ : ∀ S : Edge α, S.card = 3 → (H.filter fun E => S ⊆ E).card ≤ D₃)
    (hD₄ : ∀ S : Edge α, S.card = 4 → (H.filter fun E => S ⊆ E).card ≤ D₄)
    (hD₅ : ∀ S : Edge α, S.card = 5 → (H.filter fun E => S ⊆ E).card ≤ D₅)
    (hDBase : ∀ S : Edge α, S.card = n + 1 →
      (H.filter fun E => S ⊆ E).card ≤ DBase)
    (hDFacet : ∀ S : Edge α, S.card = n + 2 →
      (H.filter fun E => S ⊆ E).card ≤ DFacet) :
    let M₂ := tPair * (2 * LPair)
    let M₃ := tTriple * (LPair * LTriple)
    let W₂ := 8 * (V.powersetCard 2).card ^ 2 * D₃ * DFacet * D₄
    let W₃ := 12 * (V.powersetCard 3).card ^ 2 * D₄ * DBase * D₅
    Q * M₂ * M₃ *
      (K.card - (repairedHigherRankFamily K H V n tSingleton z hKH hSingleton).card) ≤
      M₂ * M₃ * ((HigherRankUpper.lowFacetIncidenceConstant (n + 1) +
        HigherRankLower.lowFacetIncidenceConstant n) * P * H.card) +
      Q * (M₂ * W₃ + M₃ * W₂) := by
  classical
  let B := repairRankInheritance K (n + 1) z
  have hBK : B ⊆ K := repair_rank_inheritance_subset K (n + 1) z
  have hBH := hBK.trans hKH
  have hAmbientK : ∀ E ∈ K, E ⊆ V := fun E hE => hAmbientH E (hKH hE)
  have hSingletonB := Finset.disjoint_of_subset_left hBK hSingleton
  have hPairB := Finset.disjoint_of_subset_left hBK hPair
  have hUniformB : Uniform ((n + 1) + 2) B := by
    intro E hE
    simpa only [Nat.add_assoc] using hUniformK (hBK hE)
  let center := HigherRankUpper.facetColorCenter B H V (n + 2) tSingleton
    hBH hSingletonB
  let L := HigherRankUpper.repairSharedFacet B V (n + 2) center z
  have hBaseCount := HigherRankLower.lower_incidence_budget_of_actual_cleanups
    K H V n P Q LPair LTriple tTriple tPair uTriple qTriple uPair qPair
    D₄ D₅ DBase z z hKH hUniformK hUniformH hAmbientH hPair hTriple hQ
    hScalePair hScaleTriple (by omega) hqTriple hGapPair hGapTriple htTriple
    hD₄ hDBase hD₅
  have hBaseLoss := HigherRankLower.rank_repair_loss_le_lower_bad_incidences
    K V (n + 1) z hAmbientK
  have hBase : Q * (tTriple * (LPair * LTriple) * (K.card - B.card)) ≤
      tTriple * (LPair * LTriple) *
        (HigherRankLower.lowFacetIncidenceConstant n * P * H.card) +
      Q * (12 * (V.powersetCard 3).card ^ 2 * D₄ * DBase * D₅) :=
    (Nat.mul_le_mul_left Q
      (Nat.mul_le_mul_left (tTriple * (LPair * LTriple)) hBaseLoss)).trans hBaseCount
  have hFacetRaw := HigherRankUpper.facet_repair_loss_budget_of_actual_cleanups
    B H V (n + 1) P Q LPair tPair tSingleton uPair qPair D₃ D₄ DFacet z
    hBH hUniformB (by simpa only [Nat.add_assoc] using hUniformH) hAmbientH
    (by simpa only [Nat.add_assoc] using hSingletonB) hPairB hQ hScalePair
    hqPair hGapPair htPair hD₃ (by simpa only [Nat.add_assoc] using hDFacet) hD₄
  have hFacet : Q * (tPair * (2 * LPair) * (B.card - L.card)) ≤
      tPair * (2 * LPair) *
        (HigherRankUpper.lowFacetIncidenceConstant (n + 1) * P * H.card) +
      Q * (8 * (V.powersetCard 2).card ^ 2 * D₃ * DFacet * D₄) := by
    simpa only [Nat.add_assoc] using hFacetRaw
  have hBaseScaled := Nat.mul_le_mul_left (tPair * (2 * LPair)) hBase
  have hFacetScaled := Nat.mul_le_mul_left (tTriple * (LPair * LTriple)) hFacet
  have hBcard := Finset.card_le_card hBK
  have hLcard := Finset.card_le_card
    (HigherRankUpper.repair_shared_facet_subset B V (n + 2) center z)
  change B.card ≤ K.card at hBcard
  change L.card ≤ B.card at hLcard
  have hLossEq : K.card - L.card = (K.card - B.card) + (B.card - L.card) := by omega
  change Q * (tPair * (2 * LPair)) * (tTriple * (LPair * LTriple)) *
    (K.card - L.card) ≤ _
  rw [hLossEq]
  nlinarith

end JSP523.Rank5
