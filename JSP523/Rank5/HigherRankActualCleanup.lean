import JSP523.Rank5.HigherRankRepairedPrefix
import JSP523.Rank5.ColorQuantitativeFixedPaletteBudget

/-! # One actual center assignment for both higher-rank majority cleanups -/
namespace JSP523.Rank5
variable {α : Type*} [DecidableEq α] [Nonempty α]

noncomputable def higherMajorityCenter
    (H : Family α) (V : Edge α) (n tPair tTriple : ℕ) (B : Edge α) : α :=
  if B.card = n then fixedPaletteMajorityLabel H V 3 n tTriple B
  else fixedPaletteMajorityLabel H V 2 (n + 1) tPair B

theorem higher_majority_center_triple
    (H : Family α) (V B : Edge α) (n tPair tTriple : ℕ) (hB : B.card = n) :
    higherMajorityCenter H V n tPair tTriple B =
      fixedPaletteMajorityLabel H V 3 n tTriple B := by
  simp [higherMajorityCenter, hB]

theorem higher_majority_center_pair
    (H : Family α) (V B : Edge α) (n tPair tTriple : ℕ) (hB : B.card = n + 1) :
    higherMajorityCenter H V n tPair tTriple B =
      fixedPaletteMajorityLabel H V 2 (n + 1) tPair B := by
  simp [higherMajorityCenter, hB]

omit [Nonempty α] in
/-- Cleanup depends only on the chosen labels on its specified core layer. -/
theorem higher_multilevel_cleanup_label_congr
    (H : Family α) (V : Edge α) (s k t u q : ℕ)
    (z w : Edge α → α) (hLabel : ∀ B, B.card = k → z B = w B) :
    multilevelDeletedEdges H V (V.powersetCard k) s u q
      (fun B P Q => ¬ ActualStrongPartner H V P Q s k t (z B)) =
    multilevelDeletedEdges H V (V.powersetCard k) s u q
      (fun B P Q => ¬ ActualStrongPartner H V P Q s k t (w B)) := by
  classical
  apply Finset.biUnion_congr rfl
  intro B hB
  have hEq := hLabel B (Finset.mem_powersetCard.mp hB).2
  simp only [cleanupTails, actualBadPartnerDegree, hEq]

noncomputable def higherMajorityDeletedEdges
    (H : Family α) (V : Edge α) (n tPair tTriple uPair qPair uTriple qTriple : ℕ) :
    Family α :=
  multilevelDeletedEdges H V (V.powersetCard (n + 1)) 2 uPair qPair
    (fun B P Q => ¬ ActualStrongPartner H V P Q 2 (n + 1) tPair
      (fixedPaletteMajorityLabel H V 2 (n + 1) tPair B)) ∪
  multilevelDeletedEdges H V (V.powersetCard n) 3 uTriple qTriple
    (fun B P Q => ¬ ActualStrongPartner H V P Q 3 n tTriple
      (fixedPaletteMajorityLabel H V 3 n tTriple B))

noncomputable def higherCleanedFamily
    (H : Family α) (V : Edge α)
    (n tSingleton tPair tTriple uPair qPair uTriple qTriple : ℕ) : Family α :=
  H \ (HigherRankUpper.upperFacetColorCleanupEdges (n + 2) H V tSingleton ∪
    higherMajorityDeletedEdges H V n tPair tTriple uPair qPair uTriple qTriple)

theorem higher_cleaned_family_properties
    (H : Family α) (V : Edge α)
    (n tSingleton tPair tTriple uPair qPair uTriple qTriple : ℕ) :
    let K := higherCleanedFamily H V n tSingleton tPair tTriple uPair qPair uTriple qTriple
    let z := higherMajorityCenter H V n tPair tTriple
    K ⊆ H ∧
    Disjoint K (HigherRankUpper.upperFacetColorCleanupEdges (n + 2) H V tSingleton) ∧
    Disjoint K (multilevelDeletedEdges H V (V.powersetCard (n + 1)) 2 uPair qPair
      (fun B P Q => ¬ ActualStrongPartner H V P Q 2 (n + 1) tPair (z B))) ∧
    Disjoint K (multilevelDeletedEdges H V (V.powersetCard n) 3 uTriple qTriple
      (fun B P Q => ¬ ActualStrongPartner H V P Q 3 n tTriple (z B))) := by
  classical
  dsimp only
  rw [higher_multilevel_cleanup_label_congr H V 2 (n + 1) tPair uPair qPair
    _ _ (fun B hB => higher_majority_center_pair H V B n tPair tTriple hB)]
  rw [higher_multilevel_cleanup_label_congr H V 3 n tTriple uTriple qTriple
    _ _ (fun B hB => higher_majority_center_triple H V B n tPair tTriple hB)]
  unfold higherCleanedFamily higherMajorityDeletedEdges
  constructor
  · exact Finset.sdiff_subset
  · simp only [Finset.disjoint_left, Finset.mem_sdiff, Finset.mem_union]
    tauto

/-- Fully specified family after actual colors, both majority cleanups, and repairs. -/
noncomputable def higherFinalFamily
    (H : Family α) (V : Edge α)
    (n tSingleton tPair tTriple uPair qPair uTriple qTriple : ℕ) : Family α :=
  let h := higher_cleaned_family_properties H V n tSingleton tPair tTriple
    uPair qPair uTriple qTriple
  repairedHigherRankFamily
    (higherCleanedFamily H V n tSingleton tPair tTriple uPair qPair uTriple qTriple)
    H V n tSingleton (higherMajorityCenter H V n tPair tTriple) h.1 h.2.1

theorem higher_final_family_subset
    (H : Family α) (V : Edge α)
    (n tSingleton tPair tTriple uPair qPair uTriple qTriple : ℕ) :
    higherFinalFamily H V n tSingleton tPair tTriple uPair qPair uTriple qTriple ⊆ H := by
  have h := higher_cleaned_family_properties H V n tSingleton tPair tTriple
    uPair qPair uTriple qTriple
  exact (repaired_higher_rank_family_subset _ _ _ _ _ _ h.1 h.2.1).trans h.1

/-- The actual final family satisfies the prefix bound without auxiliary labels. -/
theorem higher_final_family_prefix_bound
    (H : Family α) (V : Edge α)
    (n tSingleton tPair tTriple uPair qPair uTriple qTriple D D₄ : ℕ) (ε : ℝ)
    (hn : 3 ≤ n) (hD₄pos : 1 ≤ D₄) (hε : 0 ≤ ε)
    (hAdm : Admissible H) (hUniform : Uniform (n + 3) H)
    (hAmbient : ∀ E ∈ H, E ⊆ V)
    (hGap : qPair < uPair) (hScale : (qPair : ℝ) ≤ ε * uPair)
    (hD : ∀ A : Edge α, A.card = n + 1 → (H.filter fun E => A ⊆ E).card ≤ D)
    (hD₄ : ∀ A : Edge α, A.card = 4 → (H.filter fun E => A ⊆ E).card ≤ D₄) :
    let L := higherFinalFamily H V n tSingleton tPair tTriple uPair qPair uTriple qTriple
    (L.card : ℝ) ^ 2 ≤ (V.card.choose 3 : ℝ) *
      (((1 + n * (D₄ - 1) : ℕ) : ℝ) * L.card +
        ((V.card.choose n * (V.card - n).choose n : ℕ) : ℝ) * max 7 (1 + ε * D)) := by
  let K := higherCleanedFamily H V n tSingleton tPair tTriple uPair qPair uTriple qTriple
  have h := higher_cleaned_family_properties H V n tSingleton tPair tTriple
    uPair qPair uTriple qTriple
  exact repaired_higher_rank_prefix_bound K H V n tPair tSingleton uPair qPair D D₄ ε
    (higherMajorityCenter H V n tPair tTriple) hn hD₄pos hε hAdm h.1
    (fun _ hE => hUniform (h.1 hE)) hUniform hAmbient h.2.1 h.2.2.1 hGap hScale hD
    (fun A hA => (Finset.card_le_card (Finset.filter_subset_filter _ h.1)).trans (hD₄ A hA))

/-- Initial cleanup loss plus actual repair loss accounts for every parent edge. -/
theorem higher_final_family_mass_accounting
    (H : Family α) (V : Edge α)
    (n tSingleton tPair tTriple uPair qPair uTriple qTriple : ℕ) :
    let K := higherCleanedFamily H V n tSingleton tPair tTriple uPair qPair uTriple qTriple
    let L := higherFinalFamily H V n tSingleton tPair tTriple uPair qPair uTriple qTriple
    H.card ≤ L.card +
      (HigherRankUpper.upperFacetColorCleanupEdges (n + 2) H V tSingleton).card +
      (higherMajorityDeletedEdges H V n tPair tTriple uPair qPair uTriple qTriple).card +
      (K.card - L.card) := by
  classical
  let K := higherCleanedFamily H V n tSingleton tPair tTriple uPair qPair uTriple qTriple
  let L := higherFinalFamily H V n tSingleton tPair tTriple uPair qPair uTriple qTriple
  have h := higher_cleaned_family_properties H V n tSingleton tPair tTriple
    uPair qPair uTriple qTriple
  have hLK : L ⊆ K := repaired_higher_rank_family_subset _ _ _ _ _ _ h.1 h.2.1
  have hCard : L.card ≤ K.card := Finset.card_le_card hLK
  have hCleanup := Finset.card_le_card_sdiff_add_card (s := H)
    (t := HigherRankUpper.upperFacetColorCleanupEdges (n + 2) H V tSingleton ∪
      higherMajorityDeletedEdges H V n tPair tTriple uPair qPair uTriple qTriple)
  have hUnion := Finset.card_union_le
    (HigherRankUpper.upperFacetColorCleanupEdges (n + 2) H V tSingleton)
    (higherMajorityDeletedEdges H V n tPair tTriple uPair qPair uTriple qTriple)
  change H.card ≤ K.card + _ at hCleanup
  change H.card ≤ L.card + _ + _ + (K.card - L.card)
  omega

end JSP523.Rank5
