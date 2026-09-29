import JSP523.Rank4.PreprocessInitialOuterCoverTouching
import JSP523.Rank4.PreprocessInitialOuterPairCap

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- Distinct owners retain disjoint triple families. -/
theorem initial_outer_cleaned_union_card
    (L : α → Family α) (C : Edge α) (owner : Edge α → α)
    (hUniform : ∀ c ∈ C, Uniform 3 (L c)) :
    (C.biUnion (pairOwnerCleanedLink L owner)).card =
      ∑ c ∈ C, (pairOwnerCleanedLink L owner c).card := by
  classical
  apply Finset.card_biUnion
  intro c hc d hd hcd
  apply Finset.disjoint_left.mpr
  intro T hcT hdT
  have hcSpec := Finset.mem_filter.mp hcT
  have hdSpec := Finset.mem_filter.mp hdT
  have hT : T.card = 3 := hUniform c hc hcSpec.1
  obtain ⟨P, hPT, hP⟩ := Finset.exists_subset_card_eq (show 2 ≤ T.card by omega)
  have hMem : P ∈ T.powersetCard 2 := Finset.mem_powersetCard.mpr ⟨hPT, hP⟩
  exact hcd ((hcSpec.2 P hMem).symm.trans (hdSpec.2 P hMem))

/-- Once a set of centers is deleted, the sum of its actual disjoint star
layers is bounded by the number of deleted original edges. -/
theorem initial_outer_star_sum_le_touching
    (H : Family α) (W X : Edge α) :
    (∑ c ∈ X, (rankFourStarLink H (W \ X) c).card) ≤
      (H \ fixedDecompositionCore H (W \ X)).card := by
  classical
  let V := W \ X
  let S := fun c => (rankFourStarLink H V c).image (fun T => insert c T)
  have hOutside : ∀ c ∈ X, c ∉ V := fun c hc hV => (Finset.mem_sdiff.mp hV).2 hc
  have hInj (c : α) (hc : c ∈ X) :
      Set.InjOn (fun T : Edge α => insert c T) ↑(rankFourStarLink H V c) := by
    intro T hT R hR hEq
    have hcT : c ∉ T := fun h => hOutside c hc
      ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).1 h)
    have hcR : c ∉ R := fun h => hOutside c hc
      ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp hR).1).1 h)
    have h := congrArg (fun E : Edge α => E.erase c) hEq
    simpa only [Finset.erase_insert hcT, Finset.erase_insert hcR] using h
  have hDisj : (↑X : Set α).PairwiseDisjoint S := by
    intro c hc d hd hcd
    apply Finset.disjoint_left.mpr
    intro E hcE hdE
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hcE
    obtain ⟨R, hR, hEq⟩ := Finset.mem_image.mp hdE
    have hdT : d ∈ T := by
      have h : d ∈ insert c T := by rw [← hEq]; simp
      exact (Finset.mem_insert.mp h).resolve_left (Ne.symm hcd)
    exact hOutside d hd ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).1 hdT)
  have hSub : X.biUnion S ⊆ H \ fixedDecompositionCore H V := by
    intro E hE
    obtain ⟨c, hc, hImage⟩ := Finset.mem_biUnion.mp hE
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hImage
    apply Finset.mem_sdiff.mpr
    refine ⟨(Finset.mem_filter.mp hT).2, ?_⟩
    intro hCore
    exact hOutside c hc ((Finset.mem_filter.mp hCore).2 (Finset.mem_insert_self _ _))
  calc
    _ = ∑ c ∈ X, (S c).card := by
      apply Finset.sum_congr rfl
      intro c hc
      exact (Finset.card_image_iff.mpr (hInj c hc)).symm
    _ = (X.biUnion S).card := (Finset.card_biUnion hDisj).symm
    _ ≤ _ := Finset.card_le_card hSub

/-- Restricting a parent to a ground set preserves each star whose center
and triple already lie in that ground set. -/
theorem initial_outer_core_star_link
    (H : Family α) (W V : Edge α) (c : α) (hVW : V ⊆ W) (hc : c ∈ W) :
    rankFourStarLink (fixedDecompositionCore H W) V c = rankFourStarLink H V c := by
  ext T
  constructor
  · intro h
    have hs := Finset.mem_filter.mp h
    exact Finset.mem_filter.mpr ⟨hs.1, (Finset.mem_filter.mp hs.2).1⟩
  · intro h
    have hs := Finset.mem_filter.mp h
    apply Finset.mem_filter.mpr
    refine ⟨hs.1, Finset.mem_filter.mpr ⟨hs.2, ?_⟩⟩
    exact Finset.insert_subset_iff.mpr ⟨hc,
      (Finset.mem_powersetCard.mp hs.1).1.trans hVW⟩

/-- Actual initial decomposition in precisely the original-mass form used
by the completion assembly. The loss contains multiple-center hits, the
entire X layer, and the actual Z owner deletions. -/
theorem initial_outer_original_mass_bound
    {n : ℕ} (H : Family (Fin n)) (Z X : Edge (Fin n))
    (owner : Edge (Fin n) → Fin n)
    (hUniform : Uniform 4 H) (hX : X ⊆ Finset.univ \ Z) :
    let U := Finset.univ \ (Z ∪ X)
    let H₀ := fixedDecompositionCore H (Finset.univ \ Z)
    let L := fun c => rankFourStarLink H U c
    H.card ≤ (Z.biUnion (pairOwnerCleanedLink L owner)).card +
      (fixedDecompositionCore H U).card +
      ((Z ∪ X).card.choose 2 * n ^ 2 +
        (H₀ \ fixedDecompositionCore H₀ U).card +
        ∑ c ∈ Z, (L c \ pairOwnerCleanedLink L owner c).card) := by
  classical
  dsimp only
  let U := Finset.univ \ (Z ∪ X)
  let W := Finset.univ \ Z
  let H₀ := fixedDecompositionCore H W
  let L := fun c => rankFourStarLink H U c
  have hOutside : ∀ c ∈ Z ∪ X, c ∉ U := fun c hc hU =>
    (Finset.mem_sdiff.mp hU).2 hc
  have hZX : Disjoint Z X := Finset.disjoint_left.mpr fun z hz hx =>
    (Finset.mem_sdiff.mp (hX hx)).2 hz
  have hU : W \ X = U := by ext x; simp only [W, U, Finset.mem_sdiff, Finset.mem_union]; tauto
  have hDecomp := fixed_decomposition_card_bound H U (Z ∪ X) hOutside
  rw [Finset.sum_union hZX] at hDecomp
  have hError := fixed_decomposition_error_card_le_pair_budget H Finset.univ (Z ∪ X)
    (n ^ 2) hUniform (fun E _ => Finset.subset_univ E)
    (rank_four_pair_degree_le_ground_square H hUniform)
  have hTouch := initial_outer_star_sum_le_touching H₀ W X
  rw [hU] at hTouch
  have hLinks : ∀ c ∈ X, rankFourStarLink H₀ U c = L c := by
    intro c hc
    exact initial_outer_core_star_link H W U c
      (fun z hz => Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hz).1,
        fun hzZ => (Finset.mem_sdiff.mp hz).2 (Finset.mem_union_left _ hzZ)⟩) (hX hc)
  have hSumX : (∑ c ∈ X, (L c).card) ≤ (H₀ \ fixedDecompositionCore H₀ U).card := by
    convert hTouch using 1
    apply Finset.sum_congr rfl
    intro c hc
    rw [hLinks c hc]
  have hParts : (∑ c ∈ Z, (L c).card) =
      (∑ c ∈ Z, (pairOwnerCleanedLink L owner c).card) +
      ∑ c ∈ Z, (L c \ pairOwnerCleanedLink L owner c).card := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    have h := Finset.card_sdiff_add_card_eq_card (pair_owner_cleaned_link_subset L owner c)
    omega
  have hUnion := initial_outer_cleaned_union_card L Z owner (fun c _ T hT =>
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).2)
  change H.card ≤ (Z.biUnion (pairOwnerCleanedLink L owner)).card +
    (fixedDecompositionCore H U).card + _
  change (fixedDecompositionError H U (Z ∪ X)).card ≤ _ at hError
  change H.card ≤ (fixedDecompositionCore H U).card +
    ((∑ c ∈ Z, (L c).card) + ∑ c ∈ X, (L c).card) + _ at hDecomp
  dsimp only [H₀, W, U, L] at hDecomp hError hSumX hParts hUnion ⊢
  omega

end JSP523.Rank4
