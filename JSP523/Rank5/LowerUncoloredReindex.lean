import JSP523.Rank5.LowerCoreColoring

/-! # Reindexing actual lower-core uncolored supports

Uncolored support pairs are charged either to overlapping parent partners
or to the actual disjoint nonstrong common cells.
-/

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α]

noncomputable def lowerCoreUncoloredDisjointPairs
    (H : Family α) (V B : Edge α) (t : ℕ) : Finset (Edge α × Edge α) := by
  classical
  exact (lowerUncoloredRootPairs H V t).filter fun p => B ∈ commonPrefixTails H V p.1 p.2 3

theorem lower_core_uncolored_supports_le_pair_counts
    (H : Family α) (V B : Edge α) (t : ℕ)
    (hB : B ∈ V.powersetCard 3) :
    (uncoloredEdgeSupports (actualCoreLink H V B 2) (lowerCoreSupportColor H V B t)).card ≤
      (∑ P ∈ parentPairLink H V B, (overlappingParentPartners H V B P).card) +
      (lowerCoreUncoloredDisjointPairs H V B t).card := by
  classical
  let L := actualCoreLink H V B 2
  let O := (L ×ˢ L).filter fun p => ¬ Disjoint p.1 p.2
  let D := lowerCoreUncoloredDisjointPairs H V B t
  have hCover : uncoloredEdgeSupports L (lowerCoreSupportColor H V B t) ⊆
      (O.image fun p => ({p.1,p.2} : Finset (Edge α))) ∪
      (D.image fun p => ({p.1,p.2} : Finset (Edge α))) := by
    intro e he
    have hParts := Finset.mem_filter.mp he
    have hE := Finset.mem_powersetCard.mp hParts.1
    obtain ⟨P,Q,hPQ,hPair⟩ := Finset.card_eq_two.mp hE.2
    have hP : P ∈ L := hE.1 (by rw [hPair]; simp)
    have hQ : Q ∈ L := hE.1 (by rw [hPair]; simp)
    have hp := mem_actual_core_link.mp hP
    have hq := mem_actual_core_link.mp hQ
    have hPRoot : P ∈ V.powersetCard 2 := Finset.mem_powersetCard.mpr ⟨hp.1,hp.2.1⟩
    have hQRoot : Q ∈ V.powersetCard 2 := Finset.mem_powersetCard.mpr ⟨hq.1,hq.2.1⟩
    have hNone : lowerCoreSupportColor H V B t {P,Q} = none := by simpa only [hPair] using hParts.2
    have hNoStrong : ∀ z, ¬ ActualStrongPartner H V P Q 2 3 t z := by
      intro z hz
      have hzB := lower_strong_label_mem_actual_core H V B P Q t
        (Finset.mem_powersetCard.mp hB).1 (Finset.mem_powersetCard.mp hB).2 hP hQ hz
      have hColor := (lower_core_support_color_eq_some_iff H V B t
        (Finset.card_pair hPQ) (z := ⟨z,hzB⟩)).2
          ((lower_support_pair_has_label_iff H V P Q t hPRoot hPQ).2 hz)
      rw [hNone] at hColor
      cases hColor
    by_cases hDisj : Disjoint P Q
    · have hCell : B ∈ commonPrefixTails H V P Q 3 := mem_common_prefix_tails.mpr
        ⟨(Finset.mem_powersetCard.mp hB).1,(Finset.mem_powersetCard.mp hB).2,
          Finset.disjoint_union_right.mpr ⟨hp.2.2.1.symm,hq.2.2.1.symm⟩,
          by simpa only [Finset.union_comm] using hp.2.2.2,
          by simpa only [Finset.union_comm] using hq.2.2.2⟩
      have hD : (P,Q) ∈ D := Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hPRoot,hQRoot⟩,hDisj,hNoStrong⟩,hCell⟩
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(P,Q),hD,hPair.symm⟩)
    · have hO : (P,Q) ∈ O := Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hP,hQ⟩,hDisj⟩
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(P,Q),hO,hPair.symm⟩)
  have hO : O.card = ∑ P ∈ parentPairLink H V B,
      (overlappingParentPartners H V B P).card := by
    simp only [O,L,actual_core_link_two_eq_parent_pair_link, overlappingParentPartners,
      Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
  have hCount := (Finset.card_le_card hCover).trans (Finset.card_union_le _ _)
  have hImageO := Finset.card_image_le (s := O) (f := fun p => ({p.1,p.2} : Finset (Edge α)))
  have hImageD := Finset.card_image_le (s := D) (f := fun p => ({p.1,p.2} : Finset (Edge α)))
  dsimp only [L,D] at hCount hImageD
  omega

/-- Reindex the disjoint bad pairs by their two roots. Their possible
    supporting triple cores are exactly the actual common cell. -/
theorem lower_core_uncolored_disjoint_pairs_sum_eq_cells
    (H : Family α) (V : Edge α) (t : ℕ) :
    (∑ B ∈ V.powersetCard 3, (lowerCoreUncoloredDisjointPairs H V B t).card) =
      ∑ p ∈ lowerUncoloredRootPairs H V t, (commonPrefixTails H V p.1 p.2 3).card := by
  classical
  have hSwap : (∑ B ∈ V.powersetCard 3, (lowerCoreUncoloredDisjointPairs H V B t).card) =
      ∑ p ∈ lowerUncoloredRootPairs H V t,
        ((V.powersetCard 3).filter fun B => B ∈ commonPrefixTails H V p.1 p.2 3).card := by
    simp only [lowerCoreUncoloredDisjointPairs, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
  rw [hSwap]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  ext B
  simp only [Finset.mem_filter]
  constructor
  · exact And.right
  · intro hB
    have hParts := mem_common_prefix_tails.mp hB
    exact ⟨Finset.mem_powersetCard.mpr ⟨hParts.1,hParts.2.1⟩,hB⟩

/-- The complete actual uncolored-support budget in IV.7.3 at rank five. -/
theorem lower_uncolored_support_sum_budget
    (H : Family α) (V : Edge α) (t D₄ : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform 5 H)
    (hAmbient : ∀ E ∈ H, E ⊆ V)
    (hD₄ : ∀ S : Edge α, S.card = 4 → (H.filter fun E => S ⊆ E).card ≤ D₄) :
    (∑ B ∈ V.powersetCard 3,
      (uncoloredEdgeSupports (actualCoreLink H V B 2) (lowerCoreSupportColor H V B t)).card) ≤
      (V.powersetCard 2).card ^ 2 * (t + 9 * D₄) + 20 * D₄ * H.card := by
  have hLocal := Finset.sum_le_sum (fun B (hB : B ∈ V.powersetCard 3) =>
    lower_core_uncolored_supports_le_pair_counts H V B t hB)
  rw [Finset.sum_add_distrib, lower_core_uncolored_disjoint_pairs_sum_eq_cells] at hLocal
  have hOverlap := overlapping_partner_incidence_sum_le_four_codegree_budget
    H V D₄ hUniform hAmbient hD₄
  have hDisjoint := lower_uncolored_cell_incidence_budget H V t D₄ hAdm hD₄
  omega

end JSP523.Rank5
