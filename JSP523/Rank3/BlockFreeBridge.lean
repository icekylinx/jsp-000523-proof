import JSP523.Rank3.NearCompleteBlocks
import JSP523.Rank3.BridgeNonduplication

/-!
# Bridging the block-free reduction to bridge-book nonduplication

The sequential reduction excludes dense five-blocks within the ground set.
A grounded uniform triple family cannot have a nine-triple five-block
containing an outside vertex, since only four ground vertices remain.
-/

namespace JSP523.Rank3

variable {α : Type*} [DecidableEq α]

theorem noNineOrTenTripleBlock_of_ground_blockFree
    (H : Family α) (V : Edge α)
    (hU : Uniform 3 H)
    (hGround : ∀ E ∈ H, E ⊆ V)
    (hFree : ∀ A : Edge α, A ⊆ V → ¬ nearCompleteBlock H A) :
    NoNineOrTenTripleBlock H := by
  intro S hScard
  let B := blockTriples H S
  have hBound : B.card ≤ 8 := by
    by_cases hSV : S ⊆ V
    · have hNot := hFree S hSV
      have hNotDense : ¬ 9 ≤ B.card := by
        intro hDense
        exact hNot ⟨hScard, hDense⟩
      omega
    · have hOut : (S \ V).Nonempty := by
        by_contra h
        exact hSV (Finset.sdiff_eq_empty_iff_subset.mp
          (Finset.not_nonempty_iff_eq_empty.mp h))
      obtain ⟨x, hxOut⟩ := hOut
      have hxS : x ∈ S := (Finset.mem_sdiff.mp hxOut).1
      have hxV : x ∉ V := (Finset.mem_sdiff.mp hxOut).2
      have hEraseCard : (S.erase x).card = 4 := by
        have hCard := Finset.card_erase_add_one hxS
        omega
      have hSub : B ⊆ (S.erase x).powersetCard 3 := by
        intro E hEB
        obtain ⟨hEH, hES⟩ := Finset.mem_filter.mp hEB
        have hxE : x ∉ E := fun h => hxV (hGround E hEH h)
        apply Finset.mem_powersetCard.mpr
        constructor
        · intro y hy
          exact Finset.mem_erase.mpr
            ⟨fun h => hxE (h ▸ hy), hES hy⟩
        · exact hU hEH
      have hCard := Finset.card_le_card hSub
      rw [Finset.card_powersetCard, hEraseCard] at hCard
      norm_num at hCard
      omega
  change B.card ≠ 9 ∧ B.card ≠ 10
  omega

end JSP523.Rank3
