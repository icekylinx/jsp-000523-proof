import JSP523.Rank3.PartIIAssembly
import JSP523.Rank3.ReceiverCapacityFinal
import JSP523.Rank3.BridgeDemandAccounting
import JSP523.Rank3.BridgePaymentGlobal
import JSP523.Rank3.BlockFreeBridge

/-!
# Theorem II.1: actual rank-three support inequality

This module assembles the independently proved geometric steps of Part II in
`paper/proof.pdf`: actual receiver capacity (II.8), removal of
near-complete five-blocks, nonduplication of positive bridge demands, local
bridge payment, and the signed support ledger (II.9).
-/

namespace JSP523.Rank3

variable {α : Type*} [DecidableEq α]

/-- The bridge excess of a block-free admissible triple family is paid by
its actual local signed defects. -/
theorem actual_xi_le_local_defects_of_block_free
    (H : Family α) (V : Edge α)
    (hU : Uniform 3 H) (hAdm : Admissible H)
    (hGround : ∀ E ∈ H, E ⊆ V)
    (hFree : ∀ A : Edge α, A ⊆ V → ¬ nearCompleteBlock H A) :
    actualXi H V ≤ ∑ E ∈ H, localSignedDefect H V E := by
  have hNoBlock := no_nine_or_ten_triple_block_of_ground_block_free
    H V hU hGround hFree
  apply actual_xi_le_local_signed_defect_sum_of_bridge_geometry
    H V hAdm hU hGround
  · intro E hE q₁ hq₁ q₂ hq₂ hpos₁ hpos₂
    exact positive_bridge_demand_unique hAdm hU hNoBlock
      E hE q₁ q₂ hq₁ hq₂ hpos₁ hpos₂
  · intro E hE q hq hpos
    exact bridge_demand_le_local_signed_defect_of_positive
      H V q E hAdm hU hGround hE hpos

/-- The first inequality of Theorem II.1 on the actual pair and cell
supports, for every finite ambient vertex set. -/
theorem rank_three_actual_support_bound
    (H : Family α) (V : Edge α)
    (hU : Uniform 3 H) (hAdm : Admissible H)
    (hGround : ∀ E ∈ H, E ⊆ V) :
    2 * H.card ≤ (usedPairs H V).card + (usedCells H V).card := by
  apply actual_support_of_block_free_case H V hU hAdm hGround
  intro K hUK hAdmK hGroundK hFreeK
  have hIncoming := incoming_charge_le_actual_capacity K V hAdmK
  have hCapacity := positive_total_le_capacity_of_incoming_bound
    K V hUK hGroundK hIncoming
  have hPaid := actual_xi_le_local_defects_of_block_free
    K V hUK hAdmK hGroundK hFreeK
  exact actual_support_of_capacity_and_bridge_payment
    K V (actualXi K V) hUK hAdmK hGroundK hCapacity hPaid

/-- The second inequality of Theorem II.1: each support is a collection
of actual pairs in the ambient vertex set. -/
theorem rank_three_actual_supports_le_two_choose
    (H : Family α) (V : Edge α) :
    (usedPairs H V).card + (usedCells H V).card ≤
      2 * V.card.choose 2 := by
  have hPairs := Finset.card_le_card (used_pairs_subset H V)
  have hCells := Finset.card_le_card (used_cells_subset H V)
  rw [Finset.card_powersetCard] at hPairs hCells
  omega

/-- Theorem II.1, including both support inequalities and the resulting
rank-three extremal bound. -/
theorem rank_three_part_ii_theorem
    (H : Family α) (V : Edge α)
    (hU : Uniform 3 H) (hAdm : Admissible H)
    (hGround : ∀ E ∈ H, E ⊆ V) :
    2 * H.card ≤ (usedPairs H V).card + (usedCells H V).card ∧
    (usedPairs H V).card + (usedCells H V).card ≤
      2 * V.card.choose 2 ∧
    H.card ≤ V.card.choose 2 := by
  have hFirst := rank_three_actual_support_bound H V hU hAdm hGround
  have hSecond := rank_three_actual_supports_le_two_choose H V
  exact ⟨hFirst, hSecond, by omega⟩

end JSP523.Rank3
