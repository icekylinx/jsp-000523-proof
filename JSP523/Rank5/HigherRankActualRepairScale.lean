import JSP523.Rank5.HigherRankActualCleanup
import JSP523.Rank5.HigherRankParameterError

/-! # Numerical loss of both repairs on the actual cleaned family -/
namespace JSP523.Rank5
variable {α : Type*} [DecidableEq α] [Nonempty α]

theorem higher_actual_repair_scale_bound
    (H : Family α) (V : Edge α) (U k tSingleton : ℕ)
    (hU : 2 ≤ U) (hN : U ^ 32 ≤ V.card)
    (hUniform : Uniform (k + 6) H) (hAmbient : ∀ E ∈ H, E ⊆ V)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ 4 * U ^ 2 * V.card ^ (k + 2))
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ 4 * U ^ 2 * V.card ^ (k + 1))
    (hD₅ : ∀ S : Edge α, S.card = 5 →
      (H.filter fun E => S ⊆ E).card ≤ 4 * U ^ 2 * V.card ^ k)
    (hDBase : ∀ S : Edge α, S.card = k + 4 →
      (H.filter fun E => S ⊆ E).card ≤ 4 * U ^ 2 * V.card)
    (hDFacet : ∀ S : Edge α, S.card = k + 5 →
      (H.filter fun E => S ⊆ E).card ≤ 4 * U ^ 2) :
    let N := V.card
    let tPair := N ^ (k + 2) / U ^ 9
    let tTriple := N ^ (k + 1) / U ^ 9
    let uPair := N / U ^ 3
    let qPair := N / U ^ 6
    let uTriple := N ^ 2 / U ^ 3
    let qTriple := N ^ 2 / U ^ 6
    let K := higherCleanedFamily H V (k + 3) tSingleton tPair tTriple
      uPair qPair uTriple qTriple
    let L := higherFinalFamily H V (k + 3) tSingleton tPair tTriple
      uPair qPair uTriple qTriple
    let C := HigherRankUpper.lowFacetIncidenceConstant (k + 4) +
      HigherRankLower.lowFacetIncidenceConstant (k + 3)
    ((K.card - L.card : ℕ) : ℝ) ≤
      16 * C * ((H.card : ℝ) / U) + 640 * ((N : ℝ) ^ (k + 5) / U) := by
  classical
  let N := V.card
  let tPair := N ^ (k + 2) / U ^ 9
  let tTriple := N ^ (k + 1) / U ^ 9
  let uPair := N / U ^ 3
  let qPair := N / U ^ 6
  let uTriple := N ^ 2 / U ^ 3
  let qTriple := N ^ 2 / U ^ 6
  let K := higherCleanedFamily H V (k + 3) tSingleton tPair tTriple
    uPair qPair uTriple qTriple
  let L := higherFinalFamily H V (k + 3) tSingleton tPair tTriple
    uPair qPair uTriple qTriple
  let C := HigherRankUpper.lowFacetIncidenceConstant (k + 4) +
    HigherRankLower.lowFacetIncidenceConstant (k + 3)
  have hUOne : 1 ≤ U := by omega
  have hNOne : 1 ≤ N := (Nat.one_le_pow _ _ hUOne).trans hN
  have hNSq : U ^ 32 ≤ N ^ 2 := hN.trans (by nlinarith)
  have hp := higher_parameter_feasibility N U hU hN
  have ht := higher_parameter_feasibility (N ^ 2) U hU hNSq
  rcases hp with ⟨_, _, _, hqPairPos, hScalePair, hGapPair, _⟩
  rcases ht with ⟨_, _, _, hqTriplePos, hScaleTriple, hGapTriple, _⟩
  have hPairBounds := higher_power_quotient_real_bounds N U (k + 2) 9 hUOne hN
    (by omega) (by omega)
  have hTripleBounds := higher_power_quotient_real_bounds N U (k + 1) 9 hUOne hN
    (by omega) (by omega)
  have hQPairBounds := higher_power_quotient_real_bounds N U 1 6 hUOne hN
    (by omega) (by omega)
  have hQTripleBounds := higher_power_quotient_real_bounds N U 2 6 hUOne hN
    (by omega) (by omega)
  have hUp : (0 : ℝ) < U := by exact_mod_cast (by omega : 0 < U)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have htPairReal : (0 : ℝ) < tPair := lt_of_lt_of_le (by positivity) hPairBounds.1
  have htTripleReal : (0 : ℝ) < tTriple := lt_of_lt_of_le (by positivity) hTripleBounds.1
  have htPair : 1 ≤ tPair := by exact_mod_cast htPairReal
  have htTriple : 1 ≤ tTriple := by exact_mod_cast htTripleReal
  have h := higher_cleaned_family_properties H V (k + 3) tSingleton tPair tTriple
    uPair qPair uTriple qTriple
  have hRaw := repaired_higher_rank_loss_budget K H V (k + 3) 16 (U ^ 3)
    (4 * qPair) (4 * qTriple) tSingleton tPair tTriple uPair qPair uTriple qTriple
    (4 * U ^ 2 * N ^ (k + 2)) (4 * U ^ 2 * N ^ (k + 1))
    (4 * U ^ 2 * N ^ k) (4 * U ^ 2 * N) (4 * U ^ 2)
    (higherMajorityCenter H V (k + 3) tPair tTriple) h.1
    (fun E hE => by simpa only [Nat.add_assoc] using hUniform (h.1 hE))
    (by simpa only [Nat.add_assoc] using hUniform) hAmbient h.2.1 h.2.2.1 h.2.2.2
    (pow_pos (by omega) _) hScalePair hScaleTriple (by omega) (by omega)
    hGapPair hGapTriple htPair htTriple hD₃ hD₄ hD₅
    (by simpa only [Nat.add_assoc] using hDBase)
    (by simpa only [Nat.add_assoc] using hDFacet)
  let W₂ := 8 * N.choose 2 ^ 2 * (4 * U ^ 2 * N ^ (k + 2)) *
    (4 * U ^ 2) * (4 * U ^ 2 * N ^ (k + 1))
  let W₃ := 12 * N.choose 3 ^ 2 * (4 * U ^ 2 * N ^ (k + 1)) *
    (4 * U ^ 2 * N) * (4 * U ^ 2 * N ^ k)
  have hBudget : U ^ 3 * (8 * tPair * qPair) * (16 * tTriple * qPair * qTriple) *
      (K.card - L.card) ≤
      (8 * tPair * qPair) * (16 * tTriple * qPair * qTriple) * (16 * C * H.card) +
      U ^ 3 * ((8 * tPair * qPair) * W₃ + (16 * tTriple * qPair * qTriple) * W₂) := by
    dsimp only at hRaw
    simp only [Finset.card_powersetCard, Nat.add_assoc] at hRaw
    convert hRaw using 1 <;> dsimp [W₂, W₃, C, L, higherFinalFamily, N] <;> ring
  exact higher_repair_scale_bound_of_budget N U k (K.card - L.card) H.card C
    tPair tTriple qPair qTriple W₂ W₃ hU hN hPairBounds.1 hTripleBounds.1
    (by simpa only [pow_one] using hQPairBounds.1) hQTripleBounds.1
    (higher_facet_witness_numerator_bound N U _ _ _ k (by rfl) (by rfl) (by rfl))
    (higher_lower_witness_numerator_bound N U _ _ _ k (by rfl) (by rfl) (by rfl)) hBudget

end JSP523.Rank5
