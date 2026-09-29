import JSP523.Rank5.HigherRankPrefixScale
import JSP523.Rank5.HigherRankUpperParameter
import JSP523.Rank5.HigherRankMajorityScale

/-! # Complete actual structural error at every rank at least six -/
namespace JSP523.Rank5

noncomputable def higherStructuralAmbientConstant (k : ℕ) : ℕ :=
  1166 + 8 * (k + 5) ^ 2 + fixedPaletteAmbientErrorConstant (k + 4) +
    fixedPaletteAmbientErrorConstant (k + 3) + 640 + 4 * k + 13

noncomputable def higherStructuralMassConstant (k : ℕ) : ℕ :=
  fixedPaletteMassErrorConstant (k + 6) 2 (k + 4) +
    fixedPaletteMassErrorConstant (k + 6) 3 (k + 3) +
    16 * (HigherRankUpper.lowFacetIncidenceConstant (k + 4) +
      HigherRankLower.lowFacetIncidenceConstant (k + 3))

variable {α : Type*} [DecidableEq α] [Nonempty α]

theorem higher_actual_structural_scale_bound
    (H : Family α) (V : Edge α) (U k : ℕ)
    (hU : 2 ≤ U) (hN : U ^ 32 ≤ V.card)
    (hAdm : Admissible H) (hUniform : Uniform (k + 6) H) (hAmbient : ∀ E ∈ H, E ⊆ V)
    (hSamplePair : 2 * fixedPaletteSampleSize (k + 4) ≤ V.card / U ^ 3)
    (hSampleTriple : 2 * fixedPaletteSampleSize (k + 3) ≤ V.card ^ 2 / U ^ 3)
    (hCap : ∀ S : Edge α, 2 ≤ S.card → S.card ≤ k + 5 →
      (H.filter fun E => S ⊆ E).card ≤ 4 * U ^ 2 * V.card ^ (k + 5 - S.card)) :
    (H.card : ℝ) ≤ (higherStructuralAmbientConstant k : ℝ) *
        ((V.card : ℝ) ^ (k + 5) / U) +
      3 * ((V.card : ℝ) ^ (k + 5) / Real.sqrt U) +
      (higherStructuralMassConstant k : ℝ) * ((H.card : ℝ) / U) := by
  classical
  let N := V.card
  let tSingleton := N ^ (k + 3) / U ^ 9
  let tPair := N ^ (k + 2) / U ^ 9
  let tTriple := N ^ (k + 1) / U ^ 9
  let uPair := N / U ^ 3
  let qPair := N / U ^ 6
  let uTriple := N ^ 2 / U ^ 3
  let qTriple := N ^ 2 / U ^ 6
  have hAt (j : ℕ) (hj : 2 ≤ j) (hj' : j ≤ k + 5)
      (S : Edge α) (hS : S.card = j) :
      (H.filter fun E => S ⊆ E).card ≤ 4 * U ^ 2 * N ^ (k + 5 - j) := by
    simpa only [hS] using hCap S (by omega) (by omega)
  have hD₂ : ∀ S : Edge α, S.card = 2 →
      (H.filter fun E => S ⊆ E).card ≤ 4 * U ^ 2 * N ^ (k + 3) := by
    simpa only [show k + 5 - 2 = k + 3 by omega] using hAt 2 (by omega) (by omega)
  have hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ 4 * U ^ 2 * N ^ (k + 2) := by
    simpa only [show k + 5 - 3 = k + 2 by omega] using hAt 3 (by omega) (by omega)
  have hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ 4 * U ^ 2 * N ^ (k + 1) := by
    simpa only [show k + 5 - 4 = k + 1 by omega] using hAt 4 (by omega) (by omega)
  have hD₅ : ∀ S : Edge α, S.card = 5 →
      (H.filter fun E => S ⊆ E).card ≤ 4 * U ^ 2 * N ^ k := by
    simpa only [show k + 5 - 5 = k by omega] using hAt 5 (by omega) (by omega)
  have hDBase : ∀ S : Edge α, S.card = k + 4 →
      (H.filter fun E => S ⊆ E).card ≤ 4 * U ^ 2 * N := by
    simpa only [show k + 5 - (k + 4) = 1 by omega, pow_one] using
      hAt (k + 4) (by omega) (by omega)
  have hDFacet : ∀ S : Edge α, S.card = k + 5 →
      (H.filter fun E => S ⊆ E).card ≤ 4 * U ^ 2 := by
    simpa only [Nat.sub_self, pow_zero, mul_one] using hAt (k + 5) (by omega) (by omega)
  have hSingle := higher_actual_singleton_cleanup_scale_bound H V U k hU hN hAdm
    hD₂ hD₃ hD₄ hDFacet
  have hMajority := higher_actual_majority_cleanup_scale_bound H V U k hU hN hAdm
    hUniform hAmbient hSamplePair hSampleTriple hCap
  have hRepair := higher_actual_repair_scale_bound H V U k tSingleton hU hN hUniform
    hAmbient hD₃ hD₄ hD₅ hDBase hDFacet
  have hPrefix := higher_actual_final_family_scale_bound H V U k tSingleton hU hN hAdm
    hUniform hAmbient hDBase hD₄
  have hMass := higher_final_family_mass_accounting H V (k + 3) tSingleton tPair tTriple
    uPair qPair uTriple qTriple
  have hMassReal : (H.card : ℝ) ≤
      ((higherFinalFamily H V (k + 3) tSingleton tPair tTriple uPair qPair uTriple qTriple).card : ℝ) +
      ((HigherRankUpper.upperFacetColorCleanupEdges (k + 5) H V tSingleton).card : ℝ) +
      ((higherMajorityDeletedEdges H V (k + 3) tPair tTriple uPair qPair uTriple qTriple).card : ℝ) +
      (((higherCleanedFamily H V (k + 3) tSingleton tPair tTriple uPair qPair uTriple qTriple).card -
        (higherFinalFamily H V (k + 3) tSingleton tPair tTriple uPair qPair uTriple qTriple).card : ℕ) : ℝ) := by
    simpa only [Nat.add_assoc, Nat.cast_add] using (show
      (H.card : ℝ) ≤ _ by exact_mod_cast hMass)
  dsimp only at hSingle hRepair hPrefix hMajority
  push_cast at hRepair hMajority
  dsimp [higherStructuralAmbientConstant, higherStructuralMassConstant]
  push_cast
  dsimp [tSingleton, tPair, tTriple, uPair, qPair, uTriple, qTriple, N] at hMassReal
  nlinarith only [hMassReal, hSingle, hMajority, hRepair, hPrefix]

end JSP523.Rank5
