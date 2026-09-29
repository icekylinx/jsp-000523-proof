import JSP523.Rank5.HigherRankActualCleanup
import JSP523.Rank5.ColorQuantitativeFixedPaletteInteger

/-!
# The two actual higher-rank majority cleanup costs at rounded scales
-/

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α] [Nonempty α]

/-- One root layer of the actual fixed-palette cleanup, with all four
ordinary degree caps taken from the common parent. -/
theorem higher_actual_palette_layer_scale_bound
    (H : Family α) (V : Edge α) (U r s core : ℕ)
    (hU : 2 ≤ U) (hN : U ^ 32 ≤ V.card)
    (hs : 2 ≤ s) (hCore : 3 ≤ core) (hRank : r = core + s)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hAmbient : ∀ E ∈ H, E ⊆ V)
    (hSample : 2 * fixedPaletteSampleSize core ≤
      V.card ^ (s - 1) / U ^ 3)
    (hCap : ∀ S : Edge α, 2 ≤ S.card → S.card ≤ r - 1 →
      (H.filter fun E => S ⊆ E).card ≤
        4 * U ^ 2 * V.card ^ (r - 1 - S.card)) :
    ((multilevelDeletedEdges H V (V.powersetCard core) s
      (V.card ^ (s - 1) / U ^ 3) (V.card ^ (s - 1) / U ^ 6)
      (fun B P Q => ¬ ActualStrongPartner H V P Q s core
        (V.card ^ (core - 2) / U ^ 9)
        (fixedPaletteMajorityLabel H V s core
          (V.card ^ (core - 2) / U ^ 9) B))).card : ℝ) ≤
      (fixedPaletteAmbientErrorConstant core : ℝ) *
        ((V.card : ℝ) ^ (r - 1) / U) +
      (fixedPaletteMassErrorConstant r s core : ℝ) *
        ((H.card : ℝ) / U) := by
  let N := V.card
  let t := N ^ (core - 2) / U ^ 9
  let u := N ^ (s - 1) / U ^ 3
  let q := N ^ (s - 1) / U ^ 6
  have hUOne : 1 ≤ U := by omega
  have hUpos : 0 < U := by omega
  have hNOne : 1 ≤ N := (Nat.one_le_pow _ _ hUOne).trans hN
  have hCorePow : 1 ≤ core - 2 := by omega
  have hRootPow : 1 ≤ s - 1 := by omega
  have hNCore : N ≤ N ^ (core - 2) := by
    simpa only [pow_one] using pow_le_pow_right₀ hNOne hCorePow
  have hNRoot : N ≤ N ^ (s - 1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hNOne hRootPow
  have hTDen : U ^ 9 ≤ N ^ (core - 2) :=
    ((pow_le_pow_right₀ hUOne (by omega : 9 ≤ 32)).trans hN).trans hNCore
  have hQDen : U ^ 6 ≤ N ^ (s - 1) :=
    ((pow_le_pow_right₀ hUOne (by omega : 6 ≤ 32)).trans hN).trans hNRoot
  have ht : 1 ≤ t := (Nat.le_div_iff_mul_le (pow_pos hUpos 9)).2 (by simpa [t] using hTDen)
  have hq : 0 < q := by
    have h : 1 ≤ q :=
      (Nat.le_div_iff_mul_le (pow_pos hUpos 6)).2
        (by simpa only [one_mul] using hQDen)
    omega
  have hD₃ : ∀ S : Edge α, S.card = s + 1 →
      (H.filter fun E => S ⊆ E).card ≤
        4 * U ^ 2 * N ^ (core - 2) := by
    intro S hS
    have h := hCap S (by omega) (by omega)
    have he : r - 1 - S.card = core - 2 := by omega
    simpa only [N, he] using h
  have hD₄ : ∀ S : Edge α, S.card = s + 2 →
      (H.filter fun E => S ⊆ E).card ≤
        4 * U ^ 2 * N ^ (core - 3) := by
    intro S hS
    have h := hCap S (by omega) (by omega)
    have he : r - 1 - S.card = core - 3 := by omega
    simpa only [N, he] using h
  have hDcore : ∀ S : Edge α, S.card = core →
      (H.filter fun E => S ⊆ E).card ≤
        4 * U ^ 2 * N ^ (s - 1) := by
    intro S hS
    have h := hCap S (by omega) (by omega)
    have he : r - 1 - S.card = s - 1 := by omega
    simpa only [N, he] using h
  have hDnext : ∀ S : Edge α, S.card = core + 1 →
      (H.filter fun E => S ⊆ E).card ≤
        4 * U ^ 2 * N ^ (s - 2) := by
    intro S hS
    have h := hCap S (by omega) (by omega)
    have he : r - 1 - S.card = s - 2 := by omega
    simpa only [N, he] using h
  have hCost := fixed_palette_cleanup_card_le_explicit_cost
    H V r s core t u q
    (4 * U ^ 2 * N ^ (core - 2)) (4 * U ^ 2 * N ^ (core - 3))
    (4 * U ^ 2 * N ^ (s - 1)) (4 * U ^ 2 * N ^ (s - 2))
    (by omega) (by omega) hAdm hUniform hAmbient hSample ht hq
    hD₃ hD₄ hDcore hDnext
  have hNumeric := fixed_palette_integer_cleanup_cost_bound
    N H.card U r s core hUOne hN hs hCore
  have hPower : core + s - 1 = r - 1 := by omega
  have hNumeric' : fixedPaletteCleanupCost N H.card r s core t u q
      (4 * U ^ 2 * N ^ (core - 2)) (4 * U ^ 2 * N ^ (core - 3))
      (4 * U ^ 2 * N ^ (s - 1)) (4 * U ^ 2 * N ^ (s - 2)) ≤
      (fixedPaletteAmbientErrorConstant core : ℝ) *
        ((N : ℝ) ^ (r - 1) / U) +
      (fixedPaletteMassErrorConstant r s core : ℝ) *
        ((H.card : ℝ) / U) := by
    simpa only [t, u, q, hPower] using hNumeric
  exact hCost.trans hNumeric'

/-- Both actual majority deletions are charged from the same parent
codegree caps. -/
theorem higher_actual_majority_cleanup_scale_bound
    (H : Family α) (V : Edge α) (U k : ℕ)
    (hU : 2 ≤ U) (hN : U ^ 32 ≤ V.card)
    (hAdm : Admissible H) (hUniform : Uniform (k + 6) H)
    (hAmbient : ∀ E ∈ H, E ⊆ V)
    (hSamplePair : 2 * fixedPaletteSampleSize (k + 4) ≤
      V.card / U ^ 3)
    (hSampleTriple : 2 * fixedPaletteSampleSize (k + 3) ≤
      V.card ^ 2 / U ^ 3)
    (hCap : ∀ S : Edge α, 2 ≤ S.card → S.card ≤ k + 5 →
      (H.filter fun E => S ⊆ E).card ≤
        4 * U ^ 2 * V.card ^ (k + 5 - S.card)) :
    ((higherMajorityDeletedEdges H V (k + 3)
      (V.card ^ (k + 2) / U ^ 9)
      (V.card ^ (k + 1) / U ^ 9)
      (V.card / U ^ 3) (V.card / U ^ 6)
      (V.card ^ 2 / U ^ 3) (V.card ^ 2 / U ^ 6)).card : ℝ) ≤
      ((fixedPaletteAmbientErrorConstant (k + 4) +
          fixedPaletteAmbientErrorConstant (k + 3) : ℕ) : ℝ) *
        ((V.card : ℝ) ^ (k + 5) / U) +
      ((fixedPaletteMassErrorConstant (k + 6) 2 (k + 4) +
          fixedPaletteMassErrorConstant (k + 6) 3 (k + 3) : ℕ) : ℝ) *
        ((H.card : ℝ) / U) := by
  let N := V.card
  let B₂ := multilevelDeletedEdges H V (V.powersetCard (k + 4)) 2
    (N / U ^ 3) (N / U ^ 6)
    (fun B P Q => ¬ ActualStrongPartner H V P Q 2 (k + 4)
      (N ^ (k + 2) / U ^ 9)
      (fixedPaletteMajorityLabel H V 2 (k + 4) (N ^ (k + 2) / U ^ 9) B))
  let B₃ := multilevelDeletedEdges H V (V.powersetCard (k + 3)) 3
    (N ^ 2 / U ^ 3) (N ^ 2 / U ^ 6)
    (fun B P Q => ¬ ActualStrongPartner H V P Q 3 (k + 3)
      (N ^ (k + 1) / U ^ 9)
      (fixedPaletteMajorityLabel H V 3 (k + 3) (N ^ (k + 1) / U ^ 9) B))
  have hB₂ := higher_actual_palette_layer_scale_bound
    H V U (k + 6) 2 (k + 4) hU hN
    (by omega) (by omega) (by omega)
    hAdm hUniform hAmbient
    (by simpa only [show 2 - 1 = 1 by omega, pow_one] using hSamplePair)
    (by simpa only [show k + 6 - 1 = k + 5 by omega] using hCap)
  have hB₃ := higher_actual_palette_layer_scale_bound
    H V U (k + 6) 3 (k + 3) hU hN
    (by omega) (by omega) (by omega)
    hAdm hUniform hAmbient (by simpa only [show 3 - 1 = 2 by omega] using hSampleTriple)
    (by simpa only [show k + 6 - 1 = k + 5 by omega] using hCap)
  have hUnion : (higherMajorityDeletedEdges H V (k + 3)
      (N ^ (k + 2) / U ^ 9) (N ^ (k + 1) / U ^ 9)
      (N / U ^ 3) (N / U ^ 6) (N ^ 2 / U ^ 3) (N ^ 2 / U ^ 6)).card ≤
      B₂.card + B₃.card := by
    simpa only [higherMajorityDeletedEdges, B₂, B₃,
      show k + 3 + 1 = k + 4 by omega] using Finset.card_union_le B₂ B₃
  have hUnionR : ((higherMajorityDeletedEdges H V (k + 3)
      (N ^ (k + 2) / U ^ 9) (N ^ (k + 1) / U ^ 9)
      (N / U ^ 3) (N / U ^ 6) (N ^ 2 / U ^ 3) (N ^ 2 / U ^ 6)).card : ℝ) ≤
      (B₂.card : ℝ) + (B₃.card : ℝ) := by exact_mod_cast hUnion
  have hB₂' : (B₂.card : ℝ) ≤
      (fixedPaletteAmbientErrorConstant (k + 4) : ℝ) *
        ((N : ℝ) ^ (k + 5) / U) +
      (fixedPaletteMassErrorConstant (k + 6) 2 (k + 4) : ℝ) *
        ((H.card : ℝ) / U) := by
    simpa only [B₂, N, show 2 - 1 = 1 by omega, pow_one,
      show k + 4 - 2 = k + 2 by omega,
      show k + 6 - 1 = k + 5 by omega] using hB₂
  have hB₃' : (B₃.card : ℝ) ≤
      (fixedPaletteAmbientErrorConstant (k + 3) : ℝ) *
        ((N : ℝ) ^ (k + 5) / U) +
      (fixedPaletteMassErrorConstant (k + 6) 3 (k + 3) : ℝ) *
        ((H.card : ℝ) / U) := by
    simpa only [B₃, N, show 3 - 1 = 2 by omega,
      show k + 3 - 2 = k + 1 by omega,
      show k + 6 - 1 = k + 5 by omega] using hB₃
  change ((higherMajorityDeletedEdges H V (k + 3)
      (N ^ (k + 2) / U ^ 9) (N ^ (k + 1) / U ^ 9)
      (N / U ^ 3) (N / U ^ 6) (N ^ 2 / U ^ 3) (N ^ 2 / U ^ 6)).card : ℝ) ≤ _
  push_cast
  nlinarith [hB₂', hB₃', hUnionR]

end JSP523.Rank5
