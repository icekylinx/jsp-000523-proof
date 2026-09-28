import JSP523.Rank4.SharedBudget
import JSP523.Rank4.GlobalStabilityFinite

/-!
# Explicit leading-order and stability interfaces for PART III

This file packages the finite inequalities used in §III.B.5.  Error terms
remain explicit natural numbers: passing to a sequence or removing the
fixed-parameter errors is a separate asymptotic argument.
-/

namespace JSP523.Rank4

/-! The master estimate gives an explicit leading bound once the ground
triple count is compared with the ambient triple count. -/

theorem rank_four_leading_bound_of_master
    (Hcard N n masterError ambientError : ℕ)
    (hMaster : 10 * Hcard ≤ 10 * N + masterError)
    (hAmbient : N ≤ n.choose 3 + ambientError) :
    10 * Hcard ≤ 10 * n.choose 3 + masterError + 10 * ambientError := by
  omega

/-! This is the direct finite form for the original family: the master
budget, original decomposition, retained-remainder deletion, and comparison
of the fixed ground set with the ambient set are all explicit premises. -/

theorem rank_four_original_leading_bound
    (Hcard a m outsideCard b m₀ s V N overlapError graphError
      deletionError layerError n ambientError : ℕ)
    (hDeficit : b + 6 * m₀ + 10 * m ≤ 2 * V + 4 * s)
    (hStarNative : 3 * a + V ≤ 3 * N + graphError)
    (hDisjoint : a + s ≤ N + overlapError)
    (hOriginal : Hcard ≤ a + outsideCard + layerError)
    (hDeletion : outsideCard ≤ m + deletionError)
    (hAmbient : N ≤ n.choose 3 + ambientError) :
    10 * Hcard ≤ 10 * n.choose 3 + 2 * graphError +
      4 * overlapError + 10 * (deletionError + layerError + ambientError) := by
  have hBudget := shared_budget_original_edge_bound
    hDeficit hStarNative hDisjoint hOriginal hDeletion
  omega

/-! The lower bound on the original family converts the finite master
inequality into a surplus bound, retaining every preprocessing and
decomposition loss as a named parameter. -/

theorem rank_four_surplus_bound_of_near_extremal
    (Hcard a m outsideCard S N masterError highError layerError
      deletionError : ℕ)
    (hMaster : 5 * (a + m) + S ≤ 5 * N + masterError)
    (hHigh : N ≤ Hcard + highError)
    (hOriginal : Hcard ≤ a + outsideCard + layerError)
    (hDeletion : outsideCard ≤ m + deletionError) :
    S ≤ masterError + 5 * (highError + layerError + deletionError) :=
  shared_budget_deficit_small hMaster hHigh hOriginal hDeletion

/-! Quantitative stability in terms of the cleaned surplus and the actual
degree-tail deletion.  The finite parent theorem supplies the combinatorial
step; this wrapper exposes the exact error budget needed for normalization. -/

theorem rank_four_parent_stability_explicit
    {α : Type*} [DecidableEq α]
    (B K B₁ : Family α) (U : Edge α) (M S cleanup : ℕ)
    (hKB : K ⊆ B)
    (hB₁B : B₁ ⊆ B)
    (hUniform : Uniform 4 B)
    (hGround : ∀ E ∈ B, E ⊆ U)
    (hM : 1 ≤ M)
    (hCap : ∀ T ∈ U.powersetCard 3,
      2 * (facetCompletions B₁ U T).card ≤ M)
    (hSurplus :
      (rankFourNonprivateFacets K U).card +
        6 * (rankFourAllPrivateEdges K U).card ≤ 2 * S)
    (hCleanup : (B \ K).card ≤ cleanup) :
    B.card ≤ 2 * M * S + 8 * (B \ B₁).card + cleanup := by
  have hParent := rank_four_parent_stability_from_surplus
    B K B₁ U M S hKB hB₁B hUniform hGround hM hCap hSurplus
  omega

theorem rank_four_parent_stability_normalized
    {α : Type*} [DecidableEq α]
    (B K B₁ : Family α) (U : Edge α) (M S n sigma tau kappa : ℕ)
    (hKB : K ⊆ B)
    (hB₁B : B₁ ⊆ B)
    (hUniform : Uniform 4 B)
    (hGround : ∀ E ∈ B, E ⊆ U)
    (hM : 1 ≤ M)
    (hCap : ∀ T ∈ U.powersetCard 3,
      2 * (facetCompletions B₁ U T).card ≤ M)
    (hSurplus :
      (rankFourNonprivateFacets K U).card +
        6 * (rankFourAllPrivateEdges K U).card ≤ 2 * S)
    (hS : S ≤ sigma * n ^ 3)
    (hTail : (B \ B₁).card ≤ tau * n ^ 3)
    (hCleanup : (B \ K).card ≤ kappa * n ^ 3) :
    B.card ≤ (2 * M * sigma + 8 * tau + kappa) * n ^ 3 := by
  have hParent := rank_four_parent_stability_explicit
    B K B₁ U M S (kappa * n ^ 3)
    hKB hB₁B hUniform hGround hM hCap hSurplus hCleanup
  have hScaleS := Nat.mul_le_mul_left (2 * M) hS
  have hScaleTail := Nat.mul_le_mul_left 8 hTail
  calc
    B.card ≤ 2 * M * S + 8 * (B \ B₁).card + kappa * n ^ 3 := hParent
    _ ≤ 2 * M * (sigma * n ^ 3) + 8 * (tau * n ^ 3) + kappa * n ^ 3 := by
      omega
    _ = (2 * M * sigma + 8 * tau + kappa) * n ^ 3 := by ring

end JSP523.Rank4
