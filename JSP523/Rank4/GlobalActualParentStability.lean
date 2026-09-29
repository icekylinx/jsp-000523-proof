import JSP523.Rank4.GlobalActualMasterNormalization

/-! # Parent stability directly from the actual master surplus -/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- This form consumes the actual master inequality itself, rather than
an independently assumed bound on its nonprivate/private surplus. -/
theorem actual_parent_stability_of_master
    (B K B₁ : Family α) (U : Edge α) (M Hcard N masterError highError : ℕ)
    (hKB : K ⊆ B) (hB₁B : B₁ ⊆ B)
    (hUniform : Uniform 4 B) (hGround : ∀ E ∈ B, E ⊆ U)
    (hM : 1 ≤ M)
    (hCap : ∀ T ∈ U.powersetCard 3, 2 * (facetCompletions B₁ U T).card ≤ M)
    (hMaster : 10 * Hcard + (rankFourNonprivateFacets K U).card +
      6 * (rankFourAllPrivateEdges K U).card ≤ 10 * N + masterError)
    (hLower : N ≤ Hcard + highError) :
    B.card ≤ M * (masterError + 10 * highError) +
      8 * (B \ B₁).card + (B \ K).card := by
  have hSurplus : (rankFourNonprivateFacets K U).card +
      6 * (rankFourAllPrivateEdges K U).card ≤ masterError + 10 * highError := by omega
  have hCore := rank_four_core_stability_finite B K B₁ U M hKB hB₁B hUniform hGround hCap
  have hPrivate : (rankFourAllPrivateEdges K U).card ≤
      (6 * M) * (rankFourAllPrivateEdges K U).card := by
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hScale := Nat.mul_le_mul_left M hSurplus
  have hCard := Finset.card_sdiff_add_card_eq_card hKB
  nlinarith

/-- The parameter order required by stability is explicit: after the
degree cap `M` has been fixed, choose `ν` as this positive fraction. -/
theorem actual_stability_parameters (ε : ℝ) (hε : 0 < ε) (M : ℝ) (hM : 1 ≤ M) :
    let τ := ε / 4
    let ν := ε / (4 * (10 * M + 1))
    0 < τ ∧ 0 < ν ∧ (10 * M + 1) * ν + τ < ε := by
  dsimp
  have hDen : 0 < 4 * (10 * M + 1) := by linarith
  refine ⟨by positivity, div_pos hε hDen, ?_⟩
  have hCancel : (10 * M + 1) * (ε / (4 * (10 * M + 1))) = ε / 4 := by
    field_simp
  rw [hCancel]
  linarith

end JSP523.Rank4
