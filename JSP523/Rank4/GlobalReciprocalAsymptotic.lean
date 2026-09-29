import JSP523.Rank4.PreprocessReciprocalC4Asymptotic
import JSP523.Rank4.GlobalAsymptotic

/-! # Actual reciprocal cleanup in the rank-four limit interface -/

namespace JSP523.Rank4

/-- The three actual reciprocal preprocessing rounds supply the vanishing
remainder in the rank-four extremal parameter cleanup. The remaining
finite upper estimate is stated with that concrete loss term. -/
theorem rank_four_extremal_ratio_tendsto_one_of_actual_reciprocal_cleanup
    (g₄ : ℕ → ℕ)
    (D : (n : ℕ) → FiniteCompletionCliqueData (Fin n))
    (Dcap Kstar : ℕ)
    (h_ground : ∀ n : ℕ, ∀ E ∈ (D n).K,
      E ⊆ (D n).ground)
    (h_facet : ∀ n : ℕ, ∀ T : Edge (Fin n), T.card = 3 →
      ((D n).K.filter fun E => T ⊆ E).card ≤ Dcap)
    (h_label : ∀ n : ℕ, ∀ a b : Fin n,
      (reciprocalUsedLabelFiber (D n) a b).card ≤ Kstar)
    (h_star_lower : ∀ᶠ n in Filter.atTop,
      1 ≤ rankFourExtremalRatio g₄ n)
    (h_upper : ∀ ε : ℝ, 0 < ε →
      ∃ r : ℕ → ℝ,
        Filter.Tendsto r Filter.atTop (nhds 0) ∧
        ∀ᶠ n in Filter.atTop,
          rankFourExtremalRatio g₄ n ≤
            1 + ε + r n +
              ((((D n).K \
                (clearUsedParentThenReciprocal (D n)).K).card : ℕ) : ℝ) /
                (n.choose 3 : ℝ)) :
    Filter.Tendsto (rankFourExtremalRatio g₄)
      Filter.atTop (nhds 1) := by
  have h_cleanup :=
    clear_used_parent_then_reciprocal_loss_choose_ratio_tendsto_zero
      D Dcap Kstar h_ground h_facet h_label
  apply rank_four_extremal_ratio_tendsto_one g₄ h_star_lower
  intro ε hε
  obtain ⟨r, hr, hBound⟩ := h_upper ε hε
  have hRemainder : Filter.Tendsto
      (fun n =>
        r n +
          ((((D n).K \
            (clearUsedParentThenReciprocal (D n)).K).card : ℕ) : ℝ) /
            (n.choose 3 : ℝ)) Filter.atTop (nhds 0) := by
    simpa using hr.add h_cleanup
  refine ⟨fun n =>
    r n +
      ((((D n).K \
        (clearUsedParentThenReciprocal (D n)).K).card : ℕ) : ℝ) /
        (n.choose 3 : ℝ), hRemainder, ?_⟩
  filter_upwards [hBound] with n hn
  linarith

/-- The same actual cleanup remainder can be absorbed in the stability
parameter order after τ, M, ν have been chosen. -/
theorem rank_four_stability_ratio_tendsto_zero_of_actual_reciprocal_cleanup
    (bad_ratio : ℕ → ℝ)
    (D : (n : ℕ) → FiniteCompletionCliqueData (Fin n))
    (Dcap Kstar : ℕ)
    (h_ground : ∀ n : ℕ, ∀ E ∈ (D n).K,
      E ⊆ (D n).ground)
    (h_facet : ∀ n : ℕ, ∀ T : Edge (Fin n), T.card = 3 →
      ((D n).K.filter fun E => T ⊆ E).card ≤ Dcap)
    (h_label : ∀ n : ℕ, ∀ a b : Fin n,
      (reciprocalUsedLabelFiber (D n) a b).card ≤ Kstar)
    (h_nonneg : ∀ᶠ n in Filter.atTop, 0 ≤ bad_ratio n)
    (h_parameter_cleanup : ∀ ε : ℝ, 0 < ε →
      ∃ τ M ν : ℝ, ∃ r : ℕ → ℝ,
        0 < τ ∧ 1 ≤ M ∧ 0 < ν ∧
        (10 * M + 1) * ν + τ < ε ∧
        Filter.Tendsto r Filter.atTop (nhds 0) ∧
        ∀ᶠ n in Filter.atTop,
          bad_ratio n ≤ (10 * M + 1) * ν + τ + r n +
            ((((D n).K \
              (clearUsedParentThenReciprocal (D n)).K).card : ℕ) : ℝ) /
              (n.choose 3 : ℝ)) :
    Filter.Tendsto bad_ratio Filter.atTop (nhds 0) := by
  have h_cleanup :=
    clear_used_parent_then_reciprocal_loss_choose_ratio_tendsto_zero
      D Dcap Kstar h_ground h_facet h_label
  apply rank_four_stability_ratio_tendsto_zero bad_ratio h_nonneg
  intro ε hε
  obtain ⟨τ, M, ν, r, hτ, hM, hν, hCoeff, hr, hBound⟩ :=
    h_parameter_cleanup ε hε
  have hRemainder : Filter.Tendsto
      (fun n =>
        r n +
          ((((D n).K \
            (clearUsedParentThenReciprocal (D n)).K).card : ℕ) : ℝ) /
            (n.choose 3 : ℝ)) Filter.atTop (nhds 0) := by
    simpa using hr.add h_cleanup
  refine ⟨τ, M, ν, fun n =>
    r n +
      ((((D n).K \
        (clearUsedParentThenReciprocal (D n)).K).card : ℕ) : ℝ) /
        (n.choose 3 : ℝ),
      hτ, hM, hν, hCoeff, hRemainder, ?_⟩
  filter_upwards [hBound] with n hn
  linarith

end JSP523.Rank4
