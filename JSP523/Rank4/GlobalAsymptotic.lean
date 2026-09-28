import JSP523.Rank4.GlobalLeadingInterface

/-!
# Parameter-cleanup limits for PART III

The theorems here are abstract sequence limit steps.  Their hypotheses
state the parameter-cleanup conclusions that are needed from the finite
arguments; they do not prove that cleanup for the parameters of III.A.
-/

namespace JSP523.Rank4

/-- A finite-error upper bound with an arbitrarily small fixed coefficient
and a remainder tending to zero implies the desired upper limit. -/
theorem tendsto_one_of_small_error_coefficients
    (f : ℕ → ℝ)
    (hLower : ∀ᶠ n in Filter.atTop, 1 ≤ f n)
    (hUpper : ∀ ε : ℝ, 0 < ε →
      ∃ r : ℕ → ℝ,
        Filter.Tendsto r Filter.atTop (nhds 0) ∧
        ∀ᶠ n in Filter.atTop, f n ≤ 1 + ε + r n) :
    Filter.Tendsto f Filter.atTop (nhds 1) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards [hLower] with n hn
    exact lt_of_lt_of_le ha hn
  · intro a ha
    let ε := (a - 1) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    obtain ⟨r, hr, hEventually⟩ := hUpper ε hε
    have hrSmall : ∀ᶠ n in Filter.atTop, r n < ε := by
      exact (tendsto_order.1 hr).2 ε hε
    filter_upwards [hEventually, hrSmall] with n hFn hrn
    dsimp [ε] at *
    linarith

/-- The ratio used in the extremal asymptotic statement. -/
noncomputable def rankFourExtremalRatio (g₄ : ℕ → ℕ) (n : ℕ) : ℝ :=
  (g₄ n : ℝ) / (n.choose 3 : ℝ)

/-- Abstract III.B.5 extremal limit: the star construction supplies the
eventual lower bound, while parameter cleanup supplies arbitrarily small
finite error coefficients and a normalized `o(1)` remainder. -/
theorem rank_four_extremal_ratio_tendsto_one
    (g₄ : ℕ → ℕ)
    (hStarLower : ∀ᶠ n in Filter.atTop,
      1 ≤ rankFourExtremalRatio g₄ n)
    (hCleanedUpper : ∀ ε : ℝ, 0 < ε →
      ∃ r : ℕ → ℝ,
        Filter.Tendsto r Filter.atTop (nhds 0) ∧
        ∀ᶠ n in Filter.atTop,
          rankFourExtremalRatio g₄ n ≤ 1 + ε + r n) :
    Filter.Tendsto (rankFourExtremalRatio g₄) Filter.atTop (nhds 1) :=
  tendsto_one_of_small_error_coefficients
    (rankFourExtremalRatio g₄) hStarLower hCleanedUpper

/-- A nonnegative normalized remainder goes to zero when the parameter
choice makes its fixed coefficient arbitrarily small and its remaining
normalized error tends to zero. -/
theorem tendsto_zero_of_small_error_coefficients
    (f : ℕ → ℝ)
    (hNonneg : ∀ᶠ n in Filter.atTop, 0 ≤ f n)
    (hUpper : ∀ ε : ℝ, 0 < ε →
      ∃ r : ℕ → ℝ,
        Filter.Tendsto r Filter.atTop (nhds 0) ∧
        ∀ᶠ n in Filter.atTop, f n ≤ ε + r n) :
    Filter.Tendsto f Filter.atTop (nhds 0) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    have hEventually : ∀ᶠ n in Filter.atTop, a < f n := by
      filter_upwards [hNonneg] with n hn
      linarith
    exact hEventually
  · intro a ha
    let ε := a / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    obtain ⟨r, hr, hEventually⟩ := hUpper ε hε
    have hrSmall : ∀ᶠ n in Filter.atTop, r n < ε := by
      exact (tendsto_order.1 hr).2 ε hε
    filter_upwards [hEventually, hrSmall] with n hFn hrn
    dsimp [ε] at *
    linarith

/-- Stability's parameter order in explicit form.  For each target
`ε`, preprocessing/cleanup must choose `τ`, then a fixed degree threshold
`M`, then the master parameter `ν`; the normalized remainder may depend on
all three.  This theorem is the sequence-limit conclusion of precisely
that premise. -/
theorem rank_four_stability_ratio_tendsto_zero
    (badRatio : ℕ → ℝ)
    (hNonneg : ∀ᶠ n in Filter.atTop, 0 ≤ badRatio n)
    (hParameterCleanup : ∀ ε : ℝ, 0 < ε →
      ∃ τ M ν : ℝ, ∃ r : ℕ → ℝ,
        0 < τ ∧ 1 ≤ M ∧ 0 < ν ∧
        (10 * M + 1) * ν + τ < ε ∧
        Filter.Tendsto r Filter.atTop (nhds 0) ∧
        ∀ᶠ n in Filter.atTop,
          badRatio n ≤ (10 * M + 1) * ν + τ + r n) :
    Filter.Tendsto badRatio Filter.atTop (nhds 0) := by
  apply tendsto_zero_of_small_error_coefficients badRatio hNonneg
  intro ε hε
  obtain ⟨τ, M, ν, r, hτ, hM, hν, hCoeff, hr, hBound⟩ :=
    hParameterCleanup ε hε
  refine ⟨r, hr, ?_⟩
  filter_upwards [hBound] with n hn
  linarith

end JSP523.Rank4
