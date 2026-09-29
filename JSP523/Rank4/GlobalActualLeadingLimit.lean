import JSP523.Rank4.GlobalActualMasterNormalization

/-! # Leading limit from concrete finite masters

This conditional limit theorem takes the actual star decomposition and its
outer loss as inputs. Imported finite estimates supply the inner preprocessing
remainders, and the proof chooses the weak-cell parameter.
-/

namespace JSP523.Rank4

/-- Assemble the actual finite master and its proved error limits.  The
outer decomposition and overlap have an arbitrarily small
normalized budget. -/
theorem rank_four_ratio_tendsto_one_of_actual_masters
    (g : ℕ → ℕ)
    (hLower : ∀ᶠ n in Filter.atTop, 1 ≤ rankFourExtremalRatio g n)
    (hMasters : ∀ a : ℝ, 0 < a →
      ∃ d κ : ℕ, ∃ D : (n : ℕ) → FiniteCompletionCliqueData (Fin n),
      ∃ u b m overlap outerLoss : ℕ → ℕ,
        (∀ n, u n ≤ n) ∧
        (∀ n, ∀ E ∈ (D n).K, E ⊆ (D n).ground) ∧
        (∀ n, ∀ T : Edge (Fin n), T.card = 3 →
          ((D n).K.filter fun E => T ⊆ E).card ≤ d) ∧
        (∀ n, ∀ x y, (reciprocalUsedLabelFiber (D n) x y).card ≤ κ) ∧
        (∀ᶠ n in Filter.atTop,
          (outerLoss n : ℝ) / (n.choose 3 : ℝ) +
            2 * (overlap n : ℝ) / (5 * (n.choose 3 : ℝ)) ≤ a) ∧
        (∀ᶠ n in Filter.atTop,
          10 * g n + b n + 6 * m n ≤
            10 * (u n).choose 3 + 2 * (u n ^ 2 * (Nat.sqrt (u n) + 1)) + 4 * overlap n +
              10 * (outerLoss n + (2 * (actualWeakCellThreshold a n - 1) * (u n).choose 2 +
                d ^ 2 * u n ^ 2 * κ ^ 2 +
                ((D n).K \ (clearUsedParentThenReciprocal (D n)).K).card)))) :
    Filter.Tendsto (rankFourExtremalRatio g) Filter.atTop (nhds 1) := by
  apply rank_four_extremal_ratio_tendsto_one g hLower
  intro ε hε
  let a := ε / 13
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨d, κ, D, u, b, m, overlap, outerLoss, hu, hGround, hFacet, hFiber, hOuter, hMaster⟩ :=
    hMasters a ha
  refine ⟨actualMasterVanishingRemainder D d κ,
    actual_master_vanishing_remainder_tendsto_zero D d κ hGround hFacet hFiber, ?_⟩
  have hNormalized := actual_master_normalized_eventually D a (le_of_lt ha) d κ
    u g b m overlap outerLoss hu hMaster
  filter_upwards [hNormalized, hOuter] with n hN hO
  have hSurplus : 0 ≤ ((b n : ℝ) + 6 * m n) / (10 * (n.choose 3 : ℝ)) := by positivity
  dsimp only [rankFourExtremalRatio]
  dsimp only [a] at hN hO
  linarith

end JSP523.Rank4
