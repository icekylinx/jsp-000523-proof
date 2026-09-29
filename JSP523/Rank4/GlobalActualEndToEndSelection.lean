import JSP523.Rank4.GlobalActualEndToEndError

/-! # Selecting eventual actual data and its concrete vanishing error -/

namespace JSP523.Rank4

/-- Select actual completion data only after the finite construction applies.
The error function is built from the actual selected reciprocal deletions. -/
theorem select_actual_end_to_end_data_with_error
    (H : (n : ℕ) → Family (Fin n)) (U : (n : ℕ) → Edge (Fin n))
    (overlap outerLoss : ℕ → ℕ) (level : ℕ) (a : ℝ)
    (hLevel : 0 < level) (ha : 0 ≤ a)
    (hExists : ∀ᶠ n in Filter.atTop, Nonempty (ActualEndToEndData (H n) (U n) level a (overlap n) (outerLoss n)))
    (hOverlap : Filter.Tendsto (fun n => (overlap n : ℝ) / (n : ℝ) ^ 3) Filter.atTop (nhds 0))
    (hOuter : Filter.Tendsto (fun n => (outerLoss n : ℝ) / (n : ℝ) ^ 3) Filter.atTop (nhds 0)) :
    ∃ D : (n : ℕ) → FiniteCompletionCliqueData (Fin n), ∃ r : ℕ → ℝ,
      Filter.Tendsto r Filter.atTop (nhds 0) ∧
      (∀ᶠ n in Filter.atTop,
        ∃ A : ActualEndToEndData (H n) (U n) level a (overlap n) (outerLoss n),
          D n = A.completion ∧
          (A.masterError : ℝ) / (n : ℝ) ^ 3 ≤ 10 * (256 / (level : ℝ) + a) + r n) := by
  classical
  let P := fun n => Nonempty (ActualEndToEndData (H n) (U n) level a (overlap n) (outerLoss n))
  let D : (n : ℕ) → FiniteCompletionCliqueData (Fin n) :=
    fun n => if h : P n then (Classical.choice h).completion else emptyCompletionData n
  have hCaps : ∀ᶠ n in Filter.atTop,
      (∀ E ∈ (D n).K, E ⊆ (D n).ground) ∧
      (∀ Q : Edge (Fin n), Q.card = 3 → ((D n).K.filter fun E => Q ⊆ E).card ≤ level ^ 8) ∧
      (∀ x y, (reciprocalUsedLabelFiber (D n) x y).card ≤ actualUsedCenterCap (level ^ 8) (level ^ 8) a) := by
    filter_upwards [hExists] with n hn
    change P n at hn
    have hD : D n = (Classical.choice hn).completion := by simp only [D, dite_eq_left hn]
    rw [hD]
    exact (Classical.choice hn).completion_caps
  let r := fun n => 4 * ((overlap n : ℝ) / (n : ℝ) ^ 3) +
    10 * ((outerLoss n : ℝ) / (n : ℝ) ^ 3) + endToEndVanishingError D level a n
  have hr : Filter.Tendsto r Filter.atTop (nhds 0) := by
    simpa only [r, mul_zero, add_zero] using ((hOverlap.const_mul 4).add (hOuter.const_mul 10)).add
      (end_to_end_vanishing_error_tendsto_zero D level a hCaps)
  refine ⟨D, r, hr, ?_⟩
  filter_upwards [hExists, Filter.eventually_ge_atTop (1 : ℕ)] with n hn hn1
  change P n at hn
  let A := Classical.choice hn
  have hD : D n = A.completion := by simp only [D, dite_eq_left hn, A]
  refine ⟨A, hD, ?_⟩
  have h := A.master_error_ratio_bound D hD hn1 hLevel ha
  dsimp only [r]
  simpa only [mul_div_assoc, add_assoc] using h

/-- The prescribed level and weak-cell coefficient leave half of ε unused;
the actual remainder still tends to zero. -/
theorem select_actual_end_to_end_data_with_small_error
    (H : (n : ℕ) → Family (Fin n)) (U : (n : ℕ) → Edge (Fin n))
    (overlap outerLoss : ℕ → ℕ) (ε : ℝ) (hε : 0 < ε)
    (hExists : ∀ᶠ n in Filter.atTop,
      Nonempty (ActualEndToEndData (H n) (U n) (endToEndLevel ε) (endToEndWeakCoefficient ε) (overlap n) (outerLoss n)))
    (hOverlap : Filter.Tendsto (fun n => (overlap n : ℝ) / (n : ℝ) ^ 3) Filter.atTop (nhds 0))
    (hOuter : Filter.Tendsto (fun n => (outerLoss n : ℝ) / (n : ℝ) ^ 3) Filter.atTop (nhds 0)) :
    ∃ D : (n : ℕ) → FiniteCompletionCliqueData (Fin n), ∃ r : ℕ → ℝ,
      Filter.Tendsto r Filter.atTop (nhds 0) ∧
      (∀ᶠ n in Filter.atTop,
        ∃ A : ActualEndToEndData (H n) (U n) (endToEndLevel ε) (endToEndWeakCoefficient ε) (overlap n) (outerLoss n),
          D n = A.completion ∧ (A.masterError : ℝ) / (n : ℝ) ^ 3 ≤ ε / 2 + r n) := by
  have hp := end_to_end_parameter_bounds ε hε
  obtain ⟨D, r, hr, hData⟩ := select_actual_end_to_end_data_with_error H U overlap outerLoss
    (endToEndLevel ε) (endToEndWeakCoefficient ε) (by omega) (le_of_lt hp.2.1) hExists hOverlap hOuter
  refine ⟨D, r, hr, ?_⟩
  filter_upwards [hData] with n hn
  obtain ⟨A, hD, hBound⟩ := hn
  refine ⟨A, hD, ?_⟩
  linarith [hp.2.2]

end JSP523.Rank4
