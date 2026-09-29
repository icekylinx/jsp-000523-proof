import JSP523.Rank4.GlobalActualEndToEndSelection

namespace JSP523.Rank4

def liftSuccCompletion (D : (n : ℕ) → FiniteCompletionCliqueData (Fin (n + 1))) :
    (m : ℕ) → FiniteCompletionCliqueData (Fin m)
  | 0 => emptyCompletionData 0
  | m + 1 => D m

/-- Select the actual packets with the `Fin (n+1)` indexing used by the
near-star endpoint. The radius coefficient absorbs the factor eight. -/
theorem select_actual_end_to_end_succ_with_small_error
    (H : (n : ℕ) → Family (Fin (n + 1))) (U : (n : ℕ) → Edge (Fin (n + 1)))
    (overlap outerLoss : ℕ → ℕ) (ε : ℝ) (hε : 0 < ε)
    (hExists : ∀ᶠ n in Filter.atTop,
      Nonempty (ActualEndToEndData (H n) (U n) (endToEndLevel (ε / 8)) (endToEndWeakCoefficient (ε / 8)) (overlap n) (outerLoss n)))
    (hOverlap : Filter.Tendsto (fun n => (overlap n : ℝ) / (n : ℝ) ^ 3) Filter.atTop (nhds 0))
    (hOuter : Filter.Tendsto (fun n => (outerLoss n : ℝ) / (n : ℝ) ^ 3) Filter.atTop (nhds 0)) :
    ∃ D : (n : ℕ) → FiniteCompletionCliqueData (Fin (n + 1)), ∃ r : ℕ → ℝ,
      Filter.Tendsto r Filter.atTop (nhds 0) ∧
      (∀ᶠ n in Filter.atTop,
        ∃ A : ActualEndToEndData (H n) (U n) (endToEndLevel (ε / 8)) (endToEndWeakCoefficient (ε / 8)) (overlap n) (outerLoss n),
          D n = A.completion ∧ (A.masterError : ℝ) / (n : ℝ) ^ 3 ≤ ε / 2 + r n) := by
  classical
  let level := endToEndLevel (ε / 8)
  let a := endToEndWeakCoefficient (ε / 8)
  have hp := end_to_end_parameter_bounds (ε / 8) (by positivity)
  let P := fun n => Nonempty (ActualEndToEndData (H n) (U n) level a (overlap n) (outerLoss n))
  let D : (n : ℕ) → FiniteCompletionCliqueData (Fin (n + 1)) :=
    fun n => if h : P n then (Classical.choice h).completion else emptyCompletionData (n + 1)
  have hCaps : ∀ᶠ m in Filter.atTop,
      (∀ E ∈ (liftSuccCompletion D m).K, E ⊆ (liftSuccCompletion D m).ground) ∧
      (∀ Q : Edge (Fin m), Q.card = 3 → ((liftSuccCompletion D m).K.filter fun E => Q ⊆ E).card ≤ level ^ 8) ∧
      (∀ x y, (reciprocalUsedLabelFiber (liftSuccCompletion D m) x y).card ≤ actualUsedCenterCap (level ^ 8) (level ^ 8) a) := by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hExists
    filter_upwards [Filter.eventually_ge_atTop (N + 1)] with m hm
    cases m with
    | zero => omega
    | succ n =>
      have hn : P n := hN n (by omega)
      have hD : D n = (Classical.choice hn).completion := by simp only [D, dite_eq_left hn]
      simp only [liftSuccCompletion]
      rw [hD]
      exact (Classical.choice hn).completion_caps
  have hErr := (end_to_end_vanishing_error_tendsto_zero (liftSuccCompletion D) level a hCaps).comp
    (Filter.tendsto_add_atTop_nat 1)
  let r := fun n => 32 * ((overlap n : ℝ) / (n : ℝ) ^ 3) +
    80 * ((outerLoss n : ℝ) / (n : ℝ) ^ 3) + 8 * endToEndVanishingError (liftSuccCompletion D) level a (n + 1)
  have hr : Filter.Tendsto r Filter.atTop (nhds 0) := by
    simpa only [r, mul_zero, add_zero, Function.comp_def] using
      ((hOverlap.const_mul 32).add (hOuter.const_mul 80)).add (hErr.const_mul 8)
  refine ⟨D, r, hr, ?_⟩
  filter_upwards [hExists, Filter.eventually_ge_atTop (1 : ℕ)] with n hn hn1
  change P n at hn
  let A := Classical.choice hn
  have hD : D n = A.completion := by simp only [D, dite_eq_left hn, A]
  have hBound := A.master_error_ratio_bound (liftSuccCompletion D) hD (Nat.succ_pos n) (by omega) (le_of_lt hp.2.1)
  have hnPos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hSuccPos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ 3 := by positivity
  have hCube : ((n + 1 : ℕ) : ℝ) ^ 3 ≤ 8 * (n : ℝ) ^ 3 := by
    have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    push_cast
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hScale : (A.masterError : ℝ) / (n : ℝ) ^ 3 ≤
      8 * ((A.masterError : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 3) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 3)).2
    have hNum := mul_le_mul_of_nonneg_left hCube (show (0 : ℝ) ≤ A.masterError by positivity)
    have hDiv := (le_div_iff₀ hSuccPos).2 hNum
    convert hDiv using 1
    ring
  have hMono : (n : ℝ) ^ 3 ≤ ((n + 1 : ℕ) : ℝ) ^ 3 := by push_cast; gcongr; norm_num
  have hO : (overlap n : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 3 ≤ (overlap n : ℝ) / (n : ℝ) ^ 3 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hMono
  have hL : (outerLoss n : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 3 ≤ (outerLoss n : ℝ) / (n : ℝ) ^ 3 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hMono
  refine ⟨A, hD, ?_⟩
  dsimp only [r]
  simp only [mul_div_assoc] at hBound
  have hCoeff : 10 * (256 / (level : ℝ) + a) ≤ ε / 16 := by linarith [hp.2.2]
  linarith

end JSP523.Rank4
