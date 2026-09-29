import JSP523.Rank4.PreprocessActualCompletionAssembly
import JSP523.Rank4.GlobalReciprocalAsymptotic

/-! # Limits of the actual finite master error terms -/

namespace JSP523.Rank4

/-- An actual nonnegative error negligible on the cubic scale is also
negligible on the binomial scale in the master estimate. -/
theorem nonnegative_cubic_error_choose_ratio_tendsto_zero
    (f : ℕ → ℝ) (hNonneg : ∀ n, 0 ≤ f n)
    (hCube : Filter.Tendsto (fun n => f n / (n : ℝ) ^ 3) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => f n / (n.choose 3 : ℝ)) Filter.atTop (nhds 0) := by
  have hUpper : Filter.Tendsto (fun n => 12 * (f n / (n : ℝ) ^ 3)) Filter.atTop (nhds 0) := by
    simpa using hCube.const_mul 12
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => div_nonneg (hNonneg n) (by positivity))) ?_ hUpper
  filter_upwards [cubic_le_twelve_choose_eventually, Filter.eventually_ge_atTop (3 : ℕ)] with n hn hn3
  have hChoose : (0 : ℝ) < n.choose 3 := by exact_mod_cast Nat.choose_pos hn3
  have hCubePos : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  have hInv : 1 / (n.choose 3 : ℝ) ≤ 12 / (n : ℝ) ^ 3 := by
    apply (div_le_div_iff₀ hChoose hCubePos).2
    nlinarith
  simpa only [one_div, div_eq_mul_inv, mul_assoc, mul_left_comm, one_mul] using
    mul_le_mul_of_nonneg_left hInv (hNonneg n)

/-- The explicit quadratic repeated-color wedge budget vanishes after
normalization; the coefficient may depend on the fixed preprocessing parameters. -/
theorem quadratic_error_choose_ratio_tendsto_zero (C : ℕ) :
    Filter.Tendsto (fun n : ℕ => ((C * n ^ 2 : ℕ) : ℝ) / (n.choose 3 : ℝ))
      Filter.atTop (nhds 0) := by
  apply nonnegative_cubic_error_choose_ratio_tendsto_zero _ (fun _ => by positivity)
  have hInv : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  have hSimple := hInv.const_mul (C : ℝ)
  apply (show Filter.Tendsto (fun n : ℕ => (C : ℝ) * (n : ℝ)⁻¹) Filter.atTop (nhds 0) by simpa using hSimple).congr'
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  push_cast
  field_simp

/-- The actual integer square-root sampling error is negligible. -/
theorem star_sampling_error_choose_ratio_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => ((n ^ 2 * (Nat.sqrt n + 1) : ℕ) : ℝ) / (n.choose 3 : ℝ))
      Filter.atTop (nhds 0) := by
  apply nonnegative_cubic_error_choose_ratio_tendsto_zero _ (fun _ => by positivity)
  have hNat : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
  have hInv := hNat.inv_tendsto_atTop
  have hSqrtInv := (Real.tendsto_sqrt_atTop.comp hNat).inv_tendsto_atTop
  have hUpper : Filter.Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹ + (n : ℝ)⁻¹)
      Filter.atTop (nhds 0) := by simpa using hSqrtInv.add hInv
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => by positivity)) ?_ hUpper
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  have hnPos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnPos
  have hsPos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnPos
  have hs0 := ne_of_gt hsPos
  have hsq := Real.sq_sqrt (le_of_lt hnPos)
  have hNatSq : ((Nat.sqrt n : ℕ) : ℝ) ^ 2 ≤ n := by exact_mod_cast Nat.sqrt_le' n
  have hSqrt : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) := by nlinarith
  have hUpperEq : (Real.sqrt (n : ℝ))⁻¹ + (n : ℝ)⁻¹ =
      ((n : ℝ) ^ 2 * (Real.sqrt (n : ℝ) + 1)) / (n : ℝ) ^ 3 := by
    field_simp
    nlinarith [hsq]
  rw [hUpperEq]
  apply div_le_div_of_nonneg_right _ (by positivity)
  push_cast
  gcongr

/-- The complete fixed-parameter remainder in the actual master bound:
star sampling, bicolored wedge deletion, and reciprocal cleanup. -/
noncomputable def actualMasterVanishingRemainder
    (D : (n : ℕ) → FiniteCompletionCliqueData (Fin n)) (d κ n : ℕ) : ℝ :=
  (((n ^ 2 * (Nat.sqrt n + 1) : ℕ) : ℝ) / (n.choose 3 : ℝ)) / 5 +
    ((d ^ 2 * κ ^ 2 * n ^ 2 : ℕ) : ℝ) / (n.choose 3 : ℝ) +
    (((D n).K \ (clearUsedParentThenReciprocal (D n)).K).card : ℝ) / (n.choose 3 : ℝ)

/-- Every term remaining after weak-cell and decomposition coefficients
is an actual normalized error tending to zero. -/
theorem actual_master_vanishing_remainder_tendsto_zero
    (D : (n : ℕ) → FiniteCompletionCliqueData (Fin n)) (d κ : ℕ)
    (hGround : ∀ n, ∀ E ∈ (D n).K, E ⊆ (D n).ground)
    (hFacet : ∀ n, ∀ T : Edge (Fin n), T.card = 3 →
      ((D n).K.filter fun E => T ⊆ E).card ≤ d)
    (hFiber : ∀ n, ∀ a b, (reciprocalUsedLabelFiber (D n) a b).card ≤ κ) :
    Filter.Tendsto (actualMasterVanishingRemainder D d κ) Filter.atTop (nhds 0) := by
  have hStar := star_sampling_error_choose_ratio_tendsto_zero.div_const 5
  have hColor := quadratic_error_choose_ratio_tendsto_zero (d ^ 2 * κ ^ 2)
  have hRecip := clear_used_parent_then_reciprocal_loss_choose_ratio_tendsto_zero D d κ hGround hFacet hFiber
  unfold actualMasterVanishingRemainder
  simpa using (hStar.add hColor).add hRecip

end JSP523.Rank4
