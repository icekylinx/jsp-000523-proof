import JSP523.Rank4.PreprocessReciprocalC4Scale
import Mathlib.Analysis.SpecialFunctions.Choose

/-! # Vanishing normalized fixed-center C4 budget -/

namespace JSP523.Rank4

private theorem real_sqrt_cube (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (x ^ 3) = x * Real.sqrt x := by
  rw [show x ^ 3 = x ^ 2 * x by ring,
    Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq_eq_abs,
    abs_of_nonneg hx]

/-- For fixed color count and pair degree, the explicit finite C4
bound divided by a cubic ambient scale tends to zero. -/
theorem reciprocal_c4_scaled_error_tendsto_zero (A c : ℕ) :
    Filter.Tendsto
      (fun n : ℕ =>
        ((n : ℝ) * (A : ℝ) *
          (Real.sqrt (((c * n : ℕ) : ℝ) ^ 3) +
            ((c * n : ℕ) : ℝ) / 2)) / (n : ℝ) ^ 3)
      Filter.atTop (nhds 0) := by
  have hNat : Filter.Tendsto (fun n : ℕ => (n : ℝ))
      Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
  have hInvNat : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹)
      Filter.atTop (nhds 0) := hNat.inv_tendsto_atTop
  have hInvSqrt : Filter.Tendsto
      (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹)
      Filter.atTop (nhds 0) :=
    (Real.tendsto_sqrt_atTop.comp hNat).inv_tendsto_atTop
  have hSimple : Filter.Tendsto
      (fun n : ℕ =>
        (A : ℝ) * (c : ℝ) * Real.sqrt (c : ℝ) *
          (Real.sqrt (n : ℝ))⁻¹ +
        (A : ℝ) * (c : ℝ) / 2 * (n : ℝ)⁻¹)
      Filter.atTop (nhds 0) := by
    convert (hInvSqrt.const_mul
      ((A : ℝ) * (c : ℝ) * Real.sqrt (c : ℝ))).add
      (hInvNat.const_mul ((A : ℝ) * (c : ℝ) / 2)) using 1; ring_nf
  apply hSimple.congr'
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hs0 : Real.sqrt (n : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hsq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hc : 0 ≤ (c : ℝ) := by positivity
  have hnNonneg : 0 ≤ (n : ℝ) := by positivity
  simp only [Nat.cast_mul]
  rw [real_sqrt_cube ((c : ℝ) * (n : ℝ))
      (mul_nonneg hc hnNonneg),
    Real.sqrt_mul hc]
  field_simp [hn0, hs0]
  have hsqMul := congrArg
    (fun x : ℝ => 2 * (A : ℝ) * (c : ℝ) * Real.sqrt (c : ℝ) * x) hsq
  nlinarith [hsqMul]

/-- For an actual sequence of finite rank-four families on Fin n, the
derived C4 budget is negligible against the cubic ambient scale whenever
the corrected parent-label pair degree has one fixed cap. -/
theorem reciprocal_actual_c4_graph_budget_ratio_tendsto_zero
    (D : (n : ℕ) → FiniteCompletionCliqueData (Fin n))
    (κ : ℕ)
    (color : (n : ℕ) → (x : Fin n) →
      fixedCenterPairNodes (reciprocalUsedParentLabelTriples (D n))
        (D n).ground x → Fin (2 * κ - 1))
    (h_pair : ∀ n : ℕ, ∀ P ∈ (D n).ground.powersetCard 2,
      qPairDegree (reciprocalUsedParentLabelTriples (D n)) P ≤ κ) :
    Filter.Tendsto
      (fun n : ℕ =>
        reciprocalActualC4GraphBudget (D n) κ (color n) /
          (n : ℝ) ^ 3)
      Filter.atTop (nhds 0) := by
  let A := Fintype.card
    (Fin (2 * κ - 1) × Fin (2 * κ - 1))
  have hUpper :=
    reciprocal_c4_scaled_error_tendsto_zero A (2 * κ)
  apply squeeze_zero'
    (Filter.Eventually.of_forall (fun n => by
      apply div_nonneg
      · unfold reciprocalActualC4GraphBudget
        positivity
      · positivity))
    ?_ hUpper
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  have hnPos : (0 : ℝ) < n := by exact_mod_cast hn
  have hU : (D n).ground.card ≤ n := by
    calc
      _ ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  have hUreal : ((D n).ground.card : ℝ) ≤ n := by
    exact_mod_cast hU
  have hC4 := reciprocal_actual_c4_graph_budget_le_scaled
    (D n) κ (color n) (h_pair n)
  have hC : (2 * (D n).ground.card * κ : ℕ) ≤ (2 * κ) * n := by
    nlinarith
  have hCreal :
      ((2 * (D n).ground.card * κ : ℕ) : ℝ) ≤
        (((2 * κ) * n : ℕ) : ℝ) := by exact_mod_cast hC
  have hScale :
      ((D n).ground.card : ℝ) * (A : ℝ) *
        (Real.sqrt (((2 * (D n).ground.card * κ : ℕ) : ℝ) ^ 3) +
          ((2 * (D n).ground.card * κ : ℕ) : ℝ) / 2) ≤
      (n : ℝ) * (A : ℝ) *
        (Real.sqrt (((((2 * κ) * n : ℕ) : ℝ)) ^ 3) +
          ((((2 * κ) * n : ℕ) : ℝ)) / 2) := by
    gcongr
  have hTotal := hC4.trans hScale
  exact div_le_div_of_nonneg_right hTotal (by positivity)

/-- The actual used-parent and reciprocal three-round cleanup loses o(n³)
edges, assuming fixed initial facet and label-fiber degree caps. The
corrected Q degree, reciprocal tail cap, and all C4 colorings are derived
internally from the actual family sequence. -/
theorem clear_used_parent_then_reciprocal_loss_ratio_tendsto_zero
    (D : (n : ℕ) → FiniteCompletionCliqueData (Fin n))
    (Dcap Kstar : ℕ)
    (h_ground : ∀ n : ℕ, ∀ E ∈ (D n).K,
      E ⊆ (D n).ground)
    (h_facet : ∀ n : ℕ, ∀ T : Edge (Fin n), T.card = 3 →
      ((D n).K.filter fun E => T ⊆ E).card ≤ Dcap)
    (h_label : ∀ n : ℕ, ∀ a b : Fin n,
      (reciprocalUsedLabelFiber (D n) a b).card ≤ Kstar) :
    Filter.Tendsto
      (fun n : ℕ =>
        (((D n).K \ (clearUsedParentThenReciprocal (D n)).K).card : ℝ) /
          (n : ℝ) ^ 3)
      Filter.atTop (nhds 0) := by
  classical
  let κ := 2 + 4 * Kstar
  let C := Dcap * κ ^ 2 + Kstar ^ 2 * max Dcap 3 + Dcap
  have hExist (n : ℕ) :
      ∃ color : (x : Fin n) →
          fixedCenterPairNodes
            (reciprocalUsedParentLabelTriples (D n))
            (D n).ground x → Fin (2 * κ - 1),
        (((((D n).K \
          (clearUsedParentThenReciprocal (D n)).K).card : ℕ) : ℝ)) ≤
          reciprocalActualC4GraphBudget (D n) κ color +
          (((D n).ground.card ^ 2 * C : ℕ) : ℝ) := by
    obtain ⟨color, hBound⟩ :=
      clear_used_parent_then_reciprocal_loss_le_c4_graph_budget_of_degree_caps
        (D n) Dcap Kstar (h_ground n) (h_facet n) (h_label n)
    refine ⟨color, ?_⟩
    have hCeq :
        Dcap * (D n).ground.card ^ 2 * κ ^ 2 +
          (D n).ground.card ^ 2 * Kstar ^ 2 * max Dcap 3 +
          (D n).ground.card ^ 2 * Dcap =
        (D n).ground.card ^ 2 * C := by
      dsimp [C, κ]
      ring
    simpa only [κ, ←hCeq] using hBound
  let color (n : ℕ) := Classical.choose (hExist n)
  have hPair (n : ℕ) :
      ∀ P ∈ (D n).ground.powersetCard 2,
        qPairDegree (reciprocalUsedParentLabelTriples (D n)) P ≤ κ :=
    reciprocal_used_parent_pair_degree_cap_of_label_fibers
      (D n) Kstar (h_label n)
  have hC4 :=
    reciprocal_actual_c4_graph_budget_ratio_tendsto_zero
      D κ color hPair
  have hInv : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹)
      Filter.atTop (nhds 0) :=
    tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  have hUpper : Filter.Tendsto
      (fun n : ℕ =>
        reciprocalActualC4GraphBudget (D n) κ (color n) /
          (n : ℝ) ^ 3 +
        (C : ℝ) * (n : ℝ)⁻¹)
      Filter.atTop (nhds 0) := by
    convert hC4.add (hInv.const_mul (C : ℝ)) using 1; ring_nf
  apply squeeze_zero'
    (Filter.Eventually.of_forall (fun n => by
      apply div_nonneg
      · positivity
      · positivity))
    ?_ hUpper
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hU : (D n).ground.card ≤ n := by
    calc
      _ ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  have hU2 : (D n).ground.card ^ 2 ≤ n ^ 2 :=
    Nat.pow_le_pow_left hU 2
  have hPoly : (D n).ground.card ^ 2 * C ≤ n ^ 2 * C :=
    Nat.mul_le_mul_right C hU2
  have hLoss := Classical.choose_spec (hExist n)
  change
      ((((D n).K \
        (clearUsedParentThenReciprocal (D n)).K).card : ℕ) : ℝ) ≤
        reciprocalActualC4GraphBudget (D n) κ (color n) +
          (((D n).ground.card ^ 2 * C : ℕ) : ℝ) at hLoss
  have hPolyR :
      (((D n).ground.card ^ 2 * C : ℕ) : ℝ) ≤
        ((n ^ 2 * C : ℕ) : ℝ) := by exact_mod_cast hPoly
  have hEq : (((n ^ 2 * C : ℕ) : ℝ) / (n : ℝ) ^ 3) =
      (C : ℝ) * (n : ℝ)⁻¹ := by
    push_cast
    field_simp [hn0]
  have hLoss' :
      ((((D n).K \
        (clearUsedParentThenReciprocal (D n)).K).card : ℕ) : ℝ) ≤
        reciprocalActualC4GraphBudget (D n) κ (color n) +
          ((n ^ 2 * C : ℕ) : ℝ) := by
    exact hLoss.trans (by
      simpa only [add_comm] using
        (add_le_add_left hPolyR
          (reciprocalActualC4GraphBudget (D n) κ (color n))))
  have hDiv :=
    div_le_div_of_nonneg_right hLoss'
      (by positivity : 0 ≤ (n : ℝ) ^ 3)
  rw [add_div, hEq] at hDiv
  exact hDiv

/-- The cubic denominator and the paper's binomial denominator differ
by an eventually bounded factor. -/
theorem cubic_le_twelve_choose_eventually :
    ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) ^ 3 ≤ 12 * (n.choose 3 : ℝ) := by
  have hVnonzero :
      ∀ᶠ n : ℕ in Filter.atTop,
        (n : ℝ) ^ 3 / ((3 : ℕ).factorial : ℝ) ≠ 0 := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hRatio : Filter.Tendsto
      (fun n : ℕ =>
        (n.choose 3 : ℝ) / ((n : ℝ) ^ 3 / 6))
      Filter.atTop (nhds 1) := by
    have hRaw :=
      (Asymptotics.isEquivalent_iff_tendsto_one hVnonzero).mp
        (isEquivalent_choose 3)
    change Filter.Tendsto
      (fun n : ℕ =>
        (n.choose 3 : ℝ) / ((n : ℝ) ^ 3 / 6))
      Filter.atTop (nhds 1) at hRaw
    exact hRaw
  have hNear : ∀ᶠ n : ℕ in Filter.atTop,
      (1 / 2 : ℝ) <
        (n.choose 3 : ℝ) / ((n : ℝ) ^ 3 / 6) :=
    (tendsto_order.1 hRatio).1 (1 / 2) (by norm_num)
  filter_upwards [hNear, Filter.eventually_ge_atTop (1 : ℕ)]
    with n hLower hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) ^ 3 / 6 := by positivity
  have hMul := (lt_div_iff₀ hden).mp hLower
  nlinarith

/-- The actual three-round cleanup is negligible in the exact
binomial normalization used by the rank-four extremal ratio. -/
theorem clear_used_parent_then_reciprocal_loss_choose_ratio_tendsto_zero
    (D : (n : ℕ) → FiniteCompletionCliqueData (Fin n))
    (Dcap Kstar : ℕ)
    (h_ground : ∀ n : ℕ, ∀ E ∈ (D n).K,
      E ⊆ (D n).ground)
    (h_facet : ∀ n : ℕ, ∀ T : Edge (Fin n), T.card = 3 →
      ((D n).K.filter fun E => T ⊆ E).card ≤ Dcap)
    (h_label : ∀ n : ℕ, ∀ a b : Fin n,
      (reciprocalUsedLabelFiber (D n) a b).card ≤ Kstar) :
    Filter.Tendsto
      (fun n : ℕ =>
        (((D n).K \ (clearUsedParentThenReciprocal (D n)).K).card : ℝ) /
          (n.choose 3 : ℝ))
      Filter.atTop (nhds 0) := by
  have hCubic :=
    clear_used_parent_then_reciprocal_loss_ratio_tendsto_zero
      D Dcap Kstar h_ground h_facet h_label
  have hUpper : Filter.Tendsto
      (fun n : ℕ =>
        12 * (((D n).K \
          (clearUsedParentThenReciprocal (D n)).K).card : ℝ) /
            (n : ℝ) ^ 3)
      Filter.atTop (nhds 0) := by
    simpa only [mul_div_assoc, mul_zero] using hCubic.const_mul 12
  apply squeeze_zero'
    (Filter.Eventually.of_forall (fun n => by
      apply div_nonneg <;> positivity))
    ?_ hUpper
  filter_upwards [cubic_le_twelve_choose_eventually,
      Filter.eventually_ge_atTop (3 : ℕ)] with n hBound hn
  have hChoose : (0 : ℝ) < n.choose 3 := by
    exact_mod_cast (Nat.choose_pos hn)
  have hCube : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  have hInv :
      1 / (n.choose 3 : ℝ) ≤ 12 / (n : ℝ) ^ 3 := by
    apply (div_le_div_iff₀ hChoose hCube).2
    nlinarith
  have hLossNonneg :
      (0 : ℝ) ≤
        (((D n).K \
          (clearUsedParentThenReciprocal (D n)).K).card : ℝ) := by
    positivity
  have hMul := mul_le_mul_of_nonneg_left hInv hLossNonneg
  calc
    _ =
        (((D n).K \
          (clearUsedParentThenReciprocal (D n)).K).card : ℝ) *
          (1 / (n.choose 3 : ℝ)) := by ring
    _ ≤
        (((D n).K \
          (clearUsedParentThenReciprocal (D n)).K).card : ℝ) *
          (12 / (n : ℝ) ^ 3) := hMul
    _ = _ := by ring

end JSP523.Rank4
