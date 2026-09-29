import JSP523.Rank4.GlobalActualNearExtremalMaster

namespace JSP523.Rank4

theorem actual_near_master_stability_outside_ratio_tendsto_zero
    (H : (n : ℕ) → Family (Fin (n + 1))) (q missing : ℕ → ℕ)
    (hAdm : ∀ n, Admissible (H n)) (hUniform : ∀ n, Uniform 4 (H n))
    (hLower : ∀ᶠ n in Filter.atTop, n.choose 3 ≤ (H n).card + missing n)
    (hMissing : Filter.Tendsto (fun n => (missing n : ℝ) / (n : ℝ) ^ 3) Filter.atTop (nhds 0))
    (hScale : ∀ᶠ n in Filter.atTop, q n ^ 11 ≤ n + 1)
    (hMasters : ∀ ν : ℝ, 0 < ν →
      ∃ rMaster rCleanup : ℕ → ℝ,
        Filter.Tendsto rMaster Filter.atTop (nhds 0) ∧
        Filter.Tendsto rCleanup Filter.atTop (nhds 0) ∧
        ∀ᶠ n in Filter.atTop, ∃ d : ActualMasterStabilityData (H n),
          actual_master_stability_initial_caps d (q n) ∧
          ((d.masterError + 10 * d.highError : ℕ) : ℝ) / (n : ℝ) ^ 3 ≤ ν + rMaster n ∧
          ((d.cleanup_loss + d.outerLoss : ℕ) : ℝ) / (n : ℝ) ^ 3 ≤ ν + rCleanup n) :
    Filter.Tendsto
      (fun n => ((outsideEdges (H n) (Finset.univ.erase (actualGlobalMainCenter (H n)))).card : ℝ) /
        (n : ℝ) ^ 3) Filter.atTop (nhds 0) := by
  apply tendsto_zero_of_small_error_coefficients _
    (Filter.Eventually.of_forall (fun _ => by positivity))
  intro ε hε
  let τ := ε / 96
  have hτ : 0 < τ := by dsimp [τ]; positivity
  let M := actualDegreeTailThreshold τ
  let ν := ε / (4 * (3 * (M : ℝ) + 3))
  have hDen : 0 < 3 * (M : ℝ) + 3 := by positivity
  have hν : 0 < ν := by dsimp [ν]; positivity
  have hCancel : (3 * (M : ℝ) + 3) * ν = ε / 4 := by
    dsimp [ν]
    field_simp
  have hCoeff : (3 * (M : ℝ) + 3) * ν + 24 * τ ≤ ε := by
    rw [hCancel]
    dsimp [τ]
    linarith
  obtain ⟨rMaster, rCleanup, hrMaster, hrCleanup, hData⟩ := hMasters ν hν
  have hInv : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  let remainder := fun n => 3 * (M : ℝ) * rMaster n + 3 * rCleanup n + 20 * (n : ℝ)⁻¹ + 2 * ((missing n : ℝ) / (n : ℝ) ^ 3)
  have hRemainder : Filter.Tendsto remainder Filter.atTop (nhds 0) := by
    simpa [remainder] using
      (((hrMaster.const_mul (3 * (M : ℝ))).add (hrCleanup.const_mul 3)).add (hInv.const_mul 20)).add (hMissing.const_mul 2)
  refine ⟨remainder, hRemainder, ?_⟩
  filter_upwards [hData, hScale, hLower, Filter.eventually_ge_atTop (2 : ℕ)]
    with n hData hScale hLower hn
  obtain ⟨d, hInitial, hError, hCleanup⟩ := hData
  have hFinite := actual_near_master_stability_with_chosen_tail (H n) d (q n) (missing n) τ hτ hn hScale
    (hAdm n) (hUniform n) hLower hInitial
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hCubePos : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  have hErrorMul := (div_le_iff₀ hCubePos).1 hError
  have hCleanupMul := (div_le_iff₀ hCubePos).1 hCleanup
  push_cast at hErrorMul hCleanupMul
  have hMasterScale := mul_le_mul_of_nonneg_left hErrorMul
    (by positivity : 0 ≤ 3 * (M : ℝ))
  have hCleanupScale := mul_le_mul_of_nonneg_left hCleanupMul (by norm_num : (0 : ℝ) ≤ 3)
  have hDouble : (n : ℝ) + 1 ≤ 2 * n := by exact_mod_cast (by omega : n + 1 ≤ 2 * n)
  have hCube : ((n : ℝ) + 1) ^ 3 ≤ 8 * (n : ℝ) ^ 3 := by
    calc
      _ ≤ (2 * (n : ℝ)) ^ 3 := by gcongr
      _ = _ := by ring
  have hTailScale := mul_le_mul_of_nonneg_left hCube (by positivity : 0 ≤ 3 * τ)
  have hSquare : 5 * ((n : ℝ) + 1) ^ 2 ≤ 20 * (n : ℝ) ^ 2 := by
    calc
      _ ≤ 5 * (2 * (n : ℝ)) ^ 2 := by gcongr
      _ = _ := by ring
  have hAll : ((outsideEdges (H n) (Finset.univ.erase (actualGlobalMainCenter (H n)))).card : ℝ) ≤
      ((3 * (M : ℝ) + 3) * ν + 24 * τ + 3 * (M : ℝ) * rMaster n + 3 * rCleanup n) *
        (n : ℝ) ^ 3 + 20 * (n : ℝ) ^ 2 + 2 * missing n := by
    nlinarith only [hFinite, hMasterScale, hCleanupScale, hTailScale, hSquare]
  apply (div_le_iff₀ hCubePos).2
  have hId : (ε + remainder n) * (n : ℝ) ^ 3 =
      (ε + 3 * (M : ℝ) * rMaster n + 3 * rCleanup n) * (n : ℝ) ^ 3 + 20 * (n : ℝ) ^ 2 + 2 * missing n := by
    dsimp [remainder]
    field_simp
    ring
  rw [hId]
  have hCoeffScale := mul_le_mul_of_nonneg_right hCoeff hCubePos.le
  nlinarith only [hAll, hCoeffScale]


end JSP523.Rank4
