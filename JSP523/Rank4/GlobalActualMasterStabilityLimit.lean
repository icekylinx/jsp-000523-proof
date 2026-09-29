import JSP523.Rank4.GlobalActualMasterStabilityFinite

/-! # Actual-master stability in the order τ, then M, then ν -/
namespace JSP523.Rank4

/-- Ordinary initial caps on the original induced parent, before either
the main cleanup or the auxiliary degree-tail cleanup. -/
def actual_master_stability_initial_caps {n : ℕ} {H : Family (Fin (n + 1))}
    (d : ActualMasterStabilityData H) (q : ℕ) : Prop :=
  (∀ v, (d.parent.filter fun E => v ∈ E).card ≤ q ^ 8 * (n + 1) ^ 2) ∧
  (∀ P : Edge (Fin (n + 1)), P.card = 2 → rankFourPairDegree d.parent P ≤ q ^ 8 * (n + 1)) ∧
  (∀ T : Edge (Fin (n + 1)), T.card = 3 →
    (facetCompletions d.parent Finset.univ T).card ≤ q ^ 8)

/-- Actual finite masters with arbitrarily small main-cleanup errors
force one original-parent center to contain all but `o(n³)` edges.

For a requested accuracy, τ is fixed first, then its actual degree-tail
threshold M, then ν. All cleaned objects remain inside the existential
actual data. Neither a small-parent nor a center-stability input occurs.
-/
theorem actual_master_stability_outside_ratio_tendsto_zero
    (H : (n : ℕ) → Family (Fin (n + 1))) (q : ℕ → ℕ)
    (hAdm : ∀ n, Admissible (H n)) (hUniform : ∀ n, Uniform 4 (H n))
    (hLower : ∀ᶠ n in Filter.atTop, n.choose 3 ≤ (H n).card)
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
  let remainder := fun n => 3 * (M : ℝ) * rMaster n + 3 * rCleanup n + 20 * (n : ℝ)⁻¹
  have hRemainder : Filter.Tendsto remainder Filter.atTop (nhds 0) := by
    simpa [remainder] using
      ((hrMaster.const_mul (3 * (M : ℝ))).add (hrCleanup.const_mul 3)).add (hInv.const_mul 20)
  refine ⟨remainder, hRemainder, ?_⟩
  filter_upwards [hData, hScale, hLower, Filter.eventually_ge_atTop (2 : ℕ)]
    with n hData hScale hLower hn
  obtain ⟨d, hInitial, hError, hCleanup⟩ := hData
  rcases hInitial with ⟨hVertex, hPair, hFacet⟩
  have hFinite := actual_master_stability_with_chosen_tail (H n) d (q n) τ hτ hn hScale
    (hAdm n) (hUniform n) hLower hVertex hPair hFacet
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
        (n : ℝ) ^ 3 + 20 * (n : ℝ) ^ 2 := by
    nlinarith only [hFinite, hMasterScale, hCleanupScale, hTailScale, hSquare]
  apply (div_le_iff₀ hCubePos).2
  have hId : (ε + remainder n) * (n : ℝ) ^ 3 =
      (ε + 3 * (M : ℝ) * rMaster n + 3 * rCleanup n) * (n : ℝ) ^ 3 + 20 * (n : ℝ) ^ 2 := by
    dsimp [remainder]
    field_simp
    ring
  rw [hId]
  have hCoeffScale := mul_le_mul_of_nonneg_right hCoeff hCubePos.le
  nlinarith only [hAll, hCoeffScale]

/-- The actual master sequence therefore reaches the explicit local
near-star theorem, including its linear outside-family conclusion. -/
theorem actual_master_stability_eventual_exact_bound
    (H : (n : ℕ) → Family (Fin (n + 1))) (q : ℕ → ℕ)
    (hAdm : ∀ n, Admissible (H n)) (hUniform : ∀ n, Uniform 4 (H n))
    (hLower : ∀ᶠ n in Filter.atTop, n.choose 3 ≤ (H n).card)
    (hScale : ∀ᶠ n in Filter.atTop, q n ^ 11 ≤ n + 1)
    (hMasters : ∀ ν : ℝ, 0 < ν →
      ∃ rMaster rCleanup : ℕ → ℝ,
        Filter.Tendsto rMaster Filter.atTop (nhds 0) ∧
        Filter.Tendsto rCleanup Filter.atTop (nhds 0) ∧
        ∀ᶠ n in Filter.atTop, ∃ d : ActualMasterStabilityData (H n),
          actual_master_stability_initial_caps d (q n) ∧
          ((d.masterError + 10 * d.highError : ℕ) : ℝ) / (n : ℝ) ^ 3 ≤ ν + rMaster n ∧
          ((d.cleanup_loss + d.outerLoss : ℕ) : ℝ) / (n : ℝ) ^ 3 ≤ ν + rCleanup n) :
    ∀ᶠ n in Filter.atTop,
      (H n).card ≤ n.choose 3 + n / 4 ∧
      LinearFamily (outsideEdges (H n) (Finset.univ.erase (actualGlobalMainCenter (H n)))) ∧
      4 * (outsideEdges (H n) (Finset.univ.erase (actualGlobalMainCenter (H n)))).card ≤
        (missingStarTriples (H n) (Finset.univ.erase (actualGlobalMainCenter (H n)))
          (actualGlobalMainCenter (H n))).card + n :=
  rank_four_eventual_exact_bound_of_outside_stability H (fun n => actualGlobalMainCenter (H n))
    hAdm hUniform hLower
    (actual_master_stability_outside_ratio_tendsto_zero H q hAdm hUniform hLower hScale hMasters)

end JSP523.Rank4
