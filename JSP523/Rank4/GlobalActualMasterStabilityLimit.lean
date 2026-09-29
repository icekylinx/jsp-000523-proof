import JSP523.Rank4.GlobalActualNearExtremalLimit

/-! # Actual-master stability in the order τ, then M, then ν -/
namespace JSP523.Rank4

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
  exact actual_near_master_stability_outside_ratio_tendsto_zero H q (fun _ => 0)
    hAdm hUniform (by simpa only [Nat.add_zero] using hLower)
    (by simpa only [Nat.cast_zero, zero_div] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0)))
    hScale hMasters

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
