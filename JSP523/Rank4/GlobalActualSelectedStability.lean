import JSP523.Rank4.GlobalActualMasterStabilityEndToEnd
import JSP523.Rank4.GlobalActualNearExtremal

namespace JSP523.Rank4

/-- Consume selected actual master data, retaining the original initial
parent for the independently chosen degree tail. -/
theorem actual_selected_master_sequence_outside
    (H : (n : ℕ) → Family (Fin (n + 1)))
    (hAdm : ∀ n, Admissible (H n)) (hUniform : ∀ n, Uniform 4 (H n))
    (hLower : ∀ᶠ n in Filter.atTop, n.choose 3 ≤ (H n).card)
    (Z X : (n : ℕ) → Edge (Fin (n + 1)))
    (owner : (n : ℕ) → Edge (Fin (n + 1)) → Fin (n + 1))
    (outerLoss overlap : ℕ → ℕ)
    (hInitial : ∀ᶠ n in Filter.atTop,
      ActualInitialOuterData (H n) (Z n) (X n) (owner n) (outerLoss n))
    (hErrors : ∀ ε : ℝ, 0 < ε → ∃ remainder : ℕ → ℝ,
      Filter.Tendsto remainder Filter.atTop (nhds 0) ∧
      ∀ᶠ n in Filter.atTop, ∃ level : ℕ, ∃ a : ℝ,
        ∃ A : ActualEndToEndData (H n) (Finset.univ \ (Z n ∪ X n)) level a (overlap n) (outerLoss n),
          (A.masterError : ℝ) / (n : ℝ) ^ 3 ≤ ε / 2 + remainder n) :
    Filter.Tendsto
      (fun n => ((outsideEdges (H n) (Finset.univ.erase (actualGlobalMainCenter (H n)))).card : ℝ) /
        (n : ℝ) ^ 3) Filter.atTop (nhds 0) := by
  exact actual_selected_near_master_sequence_outside H (fun _ => 0) hAdm hUniform
    (by simpa only [Nat.add_zero] using hLower)
    (by simpa only [Nat.cast_zero, zero_div] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0)))
    Z X owner outerLoss overlap hInitial hErrors

end JSP523.Rank4
