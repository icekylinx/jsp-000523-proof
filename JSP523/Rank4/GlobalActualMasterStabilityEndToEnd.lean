import JSP523.Rank4.GlobalActualMasterStabilityLimit
import JSP523.Rank4.GlobalActualEndToEndParameters

/-! # Actual end-to-end data as master stability data -/

namespace JSP523.Rank4

namespace ActualEndToEndData

variable {n level overlap outerLoss : ℕ} {H : Family (Fin (n + 1))}
  {U : Edge (Fin (n + 1))} {a : ℝ}

/-- Keep the actual completion and all original star layers when passing
to the stability interface. -/
noncomputable def to_master_stability_data
    (A : ActualEndToEndData H U level a overlap outerLoss)
    (centers : Edge (Fin (n + 1))) (L : Fin (n + 1) → Family (Fin (n + 1)))
    (owner : Edge (Fin (n + 1)) → Fin (n + 1))
    (hOutside : ∀ c ∈ centers, c ∉ U)
    (hGround : ∀ c ∈ centers, ∀ T ∈ L c, T ∈ U.powersetCard 3)
    (hEdges : ∀ c ∈ centers, ∀ T ∈ L c, insert c T ∈ H)
    (hOriginal : H.card ≤ (centers.biUnion (pairOwnerCleanedLink L owner)).card +
      (fixedDecompositionCore H U).card + outerLoss)
    (hLower : n.choose 3 ≤ H.card) : ActualMasterStabilityData H where
  ground := U
  centers := centers
  links := L
  owner := owner
  regularized := A.regularized
  completion := A.completion
  normalization := U.card.choose 3
  masterError := A.masterError
  highError := n ^ 2
  outerLoss := outerLoss
  completion_ground := A.ground_eq
  regularized_sub := A.regularized_sub
  completion_sub := A.completion_sub
  centers_outside := hOutside
  links_ground := hGround
  links_edges := hEdges
  original_mass := hOriginal
  master := A.master_with_error
  near_master := by
    have hU : U.card ≤ n + 1 := by
      simpa using Finset.card_le_card (Finset.subset_univ U)
    have hChoose := Nat.choose_le_choose 3 hU
    have hSucc := Nat.choose_succ_succ n 2
    norm_num only [Nat.succ_eq_add_one] at hSucc
    have hQuadratic := Nat.choose_le_pow n 2
    omega

/-- The three losses in the stability record are bounded by the very
same budget which was charged in the end-to-end master. -/
theorem to_master_stability_data_cleanup_le
    (A : ActualEndToEndData H U level a overlap outerLoss)
    (centers : Edge (Fin (n + 1))) (L : Fin (n + 1) → Family (Fin (n + 1)))
    (owner : Edge (Fin (n + 1)) → Fin (n + 1))
    (hOutside : ∀ c ∈ centers, c ∉ U)
    (hGround : ∀ c ∈ centers, ∀ T ∈ L c, T ∈ U.powersetCard 3)
    (hEdges : ∀ c ∈ centers, ∀ T ∈ L c, insert c T ∈ H)
    (hOriginal : H.card ≤ (centers.biUnion (pairOwnerCleanedLink L owner)).card +
      (fixedDecompositionCore H U).card + outerLoss)
    (hLower : n.choose 3 ≤ H.card) :
    (A.to_master_stability_data centers L owner hOutside hGround hEdges hOriginal hLower).cleanup_loss ≤
      A.cleanupBudget := by
  rw [ActualMasterStabilityData.cleanup_loss_eq_parent_sdiff]
  exact A.parent_cleanup_le_budget

end ActualEndToEndData

/-- A single actual master-error ledger suffices for the two errors in
the stability limit. The main cleanup parameters may depend on ν. -/
theorem actual_master_stability_outside_ratio_of_single_error
    (H : (n : ℕ) → Family (Fin (n + 1))) (q : ℕ → ℕ)
    (hAdm : ∀ n, Admissible (H n)) (hUniform : ∀ n, Uniform 4 (H n))
    (hLower : ∀ᶠ n in Filter.atTop, n.choose 3 ≤ (H n).card)
    (hScale : ∀ᶠ n in Filter.atTop, q n ^ 11 ≤ n + 1)
    (hMasters : ∀ ν : ℝ, 0 < ν → ∃ remainder : ℕ → ℝ,
      Filter.Tendsto remainder Filter.atTop (nhds 0) ∧
      ∀ᶠ n in Filter.atTop, ∃ d : ActualMasterStabilityData (H n),
        actual_master_stability_initial_caps d (q n) ∧
        d.cleanup_loss + d.outerLoss ≤ d.masterError ∧
        ((d.masterError + 10 * d.highError : ℕ) : ℝ) / (n : ℝ) ^ 3 ≤ ν + remainder n) :
    Filter.Tendsto
      (fun n => ((outsideEdges (H n) (Finset.univ.erase (actualGlobalMainCenter (H n)))).card : ℝ) /
        (n : ℝ) ^ 3) Filter.atTop (nhds 0) := by
  apply actual_master_stability_outside_ratio_tendsto_zero H q hAdm hUniform hLower hScale
  intro ν hν
  obtain ⟨remainder, hLimit, hData⟩ := hMasters ν hν
  refine ⟨remainder, remainder, hLimit, hLimit, ?_⟩
  filter_upwards [hData] with n hn
  obtain ⟨d, hCaps, hCleanup, hError⟩ := hn
  refine ⟨d, hCaps, hError, le_trans ?_ hError⟩
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast (show d.cleanup_loss + d.outerLoss ≤ d.masterError + 10 * d.highError by omega)

end JSP523.Rank4
