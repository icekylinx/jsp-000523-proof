import JSP523.Rank4.GlobalActualMasterStabilityFinite

/-! # Actual master stability with a vanishing deficit below the star -/
namespace JSP523.Rank4

/-- The actual original star allocation also permits a deficit in the
star lower bound; empty center sets require no separate hypothesis. -/
theorem actual_global_center_near_master_decomposition
    {n : ℕ} (H : Family (Fin (n + 1))) (d : ActualMasterStabilityData H)
    (missing : ℕ) (hn : 2 ≤ n) (hLower : n.choose 3 ≤ H.card + missing) :
    (outsideEdges H (Finset.univ.erase (actualGlobalMainCenter H))).card ≤
      2 * missing + 3 * d.parent.card + 3 * d.outerLoss + 5 * (n + 1) ^ 2 := by
  classical
  have hUnion := Finset.card_biUnion_le (s := d.centers) (t := pairOwnerCleanedLink d.links d.owner)
  have hMass : H.card ≤ (∑ c ∈ d.centers, (pairOwnerCleanedLink d.links d.owner c).card) +
      (d.parent.card + d.outerLoss) := by
    have h := d.original_mass
    change H.card ≤ _ + d.parent.card + d.outerLoss at h
    omega
  by_cases hCenters : d.centers.Nonempty
  · obtain ⟨c, _, hBound⟩ := actual_original_single_center_of_near_star_lower H d.ground d.centers
      d.links d.owner missing (d.parent.card + d.outerLoss) hn hCenters
      d.centers_outside d.links_ground d.links_edges hLower hMass
    have h := (actual_global_main_center_outside_le H c).trans hBound
    simpa only [Nat.mul_add, Nat.add_assoc] using h
  · have hEmpty := Finset.not_nonempty_iff_eq_empty.mp hCenters
    have hSmall : H.card ≤ d.parent.card + d.outerLoss := by
      simpa only [hEmpty, Finset.sum_empty, zero_add] using hMass
    have hSub : (outsideEdges H (Finset.univ.erase (actualGlobalMainCenter H))).card ≤ H.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    omega

/-- The independent degree-tail cleanup stays in the original parent. -/
theorem actual_near_master_stability_with_chosen_tail
    {n : ℕ} (H : Family (Fin (n + 1))) (d : ActualMasterStabilityData H)
    (q missing : ℕ) (τ : ℝ) (hτ : 0 < τ)
    (hn : 2 ≤ n) (hScale : q ^ 11 ≤ n + 1)
    (hAdm : Admissible H) (hUniform : Uniform 4 H) (hLower : n.choose 3 ≤ H.card + missing)
    (hInitial : actual_master_stability_initial_caps d q) :
    ((outsideEdges H (Finset.univ.erase (actualGlobalMainCenter H))).card : ℝ) ≤
      3 * (actualDegreeTailThreshold τ : ℝ) * (d.masterError + 10 * (d.highError : ℝ)) +
      3 * τ * ((n : ℝ) + 1) ^ 3 + 3 * (d.cleanup_loss : ℝ) +
      3 * (d.outerLoss : ℝ) + 5 * ((n : ℝ) + 1) ^ 2 + 2 * missing := by
  classical
  have hBH : d.parent ⊆ H := Finset.filter_subset _ _
  obtain ⟨hM, B₁, hB₁, hTail, hCap⟩ := exists_actual_degree_tail_cleanup d.parent q τ hτ hScale
    (admissible_mono hBH hAdm) (fun _ hE => hUniform (hBH hE)) hInitial.1 hInitial.2.1 hInitial.2.2
  have hCapGround : ∀ T ∈ d.ground.powersetCard 3,
      2 * (facetCompletions B₁ d.ground T).card ≤ actualDegreeTailThreshold τ := by
    intro T hT
    have hSub : facetCompletions B₁ d.ground T ⊆ facetCompletions B₁ Finset.univ T := by
      intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, (Finset.mem_filter.mp hv).2⟩
    exact (Nat.mul_le_mul_left 2 (Finset.card_le_card hSub)).trans
      (hCap T (Finset.mem_powersetCard.mp hT).2)
  have hParent := actual_parent_stability_of_master d.parent d.final_core B₁ d.ground
    (actualDegreeTailThreshold τ) H.card d.normalization d.masterError d.highError
    d.final_core_sub_parent hB₁ (fun E hE => hUniform (hBH hE))
    (fun _ hE => (Finset.mem_filter.mp hE).2) hM hCapGround d.master d.near_master
  have hCenter := actual_global_center_near_master_decomposition H d missing hn hLower
  have hLossEq := d.cleanup_loss_eq_parent_sdiff
  have hFinite : (outsideEdges H (Finset.univ.erase (actualGlobalMainCenter H))).card ≤
      3 * (actualDegreeTailThreshold τ) * (d.masterError + 10 * d.highError) +
      24 * (d.parent \ B₁).card + 3 * d.cleanup_loss + 3 * d.outerLoss +
      5 * (n + 1) ^ 2 + 2 * missing := by nlinarith only [hParent, hCenter, hLossEq]
  have hReal : ((outsideEdges H (Finset.univ.erase (actualGlobalMainCenter H))).card : ℝ) ≤
      3 * (actualDegreeTailThreshold τ : ℝ) * (d.masterError + 10 * (d.highError : ℝ)) +
      24 * ((d.parent \ B₁).card : ℝ) + 3 * (d.cleanup_loss : ℝ) +
      3 * (d.outerLoss : ℝ) + 5 * ((n : ℝ) + 1) ^ 2 + 2 * missing := by exact_mod_cast hFinite
  push_cast at hTail
  nlinarith only [hReal, hTail]

end JSP523.Rank4
