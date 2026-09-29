import JSP523.Rank4.GlobalActualNearExtremalLimit
import JSP523.Rank4.GlobalActualEndToEndSequence

namespace JSP523.Rank4

namespace ActualEndToEndData
variable {n level overlap outerLoss : ℕ} {H : Family (Fin (n + 1))}
  {U : Edge (Fin (n + 1))} {a : ℝ}

noncomputable def to_near_master_stability_data
    (A : ActualEndToEndData H U level a overlap outerLoss)
    (centers : Edge (Fin (n + 1))) (L : Fin (n + 1) → Family (Fin (n + 1)))
    (owner : Edge (Fin (n + 1)) → Fin (n + 1))
    (hOutside : ∀ c ∈ centers, c ∉ U)
    (hGround : ∀ c ∈ centers, ∀ T ∈ L c, T ∈ U.powersetCard 3)
    (hEdges : ∀ c ∈ centers, ∀ T ∈ L c, insert c T ∈ H)
    (hOriginal : H.card ≤ (centers.biUnion (pairOwnerCleanedLink L owner)).card +
      (fixedDecompositionCore H U).card + outerLoss)
    (missing : ℕ) (hLower : n.choose 3 ≤ H.card + missing) : ActualMasterStabilityData H where
  ground := U
  centers := centers
  links := L
  owner := owner
  regularized := A.regularized
  completion := A.completion
  normalization := U.card.choose 3
  masterError := A.masterError
  highError := n ^ 2 + missing
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

end ActualEndToEndData

theorem actual_selected_near_master_sequence_outside
    (H : (n : ℕ) → Family (Fin (n + 1))) (missing : ℕ → ℕ)
    (hAdm : ∀ n, Admissible (H n)) (hUniform : ∀ n, Uniform 4 (H n))
    (hLower : ∀ᶠ n in Filter.atTop, n.choose 3 ≤ (H n).card + missing n)
    (hMissing : Filter.Tendsto (fun n => (missing n : ℝ) / (n : ℝ) ^ 3) Filter.atTop (nhds 0))
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
  classical
  let q := fun n => initialOuterRegularizationScale (n + 1)
  have hScale : ∀ᶠ n in Filter.atTop, q n ^ 11 ≤ n + 1 :=
    hInitial.mono (fun _ h => h.scale_range)
  apply actual_near_master_stability_outside_ratio_tendsto_zero H q missing hAdm hUniform hLower hMissing hScale
  intro ν hν
  obtain ⟨r, hr, hData⟩ := hErrors ν hν
  have hInv : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  let rem := fun n => r n + 10 * (n : ℝ)⁻¹ + 10 * ((missing n : ℝ) / (n : ℝ) ^ 3)
  have hRem : Filter.Tendsto rem Filter.atTop (nhds 0) := by
    simpa only [rem, mul_zero, add_zero] using (hr.add (hInv.const_mul 10)).add (hMissing.const_mul 10)
  refine ⟨rem, rem, hRem, hRem, ?_⟩
  filter_upwards [hInitial, hLower, hData, Filter.eventually_ge_atTop (1 : ℕ)]
    with n hI hLower hData hn
  obtain ⟨level, a, A, hError⟩ := hData
  let U : Edge (Fin (n + 1)) := Finset.univ \ (Z n ∪ X n)
  let L := fun c => rankFourStarLink (H n) U c
  have hOutside : ∀ c ∈ Z n, c ∉ U := by
    intro c hc hu
    exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_union_left _ hc)
  have hGround : ∀ c ∈ Z n, ∀ T ∈ L c, T ∈ U.powersetCard 3 := by
    intro c _ T hT
    exact (Finset.mem_filter.mp hT).1
  have hEdges : ∀ c ∈ Z n, ∀ T ∈ L c, insert c T ∈ H n := by
    intro c _ T hT
    exact (Finset.mem_filter.mp hT).2
  let d := A.to_near_master_stability_data (Z n) L (owner n) hOutside hGround hEdges hI.original_mass (missing n) hLower
  have hErrorFinal : ((d.masterError + 10 * d.highError : ℕ) : ℝ) / (n : ℝ) ^ 3 ≤ ν + rem n := by
    change ((A.masterError + 10 * (n ^ 2 + missing n) : ℕ) : ℝ) / (n : ℝ) ^ 3 ≤ _
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hIdentity : ((A.masterError + 10 * (n ^ 2 + missing n) : ℕ) : ℝ) / (n : ℝ) ^ 3 =
        (A.masterError : ℝ) / (n : ℝ) ^ 3 + 10 * (n : ℝ)⁻¹ +
          10 * ((missing n : ℝ) / (n : ℝ) ^ 3) := by
      push_cast
      field_simp
      ring
    rw [hIdentity]
    dsimp only [rem]
    linarith
  refine ⟨d, ⟨hI.vertex_cap, hI.pair_cap, hI.facet_cap⟩, hErrorFinal, ?_⟩
  have hCleanup : d.cleanup_loss + d.outerLoss ≤ d.masterError + 10 * d.highError := by
    have h := A.parent_cleanup_and_outer_le_master_error
    have hExact := d.cleanup_loss_eq_parent_sdiff
    change d.cleanup_loss =
      (fixedDecompositionCore (H n) U \ (clearUsedParentThenReciprocal A.completion).K).card at hExact
    change d.cleanup_loss + outerLoss n ≤ A.masterError + 10 * (n ^ 2 + missing n)
    dsimp only [U] at hExact
    omega
  apply le_trans ?_ hErrorFinal
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast hCleanup

/-- The full near-extremal stability assertion of §III.B.5, allowing any
vanishing cubic deficit below the complete star. -/
theorem rank_four_actual_near_extremal_outside_tendsto_zero
    (H : (n : ℕ) → Family (Fin (n + 1))) (missing : ℕ → ℕ)
    (hAdm : ∀ n, Admissible (H n)) (hUniform : ∀ n, Uniform 4 (H n))
    (hLower : ∀ᶠ n in Filter.atTop, n.choose 3 ≤ (H n).card + missing n)
    (hMissing : Filter.Tendsto (fun n => (missing n : ℝ) / (n : ℝ) ^ 3) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => ((outsideEdges (H n) (Finset.univ.erase (actualGlobalMainCenter (H n)))).card : ℝ) /
        (n : ℝ) ^ 3) Filter.atTop (nhds 0) := by
  obtain ⟨Z, X, owner, loss, overlap, hInitial, hErrors⟩ :=
    exists_actual_master_sequence H (Filter.Eventually.of_forall hAdm) (Filter.Eventually.of_forall hUniform)
  exact actual_selected_near_master_sequence_outside H missing hAdm hUniform hLower hMissing
    Z X owner loss overlap hInitial hErrors

end JSP523.Rank4
