import JSP523.Rank4.GlobalActualSingleCenterLimit

/-! # Parameter-independent actual centers and the near-star endpoint -/
namespace JSP523.Rank4

noncomputable def actualGlobalMainCenter {n : ℕ}
    (H : Family (Fin (n + 1))) : Fin (n + 1) :=
  actualOriginalMainCenter H Finset.univ

theorem actual_global_main_center_outside_le {n : ℕ}
    (H : Family (Fin (n + 1))) (c : Fin (n + 1)) :
    (outsideEdges H (Finset.univ.erase (actualGlobalMainCenter H))).card ≤
      (outsideEdges H (Finset.univ.erase c)).card :=
  (actual_original_main_center_spec H Finset.univ Finset.univ_nonempty).2 c (Finset.mem_univ c)

/-- This center was chosen from the original parent before any of the
parameter-dependent layer cleanups. Empty layer systems are included. -/
theorem actual_global_center_of_actual_layer_mass
    {n : ℕ} (H : Family (Fin (n + 1))) (V centers : Edge (Fin (n + 1)))
    (L : Fin (n + 1) → Family (Fin (n + 1))) (owner : Edge (Fin (n + 1)) → Fin (n + 1))
    (loss : ℕ) (hn : 2 ≤ n)
    (hOutside : ∀ c ∈ centers, c ∉ V)
    (hGround : ∀ c ∈ centers, ∀ T ∈ L c, T ∈ V.powersetCard 3)
    (hEdges : ∀ c ∈ centers, ∀ T ∈ L c, insert c T ∈ H)
    (hLower : n.choose 3 ≤ H.card)
    (hMass : H.card ≤ (∑ c ∈ centers, (pairOwnerCleanedLink L owner c).card) + loss) :
    (outsideEdges H (Finset.univ.erase (actualGlobalMainCenter H))).card ≤
      3 * loss + 5 * (n + 1) ^ 2 := by
  classical
  by_cases hCenters : centers.Nonempty
  · obtain ⟨c, _, hBound⟩ := actual_original_single_center_of_star_lower H V centers L owner
      loss hn hCenters hOutside hGround hEdges hLower hMass
    exact (actual_global_main_center_outside_le H c).trans hBound
  · have hEmpty : centers = ∅ := Finset.not_nonempty_iff_eq_empty.mp hCenters
    have hSmall : H.card ≤ loss := by simpa only [hEmpty, Finset.sum_empty, zero_add] using hMass
    have hSub : (outsideEdges H (Finset.univ.erase (actualGlobalMainCenter H))).card ≤ H.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    omega

/-- Directly consume the original-family mass premise used by the actual
master normalization. The parent core and outer deletion are the only losses. -/
theorem actual_global_center_of_master_decomposition
    {n : ℕ} (H : Family (Fin (n + 1))) (V centers : Edge (Fin (n + 1)))
    (L : Fin (n + 1) → Family (Fin (n + 1))) (owner : Edge (Fin (n + 1)) → Fin (n + 1))
    (outerLoss : ℕ) (hn : 2 ≤ n)
    (hOutside : ∀ c ∈ centers, c ∉ V)
    (hGround : ∀ c ∈ centers, ∀ T ∈ L c, T ∈ V.powersetCard 3)
    (hEdges : ∀ c ∈ centers, ∀ T ∈ L c, insert c T ∈ H)
    (hLower : n.choose 3 ≤ H.card)
    (hOriginal : H.card ≤ (centers.biUnion (pairOwnerCleanedLink L owner)).card +
      (fixedDecompositionCore H V).card + outerLoss) :
    (outsideEdges H (Finset.univ.erase (actualGlobalMainCenter H))).card ≤
      3 * (fixedDecompositionCore H V).card + 3 * outerLoss + 5 * (n + 1) ^ 2 := by
  classical
  have hUnion := Finset.card_biUnion_le (s := centers) (t := pairOwnerCleanedLink L owner)
  have hMass : H.card ≤ (∑ c ∈ centers, (pairOwnerCleanedLink L owner c).card) +
      ((fixedDecompositionCore H V).card + outerLoss) := by omega
  have h := actual_global_center_of_actual_layer_mass H V centers L owner
    ((fixedDecompositionCore H V).card + outerLoss) hn hOutside hGround hEdges hLower hMass
  simpa only [Nat.mul_add, Nat.add_assoc] using h

/-- The only input to this limit step is actual star-layer mass with
arbitrarily small loss. All choices of cleanup parameters share one
original-parent center. -/
theorem actual_global_center_stability_of_parameter_layers
    (H : (n : ℕ) → Family (Fin (n + 1)))
    (hLower : ∀ᶠ n in Filter.atTop, n.choose 3 ≤ (H n).card)
    (hLayers : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop,
      ∃ V centers : Edge (Fin (n + 1)),
      ∃ L : Fin (n + 1) → Family (Fin (n + 1)),
      ∃ owner : Edge (Fin (n + 1)) → Fin (n + 1), ∃ loss : ℕ,
        (∀ c ∈ centers, c ∉ V) ∧
        (∀ c ∈ centers, ∀ T ∈ L c, T ∈ V.powersetCard 3) ∧
        (∀ c ∈ centers, ∀ T ∈ L c, insert c T ∈ H n) ∧
        (H n).card ≤ (∑ c ∈ centers, (pairOwnerCleanedLink L owner c).card) + loss ∧
        (loss : ℝ) / (n : ℝ) ^ 3 ≤ ε) :
    Filter.Tendsto
      (fun n => ((outsideEdges (H n) (Finset.univ.erase (actualGlobalMainCenter (H n)))).card : ℝ) /
        (n : ℝ) ^ 3) Filter.atTop (nhds 0) := by
  apply tendsto_zero_of_small_error_coefficients _
    (Filter.Eventually.of_forall (fun _ => by positivity))
  intro ε hε
  have hInv : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  refine ⟨fun n => 20 * (n : ℝ)⁻¹, by simpa using hInv.const_mul 20, ?_⟩
  filter_upwards [hLayers (ε / 3) (by positivity), hLower,
    Filter.eventually_ge_atTop (2 : ℕ)] with n hData hLow hn
  obtain ⟨V, centers, L, owner, loss, hOutside, hGround, hEdges, hMass, hLoss⟩ := hData
  have hBound := actual_global_center_of_actual_layer_mass (H n) V centers L owner loss hn
    hOutside hGround hEdges hLow hMass
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hSquare : 5 * (n + 1) ^ 2 ≤ 20 * n ^ 2 := by nlinarith
  have hReal : ((outsideEdges (H n) (Finset.univ.erase (actualGlobalMainCenter (H n)))).card : ℝ) ≤
      3 * (loss : ℝ) + 20 * (n : ℝ) ^ 2 := by
    exact_mod_cast hBound.trans (Nat.add_le_add_left hSquare (3 * loss))
  have hDiv := div_le_div_of_nonneg_right hReal (by positivity : 0 ≤ (n : ℝ) ^ 3)
  have hEq : (3 * (loss : ℝ) + 20 * (n : ℝ) ^ 2) / (n : ℝ) ^ 3 =
      3 * ((loss : ℝ) / (n : ℝ) ^ 3) + 20 * (n : ℝ)⁻¹ := by field_simp
  rw [hEq] at hDiv
  linarith

/-- Actual layer stability now feeds exactly the finite near-star theorem. -/
theorem actual_global_eventual_exact_bound_of_parameter_layers
    (H : (n : ℕ) → Family (Fin (n + 1)))
    (hAdm : ∀ n, Admissible (H n)) (hUniform : ∀ n, Uniform 4 (H n))
    (hLower : ∀ᶠ n in Filter.atTop, n.choose 3 ≤ (H n).card)
    (hLayers : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop,
      ∃ V centers : Edge (Fin (n + 1)),
      ∃ L : Fin (n + 1) → Family (Fin (n + 1)),
      ∃ owner : Edge (Fin (n + 1)) → Fin (n + 1), ∃ loss : ℕ,
        (∀ c ∈ centers, c ∉ V) ∧
        (∀ c ∈ centers, ∀ T ∈ L c, T ∈ V.powersetCard 3) ∧
        (∀ c ∈ centers, ∀ T ∈ L c, insert c T ∈ H n) ∧
        (H n).card ≤ (∑ c ∈ centers, (pairOwnerCleanedLink L owner c).card) + loss ∧
        (loss : ℝ) / (n : ℝ) ^ 3 ≤ ε) :
    ∀ᶠ n in Filter.atTop,
      (H n).card ≤ n.choose 3 + n / 4 ∧
      LinearFamily (outsideEdges (H n) (Finset.univ.erase (actualGlobalMainCenter (H n)))) ∧
      4 * (outsideEdges (H n) (Finset.univ.erase (actualGlobalMainCenter (H n)))).card ≤
        (missingStarTriples (H n) (Finset.univ.erase (actualGlobalMainCenter (H n)))
          (actualGlobalMainCenter (H n))).card + n :=
  rank_four_eventual_exact_bound_of_outside_stability H (fun n => actualGlobalMainCenter (H n))
    hAdm hUniform hLower (actual_global_center_stability_of_parameter_layers H hLower hLayers)

end JSP523.Rank4
