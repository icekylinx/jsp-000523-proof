import JSP523.Rank4.GlobalActualMasterStabilityEndToEnd
import JSP523.Rank4.GlobalActualInitialOuterData

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
  classical
  let q := fun n => initialOuterRegularizationScale (n + 1)
  have hScale : ∀ᶠ n in Filter.atTop, q n ^ 11 ≤ n + 1 :=
    hInitial.mono (fun _ h => h.scale_range)
  apply actual_master_stability_outside_ratio_of_single_error H q hAdm hUniform hLower hScale
  intro ν hν
  obtain ⟨r, hr, hData⟩ := hErrors ν hν
  have hInv : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  refine ⟨fun n => r n + 10 * (n : ℝ)⁻¹, ?_, ?_⟩
  · simpa using hr.add (hInv.const_mul 10)
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
  let d := A.to_master_stability_data (Z n) L (owner n) hOutside hGround hEdges hI.original_mass hLower
  refine ⟨d, ⟨hI.vertex_cap, hI.pair_cap, hI.facet_cap⟩, ?_, ?_⟩
  · have hCleanup := A.parent_cleanup_and_outer_le_master_error
    have hExact := d.cleanup_loss_eq_parent_sdiff
    change d.cleanup_loss =
      (fixedDecompositionCore (H n) U \ (clearUsedParentThenReciprocal A.completion).K).card at hExact
    change d.cleanup_loss + outerLoss n ≤ A.masterError
    dsimp only [U] at hExact
    omega
  · change ((A.masterError + 10 * n ^ 2 : ℕ) : ℝ) / (n : ℝ) ^ 3 ≤
      ν + (r n + 10 * (n : ℝ)⁻¹)
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hIdentity : ((A.masterError + 10 * n ^ 2 : ℕ) : ℝ) / (n : ℝ) ^ 3 =
        (A.masterError : ℝ) / (n : ℝ) ^ 3 + 10 * (n : ℝ)⁻¹ := by
      push_cast
      field_simp
    rw [hIdentity]
    linarith

end JSP523.Rank4
