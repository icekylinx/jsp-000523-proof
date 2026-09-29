import JSP523.Rank4.GlobalActualInitialOuterData
import JSP523.Rank4.GlobalActualEndToEndOuter

namespace JSP523.Rank4

open Filter

/-- The actual uncleaned overlap obeys the same uniform numerical bound
as every cleaned overlap. -/
theorem actual_initial_outer_uncleaned_overlap_bound
    {n : ℕ} (H : Family (Fin n)) (Z X : Edge (Fin n))
    (hAdm : Admissible H) (hUniform : Uniform 4 H)
    (hCover : initial_outer_overlap_cover_data H Z X) :
    endToEndOverlap H Z X ≤ Z.card * n * (n + 9) * initialOuterTripleThreshold n := by
  let U := endToEndGround Z X
  have hOutside : ∀ c ∈ Z, c ∉ U := fun c hc hU =>
    (Finset.mem_sdiff.mp hU).2 (Finset.mem_union_left _ hc)
  have hCap : ∀ T : Edge (Fin n), T ⊆ U → T.card = 3 →
      (facetCompletions H U T).card ≤ initialOuterTripleThreshold n := by
    intro T hTU hT
    rw [facet_completions_eq_induced_core_on_ground H U T hTU]
    exact (initial_outer_core_completion_cap H Z X _ hUniform hCover.2.2.2.2.2.2 T hT).le
  have hBound := rank_four_original_star_core_overlap_card_le H U Z
    (initialOuterTripleThreshold n) hAdm hUniform hOutside hCap
  have hUn : U.card ≤ n := by simpa using Finset.card_le_card (Finset.subset_univ U)
  calc
    _ ≤ _ := hBound
    _ ≤ Z.card * n * ((n + 9) * initialOuterTripleThreshold n) := by gcongr
    _ = _ := by ring

/-- The uncleaned overlap of any actual selected covers vanishes at the
predecessor cubic normalization used by the positive-size master sequence. -/
theorem actual_initial_outer_succ_uncleaned_overlap_tendsto_zero
    (H : (n : ℕ) → Family (Fin (n + 1)))
    (Z X : (n : ℕ) → Edge (Fin (n + 1)))
    (hAdm : ∀ᶠ n in atTop, Admissible (H n))
    (hUniform : ∀ᶠ n in atTop, Uniform 4 (H n))
    (hCover : ∀ᶠ n in atTop, initial_outer_overlap_cover_data (H n) (Z n) (X n)) :
    Tendsto (fun n => (endToEndOverlap (H n) (Z n) (X n) : ℝ) / (n : ℝ) ^ 3)
      atTop (nhds 0) := by
  have hPred : Tendsto (fun n : ℕ => n - 1) atTop atTop :=
    tendsto_sub_atTop_nat 1
  have hCenters : ∀ᶠ m : ℕ in atTop,
      ((Z (m - 1)).card : ℝ) ≤ 128 * (m : ℝ) ^ (3 / 10 : ℝ) := by
    filter_upwards [hPred.eventually hCover, eventually_ge_atTop 1] with m hm hm1
    simpa only [Nat.sub_add_cancel hm1] using hm.2.1
  have hBound : ∀ᶠ m : ℕ in atTop,
      endToEndOverlap (H (m - 1)) (Z (m - 1)) (X (m - 1)) ≤
        (Z (m - 1)).card * m * (m + 9) * initialOuterTripleThreshold m := by
    filter_upwards [hPred.eventually hCover, hPred.eventually hAdm,
      hPred.eventually hUniform, eventually_ge_atTop 1] with m hm hA hF hm1
    have h := actual_initial_outer_uncleaned_overlap_bound (H (m - 1)) (Z (m - 1))
      (X (m - 1)) hA hF hm
    simpa only [Nat.sub_add_cancel hm1] using h
  have hLimit := initial_outer_overlap_choose_ratio_tendsto_zero
    (fun m => (Z (m - 1)).card)
    (fun m => endToEndOverlap (H (m - 1)) (Z (m - 1)) (X (m - 1))) hCenters hBound
  have hShift : Tendsto (fun n => (endToEndOverlap (H n) (Z n) (X n) : ℝ) /
      ((n + 1).choose 3 : ℝ)) atTop (nhds 0) := by
    have hIndex (n : ℕ) : endToEndOverlap (H (n + 1 - 1)) (Z (n + 1 - 1)) (X (n + 1 - 1)) =
        endToEndOverlap (H n) (Z n) (X n) :=
      congrArg (fun k => endToEndOverlap (H k) (Z k) (X k)) (Nat.add_sub_cancel n 1)
    simpa only [Function.comp_def, hIndex] using hLimit.comp (tendsto_add_atTop_nat 1)
  exact nonnegative_choose_succ_ratio_pred_cubic_tendsto_zero _ (fun _ => by positivity) hShift

/-- Select fixed initial objects once. Both errors consumed by the master
selection theorem are actual quantities and are negligible at scale n³. -/
theorem exists_actual_initial_outer_sequence_with_uncleaned_overlap
    (H : (n : ℕ) → Family (Fin (n + 1)))
    (hAdm : ∀ᶠ n in atTop, Admissible (H n))
    (hUniform : ∀ᶠ n in atTop, Uniform 4 (H n)) :
    ∃ Z X : (n : ℕ) → Edge (Fin (n + 1)),
    ∃ owner : (n : ℕ) → Edge (Fin (n + 1)) → Fin (n + 1),
    ∃ outerLoss : ℕ → ℕ,
      (∀ᶠ n in atTop, ActualInitialOuterData (H n) (Z n) (X n) (owner n) (outerLoss n)) ∧
      Tendsto (fun n => (outerLoss n : ℝ) / (n : ℝ) ^ 3) atTop (nhds 0) ∧
      Tendsto (fun n => (endToEndOverlap (H n) (Z n) (X n) : ℝ) / (n : ℝ) ^ 3)
        atTop (nhds 0) := by
  obtain ⟨Z,X,owner,loss,overlap,hData,_,hLoss,_⟩ :=
    exists_actual_initial_outer_sequence H hAdm hUniform
  refine ⟨Z,X,owner,loss,hData,?_,?_⟩
  · exact nonnegative_choose_succ_ratio_pred_cubic_tendsto_zero _ (fun _ => by positivity) hLoss
  · apply actual_initial_outer_succ_uncleaned_overlap_tendsto_zero H Z X hAdm hUniform
    filter_upwards [hData] with n hn
    exact hn.cover

end JSP523.Rank4
