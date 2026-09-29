import JSP523.Rank4.GlobalActualOuterLimits
import JSP523.Rank4.PreprocessInitialOuterCoverScale

/-! # The actual initial-cover overlap at exponents 3/10 and 3/5 -/
namespace JSP523.Rank4

/-- Rounding the core facet threshold adds at most another copy of its
fractional-power bound once the ambient size is positive. -/
theorem initial_outer_triple_threshold_le_twice_rpow
    (n : ℕ) (hn : 1 ≤ n) :
    (initialOuterTripleThreshold n : ℝ) ≤ 2 * (n : ℝ) ^ (3 / 5 : ℝ) := by
  have hOne : (1 : ℝ) ≤ (n : ℝ) ^ (3 / 5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have hCeil := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ (3 / 5 : ℝ))
  change (initialOuterTripleThreshold n : ℝ) < _ at hCeil
  linarith

theorem initial_outer_center_threshold_product_bound
    (n centers : ℕ) (hn : 1 ≤ n)
    (hCenters : (centers : ℝ) ≤ 128 * (n : ℝ) ^ (3 / 10 : ℝ)) :
    ((centers * initialOuterTripleThreshold n : ℕ) : ℝ) / n ≤
      256 * (n : ℝ) ^ (-1 / 10 : ℝ) := by
  have hnPos : (0 : ℝ) < n := by exact_mod_cast hn
  have hThreshold := initial_outer_triple_threshold_le_twice_rpow n hn
  have hId : (n : ℝ) ^ (3 / 10 : ℝ) * (n : ℝ) ^ (3 / 5 : ℝ) / n =
      (n : ℝ) ^ (-1 / 10 : ℝ) := by
    rw [← Real.rpow_add hnPos,
      show (3 / 10 : ℝ) + 3 / 5 = -1 / 10 + 1 by norm_num,
      Real.rpow_add hnPos, Real.rpow_one, mul_div_cancel_right₀ _ (ne_of_gt hnPos)]
  calc
    _ ≤ (128 * (n : ℝ) ^ (3 / 10 : ℝ)) *
        (2 * (n : ℝ) ^ (3 / 5 : ℝ)) / n := by
      push_cast
      gcongr
    _ = 256 * ((n : ℝ) ^ (3 / 10 : ℝ) * (n : ℝ) ^ (3 / 5 : ℝ) / n) := by ring
    _ = _ := by rw [hId]

/-- The concrete initial-cover product is `O(n^(-1/10))`. -/
theorem initial_outer_center_threshold_product_tendsto_zero
    (centers : ℕ → ℕ)
    (hCenters : ∀ᶠ n in Filter.atTop,
      (centers n : ℝ) ≤ 128 * (n : ℝ) ^ (3 / 10 : ℝ)) :
    Filter.Tendsto
      (fun n : ℕ => ((centers n * initialOuterTripleThreshold n : ℕ) : ℝ) / n)
      Filter.atTop (nhds 0) := by
  have hPow : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (-1 / 10 : ℝ))
      Filter.atTop (nhds 0) := by
    simpa only [neg_div, Function.comp_def] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
        tendsto_natCast_atTop_atTop
  have hUpper : Filter.Tendsto (fun n : ℕ => 256 * (n : ℝ) ^ (-1 / 10 : ℝ))
      Filter.atTop (nhds 0) := by simpa using hPow.const_mul 256
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => by positivity)) ?_ hUpper
  filter_upwards [hCenters, Filter.eventually_ge_atTop (1 : ℕ)] with n hC hn
  exact initial_outer_center_threshold_product_bound n (centers n) hn hC

/-- Any actual overlap obeying the finite bound at the initial threshold
is negligible after the precise binomial normalization. -/
theorem initial_outer_overlap_choose_ratio_tendsto_zero
    (centers overlap : ℕ → ℕ)
    (hCenters : ∀ᶠ n in Filter.atTop,
      (centers n : ℝ) ≤ 128 * (n : ℝ) ^ (3 / 10 : ℝ))
    (hBound : ∀ᶠ n in Filter.atTop,
      overlap n ≤ centers n * n * (n + 9) * initialOuterTripleThreshold n) :
    Filter.Tendsto (fun n : ℕ => (overlap n : ℝ) / (n.choose 3 : ℝ))
      Filter.atTop (nhds 0) :=
  outer_overlap_choose_ratio_tendsto_zero_of_product centers initialOuterTripleThreshold overlap
    (initial_outer_center_threshold_product_tendsto_zero centers hCenters) hBound

/-- The actual uncleaned star/core overlap is already negligible. Thus
all choices of owner cleaning inherit the same uniform overlap error. -/
theorem actual_initial_outer_overlap_choose_ratio_tendsto_zero
    (H : (n : ℕ) → Family (Fin n)) (U Z : (n : ℕ) → Edge (Fin n))
    (hData : ∀ᶠ n in Filter.atTop,
      Admissible (H n) ∧ Uniform 4 (H n) ∧
      (Z n).card ≤ 128 * (n : ℝ) ^ (3 / 10 : ℝ) ∧
      (∀ c ∈ Z n, c ∉ U n) ∧
      (∀ T : Edge (Fin n), T.card = 3 →
        (facetCompletions (fixedDecompositionCore (H n) (U n)) (U n) T).card ≤
          initialOuterTripleThreshold n)) :
    Filter.Tendsto
      (fun n => ((((Z n).biUnion fun c => rankFourStarLink (H n) (U n) c) ∩
        rankFourFacetShadow (fixedDecompositionCore (H n) (U n)) (U n)).card : ℝ) /
          (n.choose 3 : ℝ)) Filter.atTop (nhds 0) := by
  apply initial_outer_overlap_choose_ratio_tendsto_zero (fun n => (Z n).card)
  · filter_upwards [hData] with n hn
    exact hn.2.2.1
  · filter_upwards [hData] with n hn
    rcases hn with ⟨hAdm, hUniform, _, hOutside, hCap⟩
    have hBound := rank_four_original_star_core_overlap_card_le (H n) (U n) (Z n)
      (initialOuterTripleThreshold n) hAdm hUniform hOutside (by
        intro T hTU hTc
        rw [facet_completions_eq_induced_core_on_ground _ _ _ hTU]
        exact hCap T hTc)
    have hU : (U n).card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ (U n)
    calc
      _ ≤ _ := hBound
      _ ≤ (Z n).card * n * ((n + 9) * initialOuterTripleThreshold n) := by gcongr
      _ = _ := by ring

/-- Apply the overlap limit to the exact core returned by the initial
outer-cover theorem. Its parent-edge cap supplies the completion cap. -/
theorem actual_initial_cover_overlap_choose_ratio_tendsto_zero
    (H : (n : ℕ) → Family (Fin n)) (Z X : (n : ℕ) → Edge (Fin n))
    (hData : ∀ᶠ n in Filter.atTop,
      Admissible (H n) ∧ Uniform 4 (H n) ∧
      (Z n).card ≤ 128 * (n : ℝ) ^ (3 / 10 : ℝ) ∧
      (∀ T : Edge (Fin n), T.card = 3 →
        (rankFourFacetParents (fixedDecompositionCore (H n)
          (Finset.univ \ (Z n ∪ X n))) T).card < initialOuterTripleThreshold n)) :
    Filter.Tendsto
      (fun n => ((((Z n).biUnion fun c => rankFourStarLink (H n)
          (Finset.univ \ (Z n ∪ X n)) c) ∩
        rankFourFacetShadow (fixedDecompositionCore (H n) (Finset.univ \ (Z n ∪ X n)))
          (Finset.univ \ (Z n ∪ X n))).card : ℝ) /
          (n.choose 3 : ℝ)) Filter.atTop (nhds 0) := by
  apply actual_initial_outer_overlap_choose_ratio_tendsto_zero H
    (fun n => Finset.univ \ (Z n ∪ X n)) Z
  filter_upwards [hData] with n hn
  rcases hn with ⟨hAdm, hUniform, hZ, hParents⟩
  refine ⟨hAdm, hUniform, hZ, ?_, ?_⟩
  · intro c hc hU
    exact (Finset.mem_sdiff.mp hU).2 (Finset.mem_union_left _ hc)
  · intro T hT
    rw [facet_completions_card_eq_parent_edges
      (fixedDecompositionCore (H n) (Finset.univ \ (Z n ∪ X n)))
      (Finset.univ \ (Z n ∪ X n)) T
      (fun E hE => hUniform (Finset.mem_filter.mp hE).1)
      (fun _ hE => (Finset.mem_filter.mp hE).2) hT]
    exact (hParents T hT).le

/-- Actual cleaned overlaps are allowed to use arbitrary sublinks and
owner maps at each sufficiently large size. -/
theorem actual_cleaned_initial_outer_overlap_choose_ratio_tendsto_zero
    (H : (n : ℕ) → Family (Fin n)) (U Z : (n : ℕ) → Edge (Fin n))
    (overlap : ℕ → ℕ)
    (hData : ∀ᶠ n in Filter.atTop,
      Admissible (H n) ∧ Uniform 4 (H n) ∧
      (Z n).card ≤ 128 * (n : ℝ) ^ (3 / 10 : ℝ) ∧
      (∀ c ∈ Z n, c ∉ U n) ∧
      (∀ T : Edge (Fin n), T.card = 3 →
        (facetCompletions (fixedDecompositionCore (H n) (U n)) (U n) T).card ≤
          initialOuterTripleThreshold n))
    (hCleaned : ∀ᶠ n in Filter.atTop,
      ∃ L : Fin n → Family (Fin n), ∃ owner : Edge (Fin n) → Fin n,
        (∀ c ∈ Z n, L c ⊆ rankFourStarLink (H n) (U n) c) ∧
        overlap n = (((Z n).biUnion fun c => pairOwnerCleanedLink L owner c) ∩
          rankFourFacetShadow (fixedDecompositionCore (H n) (U n)) (U n)).card) :
    Filter.Tendsto (fun n => (overlap n : ℝ) / (n.choose 3 : ℝ))
      Filter.atTop (nhds 0) := by
  apply initial_outer_overlap_choose_ratio_tendsto_zero (fun n => (Z n).card)
  · filter_upwards [hData] with n hn
    exact hn.2.2.1
  · filter_upwards [hData, hCleaned] with n hData hCleaned
    rcases hData with ⟨hAdm, hUniform, _, hOutside, hCap⟩
    obtain ⟨L, owner, hLink, hEq⟩ := hCleaned
    rw [hEq]
    have hBound := rank_four_cleaned_star_core_overlap_card_le_of_core_cap
      (H n) (U n) (Z n) L owner (initialOuterTripleThreshold n)
      hAdm hUniform hOutside hLink hCap
    have hU : (U n).card ≤ n := by
      simpa only [Fintype.card_fin] using Finset.card_le_univ (U n)
    calc
      _ ≤ _ := hBound
      _ ≤ (Z n).card * n * ((n + 9) * initialOuterTripleThreshold n) := by gcongr
      _ = _ := by ring

/-- All data of the initial cover, retained while selecting a sequence. -/
def initial_outer_overlap_cover_data {n : ℕ}
    (H : Family (Fin n)) (Z X : Edge (Fin n)) : Prop :=
  X ⊆ Finset.univ \ Z ∧
  (Z.card : ℝ) ≤ 128 * (n : ℝ) ^ (3 / 10 : ℝ) ∧
  (X.card : ℝ) ≤ 6 * (n : ℝ) ^ (2 / 5 : ℝ) ∧
  (n : ℝ) - (Finset.univ \ (Z ∪ X)).card ≤ 134 * (n : ℝ) ^ (2 / 5 : ℝ) ∧
  (∀ z : Fin n, (((fixedDecompositionCore H (Finset.univ \ Z)).filter
    fun E => z ∈ E).card : ℝ) ≤ (n : ℝ) ^ (27 / 10 : ℝ)) ∧
  (∀ z : Fin n, (((fixedDecompositionCore H (Finset.univ \ (Z ∪ X))).filter
    fun E => z ∈ E).card : ℝ) ≤ (n : ℝ) ^ (27 / 10 : ℝ)) ∧
  (∀ T : Edge (Fin n), T.card = 3 →
    (rankFourFacetParents (fixedDecompositionCore H (Finset.univ \ (Z ∪ X))) T).card <
      initialOuterTripleThreshold n)

/-- Select actual covers from the uniform initial-cover theorem. Every
original cover estimate is retained, and their actual star/core overlap
has vanishing binomial ratio. -/
theorem exists_initial_outer_cover_with_vanishing_overlap
    (H : (n : ℕ) → Family (Fin n))
    (hAdm : ∀ n, Admissible (H n)) (hUniform : ∀ n, Uniform 4 (H n)) :
    ∃ Z X : (n : ℕ) → Edge (Fin n),
      (∀ᶠ n in Filter.atTop, initial_outer_overlap_cover_data (H n) (Z n) (X n)) ∧
      Filter.Tendsto
        (fun n => ((((Z n).biUnion fun c => rankFourStarLink (H n)
            (Finset.univ \ (Z n ∪ X n)) c) ∩
          rankFourFacetShadow (fixedDecompositionCore (H n) (Finset.univ \ (Z n ∪ X n)))
            (Finset.univ \ (Z n ∪ X n))).card : ℝ) /
            (n.choose 3 : ℝ)) Filter.atTop (nhds 0) := by
  classical
  have hExists : ∀ᶠ n in Filter.atTop,
      ∃ Z X : Edge (Fin n), initial_outer_overlap_cover_data (H n) Z X := by
    filter_upwards [eventually_exists_initial_outer_cover] with n hn
    exact hn (H n) (hAdm n) (hUniform n)
  have hChoice : ∀ n, ∃ Z X : Edge (Fin n),
      (∃ A B, initial_outer_overlap_cover_data (H n) A B) →
        initial_outer_overlap_cover_data (H n) Z X := by
    intro n
    by_cases h : ∃ A B, initial_outer_overlap_cover_data (H n) A B
    · obtain ⟨Z, X, hZX⟩ := h
      exact ⟨Z, X, fun _ => hZX⟩
    · exact ⟨∅, ∅, fun hh => (h hh).elim⟩
  choose Z X hChoice using hChoice
  have hData : ∀ᶠ n in Filter.atTop, initial_outer_overlap_cover_data (H n) (Z n) (X n) := by
    filter_upwards [hExists] with n hn
    exact hChoice n hn
  refine ⟨Z, X, hData, ?_⟩
  apply actual_initial_cover_overlap_choose_ratio_tendsto_zero H Z X
  filter_upwards [hData] with n hn
  exact ⟨hAdm n, hUniform n, hn.2.1, hn.2.2.2.2.2.2⟩

end JSP523.Rank4
