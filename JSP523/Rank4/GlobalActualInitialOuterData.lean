import JSP523.Rank4.PreprocessInitialOuterCoverBudget
import JSP523.Rank4.PreprocessInitialOuterCoverRegularization
import JSP523.Rank4.PreprocessInitialOuterBudgetScale
import JSP523.Rank4.GlobalActualOuterOverlapScale

namespace JSP523.Rank4

open Filter

/-- All initial data needed by the actual rank-four master, retaining the
original stars and all estimates from the initial cover. -/
structure ActualInitialOuterData {n : ℕ} (H : Family (Fin n))
    (Z X : Edge (Fin n)) (owner : Edge (Fin n) → Fin n) (outerLoss : ℕ) : Prop where
  cover : initial_outer_overlap_cover_data H Z X
  ground_large : 6 ≤ (Finset.univ \ (Z ∪ X)).card
  scale_range : initialOuterRegularizationScale n ^ 11 ≤ n
  vertex_cap : ∀ v, ((fixedDecompositionCore H (Finset.univ \ (Z ∪ X))).filter
    fun E => v ∈ E).card ≤ initialOuterRegularizationScale n ^ 8 * n ^ 2
  pair_cap : ∀ P : Edge (Fin n), P.card = 2 →
    rankFourPairDegree (fixedDecompositionCore H (Finset.univ \ (Z ∪ X))) P ≤
      initialOuterRegularizationScale n ^ 8 * n
  facet_cap : ∀ T : Edge (Fin n), T.card = 3 →
    (facetCompletions (fixedDecompositionCore H (Finset.univ \ (Z ∪ X))) Finset.univ T).card ≤
      initialOuterRegularizationScale n ^ 8
  original_mass : H.card ≤
    (Z.biUnion (pairOwnerCleanedLink (fun c => rankFourStarLink H (Finset.univ \ (Z ∪ X)) c) owner)).card +
      (fixedDecompositionCore H (Finset.univ \ (Z ∪ X))).card + outerLoss
  outer_loss_bound : outerLoss ≤ initial_outer_polynomial_budget n Z.card X.card (initial_outer_radius n)
  overlap_bound :
    ((Z.biUnion (pairOwnerCleanedLink (fun c => rankFourStarLink H (Finset.univ \ (Z ∪ X)) c) owner)) ∩
      rankFourFacetShadow (fixedDecompositionCore H (Finset.univ \ (Z ∪ X)))
        (Finset.univ \ (Z ∪ X))).card ≤
      Z.card * n * (n + 9) * initialOuterTripleThreshold n

/-- Uniform construction of the actual initial outer packet. No initial
codegree, decomposition, owner, or overlap premise remains. -/
theorem eventually_exists_actual_initial_outer_data :
    ∀ᶠ n : ℕ in atTop, ∀ H : Family (Fin n), Admissible H → Uniform 4 H →
      ∃ Z X : Edge (Fin n), ∃ owner : Edge (Fin n) → Fin n, ∃ outerLoss : ℕ,
        ActualInitialOuterData H Z X owner outerLoss := by
  filter_upwards [eventually_exists_initial_outer_cover,
    eventually_initial_outer_ground_at_least_six,
    eventually_initial_outer_regularization_caps, eventually_ge_atTop 1]
      with n hCover hGround hCaps hn
  intro H hAdm hUniform
  obtain ⟨Z, X, hX, hZ, hXS, hMissing, hVertex₀, hVertex, hTriple⟩ := hCover H hAdm hUniform
  let U := Finset.univ \ (Z ∪ X)
  have hU := hGround U hMissing
  have hSize : ∀ c ∈ X, 6 * ((fixedDecompositionCore H (Finset.univ \ Z)).filter
      fun E => c ∈ E).card ≤ initial_outer_radius n ^ 3 := by
    intro c _
    have h := initial_outer_radius_cube_lower n
    have hc := hVertex₀ c
    have hReal : (6 : ℝ) * ((fixedDecompositionCore H (Finset.univ \ Z)).filter
        fun E => c ∈ E).card ≤ (initial_outer_radius n : ℝ) ^ 3 := by linarith
    exact_mod_cast hReal
  obtain ⟨owner, loss, hOriginal, hLoss⟩ := exists_initial_outer_original_budget H Z X
    ⟨0, by omega⟩ (initial_outer_radius n) hAdm hUniform hX hU hSize
  obtain ⟨hRange, hV, hP, hT⟩ := hCaps (fixedDecompositionCore H U)
    (fun E hE => hUniform (Finset.mem_filter.mp hE).1) hVertex hTriple
  refine ⟨Z, X, owner, loss, ⟨⟨hX,hZ,hXS,hMissing,hVertex₀,hVertex,hTriple⟩,
    hU, hRange, hV, hP, hT, hOriginal, hLoss, ?_⟩⟩
  have hBound := rank_four_cleaned_star_core_overlap_card_le_of_core_cap H U Z
    (fun c => rankFourStarLink H U c) owner (initialOuterTripleThreshold n)
    hAdm hUniform
    (fun c hc hu => (Finset.mem_sdiff.mp hu).2 (Finset.mem_union_left _ hc))
    (fun _ _ => Finset.Subset.refl _) (fun T hT =>
      (initial_outer_core_completion_cap H Z X _ hUniform hTriple T hT).le)
  have hUn : U.card ≤ n := by simpa using Finset.card_le_card (Finset.subset_univ U)
  calc
    _ ≤ _ := hBound
    _ ≤ Z.card * n * ((n + 9) * initialOuterTripleThreshold n) := by gcongr
    _ = _ := by ring

/-- Choose the actual initial packets on the positive ambient sizes used
by the stability theorem. Both actual errors vanish after binomial
normalization, with no additional assumption on the chosen owners. -/
theorem exists_actual_initial_outer_sequence
    (H : (n : ℕ) → Family (Fin (n + 1)))
    (hAdm : ∀ᶠ n in atTop, Admissible (H n))
    (hUniform : ∀ᶠ n in atTop, Uniform 4 (H n)) :
    ∃ Z X : (n : ℕ) → Edge (Fin (n + 1)),
    ∃ owner : (n : ℕ) → Edge (Fin (n + 1)) → Fin (n + 1),
    ∃ outerLoss overlap : ℕ → ℕ,
      (∀ᶠ n in atTop, ActualInitialOuterData (H n) (Z n) (X n) (owner n) (outerLoss n)) ∧
      (∀ n, overlap n =
        (((Z n).biUnion (pairOwnerCleanedLink
          (fun c => rankFourStarLink (H n) (Finset.univ \ (Z n ∪ X n)) c) (owner n))) ∩
          rankFourFacetShadow (fixedDecompositionCore (H n) (Finset.univ \ (Z n ∪ X n)))
            (Finset.univ \ (Z n ∪ X n))).card) ∧
      Tendsto (fun n => (outerLoss n : ℝ) / ((n + 1).choose 3 : ℝ)) atTop (nhds 0) ∧
      Tendsto (fun n => (overlap n : ℝ) / ((n + 1).choose 3 : ℝ)) atTop (nhds 0) := by
  classical
  have hExists : ∀ᶠ n in atTop,
      ∃ Z X : Edge (Fin (n + 1)), ∃ owner : Edge (Fin (n + 1)) → Fin (n + 1),
      ∃ loss : ℕ, ActualInitialOuterData (H n) Z X owner loss := by
    filter_upwards [(tendsto_add_atTop_nat 1).eventually eventually_exists_actual_initial_outer_data,
      hAdm, hUniform] with n hn hA hF
    exact hn (H n) hA hF
  have hChoice : ∀ n, ∃ Z X : Edge (Fin (n + 1)),
      ∃ owner : Edge (Fin (n + 1)) → Fin (n + 1), ∃ loss : ℕ,
      (∃ A B o l, ActualInitialOuterData (H n) A B o l) →
        ActualInitialOuterData (H n) Z X owner loss := by
    intro n
    by_cases h : ∃ A B o l, ActualInitialOuterData (H n) A B o l
    · obtain ⟨Z,X,o,l,hd⟩ := h
      exact ⟨Z,X,o,l,fun _ => hd⟩
    · exact ⟨∅,∅,fun _ => ⟨0, Nat.zero_lt_succ n⟩,0,fun hh => (h hh).elim⟩
  choose Z X owner loss hChoice using hChoice
  have hData : ∀ᶠ n in atTop, ActualInitialOuterData (H n) (Z n) (X n) (owner n) (loss n) := by
    filter_upwards [hExists] with n hn
    exact hChoice n hn
  let overlap := fun n =>
    (((Z n).biUnion (pairOwnerCleanedLink
      (fun c => rankFourStarLink (H n) (Finset.univ \ (Z n ∪ X n)) c) (owner n))) ∩
      rankFourFacetShadow (fixedDecompositionCore (H n) (Finset.univ \ (Z n ∪ X n)))
        (Finset.univ \ (Z n ∪ X n))).card
  refine ⟨Z,X,owner,loss,overlap,hData,fun _ => rfl,?_,?_⟩
  · have hPred : Tendsto (fun n : ℕ => n - 1) atTop atTop :=
      tendsto_sub_atTop_nat 1
    have hCover : ∀ᶠ m : ℕ in atTop,
        ((((Z (m - 1)).card + (X (m - 1)).card : ℕ) : ℝ)) ≤
          134 * (m : ℝ) ^ (2 / 5 : ℝ) := by
      filter_upwards [hPred.eventually hData, eventually_ge_atTop 1] with m hm hm1
      have h := initial_outer_cover_sum_bound (m - 1 + 1) (Z (m - 1)).card (X (m - 1)).card
        (by omega) hm.cover.2.1 hm.cover.2.2.1
      simpa only [Nat.sub_add_cancel hm1] using h
    have hBudget := initial_outer_polynomial_budget_choose_ratio_tendsto_zero
      (fun m => (Z (m - 1)).card) (fun m => (X (m - 1)).card) initial_outer_radius hCover
      (Eventually.of_forall initial_outer_radius_upper)
    have hShift : Tendsto
        (fun n => (initial_outer_polynomial_budget (n + 1) (Z n).card (X n).card
          (initial_outer_radius (n + 1)) : ℝ) / ((n + 1).choose 3 : ℝ)) atTop (nhds 0) := by
      have hZindex (x : ℕ) : (Z (x + 1 - 1)).card = (Z x).card :=
        congrArg (fun k => (Z k).card) (Nat.add_sub_cancel x 1)
      have hXindex (x : ℕ) : (X (x + 1 - 1)).card = (X x).card :=
        congrArg (fun k => (X k).card) (Nat.add_sub_cancel x 1)
      simpa only [Function.comp_def, hZindex, hXindex] using hBudget.comp (tendsto_add_atTop_nat 1)
    apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) ?_ hShift
    filter_upwards [hData] with n hn
    exact div_le_div_of_nonneg_right (by exact_mod_cast hn.outer_loss_bound) (Nat.cast_nonneg _)
  · have hPred : Tendsto (fun n : ℕ => n - 1) atTop atTop :=
      tendsto_sub_atTop_nat 1
    have hCenters : ∀ᶠ m : ℕ in atTop,
        ((Z (m - 1)).card : ℝ) ≤ 128 * (m : ℝ) ^ (3 / 10 : ℝ) := by
      filter_upwards [hPred.eventually hData, eventually_ge_atTop 1] with m hm hm1
      simpa only [Nat.sub_add_cancel hm1] using hm.cover.2.1
    have hBound : ∀ᶠ m : ℕ in atTop,
        overlap (m - 1) ≤ (Z (m - 1)).card * m * (m + 9) * initialOuterTripleThreshold m := by
      filter_upwards [hPred.eventually hData, eventually_ge_atTop 1] with m hm hm1
      simpa only [Nat.sub_add_cancel hm1] using hm.overlap_bound
    have hLimit := initial_outer_overlap_choose_ratio_tendsto_zero
      (fun m => (Z (m - 1)).card) (fun m => overlap (m - 1)) hCenters hBound
    simpa only [Function.comp_def, Nat.add_sub_cancel] using hLimit.comp (tendsto_add_atTop_nat 1)

/-- Binomially negligible nonnegative errors are also negligible at the
cubic normalization used by the master sequence. -/
theorem nonnegative_choose_succ_ratio_cubic_tendsto_zero
    (f : ℕ → ℝ) (hNonneg : ∀ n, 0 ≤ f n)
    (hLimit : Tendsto (fun n => f n / ((n + 1).choose 3 : ℝ)) atTop (nhds 0)) :
    Tendsto (fun n => f n / ((n + 1 : ℕ) : ℝ) ^ 3) atTop (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun n => div_nonneg (hNonneg n) (by positivity)))
    ?_ hLimit
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hPos : (0 : ℝ) < (n + 1).choose 3 := by
    exact_mod_cast Nat.choose_pos (show 3 ≤ n + 1 by omega)
  have hChoose : ((n + 1).choose 3 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 3 := by
    exact_mod_cast Nat.choose_le_pow (n + 1) 3
  exact div_le_div_of_nonneg_left (hNonneg n) hPos hChoose

/-- The same selected errors vanish with the predecessor cubic denominator. -/
theorem nonnegative_choose_succ_ratio_pred_cubic_tendsto_zero
    (f : ℕ → ℝ) (hNonneg : ∀ n, 0 ≤ f n)
    (hLimit : Tendsto (fun n => f n / ((n + 1).choose 3 : ℝ)) atTop (nhds 0)) :
    Tendsto (fun n => f n / (n : ℝ) ^ 3) atTop (nhds 0) := by
  have hSucc := nonnegative_choose_succ_ratio_cubic_tendsto_zero f hNonneg hLimit
  have hUpper : Tendsto (fun n => 8 * (f n / ((n + 1 : ℕ) : ℝ) ^ 3)) atTop (nhds 0) := by
    simpa using hSucc.const_mul 8
  apply squeeze_zero' (Eventually.of_forall (fun n => div_nonneg (hNonneg n) (by positivity)))
    ?_ hUpper
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hCube : ((n + 1 : ℕ) : ℝ) ^ 3 ≤ 8 * (n : ℝ) ^ 3 := by
    push_cast
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 3)).2
  have hMul := mul_le_mul_of_nonneg_left hCube (hNonneg n)
  have hDiv := (le_div_iff₀ (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ 3)).2 hMul
  convert hDiv using 1
  ring

end JSP523.Rank4
