import JSP523.Rank4.PreprocessInitialOuterCoverScale
import JSP523.Rank4.PreprocessInitialOuterCoverTouching

namespace JSP523.Rank4

open Filter

noncomputable def initialOuterRegularizationScale (n : ℕ) : ℕ :=
  Nat.ceil ((n : ℝ) ^ (7 / 80 : ℝ))

/-- The rounded initial scale has enough room for the vertex cap, while
its eleventh power stays below the ambient size. -/
theorem eventually_initial_outer_regularization_scale :
    ∀ᶠ n : ℕ in atTop,
      initialOuterRegularizationScale n ^ 11 ≤ n ∧
      (n : ℝ) ^ (27 / 10 : ℝ) ≤
        (initialOuterRegularizationScale n : ℝ) ^ 8 * (n : ℝ) ^ 2 ∧
      initialOuterTripleThreshold n ≤ initialOuterRegularizationScale n ^ 8 := by
  have hGrow : Tendsto (fun n : ℕ => (n : ℝ) ^ (3 / 80 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 80)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [hGrow.eventually (eventually_ge_atTop (2048 : ℝ)),
    eventually_ge_atTop 1] with n hGrow hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  let a : ℝ := (n : ℝ) ^ (7 / 80 : ℝ)
  have ha : 1 ≤ a := Real.one_le_rpow hn1 (by norm_num)
  have hqlo : a ≤ initialOuterRegularizationScale n := Nat.le_ceil _
  have hqhi : (initialOuterRegularizationScale n : ℝ) ≤ 2 * a := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ a by linarith)
    change (initialOuterRegularizationScale n : ℝ) < a + 1 at h
    linarith
  have hq8 : (n : ℝ) ^ (7 / 10 : ℝ) ≤ (initialOuterRegularizationScale n : ℝ) ^ 8 := by
    have h := pow_le_pow_left₀ (show 0 ≤ a by linarith) hqlo 8
    dsimp only [a] at h
    rw [← Real.rpow_mul_natCast hn0.le] at h
    norm_num at h ⊢
    exact h
  refine ⟨?_, ?_, ?_⟩
  · have hPow := pow_le_pow_left₀ (Nat.cast_nonneg (initialOuterRegularizationScale n)) hqhi 11
    have hId : a ^ 11 * (n : ℝ) ^ (3 / 80 : ℝ) = n := by
      dsimp only [a]
      rw [← Real.rpow_mul_natCast hn0.le, ← Real.rpow_add hn0]
      norm_num
    have hFinal : (initialOuterRegularizationScale n : ℝ) ^ 11 ≤ n := by
      calc
        _ ≤ (2 * a) ^ 11 := hPow
        _ = 2048 * a ^ 11 := by ring
        _ ≤ (n : ℝ) ^ (3 / 80 : ℝ) * a ^ 11 :=
          mul_le_mul_of_nonneg_right hGrow (by positivity)
        _ = n := by rw [mul_comm, hId]
    exact_mod_cast hFinal
  · calc
      _ = (n : ℝ) ^ (7 / 10 : ℝ) * (n : ℝ) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hn0]; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_right hq8 (sq_nonneg _)
  · apply Nat.ceil_le.mpr
    change (n : ℝ) ^ (3 / 5 : ℝ) ≤ ((initialOuterRegularizationScale n ^ 8 : ℕ) : ℝ)
    push_cast
    exact (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (3 / 5 : ℝ) ≤ 7 / 10)).trans hq8

/-- An ordinary triple cap bounds each pair by charging to a third vertex. -/
theorem initial_outer_pair_degree_le_triple_cap
    {n : ℕ} (F : Family (Fin n)) (t : ℕ) (hUniform : Uniform 4 F)
    (hTriple : ∀ T : Edge (Fin n), T.card = 3 → (rankFourFacetParents F T).card ≤ t)
    (P : Edge (Fin n)) (hP : P.card = 2) :
    rankFourPairDegree F P ≤ n * t := by
  classical
  have hSub : (F.filter fun E => P ⊆ E) ⊆
      (Finset.univ \ P).biUnion fun x => rankFourFacetParents F (insert x P) := by
    intro E hE
    obtain ⟨hEF, hPE⟩ := Finset.mem_filter.mp hE
    have hNonempty : (E \ P).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_sdiff_of_subset hPE, hUniform hEF, hP]
      norm_num
    obtain ⟨x, hx⟩ := hNonempty
    obtain ⟨hxE, hxP⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxP⟩,
      Finset.mem_filter.mpr ⟨hEF, Finset.insert_subset_iff.mpr ⟨hxE, hPE⟩⟩⟩
  calc
    _ ≤ ((Finset.univ \ P).biUnion fun x => rankFourFacetParents F (insert x P)).card :=
      Finset.card_le_card hSub
    _ ≤ ∑ x ∈ Finset.univ \ P, (rankFourFacetParents F (insert x P)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ Finset.univ \ P, t := by
      apply Finset.sum_le_sum
      intro x hx
      exact hTriple _ (by rw [Finset.card_insert_of_notMem (Finset.mem_sdiff.mp hx).2, hP])
    _ = (Finset.univ \ P).card * t := by simp
    _ ≤ n * t := Nat.mul_le_mul_right _ (by
      have h : (Finset.univ \ P).card ≤ (Finset.univ : Edge (Fin n)).card :=
        Finset.card_le_card Finset.sdiff_subset
      simpa using h)

/-- The actual initial core satisfies all three caps required by geometric
regularization, at the concrete rounded scale. -/
theorem eventually_initial_outer_regularization_caps :
    ∀ᶠ n : ℕ in atTop, ∀ F : Family (Fin n), Uniform 4 F →
      (∀ v, ((F.filter fun E => v ∈ E).card : ℝ) ≤ (n : ℝ) ^ (27 / 10 : ℝ)) →
      (∀ T : Edge (Fin n), T.card = 3 →
        (rankFourFacetParents F T).card < initialOuterTripleThreshold n) →
      initialOuterRegularizationScale n ^ 11 ≤ n ∧
      (∀ v, (F.filter fun E => v ∈ E).card ≤ initialOuterRegularizationScale n ^ 8 * n ^ 2) ∧
      (∀ P : Edge (Fin n), P.card = 2 →
        rankFourPairDegree F P ≤ initialOuterRegularizationScale n ^ 8 * n) ∧
      (∀ T : Edge (Fin n), T.card = 3 →
        (facetCompletions F Finset.univ T).card ≤ initialOuterRegularizationScale n ^ 8) := by
  filter_upwards [eventually_initial_outer_regularization_scale] with n hn
  intro F hUniform hVertex hTriple
  have hCap : ∀ T : Edge (Fin n), T.card = 3 →
      (rankFourFacetParents F T).card ≤ initialOuterRegularizationScale n ^ 8 :=
    fun T hT => (hTriple T hT).le.trans hn.2.2
  refine ⟨hn.1, ?_, ?_, ?_⟩
  · intro v
    have h := (hVertex v).trans hn.2.1
    exact_mod_cast h
  · intro P hP
    simpa only [mul_comm] using
      initial_outer_pair_degree_le_triple_cap F _ hUniform hCap P hP
  · intro T hT
    rw [facet_completions_card_eq_parent_edges F Finset.univ T hUniform
      (fun E _ => Finset.subset_univ E) hT]
    exact hCap T hT

end JSP523.Rank4
