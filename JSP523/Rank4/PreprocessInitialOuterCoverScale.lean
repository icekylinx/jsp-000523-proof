import JSP523.Rank4.PreprocessInitialOuterCover
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # The manuscript's fractional thresholds for the initial outer cover -/

namespace JSP523.Rank4

open Filter

noncomputable def initialOuterTripleThreshold (n : ℕ) : ℕ :=
  Nat.ceil ((n : ℝ) ^ (3 / 5 : ℝ))

/-- The actual rounded triple threshold eventually has the separation
needed by the heavy-triple second moment. -/
theorem eventually_initial_outer_triple_threshold_gap :
    ∀ᶠ n : ℕ in atTop, 0 < initialOuterTripleThreshold n ∧
      2 * n ≤ (initialOuterTripleThreshold n) ^ 2 := by
  have hGrow : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 5 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [hGrow.eventually (eventually_ge_atTop 2), eventually_ge_atTop 1]
    with n hn hn1
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hPowPos : (0 : ℝ) < (n : ℝ) ^ (3 / 5 : ℝ) := Real.rpow_pos_of_pos hnPos _
  have hCeil : (n : ℝ) ^ (3 / 5 : ℝ) ≤ initialOuterTripleThreshold n := Nat.le_ceil _
  have htPos : 0 < initialOuterTripleThreshold n := by
    have h : (0 : ℝ) < initialOuterTripleThreshold n := hPowPos.trans_le hCeil
    exact_mod_cast h
  refine ⟨htPos, ?_⟩
  have hIdentity : ((n : ℝ) ^ (3 / 5 : ℝ)) ^ 2 =
      (n : ℝ) * (n : ℝ) ^ (1 / 5 : ℝ) := by
    rw [← Real.rpow_mul_natCast hnPos.le]
    rw [show (3 / 5 : ℝ) * (2 : ℕ) = 1 + 1 / 5 by norm_num,
      Real.rpow_add hnPos, Real.rpow_one]
  have hPower : 2 * (n : ℝ) ≤ ((n : ℝ) ^ (3 / 5 : ℝ)) ^ 2 := by
    rw [hIdentity]
    nlinarith only [mul_le_mul_of_nonneg_left hn hnPos.le]
  have hSquare : ((n : ℝ) ^ (3 / 5 : ℝ)) ^ 2 ≤
      (initialOuterTripleThreshold n : ℝ) ^ 2 := by gcongr
  exact_mod_cast hPower.trans hSquare

/-- The complete initial rank-four outer cover at the exponents in
III.A.3, uniformly over all actual admissible families. -/
theorem eventually_exists_initial_outer_cover :
    ∀ᶠ n : ℕ in atTop, ∀ H : Family (Fin n),
      Admissible H → Uniform 4 H →
      ∃ Z X : Edge (Fin n),
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
            initialOuterTripleThreshold n) := by
  filter_upwards [eventually_initial_outer_triple_threshold_gap, eventually_ge_atTop 1]
    with n hThreshold hn1
  intro H hAdm hUniform
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hDPos : (0 : ℝ) < (n : ℝ) ^ (27 / 10 : ℝ) := Real.rpow_pos_of_pos hnPos _
  have htPos : (0 : ℝ) < (n : ℝ) ^ (3 / 5 : ℝ) := Real.rpow_pos_of_pos hnPos _
  obtain ⟨Z,X,hX,hZBudget,hXBudget,hCount,hVertex,hCore,hTriple⟩ :=
    exists_initial_outer_cover H ((n : ℝ) ^ (27 / 10 : ℝ)) (initialOuterTripleThreshold n)
      hAdm hUniform hDPos.le hThreshold.1 hThreshold.2
  have hProductZ : (n : ℝ) ^ (27 / 10 : ℝ) * (n : ℝ) ^ (3 / 10 : ℝ) = (n : ℝ) ^ 3 := by
    rw [← Real.rpow_add hnPos]
    norm_num
  have hProductX : (n : ℝ) ^ (2 / 5 : ℝ) * (n : ℝ) ^ (3 / 5 : ℝ) = n := by
    rw [← Real.rpow_add hnPos]
    norm_num
  have hZ : (Z.card : ℝ) ≤ 128 * (n : ℝ) ^ (3 / 10 : ℝ) := by
    apply (mul_le_mul_iff_right₀ hDPos).mp
    calc
      _ ≤ 128 * (n : ℝ) ^ 3 := hZBudget
      _ = _ := by rw [mul_left_comm, hProductZ]
  have hXReal : (X.card : ℝ) * initialOuterTripleThreshold n ≤ 6 * (n : ℝ) := by
    exact_mod_cast hXBudget
  have hXSize : (X.card : ℝ) ≤ 6 * (n : ℝ) ^ (2 / 5 : ℝ) := by
    apply (mul_le_mul_iff_left₀ htPos).mp
    calc
      _ ≤ (X.card : ℝ) * initialOuterTripleThreshold n :=
        mul_le_mul_of_nonneg_left (Nat.le_ceil _) (Nat.cast_nonneg X.card)
      _ ≤ 6 * (n : ℝ) := hXReal
      _ = _ := by rw [mul_assoc, hProductX]
  refine ⟨Z,X,hX,hZ,hXSize,?_,hVertex,hCore,hTriple⟩
  have hCountR : (n : ℝ) ≤ (Finset.univ \ (Z ∪ X)).card + (Z.card : ℝ) + X.card := by
    exact_mod_cast hCount
  have hPower : (n : ℝ) ^ (3 / 10 : ℝ) ≤ (n : ℝ) ^ (2 / 5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by norm_num)
  linarith

end JSP523.Rank4
