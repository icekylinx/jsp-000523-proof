import JSP523.Rank4.GlobalActualParameterChoice
import JSP523.Rank4.LocalC8Actual

/-! # Passing from actual outside-edge stability to the near-star threshold -/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- Above the full-star lower bound, every missing star triple is paid
by an actual outside edge. -/
theorem rank_four_missing_le_outside_of_star_lower
    {H : Family α} {W : Edge α} {v : α}
    (hUniform : Uniform 4 H)
    (hSupport : ∀ E ∈ H, E ⊆ insert v W) (hvW : v ∉ W)
    (hLower : W.card.choose 3 ≤ H.card) :
    (missingStarTriples H W v).card ≤ (outsideEdges H W).card := by
  have hStar := rank_four_star_outside_card hUniform hSupport hvW
  have hPartition := present_add_missing_star H W v
  omega

/-- The global outside-edge stability estimate supplies precisely the
missing-triple hypothesis consumed by Theorem III.2. -/
theorem rank_four_near_star_threshold_of_outside
    {H : Family α} {W : Edge α} {v : α}
    (hUniform : Uniform 4 H)
    (hSupport : ∀ E ∈ H, E ⊆ insert v W) (hvW : v ∉ W)
    (hLower : W.card.choose 3 ≤ H.card)
    (hOutside : 10000 * (outsideEdges H W).card ≤ W.card ^ 3) :
    10000 * (missingStarTriples H W v).card ≤ W.card ^ 3 := by
  have hMissing := rank_four_missing_le_outside_of_star_lower hUniform hSupport hvW hLower
  omega

/-- An actual vanishing outside-edge ratio eventually satisfies the
explicit constant in the local theorem. -/
theorem outside_ratio_tendsto_zero_implies_threshold
    (b : ℕ → ℕ)
    (hRatio : Filter.Tendsto (fun n => (b n : ℝ) / (n : ℝ) ^ 3)
      Filter.atTop (nhds 0)) :
    ∀ᶠ n : ℕ in Filter.atTop, 1000 ≤ n ∧ 10000 * b n ≤ n ^ 3 := by
  have hSmall := (tendsto_order.1 hRatio).2 (1 / 10000) (by norm_num)
  filter_upwards [hSmall, Filter.eventually_ge_atTop (1000 : ℕ)] with n hn hnLarge
  refine ⟨hnLarge, ?_⟩
  have hnPos : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  have hMul := (div_lt_iff₀ hnPos).1 hn
  have hReal : ((10000 * b n : ℕ) : ℝ) ≤ ((n ^ 3 : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast hReal

/-- Outside-edge stability at actual centers yields the extremal finite
formula for all sufficiently large members of a near-extremal sequence. -/
theorem rank_four_eventual_exact_bound_of_outside_stability
    (H : (n : ℕ) → Family (Fin (n + 1))) (v : (n : ℕ) → Fin (n + 1))
    (hH : ∀ n, Admissible (H n)) (hUniform : ∀ n, Uniform 4 (H n))
    (hLower : ∀ᶠ n in Filter.atTop, n.choose 3 ≤ (H n).card)
    (hOutside : Filter.Tendsto
      (fun n => ((outsideEdges (H n) (Finset.univ.erase (v n))).card : ℝ) / (n : ℝ) ^ 3)
      Filter.atTop (nhds 0)) :
    ∀ᶠ n in Filter.atTop,
      (H n).card ≤ n.choose 3 + n / 4 ∧
      LinearFamily (outsideEdges (H n) (Finset.univ.erase (v n))) ∧
      4 * (outsideEdges (H n) (Finset.univ.erase (v n))).card ≤
        (missingStarTriples (H n) (Finset.univ.erase (v n)) (v n)).card + n := by
  have hThreshold := outside_ratio_tendsto_zero_implies_threshold
    (fun n => (outsideEdges (H n) (Finset.univ.erase (v n))).card) hOutside
  filter_upwards [hThreshold, hLower] with n hn hLow
  let W : Edge (Fin (n + 1)) := Finset.univ.erase (v n)
  have hW : W.card = n := by simp [W]
  have hvW : v n ∉ W := by simp [W]
  have hSupport : ∀ E ∈ H n, E ⊆ insert (v n) W := by
    intro E hE
    have hFull : insert (v n) W = Finset.univ := by simp [W]
    rw [hFull]
    exact Finset.subset_univ E
  have hLowW : W.card.choose 3 ≤ (H n).card := by simpa only [hW] using hLow
  have hMissing := rank_four_near_star_threshold_of_outside (hUniform n) hSupport hvW hLowW
    (by simpa only [hW] using hn.2)
  have hLocal := rank_four_near_star_theorem_iii2 (hH n) (hUniform n) hSupport hvW
    (by simpa only [hW] using hn.1) hMissing
  exact ⟨by simpa only [hW] using hLocal.2.1,
    (hLocal.2.2.1 hLowW).1, by simpa only [hW] using (hLocal.2.2.1 hLowW).2⟩

end JSP523.Rank4
