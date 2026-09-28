import JSP523.ExtremalBounds
import JSP523.Rank3.PartIICorollary
import JSP523.Rank3.PartIIAsymptotic

/-!
# The finite rank-three forcing threshold

This transfers the rank-three upper theorem of Part II and the common
star-plus-matching construction of Part I to the forcing convention of
Theorem 1 in `paper/proof.pdf`.
-/

namespace JSP523.Rank3

open Filter
open scoped Topology

/-- The least rank-three forcing threshold lies between the construction
size plus one and the upper bound of Theorem II.1 plus one. -/
theorem rank_three_forcing_threshold_bounds (n : ℕ) (hn : 3 ≤ n) :
    (n - 1).choose 2 + (n - 1) / 3 + 1 ≤
        maxAvoidingCard (Finset.univ : Edge (Fin n)) 3 + 1 ∧
      maxAvoidingCard (Finset.univ : Edge (Fin n)) 3 + 1 ≤
        n.choose 2 + 1 := by
  have hLower := max_avoiding_card_fin_lower_all_rank n 3 (by omega) (by omega)
  have hLower' : (n - 1).choose 2 + (n - 1) / 3 ≤
      maxAvoidingCard (Finset.univ : Edge (Fin n)) 3 := by
    simpa using hLower
  have hUpper := rank_three_max_avoiding_card_upper
    (Finset.univ : Edge (Fin n))
  simp only [Finset.card_univ, Fintype.card_fin] at hUpper
  omega

/-- The threshold appearing between the two bounds is the least integer
that forces a repeated-union quadruple on `Fin n`. -/
theorem rank_three_least_forcing_threshold (n : ℕ) :
    IsForcingThreshold (Finset.univ : Edge (Fin n)) 3
        (maxAvoidingCard (Finset.univ : Edge (Fin n)) 3 + 1) ∧
      ∀ k, IsForcingThreshold (Finset.univ : Edge (Fin n)) 3 k →
        maxAvoidingCard (Finset.univ : Edge (Fin n)) 3 + 1 ≤ k :=
  forcing_threshold_exact (Finset.univ : Edge (Fin n)) 3

/-- The original JSP-000523 forcing threshold, divided by the natural
rank-three scale. Small ground sets are assigned zero. -/
noncomputable def rankThreeForcingDensity (n : ℕ) : ℝ :=
  if 3 ≤ n then
    ((maxAvoidingCard (Finset.univ : Edge (Fin n)) 3 + 1 : ℕ) : ℝ) /
      (n.choose 2 : ℝ)
  else 0

/-- The forcing threshold has coefficient one at rank three, as asserted
in Theorem 1 of `paper/proof.pdf`. -/
theorem rank_three_forcing_density_tendsto_one :
    Tendsto rankThreeForcingDensity atTop (nhds 1) := by
  have hChooseBound : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ≤ (n.choose 2 : ℝ) := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [Nat.cast_choose_two]
    have hProduct : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 3) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hChooseTop : Tendsto (fun n : ℕ => (n.choose 2 : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop hChooseBound tendsto_natCast_atTop_atTop
  have hExtra : Tendsto (fun n : ℕ => (n.choose 2 : ℝ)⁻¹)
      atTop (nhds 0) := hChooseTop.inv_tendsto_atTop
  have hEq : ∀ᶠ n : ℕ in atTop,
      rankThreeForcingDensity n =
        rankThreeDensity n + (n.choose 2 : ℝ)⁻¹ := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    simp only [rankThreeForcingDensity, rankThreeDensity, ite_eq_left hn,
      Nat.cast_add, Nat.cast_one, add_div, one_div]
  have hSum : Tendsto
      (fun n : ℕ => rankThreeDensity n + (n.choose 2 : ℝ)⁻¹)
      atTop (nhds 1) := by
    simpa using corollary_ii_2_asymptotic.add hExtra
  exact hSum.congr' (hEq.mono fun _ h => h.symm)

end JSP523.Rank3
