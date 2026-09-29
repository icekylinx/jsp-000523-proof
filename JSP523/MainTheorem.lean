import JSP523.Rank5.FinalMaxThreshold
import JSP523.Rank4.GlobalActualUnconditional
import JSP523.Rank4.GlobalActualNearExtremal
import JSP523.Rank3.ForcingThreshold
import JSP523.FinalDensity

/-! # The extremal and forcing conclusions of Theorem 1 -/

namespace JSP523

open Filter

/-- The finite rank-three upper bound in the manuscript's ground-set
notation. -/
theorem rank_three_max_avoiding_card_le_choose_two (n : ℕ) :
    maxAvoidingCard (Finset.univ : Edge (Fin n)) 3 ≤ n.choose 2 := by
  simpa only [Finset.card_univ, Fintype.card_fin] using
    Rank3.rank_three_max_avoiding_card_upper
      (Finset.univ : Edge (Fin n))

/-- The exact extremal formula for every fixed rank at least four and all
sufficiently large ground sets. -/
theorem eventually_fixed_rank_at_least_four_max_exact
    (r : ℕ) (hr : 4 ≤ r) :
    ∀ᶠ n : ℕ in atTop,
      maxAvoidingCard (Finset.univ : Edge (Fin n)) r =
        (n - 1).choose (r - 1) + (n - 1) / r := by
  by_cases hFour : r = 4
  · subst r
    filter_upwards [Rank4.eventually_rank_four_extremal_exact] with n hn
    exact max_avoiding_card_fin_eq_of_family_exact n 4
      ((n - 1).choose 3 + (n - 1) / 4) hn.1 hn.2
  · exact Rank5.eventually_rank_at_least_five_max_avoiding_card_exact r (by omega)

/-- The exact least forcing threshold for every fixed rank at least four. -/
theorem eventually_fixed_rank_at_least_four_forcing_exact
    (r : ℕ) (hr : 4 ≤ r) :
    ∀ᶠ n : ℕ in atTop,
      IsForcingThreshold (Finset.univ : Edge (Fin n)) r
        ((n - 1).choose (r - 1) + (n - 1) / r + 1) ∧
      (∀ k, IsForcingThreshold (Finset.univ : Edge (Fin n)) r k →
        (n - 1).choose (r - 1) + (n - 1) / r + 1 ≤ k) := by
  filter_upwards [eventually_fixed_rank_at_least_four_max_exact r hr] with n hn
  simpa only [hn] using forcing_threshold_exact (Finset.univ : Edge (Fin n)) r

/-- The avoiding maximum has coefficient one at every fixed rank at least
three. -/
theorem coefficient_one_avoiding_density
    (r : ℕ) (hr : 3 ≤ r) :
    Tendsto (fun n => (maxAvoidingCard (Finset.univ : Edge (Fin n)) r : ℝ) /
      (n.choose (r - 1) : ℝ)) atTop (nhds 1) :=
  coefficient_one_avoiding_density_of_eventual_exact
    eventually_fixed_rank_at_least_four_max_exact r hr

/-- The least forcing threshold has coefficient one at every fixed rank
at least three. -/
theorem coefficient_one_forcing_density
    (r : ℕ) (hr : 3 ≤ r) :
    Tendsto (fun n => ((maxAvoidingCard (Finset.univ : Edge (Fin n)) r + 1 : ℕ) : ℝ) /
      (n.choose (r - 1) : ℝ)) atTop (nhds 1) :=
  coefficient_one_forcing_density_of_eventual_exact
    eventually_fixed_rank_at_least_four_max_exact r hr

/-- The finite rank-three bound and all eventual exact higher-rank
formulas, stated together as Theorem 1. -/
theorem jsp_000523_main_theorem :
    (∀ n : ℕ,
      maxAvoidingCard (Finset.univ : Edge (Fin n)) 3 ≤ n.choose 2) ∧
    (∀ r : ℕ, 4 ≤ r →
      ∀ᶠ n : ℕ in atTop,
        maxAvoidingCard (Finset.univ : Edge (Fin n)) r =
          (n - 1).choose (r - 1) + (n - 1) / r) :=
  ⟨rank_three_max_avoiding_card_le_choose_two,
    eventually_fixed_rank_at_least_four_max_exact⟩

end JSP523
