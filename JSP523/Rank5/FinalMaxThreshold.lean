import JSP523.ExtremalExactTransfer
import JSP523.Rank5.FinalAllRanksGlobal

/-! # Exact extremal and forcing functions in every fixed rank at least five -/

namespace JSP523.Rank5

open Filter

/-- The eventual exact maximum in Theorem 1, in the finite extremal-function
notation, for each fixed rank at least five. -/
theorem eventually_rank_at_least_five_max_avoiding_card_exact
    (r : ℕ) (hr : 5 ≤ r) :
    ∀ᶠ n : ℕ in atTop,
      maxAvoidingCard (Finset.univ : Edge (Fin n)) r =
        (n - 1).choose (r - 1) + (n - 1) / r := by
  filter_upwards [eventually_rank_at_least_five_extremal_exact r hr]
    with n hn
  exact max_avoiding_card_fin_eq_of_family_exact n r
    ((n - 1).choose (r - 1) + (n - 1) / r) hn.1 hn.2

/-- The coefficient-one exact least forcing threshold for each fixed rank
at least five. -/
theorem eventually_rank_at_least_five_forcing_threshold_exact
    (r : ℕ) (hr : 5 ≤ r) :
    ∀ᶠ n : ℕ in atTop,
      IsForcingThreshold (Finset.univ : Edge (Fin n)) r
        ((n - 1).choose (r - 1) + (n - 1) / r + 1) ∧
      (∀ k, IsForcingThreshold (Finset.univ : Edge (Fin n)) r k →
        (n - 1).choose (r - 1) + (n - 1) / r + 1 ≤ k) := by
  filter_upwards [eventually_rank_at_least_five_max_avoiding_card_exact r hr]
    with n hn
  simpa only [hn] using forcing_threshold_exact (Finset.univ : Edge (Fin n)) r

end JSP523.Rank5
