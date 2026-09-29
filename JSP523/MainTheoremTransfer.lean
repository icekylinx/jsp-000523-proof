import JSP523.ExtremalExactTransfer
import JSP523.Rank5.FinalMaxThreshold

/-! # Combining the rank-four and higher-rank exact endpoints -/

namespace JSP523

open Filter

/-- Once the rank-four family endpoint is available, the higher-rank theorem
gives the exact maximum at every fixed rank at least four.  The index `n+1`
keeps the rank-four canonical center available at every size. -/
theorem eventually_fixed_rank_at_least_four_max_exact_succ_of_rank_four
    (hFour : ∀ᶠ n : ℕ in atTop,
      (∃ H : Family (Fin (n + 1)), Admissible H ∧ Uniform 4 H ∧
        H.card = n.choose 3 + n / 4) ∧
      (∀ H : Family (Fin (n + 1)), Admissible H → Uniform 4 H →
        H.card ≤ n.choose 3 + n / 4))
    (r : ℕ) (hr : 4 ≤ r) :
    ∀ᶠ n : ℕ in atTop,
      maxAvoidingCard (Finset.univ : Edge (Fin (n + 1))) r =
        n.choose (r - 1) + n / r := by
  by_cases hFourRank : r = 4
  · subst r
    filter_upwards [hFour] with n hn
    exact max_avoiding_card_fin_eq_of_family_exact (n + 1) 4
      (n.choose 3 + n / 4) hn.1 hn.2
  · have hFive : 5 ≤ r := by omega
    have hExact :=
      (tendsto_add_atTop_nat 1).eventually
        (Rank5.eventually_rank_at_least_five_max_avoiding_card_exact r hFive)
    simpa only [Nat.add_sub_cancel] using hExact

/-- The exact least forcing threshold follows from the same rank-four
endpoint for every fixed rank at least four. -/
theorem eventually_fixed_rank_at_least_four_forcing_exact_succ_of_rank_four
    (hFour : ∀ᶠ n : ℕ in atTop,
      (∃ H : Family (Fin (n + 1)), Admissible H ∧ Uniform 4 H ∧
        H.card = n.choose 3 + n / 4) ∧
      (∀ H : Family (Fin (n + 1)), Admissible H → Uniform 4 H →
        H.card ≤ n.choose 3 + n / 4))
    (r : ℕ) (hr : 4 ≤ r) :
    ∀ᶠ n : ℕ in atTop,
      IsForcingThreshold (Finset.univ : Edge (Fin (n + 1))) r
        (n.choose (r - 1) + n / r + 1) ∧
      (∀ k, IsForcingThreshold (Finset.univ : Edge (Fin (n + 1))) r k →
        n.choose (r - 1) + n / r + 1 ≤ k) := by
  filter_upwards [eventually_fixed_rank_at_least_four_max_exact_succ_of_rank_four
    hFour r hr] with n hn
  simpa only [hn] using
    forcing_threshold_exact (Finset.univ : Edge (Fin (n + 1))) r

/-- A property holding at every sufficiently large successor holds at every
sufficiently large natural number. -/
theorem eventually_nat_of_eventually_succ {P : ℕ → Prop}
    (hSucc : ∀ᶠ n : ℕ in atTop, P (n + 1)) :
    ∀ᶠ n : ℕ in atTop, P n := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hSucc
  apply eventually_atTop.2
  refine ⟨N + 1, ?_⟩
  intro n hn
  cases n with
  | zero => omega
  | succ k => exact hN k (by omega)

/-- The exact maximum in the manuscript's `n`-vertex indexing. -/
theorem eventually_fixed_rank_at_least_four_max_exact_of_rank_four
    (hFour : ∀ᶠ n : ℕ in atTop,
      (∃ H : Family (Fin (n + 1)), Admissible H ∧ Uniform 4 H ∧
        H.card = n.choose 3 + n / 4) ∧
      (∀ H : Family (Fin (n + 1)), Admissible H → Uniform 4 H →
        H.card ≤ n.choose 3 + n / 4))
    (r : ℕ) (hr : 4 ≤ r) :
    ∀ᶠ n : ℕ in atTop,
      maxAvoidingCard (Finset.univ : Edge (Fin n)) r =
        (n - 1).choose (r - 1) + (n - 1) / r := by
  apply eventually_nat_of_eventually_succ
  simpa only [Nat.add_sub_cancel] using
    eventually_fixed_rank_at_least_four_max_exact_succ_of_rank_four hFour r hr

/-- The least forcing threshold in the manuscript's `n`-vertex indexing. -/
theorem eventually_fixed_rank_at_least_four_forcing_exact_of_rank_four
    (hFour : ∀ᶠ n : ℕ in atTop,
      (∃ H : Family (Fin (n + 1)), Admissible H ∧ Uniform 4 H ∧
        H.card = n.choose 3 + n / 4) ∧
      (∀ H : Family (Fin (n + 1)), Admissible H → Uniform 4 H →
        H.card ≤ n.choose 3 + n / 4))
    (r : ℕ) (hr : 4 ≤ r) :
    ∀ᶠ n : ℕ in atTop,
      IsForcingThreshold (Finset.univ : Edge (Fin n)) r
        ((n - 1).choose (r - 1) + (n - 1) / r + 1) ∧
      (∀ k, IsForcingThreshold (Finset.univ : Edge (Fin n)) r k →
        (n - 1).choose (r - 1) + (n - 1) / r + 1 ≤ k) := by
  apply eventually_nat_of_eventually_succ
  simpa only [Nat.add_sub_cancel] using
    eventually_fixed_rank_at_least_four_forcing_exact_succ_of_rank_four hFour r hr

end JSP523
