import JSP523.Rank4.GlobalActualEndToEndSequence
import JSP523.Rank4.GlobalActualSelectedStability
import JSP523.Rank4.GlobalActualEqualityConverse

/-! # Unconditional rank-four stability, exactness, and equality

The actual initial cover and actual master construction supply every
input to the stability argument. The final statements have no cleanup,
codegree, or asymptotic-budget assumptions.
-/

namespace JSP523.Rank4

open Filter

/-- Every sequence above the star lower bound has one center containing
all but `o(n³)` of its edges. -/
theorem rank_four_actual_sequence_outside_tendsto_zero
    (H : (n : ℕ) → Family (Fin (n + 1)))
    (hAdm : ∀ n, Admissible (H n)) (hUniform : ∀ n, Uniform 4 (H n))
    (hLower : ∀ᶠ n in atTop, n.choose 3 ≤ (H n).card) :
    Tendsto
      (fun n => ((outsideEdges (H n) (Finset.univ.erase (actualGlobalMainCenter (H n)))).card : ℝ) /
        (n : ℝ) ^ 3) atTop (nhds 0) := by
  obtain ⟨Z, X, owner, outerLoss, overlap, hInitial, hErrors⟩ :=
    exists_actual_master_sequence H (Eventually.of_forall hAdm) (Eventually.of_forall hUniform)
  exact actual_selected_master_sequence_outside H hAdm hUniform hLower
    Z X owner outerLoss overlap hInitial hErrors

/-- The exact extremal count on `n+1` vertices, including an attaining family. -/
theorem eventually_rank_four_extremal_exact_succ :
    ∀ᶠ n : ℕ in atTop,
      (∃ H : Family (Fin (n + 1)), Admissible H ∧ Uniform 4 H ∧
        H.card = n.choose 3 + n / 4) ∧
      (∀ H : Family (Fin (n + 1)), Admissible H → Uniform 4 H →
        H.card ≤ n.choose 3 + n / 4) :=
  eventually_rank_four_extremal_exact_of_sequence_stability
    rank_four_actual_sequence_outside_tendsto_zero

/-- Both equality forms, with a canonical center, are necessary and sufficient. -/
theorem eventually_rank_four_extremal_equality_iff_succ :
    ∀ᶠ n : ℕ in atTop, ∀ H : Family (Fin (n + 1)),
      Admissible H → Uniform 4 H →
      (H.card = n.choose 3 + n / 4 ↔
        RankFourNearStarEqualityFamily H
          (Finset.univ.erase (actualGlobalMainCenter H)) (actualGlobalMainCenter H)) := by
  have hClass := eventually_rank_four_extremal_classification_of_sequence_stability
    rank_four_actual_sequence_outside_tendsto_zero
  filter_upwards [hClass, eventually_ge_atTop (1000 : ℕ)] with n hClass hn
  intro H hAdm hUniform
  exact ⟨hClass H hAdm hUniform,
    rank_four_global_equality_form_implies_card H (actualGlobalMainCenter H) hn hAdm hUniform⟩

/-- The manuscript's `n`-vertex exact extremal statement at rank four. -/
theorem eventually_rank_four_extremal_exact :
    ∀ᶠ n : ℕ in atTop,
      (∃ H : Family (Fin n), Admissible H ∧ Uniform 4 H ∧
        H.card = (n - 1).choose 3 + (n - 1) / 4) ∧
      (∀ H : Family (Fin n), Admissible H → Uniform 4 H →
        H.card ≤ (n - 1).choose 3 + (n - 1) / 4) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp eventually_rank_four_extremal_exact_succ
  apply eventually_atTop.mpr
  refine ⟨N + 1, ?_⟩
  intro n hn
  cases n with
  | zero => omega
  | succ m => simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using hN m (by omega)

/-- An extremizer on `n` vertices has exactly one of the two stated forms
at some center, and each such form attains the extremal count. -/
theorem eventually_rank_four_extremal_equality_iff :
    ∀ᶠ n : ℕ in atTop, ∀ H : Family (Fin n),
      Admissible H → Uniform 4 H →
      (H.card = (n - 1).choose 3 + (n - 1) / 4 ↔
        ∃ v : Fin n, RankFourNearStarEqualityFamily H (Finset.univ.erase v) v) := by
  have hSucc : ∀ᶠ n : ℕ in atTop, ∀ H : Family (Fin (n + 1)),
      Admissible H → Uniform 4 H →
      (H.card = n.choose 3 + n / 4 ↔
        ∃ v : Fin (n + 1), RankFourNearStarEqualityFamily H (Finset.univ.erase v) v) := by
    filter_upwards [eventually_rank_four_extremal_equality_iff_succ,
      eventually_ge_atTop (1000 : ℕ)] with n hClass hn
    intro H hAdm hUniform
    constructor
    · intro hEquality
      exact ⟨actualGlobalMainCenter H, (hClass H hAdm hUniform).mp hEquality⟩
    · rintro ⟨v, hForm⟩
      exact rank_four_global_equality_form_implies_card H v hn hAdm hUniform hForm
  obtain ⟨N, hN⟩ := eventually_atTop.mp hSucc
  apply eventually_atTop.mpr
  refine ⟨N + 1, ?_⟩
  intro n hn
  cases n with
  | zero => omega
  | succ m => simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using hN m (by omega)

end JSP523.Rank4
