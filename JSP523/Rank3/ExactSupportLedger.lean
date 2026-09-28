import JSP523.Rank3.CellDegreeLedger
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option linter.unnecessarySimpa false

/-!
# The exact support ledger for an actual triple family

This connects the abstract integer algebra in `SupportLedger` to the genuine
completion degrees and common links.  The identity requires uniformity and a
ground set, but not admissibility.  The signed payment inequality needed to
make its right side nonpositive is a separate structural theorem.
-/

namespace JSP523.Rank3

section ExactSupportLedger

variable {α : Type*} [DecidableEq α]

/-- The quadratic pair-degree budget from the rank-three proof. -/
def pairBudget (d : ℕ) : ℚ :=
  if 4 ≤ d then ((d : ℚ) - 2) * ((d : ℚ) - 3) else 0

/-- Common-link incidences beyond the third. -/
def linkSurplus (c : ℕ) : ℚ :=
  if 3 < c then (c : ℚ) - 3 else 0

def actualPairBudget (H : Family α) (V : Edge α) : ℚ :=
  ∑ p ∈ usedPairs H V, pairBudget (completionVertices H V p).card

def actualLinkSurplus (H : Family α) (V : Edge α) : ℚ :=
  ∑ q ∈ usedCells H V, linkSurplus (commonLink H V q).card

def singletonCompletionPairs (H : Family α) (V : Edge α) : Family α :=
  (usedPairs H V).filter (fun p => (completionVertices H V p).card = 1)

def doubleLinkCells (H : Family α) (V : Edge α) : Family α :=
  (usedCells H V).filter (fun q => (commonLink H V q).card = 2)

private theorem pairBudget_pointwise (d : ℕ) (hd : 0 < d) :
    2 * (d.choose 2 : ℚ) - pairBudget d =
      4 * (d : ℚ) - 6 + (if d = 1 then 2 else 0) := by
  rcases (by omega : d = 1 ∨ d = 2 ∨ d = 3 ∨ 4 ≤ d) with h | h | h | h
  · subst d; norm_num [pairBudget]
  · subst d; norm_num [pairBudget]
  · subst d; norm_num [pairBudget]
  · have hne : d ≠ 1 := by omega
    simp [pairBudget, h, hne]
    rw [Nat.cast_choose_two ℚ d]
    ring

private theorem linkSurplus_pointwise (c : ℕ) (hc : 0 < c) :
    linkSurplus c = (c : ℚ) - 3 +
      (if c = 1 then 2 else 0) + (if c = 2 then 1 else 0) := by
  rcases (by omega : c = 1 ∨ c = 2 ∨ c = 3 ∨ 3 < c) with h | h | h | h
  · subst c; norm_num [linkSurplus]
  · subst c; norm_num [linkSurplus]
  · subst c; norm_num [linkSurplus]
  · have hne1 : c ≠ 1 := by omega
    have hne2 : c ≠ 2 := by omega
    simp [linkSurplus, h, hne1, hne2]

/-- The second completion moment vanishes off the actual pair support. -/
theorem usedPairs_completion_second_moment
    (H : Family α) (V : Edge α)
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V) :
    (∑ p ∈ usedPairs H V,
        (completionVertices H V p).card.choose 2) =
      ∑ q ∈ usedCells H V, (commonLink H V q).card := by
  calc
    (∑ p ∈ usedPairs H V,
        (completionVertices H V p).card.choose 2) =
        ∑ p ∈ V.powersetCard 2,
          (completionVertices H V p).card.choose 2 := by
      apply Finset.sum_subset (usedPairs_subset H V)
      intro p hp hnot
      by_cases hz : (completionVertices H V p).card = 0
      · simp [hz]
      · have hnon : (completionVertices H V p).Nonempty :=
          Finset.card_pos.mp (Nat.pos_of_ne_zero hz)
        exact False.elim (hnot
          ((mem_usedPairs_iff_completion_nonempty H V p
            hUniform hground hp).mpr hnon))
    _ = ∑ q ∈ usedCells H V, (commonLink H V q).card :=
      (usedCells_common_link_double_count H V).symm

private theorem card_filter_eq_sum_indicator
    {β : Type*} [DecidableEq β]
    (s : Finset β) (P : β → Prop) [DecidablePred P] :
    ((s.filter P).card : ℚ) =
      ∑ x ∈ s, if P x then (1 : ℚ) else 0 := by
  simpa using
    congrArg (fun n : ℕ => (n : ℚ)) (Finset.card_filter P s)

/-- The quadratic pair-degree identity summed over actual used pairs.
    This is the first counting input to equation (II.1) in `paper/proof.pdf`,
    with no abstract ledger parameters. -/
theorem actual_pair_budget_ledger
    (H : Family α) (V : Edge α)
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V) :
    2 * (∑ q ∈ usedCells H V, ((commonLink H V q).card : ℚ)) -
      actualPairBudget H V =
      12 * (H.card : ℚ) - 6 * ((usedPairs H V).card : ℚ) +
        2 * ((singletonCompletionPairs H V).card : ℚ) := by
  let U := usedPairs H V
  let d : Edge α → ℕ := fun p => (completionVertices H V p).card
  have hfirst : (∑ p ∈ U, (d p : ℚ)) = 3 * (H.card : ℚ) := by
    simpa [U, d] using
      congrArg (fun n : ℕ => (n : ℚ))
        (usedPairs_completion_first_moment H V hUniform hground)
  have hsecond : (∑ p ∈ U, ((d p).choose 2 : ℚ)) =
      ∑ q ∈ usedCells H V, ((commonLink H V q).card : ℚ) := by
    simpa [U, d] using
      congrArg (fun n : ℕ => (n : ℚ))
        (usedPairs_completion_second_moment H V hUniform hground)
  have hK : (∑ p ∈ U, if d p = 1 then (1 : ℚ) else 0) =
      ((singletonCompletionPairs H V).card : ℚ) := by
    exact (card_filter_eq_sum_indicator U (fun p => d p = 1)).symm
  have hpoint :
      (∑ p ∈ U, (2 * ((d p).choose 2 : ℚ) - pairBudget (d p))) =
        ∑ p ∈ U, (4 * (d p : ℚ) - 6 +
          (if d p = 1 then (2 : ℚ) else 0)) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hnon : (completionVertices H V p).Nonempty :=
      usedPair_has_completion H V p hUniform hground hp
    exact pairBudget_pointwise (d p) (Finset.card_pos.mpr hnon)
  have hL :
      (∑ p ∈ U, (2 * ((d p).choose 2 : ℚ) - pairBudget (d p))) =
        2 * (∑ p ∈ U, ((d p).choose 2 : ℚ)) -
          actualPairBudget H V := by
    simp [actualPairBudget, U, d, Finset.sum_sub_distrib, Finset.mul_sum]
  have hR :
      (∑ p ∈ U, (4 * (d p : ℚ) - 6 +
        (if d p = 1 then (2 : ℚ) else 0))) =
      4 * (∑ p ∈ U, (d p : ℚ)) - 6 * (U.card : ℚ) +
        2 * (∑ p ∈ U, if d p = 1 then (1 : ℚ) else 0) := by
    have htwo :
        (∑ p ∈ U, if d p = 1 then (2 : ℚ) else 0) =
          2 * (∑ p ∈ U, if d p = 1 then (1 : ℚ) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs <;> ring
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, htwo]
    simp [Finset.mul_sum]
    ring
  rw [hL, hR, hfirst, hsecond, hK] at hpoint
  dsimp [U] at hpoint
  nlinarith

/-- The link-surplus identity summed over genuinely used cells. -/
theorem actual_link_surplus_ledger (H : Family α) (V : Edge α) :
    actualLinkSurplus H V =
      (∑ q ∈ usedCells H V, ((commonLink H V q).card : ℚ)) -
        3 * ((usedCells H V).card : ℚ) +
        2 * ((singletonLinkCells H V).card : ℚ) +
        ((doubleLinkCells H V).card : ℚ) := by
  let C := usedCells H V
  let c : Edge α → ℕ := fun q => (commonLink H V q).card
  have hOne : (∑ q ∈ C, if c q = 1 then (1 : ℚ) else 0) =
      ((singletonLinkCells H V).card : ℚ) := by
    exact (card_filter_eq_sum_indicator C (fun q => c q = 1)).symm
  have hTwo : (∑ q ∈ C, if c q = 2 then (1 : ℚ) else 0) =
      ((doubleLinkCells H V).card : ℚ) := by
    exact (card_filter_eq_sum_indicator C (fun q => c q = 2)).symm
  have hpoint :
      (∑ q ∈ C, linkSurplus (c q)) =
        ∑ q ∈ C, ((c q : ℚ) - 3 +
          (if c q = 1 then (2 : ℚ) else 0) +
          (if c q = 2 then (1 : ℚ) else 0)) := by
    apply Finset.sum_congr rfl
    intro q hq
    have hnon : (commonLink H V q).Nonempty :=
      ((mem_usedCells_iff_commonLink_nonempty H V q).mp hq).2
    exact linkSurplus_pointwise (c q) (Finset.card_pos.mpr hnon)
  have htwice :
      (∑ q ∈ C, if c q = 1 then (2 : ℚ) else 0) =
        2 * (∑ q ∈ C, if c q = 1 then (1 : ℚ) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    split_ifs <;> ring
  have hR :
      (∑ q ∈ C, ((c q : ℚ) - 3 +
        (if c q = 1 then (2 : ℚ) else 0) +
        (if c q = 2 then (1 : ℚ) else 0))) =
      (∑ q ∈ C, (c q : ℚ)) - 3 * (C.card : ℚ) +
        2 * (∑ q ∈ C, if c q = 1 then (1 : ℚ) else 0) +
        (∑ q ∈ C, if c q = 2 then (1 : ℚ) else 0) := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, htwice]
    simp
    ring
  rw [hR, hOne, hTwo] at hpoint
  simpa only [actualLinkSurplus, C, c] using hpoint

/-- The exact support identity (II.1) of `paper/proof.pdf` for the real
    pair and cell supports of a uniform triple family. -/
theorem actual_support_ledger
    (H : Family α) (V : Edge α)
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V) :
    6 * (2 * (H.card : ℚ) - ((usedPairs H V).card : ℚ) -
      ((usedCells H V).card : ℚ)) =
      2 * actualLinkSurplus H V - actualPairBudget H V -
        2 * ((singletonCompletionPairs H V).card : ℚ) -
        4 * ((singletonLinkCells H V).card : ℚ) -
        2 * ((doubleLinkCells H V).card : ℚ) := by
  have hdegree := actual_pair_budget_ledger H V hUniform hground
  have hcell := actual_link_surplus_ledger H V
  linarith

/-- Once the signed payment bounds the actual surplus budget, the support
    inequality follows with no further abstraction. -/
theorem actual_support_bound_of_payment
    (H : Family α) (V : Edge α)
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hpaid : 2 * actualLinkSurplus H V ≤
      actualPairBudget H V +
        2 * ((singletonCompletionPairs H V).card : ℚ) +
        4 * ((singletonLinkCells H V).card : ℚ) +
        2 * ((doubleLinkCells H V).card : ℚ)) :
    2 * H.card ≤ (usedPairs H V).card + (usedCells H V).card := by
  have hledger := actual_support_ledger H V hUniform hground
  have hq : 2 * (H.card : ℚ) ≤
      ((usedPairs H V).card : ℚ) + ((usedCells H V).card : ℚ) := by
    linarith
  exact_mod_cast hq

/-- The exact finite upper bound is reduced to one concrete payment
    inequality on the actual family. -/
theorem triple_family_card_le_choose_two_of_payment
    (H : Family α) (V : Edge α)
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hpaid : 2 * actualLinkSurplus H V ≤
      actualPairBudget H V +
        2 * ((singletonCompletionPairs H V).card : ℚ) +
        4 * ((singletonLinkCells H V).card : ℚ) +
        2 * ((doubleLinkCells H V).card : ℚ)) :
    H.card ≤ V.card.choose 2 := by
  exact triple_family_card_le_choose_two_of_actual_supports H V
    (actual_support_bound_of_payment H V hUniform hground hpaid)

end ExactSupportLedger

end JSP523.Rank3
