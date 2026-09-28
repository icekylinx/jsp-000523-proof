import JSP523.Counting.PrefixCommonSystem
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Finset.Powerset

set_option linter.unusedSectionVars false

/-!
# Prefix collisions and the forbidden trade

This is the set-theoretic core of the intersecting-prefix step in §IV.B:
two disjoint prefix labels and two disjoint residual triples produce the
four-edge repeated-union configuration.
-/

namespace JSP523.Rank5

section PrefixTrade

variable {α : Type*} [DecidableEq α]

/-- The exact scalar identity converting squared multiplicity into its
    first moment plus twice the number of unordered colliding pairs. -/
theorem multiplicity_sq_eq_self_add_two_choose (n : ℕ) :
    n ^ 2 = n + 2 * n.choose 2 := by
  cases n with
  | zero => norm_num
  | succ n =>
      rw [Nat.choose_two_right]
      simp only [Nat.succ_sub_one]
      have heven : Even ((n + 1) * n) := by
        simpa [Nat.succ_sub_one] using Nat.even_mul_pred_self (n + 1)
      have hdiv := Nat.div_two_mul_two_of_even heven
      have hmul : 2 * ((n + 1) * n / 2) = (n + 1) * n := by
        simpa [Nat.mul_comm] using hdiv
      nlinarith [hmul]

/-- Finite Cauchy--Schwarz in collision-count form.  For multiplicities
    indexed by `U`, the number of equal-index pairs is at least the usual
    quadratic lower bound, expressed without division.  This is the finite
    content of (IV.B.3). -/
theorem finite_multiplicity_collision_lower_bound
    (U : Finset α) (t : α → ℕ) :
    (∑ i ∈ U, t i) ^ 2 ≤
      U.card * ((∑ i ∈ U, t i) + 2 * (∑ i ∈ U, (t i).choose 2)) := by
  have hcs := (_root_.sq_sum_le_card_mul_sum_sq (s := U) (f := t))
  have hidentity :
      (∑ i ∈ U, t i ^ 2) =
        (∑ i ∈ U, t i) + 2 * (∑ i ∈ U, (t i).choose 2) := by
    calc
      (∑ i ∈ U, t i ^ 2) =
          ∑ i ∈ U, (t i + 2 * (t i).choose 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact multiplicity_sq_eq_self_add_two_choose (t i)
      _ = (∑ i ∈ U, t i) + 2 * (∑ i ∈ U, (t i).choose 2) := by
            simp_rw [Finset.sum_add_distrib, Finset.mul_sum]
  rw [hidentity] at hcs
  exact hcs

/-- For a fixed prefix `Y`, intersecting other prefixes are covered by the
    union, over vertices of `Y`, of the other prefixes containing that
    vertex. -/
theorem fixed_prefix_intersections_le
    (F : Family α) {Y : Edge α} (hY : Y ∈ F)
    (p D₄ : ℕ) (hYcard : Y.card = p) (hD₄ : 1 ≤ D₄)
    (hdegree : ∀ v : α, (F.filter (fun Z => v ∈ Z)).card ≤ D₄) :
    ((F.erase Y).filter (fun Z => ¬ Disjoint Y Z)).card ≤
      p * (D₄ - 1) := by
  let cover : Family α := Y.biUnion fun v =>
    ((F.filter fun Z => v ∈ Z).erase Y)
  have hsub : (F.erase Y).filter (fun Z => ¬ Disjoint Y Z) ⊆ cover := by
    intro Z hZ
    have hZE : Z ∈ F.erase Y := (Finset.mem_filter.mp hZ).1
    have hmeet : ¬ Disjoint Y Z := (Finset.mem_filter.mp hZ).2
    rw [Finset.not_disjoint_iff] at hmeet
    obtain ⟨v, hvY, hvZ⟩ := hmeet
    apply Finset.mem_biUnion.mpr
    refine ⟨v, hvY, ?_⟩
    apply Finset.mem_erase.mpr
    refine ⟨Finset.ne_of_mem_erase hZE, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hZE, hvZ⟩
  have hcover : cover.card ≤
      ∑ v ∈ Y, ((F.filter fun Z => v ∈ Z).erase Y).card := by
    exact Finset.card_biUnion_le
  have hterm : ∀ v ∈ Y,
      ((F.filter fun Z => v ∈ Z).erase Y).card ≤ D₄ - 1 := by
    intro v hv
    have hvY : Y ∈ F.filter (fun Z => v ∈ Z) :=
      Finset.mem_filter.mpr ⟨hY, hv⟩
    have herase := Finset.card_erase_add_one hvY
    have hdeg := hdegree v
    omega
  calc
    ((F.erase Y).filter (fun Z => ¬ Disjoint Y Z)).card ≤ cover.card :=
      Finset.card_le_card hsub
    _ ≤ ∑ v ∈ Y, ((F.filter fun Z => v ∈ Z).erase Y).card := hcover
    _ ≤ ∑ _v ∈ Y, (D₄ - 1) := by
      apply Finset.sum_le_sum
      intro v hv
      exact hterm v hv
    _ = p * (D₄ - 1) := by simp [hYcard]

/-- The full finite upper count for ordered intersecting prefix pairs.  Each
    prefix has size `p`, and every vertex belongs to at most `D₄` assigned
    prefixes, so the off-diagonal ordered collision count is at most
    `p (D₄-1) |F|`. -/
theorem ordered_prefix_intersection_count_le
    (F : Family α) (p D₄ : ℕ)
    (hUniform : Uniform p F) (hD₄ : 1 ≤ D₄)
    (hdegree : ∀ v : α, (F.filter (fun Y => v ∈ Y)).card ≤ D₄) :
    (∑ Y ∈ F, ((F.erase Y).filter (fun Z => ¬ Disjoint Y Z)).card) ≤
      p * (D₄ - 1) * F.card := by
  calc
    (∑ Y ∈ F, ((F.erase Y).filter (fun Z => ¬ Disjoint Y Z)).card) ≤
        ∑ Y ∈ F, p * (D₄ - 1) := by
          apply Finset.sum_le_sum
          intro Y hY
          exact fixed_prefix_intersections_le F hY p D₄
            (hUniform hY) hD₄ hdegree
    _ = p * (D₄ - 1) * F.card := by simp [Finset.sum_const, mul_comm]

/-- The natural nonemptiness and disjointness hypotheses suffice to prove
    all six edge inequalities and both edge disjointness conditions.  This
    is the unconditional prefix switch used by the common-system module. -/
theorem prefix_swap_forbidden_of_natural_data
    {Y Z P Q : Edge α}
    (hY : Y.Nonempty) (hZ : Z.Nonempty)
    (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hYZ : Disjoint Y Z)
    (hPY : Disjoint P Y) (hPZ : Disjoint P Z)
    (hQY : Disjoint Q Y) (hQZ : Disjoint Q Z)
    (hPQ : Disjoint P Q) :
    ForbiddenQuad (Y ∪ P) (Z ∪ Q) (Y ∪ Q) (Z ∪ P) :=
  prefix_switch_forbidden hY hZ hP hQ hYZ hPY hPZ hQY hQZ hPQ

/-- The common triple system for two disjoint prefixes intersects in every
    admissible family.  Membership supplies the natural tail avoidance
    hypotheses needed by the prefix switch above. -/
theorem prefix_common_system_intersecting
    {K : Family α} {V Y Z : Edge α}
    (hK : Admissible K)
    (hY : Y.Nonempty) (hZ : Z.Nonempty)
    (hYZ : Disjoint Y Z) :
    PairwiseIntersecting (commonPrefixTriples K V Y Z) :=
  common_prefix_triples_intersecting hK hY hZ hYZ

/-- The common triple system is linear once the parent pair-completion
    labels lie in both prefixes, as established by the center argument. -/
theorem prefix_common_system_linear
    {K : Family α} {V Y Z : Edge α}
    (label : Edge α → α)
    (hYlabel : PairCompletionLabelInPrefix K label Y)
    (hZlabel : PairCompletionLabelInPrefix K label Z)
    (hYZ : Disjoint Y Z) :
    LinearFamily (commonPrefixTriples K V Y Z) :=
  common_prefix_triples_linear label hYlabel hZlabel hYZ

/-- Consequently the common triple system is either a star or has at most
    seven triples.  Only the parent-label guarantees remain geometric input. -/
theorem prefix_common_system_star_or_small
    {K : Family α} {V Y Z : Edge α}
    (hK : Admissible K)
    (hY : Y.Nonempty) (hZ : Z.Nonempty)
    (hYZ : Disjoint Y Z)
    (label : Edge α → α)
    (hYlabel : PairCompletionLabelInPrefix K label Y)
    (hZlabel : PairCompletionLabelInPrefix K label Z) :
    (∃ x : α, ∀ ⦃P : Edge α⦄,
      P ∈ commonPrefixTriples K V Y Z → x ∈ P) ∨
      (commonPrefixTriples K V Y Z).card ≤ 7 :=
  common_prefix_triples_star_or_small hK hY hZ hYZ label hYlabel hZlabel

/-- Two disjoint prefix/residual pairs and their crossed pairs give a
    forbidden trade.  The explicit distinctness hypotheses are discharged
    in applications from the nonempty uniform prefix and residual sizes. -/
theorem prefix_swap_forbidden
    {Y Z P Q : Edge α}
    (hYZ : Disjoint Y Z) (hPQ : Disjoint P Q)
    (hYP : Disjoint Y P) (hYQ : Disjoint Y Q)
    (hZP : Disjoint Z P) (hZQ : Disjoint Z Q)
    (hd : FourDistinct (Y ∪ P) (Z ∪ Q) (Y ∪ Q) (Z ∪ P)) :
    ForbiddenQuad (Y ∪ P) (Z ∪ Q) (Y ∪ Q) (Z ∪ P) := by
  have hdisj₁ : Disjoint (Y ∪ P) (Z ∪ Q) := by
    apply Finset.disjoint_union_left.mpr
    constructor
    · exact Finset.disjoint_union_right.mpr ⟨hYZ, hYQ⟩
    · exact Finset.disjoint_union_right.mpr ⟨hZP.symm, hPQ⟩
  have hdisj₂ : Disjoint (Y ∪ Q) (Z ∪ P) := by
    apply Finset.disjoint_union_left.mpr
    constructor
    · exact Finset.disjoint_union_right.mpr ⟨hYZ, hYP⟩
    · exact Finset.disjoint_union_right.mpr ⟨hZQ.symm, hPQ.symm⟩
  have hunion : (Y ∪ P) ∪ (Z ∪ Q) = (Y ∪ Q) ∪ (Z ∪ P) := by
    ext x
    simp only [Finset.mem_union]
    tauto
  exact ⟨hd, hdisj₁, hdisj₂, hunion⟩

/-- An admissible family cannot contain all four edges from a prefix swap. -/
theorem prefix_swap_excluded
    {F : Family α} {Y Z P Q : Edge α}
    (hF : Admissible F)
    (hYP : Y ∪ P ∈ F) (hZQ : Z ∪ Q ∈ F)
    (hYQ : Y ∪ Q ∈ F) (hZP : Z ∪ P ∈ F)
    (hYZ : Disjoint Y Z) (hPQ : Disjoint P Q)
    (hY_P : Disjoint Y P) (hY_Q : Disjoint Y Q)
    (hZ_P : Disjoint Z P) (hZ_Q : Disjoint Z Q)
    (hd : FourDistinct (Y ∪ P) (Z ∪ Q) (Y ∪ Q) (Z ∪ P)) : False := by
  exact hF hYP hZQ hYQ hZP
    (prefix_swap_forbidden hYZ hPQ hY_P hY_Q hZ_P hZ_Q hd)

end PrefixTrade

end JSP523.Rank5
