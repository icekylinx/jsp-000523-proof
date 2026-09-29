import JSP523.Rank5.LowerUncoloredBudget
import JSP523.Rank5.ColorQuantitativeRankThree

/-! # Actual three-color lower-core majority labels

The palette consists of the three vertices of the parent core. A support
has a color exactly when its two roots are strong partners with that
center. Quantitative rigidity then selects a genuine core vertex.
-/

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α]

/-- All distinct roots in an edge support carry the indicated strong label. -/
def LowerSupportHasLabel (H : Family α) (V : Edge α) (t : ℕ)
    (e : Finset (Edge α)) (z : α) : Prop :=
  ∀ P ∈ e, ∀ Q ∈ e, P ≠ Q → ActualStrongPartner H V P Q 2 3 t z

noncomputable def lowerCoreSupportColor
    (H : Family α) (V B : Edge α) (t : ℕ)
    (e : Finset (Edge α)) : Option {z // z ∈ B} := by
  classical
  exact if h : ∃ z : {z // z ∈ B}, LowerSupportHasLabel H V t e z.1 then
    some (Classical.choose h) else none

/-- On actual two-element supports the strong label determines the color
    uniquely, with no choice of ordering of the roots. -/
theorem lower_core_support_color_eq_some_iff
    (H : Family α) (V B : Edge α) (t : ℕ)
    {e : Finset (Edge α)} (he : e.card = 2) {z : {z // z ∈ B}} :
    lowerCoreSupportColor H V B t e = some z ↔ LowerSupportHasLabel H V t e z.1 := by
  classical
  by_cases h : ∃ w : {z // z ∈ B}, LowerSupportHasLabel H V t e w.1
  · have hChosen := Classical.choose_spec h
    have hUnique : ∀ w : {z // z ∈ B}, LowerSupportHasLabel H V t e w.1 →
        Classical.choose h = w := by
      intro w hw
      obtain ⟨P,Q,hPQ,hPair⟩ := Finset.card_eq_two.mp he
      have hP : P ∈ e := by rw [hPair]; simp
      have hQ : Q ∈ e := by rw [hPair]; simp
      apply Subtype.ext
      exact actual_strong_partner_center_unique H V P Q 2 3 t
        (hChosen P hP Q hQ hPQ) (hw P hP Q hQ hPQ)
    simp only [lowerCoreSupportColor, dite_eq_left h, Option.some.injEq]
    exact ⟨fun hz => hz ▸ hChosen, fun hz => hUnique z hz⟩
  · simp only [lowerCoreSupportColor, dite_eq_right h, reduceCtorEq, false_iff]
    exact fun hz => h ⟨z,hz⟩

/-- Every strong pair in an actual triple-core link has its label in the
    core, since that core belongs to the pair's common cell. -/
theorem lower_strong_label_mem_actual_core
    (H : Family α) (V B P Q : Edge α) (t : ℕ)
    (hBV : B ⊆ V) (hBc : B.card = 3)
    (hP : P ∈ actualCoreLink H V B 2) (hQ : Q ∈ actualCoreLink H V B 2)
    {z : α} (hz : ActualStrongPartner H V P Q 2 3 t z) : z ∈ B := by
  have hp := mem_actual_core_link.mp hP
  have hq := mem_actual_core_link.mp hQ
  have hCell : B ∈ commonPrefixTails H V P Q 3 :=
    mem_common_prefix_tails.mpr ⟨hBV,hBc,
      Finset.disjoint_union_right.mpr ⟨hp.2.2.1.symm,hq.2.2.1.symm⟩,
      by simpa only [Finset.union_comm] using hp.2.2.2,
      by simpa only [Finset.union_comm] using hq.2.2.2⟩
  exact hz.2.2.2.1 B hCell

/-- The unordered pair support tests exactly the actual strong-partner
    predicate used by the multilevel edge deletion. -/
theorem lower_support_pair_has_label_iff
    (H : Family α) (V P Q : Edge α) (t : ℕ)
    (hP : P ∈ V.powersetCard 2) (hPQ : P ≠ Q) {z : α} :
    LowerSupportHasLabel H V t {P,Q} z ↔ ActualStrongPartner H V P Q 2 3 t z := by
  constructor
  · intro h
    exact h P (by simp) Q (by simp) hPQ
  · intro h R hR S hS hRS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hR hS
    rcases hR with hRP | hRQ <;> rcases hS with hSP | hSQ
    all_goals subst R; subst S
    · exact False.elim (hRS rfl)
    · exact h
    · exact actual_strong_partner_symm H V P Q 3 t z hP h
    · exact False.elim (hRS rfl)

noncomputable def lowerExceptionalSupports
    (H : Family α) (V B : Edge α) (t : ℕ) (z : α) : Finset (Finset (Edge α)) := by
  classical
  exact ((actualCoreLink H V B 2).powersetCard 2).filter
    (fun e => ¬ LowerSupportHasLabel H V t e z)

/-- An actual triple core of degree at least eight has a chosen vertex
    whose exceptional unordered root pairs satisfy the quantitative
    coloring bound. All terms refer to its parent link. -/
theorem exists_lower_core_majority_label
    (H : Family α) (V B : Edge α) (t : ℕ)
    (hBc : B.card = 3) (hDegree : 8 ≤ (actualCoreLink H V B 2).card) :
    ∃ z ∈ B,
      (lowerExceptionalSupports H V B t z).card ≤
      (800 : ℝ) *
        ((uncoloredEdgeSupports (actualCoreLink H V B 2)
          (lowerCoreSupportColor H V B t)).card +
        (bicoloredTriangleSupports (actualCoreLink H V B 2)
          (lowerCoreSupportColor H V B t)).card /
            ((actualCoreLink H V B 2).card : ℝ)) := by
  classical
  let : Nonempty {z // z ∈ B} := by
    obtain ⟨z,hz⟩ := Finset.card_pos.mp (by omega : 0 < B.card)
    exact ⟨⟨z,hz⟩⟩
  have hCard : Fintype.card {z // z ∈ B} = 3 := by simpa using hBc
  obtain ⟨z,hz⟩ := exists_three_color_majority_exception_bound
    (actualCoreLink H V B 2) (lowerCoreSupportColor H V B t) hCard hDegree
  refine ⟨z.1,z.2,?_⟩
  have hEq : ((actualCoreLink H V B 2).powersetCard 2).filter
      (fun e => lowerCoreSupportColor H V B t e ≠ some z) =
      ((actualCoreLink H V B 2).powersetCard 2).filter
        (fun e => ¬ LowerSupportHasLabel H V t e z.1) := by
    ext e
    by_cases he : e ∈ (actualCoreLink H V B 2).powersetCard 2
    · simp only [Finset.mem_filter, he, true_and]
      exact not_congr (lower_core_support_color_eq_some_iff H V B t
        (Finset.mem_powersetCard.mp he).2)
    · simp only [Finset.mem_filter, he, false_and]
  rw [hEq] at hz
  exact hz

end JSP523.Rank5
