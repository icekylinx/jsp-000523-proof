import JSP523.Rank5.InheritanceWitness
import JSP523.Rank5.ColorQuantitativeFixedPalette

/-! # Actual core colors for arbitrary root and core sizes -/

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α]

/-- All distinct roots in an edge support carry the indicated strong label. -/
def FixedPaletteSupportHasLabel (H : Family α) (V : Edge α) (s k t : ℕ)
    (e : Finset (Edge α)) (z : α) : Prop :=
  ∀ P ∈ e, ∀ Q ∈ e, P ≠ Q → ActualStrongPartner H V P Q s k t z

noncomputable def fixedPaletteCoreSupportColor
    (H : Family α) (V B : Edge α) (s k t : ℕ)
    (e : Finset (Edge α)) : Option {z // z ∈ B} := by
  classical
  exact if h : ∃ z : {z // z ∈ B}, FixedPaletteSupportHasLabel H V s k t e z.1 then
    some (Classical.choose h) else none

/-- On actual two-element supports the strong label determines the color
    uniquely, with no choice of ordering of the roots. -/
theorem fixed_palette_core_support_color_eq_some_iff
    (H : Family α) (V B : Edge α) (s k t : ℕ)
    {e : Finset (Edge α)} (he : e.card = 2) {z : {z // z ∈ B}} :
    fixedPaletteCoreSupportColor H V B s k t e = some z ↔ FixedPaletteSupportHasLabel H V s k t e z.1 := by
  classical
  by_cases h : ∃ w : {z // z ∈ B}, FixedPaletteSupportHasLabel H V s k t e w.1
  · have hChosen := Classical.choose_spec h
    have hUnique : ∀ w : {z // z ∈ B}, FixedPaletteSupportHasLabel H V s k t e w.1 →
        Classical.choose h = w := by
      intro w hw
      obtain ⟨P,Q,hPQ,hPair⟩ := Finset.card_eq_two.mp he
      have hP : P ∈ e := by rw [hPair]; simp
      have hQ : Q ∈ e := by rw [hPair]; simp
      apply Subtype.ext
      exact actual_strong_partner_center_unique H V P Q s k t
        (hChosen P hP Q hQ hPQ) (hw P hP Q hQ hPQ)
    simp only [fixedPaletteCoreSupportColor, dite_eq_left h, Option.some.injEq]
    exact ⟨fun hz => hz ▸ hChosen, fun hz => hUnique z hz⟩
  · simp only [fixedPaletteCoreSupportColor, dite_eq_right h, reduceCtorEq, false_iff]
    exact fun hz => h ⟨z,hz⟩

/-- Every strong pair in an actual core link has its label in the
    core, since that core belongs to the pair's common cell. -/
theorem fixed_palette_strong_label_mem_actual_core
    (H : Family α) (V B P Q : Edge α) (s k t : ℕ)
    (hBV : B ⊆ V) (hBc : B.card = k)
    (hP : P ∈ actualCoreLink H V B s) (hQ : Q ∈ actualCoreLink H V B s)
    {z : α} (hz : ActualStrongPartner H V P Q s k t z) : z ∈ B := by
  have hp := mem_actual_core_link.mp hP
  have hq := mem_actual_core_link.mp hQ
  have hCell : B ∈ commonPrefixTails H V P Q k :=
    mem_common_prefix_tails.mpr ⟨hBV,hBc,
      Finset.disjoint_union_right.mpr ⟨hp.2.2.1.symm,hq.2.2.1.symm⟩,
      by simpa only [Finset.union_comm] using hp.2.2.2,
      by simpa only [Finset.union_comm] using hq.2.2.2⟩
  exact hz.2.2.2.1 B hCell

/-- The unordered pair support tests exactly the actual strong-partner
    predicate used by the multilevel edge deletion. -/
theorem fixed_palette_support_pair_has_label_iff
    (H : Family α) (V P Q : Edge α) (s k t : ℕ)
    (hP : P ∈ V.powersetCard s) (hPQ : P ≠ Q) {z : α} :
    FixedPaletteSupportHasLabel H V s k t {P,Q} z ↔ ActualStrongPartner H V P Q s k t z := by
  constructor
  · intro h
    exact h P (by simp) Q (by simp) hPQ
  · intro h R hR S hS hRS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hR hS
    rcases hR with hRP | hRQ <;> rcases hS with hSP | hSQ
    all_goals subst R; subst S
    · exact False.elim (hRS rfl)
    · exact h
    · have hCell := common_prefix_tails_comm H V P Q k
      refine ⟨hP, h.2.1.symm, ?_, ?_⟩
      · rw [← hCell]; exact h.2.2.1
      · rw [← hCell]; exact h.2.2.2
    · exact False.elim (hRS rfl)

noncomputable def fixedPaletteExceptionalSupports
    (H : Family α) (V B : Edge α) (s k t : ℕ) (z : α) : Finset (Finset (Edge α)) := by
  classical
  exact ((actualCoreLink H V B s).powersetCard 2).filter
    (fun e => ¬ FixedPaletteSupportHasLabel H V s k t e z)

def fixedPaletteSampleSize (k : ℕ) : ℕ := max 4 ((k - 1) ^ 2 + 1)

/-- Quantitative majority selection on the actual parent link of a core. -/
theorem exists_fixed_palette_core_majority_label
    (H : Family α) (V B : Edge α) (s k t : ℕ)
    (hk : 2 ≤ k) (hBc : B.card = k)
    (hDegree : 2 * fixedPaletteSampleSize k ≤ (actualCoreLink H V B s).card) :
    ∃ z ∈ B,
      (fixedPaletteExceptionalSupports H V B s k t z).card ≤
      (fixedPaletteMajorityConstant (fixedPaletteSampleSize k) : ℝ) *
        ((uncoloredEdgeSupports (actualCoreLink H V B s)
          (fixedPaletteCoreSupportColor H V B s k t)).card +
        (bicoloredTriangleSupports (actualCoreLink H V B s)
          (fixedPaletteCoreSupportColor H V B s k t)).card /
            ((actualCoreLink H V B s).card : ℝ)) := by
  classical
  let : Nonempty {z // z ∈ B} := by
    obtain ⟨z,hz⟩ := Finset.card_pos.mp (by omega : 0 < B.card)
    exact ⟨⟨z,hz⟩⟩
  have hCard : Fintype.card {z // z ∈ B} = k := by simpa using hBc
  obtain ⟨z,hz⟩ := exists_fixed_palette_majority_exception_bound
    (actualCoreLink H V B s) (fixedPaletteCoreSupportColor H V B s k t)
    (fixedPaletteSampleSize k) (by omega) (by simp only [hCard, fixedPaletteSampleSize, le_refl]) hDegree
  refine ⟨z.1,z.2,?_⟩
  have hEq : ((actualCoreLink H V B s).powersetCard 2).filter
      (fun e => fixedPaletteCoreSupportColor H V B s k t e ≠ some z) =
      ((actualCoreLink H V B s).powersetCard 2).filter
        (fun e => ¬ FixedPaletteSupportHasLabel H V s k t e z.1) := by
    ext e
    by_cases he : e ∈ (actualCoreLink H V B s).powersetCard 2
    · simp only [Finset.mem_filter, he, true_and]
      exact not_congr (fixed_palette_core_support_color_eq_some_iff H V B s k t
        (Finset.mem_powersetCard.mp he).2)
    · simp only [Finset.mem_filter, he, false_and]
  rw [hEq] at hz
  exact hz

end JSP523.Rank5
