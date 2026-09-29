import JSP523.Rank5.UpperFacetPairLabel

/-!
# Actual lower-core labels for the rank-five prefix count

The unique center of a strong parent common-triple cell defines a label
depending only on its two roots.  This supplies the label-validity input
of the geometric assigned-prefix bound.
-/

namespace JSP523.Rank5

open JSP523.Counting

variable {α : Type*} [DecidableEq α] [Nonempty α]

noncomputable def lowerStrongPairLabel
    (H : Family α) (V : Edge α) (t : ℕ)
    (P Q : Edge α) : α := by
  classical
  if h : ∃ z : α, ActualStrongPartner H V P Q 2 3 t z then
    exact Classical.choose h
  else
    exact Classical.choice inferInstance

theorem lower_strong_pair_label_eq
    (H : Family α) (V P Q : Edge α) (t : ℕ)
    {z : α}
    (hStrong : ActualStrongPartner H V P Q 2 3 t z) :
    lowerStrongPairLabel H V t P Q = z := by
  classical
  have h : ∃ z' : α, ActualStrongPartner H V P Q 2 3 t z' :=
    ⟨z, hStrong⟩
  have hEq := actual_strong_partner_center_unique H V P Q 2 3 t
    (Classical.choose_spec h) hStrong
  unfold lowerStrongPairLabel
  rw [dite_eq_left h]
  exact hEq

/-- A parent triple core common to a strong pair is one of the pair's
    actual common-cell members, so it contains the unique strong label. -/
theorem lower_strong_label_in_parent_core
    (H : Family α) (V A P Q : Edge α) (t : ℕ)
    (hUniform : Uniform 5 H)
    (hAmbient : ∀ E ∈ H, E ⊆ V)
    (hStrong : ActualStrongPartner H V P Q 2 3 t
      (lowerStrongPairLabel H V t P Q))
    (hP : P ∈ parentPairLink H V A)
    (hQ : Q ∈ parentPairLink H V A) :
    lowerStrongPairLabel H V t P Q ∈ A := by
  have hp := mem_parent_pair_link.mp hP
  have hq := mem_parent_pair_link.mp hQ
  have hAV : A ⊆ V :=
    (Finset.subset_union_left).trans
      (hAmbient (A ∪ P) hp.2.2.2)
  have hAcard : A.card = 3 := by
    have hFive := hUniform hp.2.2.2
    have hDisj : Disjoint A P := hp.2.2.1.symm
    have hCard := Finset.card_union_of_disjoint hDisj
    rw [hCard, hp.2.1] at hFive
    omega
  have hDisj : Disjoint A (P ∪ Q) :=
    Finset.disjoint_union_right.mpr
      ⟨hp.2.2.1.symm, hq.2.2.1.symm⟩
  have hPA : P ∪ A ∈ H := by
    rw [Finset.union_comm]
    exact hp.2.2.2
  have hQA : Q ∪ A ∈ H := by
    rw [Finset.union_comm]
    exact hq.2.2.2
  have hCell : A ∈ commonPrefixTails H V P Q 3 :=
    mem_common_prefix_tails.mpr
      ⟨hAV, hAcard, hDisj, hPA, hQA⟩
  exact hStrong.2.2.2.1 A hCell

/-- The strong-pair predicate with center `tripleLabel A` has both label
    interfaces required by the rank-five assigned-prefix theorem. -/
theorem lower_strong_pair_label_interfaces
    (H : Family α) (V : Edge α) (t : ℕ)
    (tripleLabel : Edge α → α)
    (hUniform : Uniform 5 H)
    (hAmbient : ∀ E ∈ H, E ⊆ V) :
    (∀ A P Q : Edge α,
      ActualStrongPartner H V P Q 2 3 t (tripleLabel A) →
        lowerStrongPairLabel H V t P Q = tripleLabel A) ∧
    GoodPairLabelValid H V
      (fun A P Q => ActualStrongPartner H V P Q 2 3 t (tripleLabel A))
      (lowerStrongPairLabel H V t) := by
  constructor
  · intro A P Q hStrong
    exact lower_strong_pair_label_eq H V P Q t hStrong
  · intro A A' P Q hStrong hP hQ
    have hEq := lower_strong_pair_label_eq H V P Q t hStrong
    exact lower_strong_label_in_parent_core H V A' P Q t
      hUniform hAmbient (hEq ▸ hStrong) hP hQ

end JSP523.Rank5
