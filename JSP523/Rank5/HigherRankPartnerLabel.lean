import JSP523.Rank5.HigherRankCleanup
import JSP523.Rank5.RepeatedCenterDegree

/-!
# Parent strong-pair labels at arbitrary rank

The unique center of an actual parent common cell defines a label of its
two roots. This label belongs to every parent core supporting those roots.
-/

namespace JSP523.Rank5

open JSP523.Counting

variable {α : Type*} [DecidableEq α] [Nonempty α]

noncomputable def higherStrongPairLabel
    (H : Family α) (V : Edge α) (r t : ℕ)
    (P Q : Edge α) : α := by
  classical
  if h : ∃ z : α, ActualStrongPartner H V P Q 2 (r - 2) t z then
    exact Classical.choose h
  else
    exact Classical.choice inferInstance

theorem higher_strong_pair_label_eq
    (H : Family α) (V P Q : Edge α) (r t : ℕ)
    {z : α}
    (hStrong : ActualStrongPartner H V P Q 2 (r - 2) t z) :
    higherStrongPairLabel H V r t P Q = z := by
  classical
  have h : ∃ z' : α, ActualStrongPartner H V P Q 2 (r - 2) t z' :=
    ⟨z, hStrong⟩
  have hEq := ((Classical.choose_spec h).2.2.2.2 z hStrong.2.2.2.1).symm
  unfold higherStrongPairLabel
  rw [dite_eq_left h]
  exact hEq

/-- Every parent `(r-2)`-core supporting a strong root pair contains the
    pair's unique label. -/
theorem higher_strong_label_in_parent_core
    (H : Family α) (V A P Q : Edge α) (r t : ℕ)
    (hUniform : Uniform r H)
    (hAmbient : ∀ E ∈ H, E ⊆ V)
    (hStrong : ActualStrongPartner H V P Q 2 (r - 2) t
      (higherStrongPairLabel H V r t P Q))
    (hP : P ∈ parentPairLink H V A)
    (hQ : Q ∈ parentPairLink H V A) :
    higherStrongPairLabel H V r t P Q ∈ A := by
  have hp := mem_parent_pair_link.mp hP
  have hq := mem_parent_pair_link.mp hQ
  have hAV : A ⊆ V :=
    (Finset.subset_union_left).trans
      (hAmbient (A ∪ P) hp.2.2.2)
  have hAcard : A.card = r - 2 := by
    have hSize := hUniform hp.2.2.2
    have hDisj : Disjoint A P := hp.2.2.1.symm
    have hCard := Finset.card_union_of_disjoint hDisj
    rw [hCard, hp.2.1] at hSize
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
  have hCell : A ∈ commonPrefixTails H V P Q (r - 2) :=
    mem_common_prefix_tails.mpr
      ⟨hAV, hAcard, hDisj, hPA, hQA⟩
  exact hStrong.2.2.2.1 A hCell

/-- The actual parent strong-pair relation supplies both label interfaces
    of the finite assigned-prefix common-system theorem at rank `r`. -/
theorem higher_strong_pair_label_interfaces
    (H : Family α) (V : Edge α) (r t : ℕ)
    (center : Edge α → α)
    (hUniform : Uniform r H)
    (hAmbient : ∀ E ∈ H, E ⊆ V) :
    (∀ A P Q : Edge α,
      ActualStrongPartner H V P Q 2 (r - 2) t (center A) →
        higherStrongPairLabel H V r t P Q = center A) ∧
    GoodPairLabelValid H V
      (fun A P Q => ActualStrongPartner H V P Q 2 (r - 2) t (center A))
      (higherStrongPairLabel H V r t) := by
  constructor
  · intro A P Q hStrong
    exact higher_strong_pair_label_eq H V P Q r t hStrong
  · intro A A' P Q hStrong hP hQ
    have hEq := higher_strong_pair_label_eq H V P Q r t hStrong
    exact higher_strong_label_in_parent_core H V A' P Q r t
      hUniform hAmbient (hEq ▸ hStrong) hP hQ

end JSP523.Rank5
