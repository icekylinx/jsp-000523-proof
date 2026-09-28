import JSP523.Rank4.NativeVertexSupport

/-!
# Selecting the actual labels of surviving common-root cells

Weak-cell clearing supplies a unique center for every nonempty cell.
This file turns that proposition into a total finite label function and
proves that each used pair's label lies in the ground set outside the pair.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The exact empty-or-unique-center conclusion of rank-four weak-cell
clearing, restricted to pair roots in the ground set. -/
def UniqueCommonRootCenters
    (K : Family α) (U : Edge α) : Prop :=
  ∀ P ∈ U.powersetCard 2,
    (commonRootCell K U P).card = 0 ∨
      ∃! z : α, ∀ ⦃T : Edge α⦄,
        T ∈ commonRootCell K U P → z ∈ T

omit [Fintype α] in
/-- Every used pair has the center certified by the clearing theorem. -/
theorem used_common_root_has_unique_center
    (K : Family α) (U : Edge α)
    (hCenters : UniqueCommonRootCenters K U)
    (P : Edge α) (hP : P ∈ nonemptyCommonRoots K U) :
    ∃! z : α, ∀ ⦃T : Edge α⦄,
      T ∈ commonRootCell K U P → z ∈ T := by
  classical
  have hP' := Finset.mem_filter.mp hP
  rcases hCenters P hP'.1 with hZero | hCenter
  · omega
  · exact hCenter

/-- A total label map, using an arbitrary fallback only on unused pair
roots. -/
noncomputable def chosenCommonRootLabel
    (K : Family α) (U : Edge α) (fallback : α)
    (hCenters : UniqueCommonRootCenters K U)
    (P : Edge α) : α :=
  if hP : P ∈ nonemptyCommonRoots K U then
    Classical.choose
      (used_common_root_has_unique_center K U hCenters P hP)
  else fallback

omit [Fintype α] in
/-- The chosen label belongs to every triple of its used common-root
cell. -/
theorem chosen_common_root_label_center
    (K : Family α) (U : Edge α) (fallback : α)
    (hCenters : UniqueCommonRootCenters K U)
    (P : Edge α) (hP : P ∈ nonemptyCommonRoots K U)
    (T : Edge α) (hT : T ∈ commonRootCell K U P) :
    chosenCommonRootLabel K U fallback hCenters P ∈ T := by
  classical
  unfold chosenCommonRootLabel
  rw [dite_eq_left hP]
  exact
    (Classical.choose_spec
      (used_common_root_has_unique_center K U hCenters P hP)).1 hT

omit [Fintype α] in
/-- A selected center of a used pair is in the ground set and outside
the pair, as required by the native tail-graph support bound. -/
theorem chosen_common_root_label_valid
    (K : Family α) (U : Edge α) (fallback : α)
    (hCenters : UniqueCommonRootCenters K U)
    (P : Edge α) (hP : P ∈ nonemptyCommonRoots K U) :
    chosenCommonRootLabel K U fallback hCenters P ∈ U ∧
      chosenCommonRootLabel K U fallback hCenters P ∉ P := by
  classical
  have hP' := Finset.mem_filter.mp hP
  have hPcard : P.card = 2 :=
    (Finset.mem_powersetCard.mp hP'.1).2
  obtain ⟨T, hT⟩ := Finset.card_pos.mp hP'.2
  have hzT := chosen_common_root_label_center
    K U fallback hCenters P hP T hT
  have hT' : T ∈ commonTripleCell K U
      (pairRootRep P hPcard).1 (pairRootRep P hPcard).2 := by
    simpa only [commonRootCell, dite_eq_left hPcard] using hT
  have hData := mem_commonTripleCell.mp hT'
  have hPairSpec := pairRootRep_spec P hPcard
  have hDisj : Disjoint T P := by
    rw [hPairSpec.2]
    exact hData.2.2.1
  exact ⟨hData.1 hzT, fun hzP =>
    (Finset.disjoint_left.mp hDisj) hzT hzP⟩

/-- The weak-cell center selection automatically pays the total active
vertex count of the actual native graphs. -/
theorem chosen_native_tail_vertex_total_le
    (K : Family α) (U : Edge α) (fallback : α)
    (hCenters : UniqueCommonRootCenters K U) :
    nativeTailVertexTotal K U (nonemptyCommonRoots K U)
      (chosenCommonRootLabel K U fallback hCenters) ≤
      (U.card - 3) * (nonemptyCommonRoots K U).card := by
  classical
  apply native_tail_vertex_total_le
  · intro P hP
    exact (Finset.mem_filter.mp hP).1
  · intro P hP
    exact chosen_common_root_label_valid K U fallback hCenters P hP

end JSP523.Rank4
