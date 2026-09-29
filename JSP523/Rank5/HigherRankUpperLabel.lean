import JSP523.Rank5.HigherRankUpperColor

/-! # Unordered actual completion-pair labels at arbitrary rank -/
namespace JSP523.Rank5.HigherRankUpper
variable {α : Type*} [DecidableEq α] [Nonempty α] (n : ℕ)

omit [Nonempty α] in

theorem upper_pair_color_of_equal_unordered_pair
    (H : Family α) (V : Edge α) (tUpper : ℕ)
    {x y u v : α}
    (hxy : x ≠ y) (huv : u ≠ v)
    (hPair : ({x, y} : Edge α) = {u, v}) :
    upperSingletonPairColor n H V tUpper x y =
      upperSingletonPairColor n H V tUpper u v := by
  have hu : u = x ∨ u = y := by
    have : u ∈ ({x, y} : Edge α) :=
      hPair.symm ▸ Finset.mem_insert_self u ({v} : Edge α)
    simpa using this
  have hv : v = x ∨ v = y := by
    have hv' : v ∈ ({u, v} : Edge α) := by simp
    have : v ∈ ({x, y} : Edge α) := hPair.symm ▸ hv'
    simpa using this
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact False.elim (huv rfl)
  · rfl
  · exact upper_singleton_pair_color_symm n H V tUpper v u
  · exact False.elim (huv rfl)


noncomputable def upperUnorderedPairLabel
    (H : Family α) (V : Edge α) (tUpper : ℕ)
    (Q : Edge α) : α := by
  classical
  if h : ∃ c : α, ∃ x y : α,
      x ≠ y ∧ Q = {x, y} ∧
        upperSingletonPairColor n H V tUpper x y = some c then
    exact Classical.choose h
  else
    exact Classical.choice inferInstance


theorem upper_unordered_pair_label_eq
    (H : Family α) (V : Edge α) (tUpper : ℕ)
    {x y c : α} (hxy : x ≠ y)
    (hColor : upperSingletonPairColor n H V tUpper x y = some c) :
    upperUnorderedPairLabel n H V tUpper {x, y} = c := by
  classical
  have h : ∃ c' : α, ∃ u v : α,
      u ≠ v ∧ ({x, y} : Edge α) = {u, v} ∧
        upperSingletonPairColor n H V tUpper u v = some c' :=
    ⟨c, x, y, hxy, rfl, hColor⟩
  have hSpec := Classical.choose_spec h
  obtain ⟨u, v, huv, hPair, hOther⟩ := hSpec
  have hEqColor := upper_pair_color_of_equal_unordered_pair n
    H V tUpper hxy huv hPair
  have hC : c = Classical.choose h := by
    have hSome : some c = some (Classical.choose h) := by
      rw [← hColor, hEqColor, hOther]
    exact Option.some.inj hSome
  unfold upperUnorderedPairLabel
  rw [dite_eq_left h]
  exact hC.symm

end JSP523.Rank5.HigherRankUpper
