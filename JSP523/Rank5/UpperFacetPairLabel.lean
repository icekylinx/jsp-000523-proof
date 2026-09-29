import JSP523.Rank5.UpperFacetRepairColor

/-! # Unordered parent completion-pair labels -/

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α] [Nonempty α]

omit [Nonempty α] in
/-- Reversing the endpoints is the only possible change of representation
    for an unordered pair of distinct vertices. -/
theorem upper_pair_color_of_equal_unordered_pair
    (H : Family α) (V : Edge α) (tUpper : ℕ)
    {x y u v : α}
    (hxy : x ≠ y) (huv : u ≠ v)
    (hPair : ({x, y} : Edge α) = {u, v}) :
    upperSingletonPairColor H V tUpper x y =
      upperSingletonPairColor H V tUpper u v := by
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
  · exact upper_singleton_pair_color_symm H V tUpper v u
  · exact False.elim (huv rfl)

/-- A total label on unordered pairs extracted from the actual parent
    partial coloring. Its value away from colored two-sets is immaterial. -/
noncomputable def upperUnorderedPairLabel
    (H : Family α) (V : Edge α) (tUpper : ℕ)
    (Q : Edge α) : α := by
  classical
  if h : ∃ c : α, ∃ x y : α,
      x ≠ y ∧ Q = {x, y} ∧
        upperSingletonPairColor H V tUpper x y = some c then
    exact Classical.choose h
  else
    exact Classical.choice inferInstance

/-- On a colored pair the total label is exactly its parent cell color. -/
theorem upper_unordered_pair_label_eq
    (H : Family α) (V : Edge α) (tUpper : ℕ)
    {x y c : α} (hxy : x ≠ y)
    (hColor : upperSingletonPairColor H V tUpper x y = some c) :
    upperUnorderedPairLabel H V tUpper {x, y} = c := by
  classical
  have h : ∃ c' : α, ∃ u v : α,
      u ≠ v ∧ ({x, y} : Edge α) = {u, v} ∧
        upperSingletonPairColor H V tUpper u v = some c' :=
    ⟨c, x, y, hxy, rfl, hColor⟩
  have hSpec := Classical.choose_spec h
  obtain ⟨u, v, huv, hPair, hOther⟩ := hSpec
  have hEqColor := upper_pair_color_of_equal_unordered_pair
    H V tUpper hxy huv hPair
  have hC : c = Classical.choose h := by
    have hSome : some c = some (Classical.choose h) := by
      rw [← hColor, hEqColor, hOther]
    exact Option.some.inj hSome
  unfold upperUnorderedPairLabel
  rw [dite_eq_left h]
  exact hC.symm

/-- The actual IV.8 parent coloring, followed by IV.9 inheritance repair,
    supplies the pair-label premise for the selected rooted prefixes. -/
theorem rooted_pair_label_in_prefix_after_color_repair
    (K H : Family α) (V : Edge α) (tUpper : ℕ)
    (tripleLabel : Edge α → α) (Y : Edge α)
    (hKH : K ⊆ H) (hUniformK : Uniform 5 K)
    (hAmbientK : ∀ E ∈ K, E ⊆ V)
    (hSurvive : Disjoint K (upperFacetColorCleanupEdges H V tUpper)) :
    PairCompletionLabelInPrefix
      ((rootedEdges
        (repairSharedFacetInheritance K
          (upperFacetColorCenter K H V tUpper hKH hUniformK
            hAmbientK hSurvive) tripleLabel)
        tripleLabel).filter
          (fun E => rootedChosenPairPrefix tripleLabel E = Y))
      (upperUnorderedPairLabel H V tUpper) Y := by
  classical
  let center := upperFacetColorCenter K H V tUpper
    hKH hUniformK hAmbientK hSurvive
  let L := repairSharedFacetInheritance K center tripleLabel
  have hUniformL : Uniform 5 L := by
    intro E hE
    exact hUniformK (Finset.mem_filter.mp hE).1
  have hInheritance : SharedFacetCenterInheritance L tripleLabel center :=
    shared_facet_inheritance_of_repair K center tripleLabel (by
      intro A hA
      exact (upper_facet_color_center_spec K H V tUpper
        hKH hUniformK hAmbientK hSurvive hA).1)
  apply rooted_pair_completion_label_in_prefix L tripleLabel center
    (upperUnorderedPairLabel H V tUpper) Y hUniformL hInheritance
  intro A hA x y hxy hx hy
  have hColor := upper_facet_pair_color_after_inheritance_repair
    K H V tUpper tripleLabel hKH hUniformK hAmbientK hSurvive
    hA hxy hx hy
  exact upper_unordered_pair_label_eq H V tUpper hxy hColor

end JSP523.Rank5
