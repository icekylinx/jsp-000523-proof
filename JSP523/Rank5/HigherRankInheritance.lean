import JSP523.Rank5.OccurringCenterTower
import JSP523.Counting.PrefixAssignment

/-!
# Assigned prefixes from inherited higher-rank centers

The occurrence-local center tower supplies a chosen on every retained edge.
This module connects its pointwise center law to the exact chosen-chosen
fiber condition in the finite chosen collision bound.
-/

namespace JSP523.Rank5

section HigherRankInheritance

variable {α : Type*} [DecidableEq α]

/-- A center law on each chosen edge restricts to each actual assigned
    chosen fiber, with no condition on unrelated edges through the chosen. -/
theorem assigned_prefix_center_of_edge_prefix_law
    {K : Family α} {V : Edge α} {p : ℕ}
    (z : Edge α → α) (chosen : Edge α → Edge α)
    (hCenter : ∀ E ∈ K, ∀ x ∈ E \ chosen E,
      z (chosen E ∪ {x}) ∈ chosen E)
    {P Y : Edge α}
    (hY : Y ∈ JSP523.Counting.chosenPrefixesAt K V p chosen P)
    {x : α} (hx : x ∈ P) : z (Y ∪ {x}) ∈ Y := by
  obtain ⟨_, hDisj, hEK, hChosen⟩ :=
    JSP523.Counting.mem_chosen_prefixes_at.mp hY
  have hxNotY : x ∉ Y := (Finset.disjoint_left.mp hDisj.symm) hx
  have hxDiff : x ∈ (Y ∪ P) \ chosen (Y ∪ P) := by
    rw [hChosen]
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right Y hx, hxNotY⟩
  have h := hCenter (Y ∪ P) hEK x hxDiff
  simpa only [hChosen] using h

/-- All selected-chosen center premises of the finite collision theorem
    follow from local inheritance on the actual retained `(r-2)`-faces. -/
theorem higher_rank_assigned_prefix_center_exists
    {r : ℕ} (hr : 6 ≤ r) {K : Family α} {V : Edge α}
    (hUniform : Uniform r K) {z : Edge α → α}
    (hBase : FamilyRankCenterInheritance K (r - 2) z) :
    ∃ chosen : Edge α → Edge α,
      (∀ E ∈ K, chosen E ⊆ E) ∧
      (∀ E ∈ K, (chosen E).card = r - 3) ∧
      (∀ P : Edge α,
        ∀ Y ∈ JSP523.Counting.chosenPrefixesAt K V (r - 3) chosen P,
        ∀ x ∈ P, z (Y ∪ {x}) ∈ Y) := by
  obtain ⟨chosen, hPrefix⟩ :=
    exists_occurring_rooted_prefix_assignment hr hUniform hBase
  refine ⟨chosen, ?_, ?_, ?_⟩
  · intro E hE
    exact (hPrefix E hE).1
  · intro E hE
    exact (hPrefix E hE).2.1
  · intro P Y hY x hx
    exact assigned_prefix_center_of_edge_prefix_law z chosen
      (fun E hE x hx => (hPrefix E hE).2.2 x hx) hY hx

end HigherRankInheritance

end JSP523.Rank5
