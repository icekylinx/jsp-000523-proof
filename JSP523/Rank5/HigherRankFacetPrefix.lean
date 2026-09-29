import JSP523.Rank5.HigherRankInheritance

/-! # Facet centers in assigned higher-rank prefixes -/
namespace JSP523.Rank5
open JSP523.Counting
variable {α : Type*} [DecidableEq α]

/-- An inherited facet center cannot lie outside the selected prefix:
    adjoining that center would violate the prefix's base-rank center law. -/
theorem higher_rank_facet_center_in_prefix
    {K : Family α} {r : ℕ} (hr : 3 ≤ r)
    (z facet : Edge α → α)
    (hFacet : FamilyRankCenterInheritance K (r - 1) facet)
    (hPreserve : ∀ B : Edge α, B.card = r - 2 → facet B = z B)
    {E A Y : Edge α} (hE : E ∈ K)
    (hAE : A ⊆ E) (hAcard : A.card = r - 1)
    (hYA : Y ⊆ A) (hYcard : Y.card = r - 3)
    (hPrefix : ∀ x ∈ E \ Y, z (Y ∪ {x}) ∈ Y) : facet A ∈ Y := by
  classical
  by_contra hwY
  have hOcc : ∃ E ∈ K, A ⊆ E := ⟨E, hE, hAE⟩
  have hwA := (hFacet A hOcc hAcard).1
  have hBA : Y ∪ {facet A} ⊆ A :=
    Finset.union_subset hYA (Finset.singleton_subset_iff.mpr hwA)
  have hBcard : (Y ∪ {facet A}).card = r - 2 := by
    rw [Finset.union_singleton, Finset.card_insert_of_notMem hwY, hYcard]
    omega
  have hEq := family_rank_center_eq_on_subset hFacet hOcc hAcard hBA
    (by omega) (Finset.mem_union_right Y (Finset.mem_singleton_self (facet A)))
  rw [hPreserve _ hBcard] at hEq
  have hCenter := hPrefix (facet A) (Finset.mem_sdiff.mpr ⟨hAE hwA, hwY⟩)
  rw [hEq] at hCenter
  exact hwY hCenter

/-- Agreement of actual completion-pair labels with inherited facet
    centers gives the pair-label condition on each assigned prefix fiber. -/
theorem higher_rank_pair_completion_label_in_prefix
    (K : Family α) (r : ℕ) (chosen : Edge α → Edge α)
    (z facet pairLabel : Edge α → α) (Y : Edge α)
    (hr : 3 ≤ r) (hUniform : Uniform r K)
    (hCard : ∀ E ∈ K, (chosen E).card = r - 3)
    (hPrefix : ∀ E ∈ K, ∀ x ∈ E \ chosen E,
      z (chosen E ∪ {x}) ∈ chosen E)
    (hFacet : FamilyRankCenterInheritance K (r - 1) facet)
    (hPreserve : ∀ B : Edge α, B.card = r - 2 → facet B = z B)
    (hPairCenter : ∀ A : Edge α, A.card = r - 1 → ∀ x y : α,
      x ≠ y → insert x A ∈ K → insert y A ∈ K →
        pairLabel {x, y} = facet A) :
    PairCompletionLabelInPrefix
      (K.filter (fun E => chosen E = Y)) pairLabel Y := by
  intro S x y hSc hxy hEx hEy
  have hxK := (Finset.mem_filter.mp hEx).1
  have hyK := (Finset.mem_filter.mp hEy).1
  have hChosen := (Finset.mem_filter.mp hEx).2
  have hYcard : Y.card = r - 3 := by
    rw [← hChosen]
    exact hCard _ hxK
  have hExEq : Y ∪ (S ∪ {x}) = insert x (Y ∪ S) := by
    ext v
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hEyEq : Y ∪ (S ∪ {y}) = insert y (Y ∪ S) := by
    ext v
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hUpper : (Y ∪ S).card ≤ r - 1 := by
    have h := Finset.card_union_le Y S
    omega
  have hExCard := hUniform hxK
  have hxA : x ∉ Y ∪ S := by
    intro hx
    rw [hExEq, Finset.insert_eq_of_mem hx] at hExCard
    omega
  have hAcard : (Y ∪ S).card = r - 1 := by
    rw [hExEq, Finset.card_insert_of_notMem hxA] at hExCard
    omega
  have hFac := higher_rank_facet_center_in_prefix hr z facet hFacet hPreserve
    hxK (show Y ∪ S ⊆ Y ∪ (S ∪ {x}) by
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact Finset.mem_union_left _ hv
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ hv))
    hAcard Finset.subset_union_left hYcard
    (by simpa only [hChosen] using hPrefix _ hxK)
  rw [hPairCenter (Y ∪ S) hAcard x y hxy (hExEq ▸ hxK) (hEyEq ▸ hyK)]
  exact hFac

end JSP523.Rank5
