import JSP523.Rank4.GlobalMasterBudget

/-!
# The actual facet-degree tail

The facet-degree sum counts each four-edge four times. A subfamily with
bounded facet degrees therefore controls the total mass of high-degree
facets of its parent, as used in (III.B.16).
-/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- Edges of a four-family containing the specified triple facet. -/
def rankFourFacetParents (K : Family α) (T : Edge α) : Family α :=
  K.filter fun E => T ⊆ E

/-- For a triple facet, its completion vertices and its parent edges
are in bijection. -/
theorem facet_completions_card_eq_parent_edges
    (K : Family α) (U T : Edge α)
    (hUniform : Uniform 4 K)
    (hGround : ∀ E ∈ K, E ⊆ U)
    (hTcard : T.card = 3) :
    (facetCompletions K U T).card =
      (rankFourFacetParents K T).card := by
  classical
  let C := facetCompletions K U T
  let P := rankFourFacetParents K T
  let f : α → Edge α := fun x => insert x T
  have hOut (x : α) (hx : x ∈ C) : x ∉ T := by
    intro hxT
    have hFour : (insert x T).card = 4 :=
      hUniform (Finset.mem_filter.mp hx).2
    simp [Finset.insert_eq_of_mem hxT, hTcard] at hFour
  have hImage : C.image f = P := by
    ext E
    constructor
    · intro hE
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hE
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hx).2, Finset.subset_insert x T⟩
    · intro hE
      have hEK : E ∈ K := (Finset.mem_filter.mp hE).1
      have hTE : T ⊆ E := (Finset.mem_filter.mp hE).2
      have hEcard : E.card = 4 := hUniform hEK
      have hDiff : (E \ T).card = 1 := by
        rw [Finset.card_sdiff_of_subset hTE]
        omega
      obtain ⟨x, hxDiff⟩ := Finset.card_eq_one.mp hDiff
      have hxE : x ∈ E := by
        have hx : x ∈ E \ T := by simp [hxDiff]
        exact (Finset.mem_sdiff.mp hx).1
      have hxU : x ∈ U := hGround E hEK hxE
      have hEeq : E = insert x T := by
        have hUnion := Finset.union_sdiff_of_subset hTE
        rw [hxDiff] at hUnion
        simpa [Finset.union_singleton] using hUnion.symm
      exact Finset.mem_image.mpr
        ⟨x, Finset.mem_filter.mpr ⟨hxU, hEeq ▸ hEK⟩,
          hEeq.symm⟩
  have hInj : Set.InjOn f (↑C : Set α) := by
    intro x hx y hy hEq
    have hxIn : x ∈ insert y T := by
      change insert x T = insert y T at hEq
      rw [← hEq]
      simp
    rcases Finset.mem_insert.mp hxIn with hxy | hxT
    · exact hxy
    · exact False.elim (hOut x hx hxT)
  change C.card = P.card
  rw [← hImage]
  exact (Finset.card_image_of_injOn hInj).symm

/-- Counting each actual four-edge through each of its four triple
facets gives an exact finite incidence identity. -/
theorem rank_four_facet_parent_incidence_count
    (K : Family α) (U : Edge α)
    (hUniform : Uniform 4 K)
    (hGround : ∀ E ∈ K, E ⊆ U) :
    (∑ T ∈ U.powersetCard 3,
      (rankFourFacetParents K T).card) = 4 * K.card := by
  classical
  calc
    (∑ T ∈ U.powersetCard 3,
      (rankFourFacetParents K T).card) =
        ∑ T ∈ U.powersetCard 3, ∑ E ∈ K,
          if T ⊆ E then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro T _
      exact Finset.card_filter (fun E : Edge α => T ⊆ E) K
    _ = ∑ E ∈ K, ∑ T ∈ U.powersetCard 3,
          if T ⊆ E then (1 : ℕ) else 0 := Finset.sum_comm
    _ = ∑ E ∈ K, (E.powersetCard 3).card := by
      apply Finset.sum_congr rfl
      intro E hE
      have hEq : (U.powersetCard 3).filter (fun T => T ⊆ E) =
          E.powersetCard 3 := by
        ext T
        constructor
        · intro hT
          have hParts := Finset.mem_filter.mp hT
          exact Finset.mem_powersetCard.mpr
            ⟨hParts.2, (Finset.mem_powersetCard.mp hParts.1).2⟩
        · intro hT
          have hParts := Finset.mem_powersetCard.mp hT
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_powersetCard.mpr
              ⟨hParts.1.trans (hGround E hE), hParts.2⟩,
              hParts.1⟩
      calc
        _ = ((U.powersetCard 3).filter (fun T => T ⊆ E)).card :=
          (Finset.card_filter (fun T : Edge α => T ⊆ E)
            (U.powersetCard 3)).symm
        _ = (E.powersetCard 3).card := congrArg Finset.card hEq
    _ = ∑ _E ∈ K, (4 : ℕ) := by
      apply Finset.sum_congr rfl
      intro E hE
      rw [Finset.card_powersetCard, hUniform hE]
      decide
    _ = 4 * K.card := by simp [mul_comm]

/-- The degree-sum form of the same identity. -/
theorem rank_four_facet_completion_degree_sum
    (K : Family α) (U : Edge α)
    (hUniform : Uniform 4 K)
    (hGround : ∀ E ∈ K, E ⊆ U) :
    (∑ T ∈ U.powersetCard 3,
      (facetCompletions K U T).card) = 4 * K.card := by
  calc
    _ = ∑ T ∈ U.powersetCard 3,
        (rankFourFacetParents K T).card := by
      apply Finset.sum_congr rfl
      intro T hT
      exact facet_completions_card_eq_parent_edges
        K U T hUniform hGround
        (Finset.mem_powersetCard.mp hT).2
    _ = 4 * K.card :=
      rank_four_facet_parent_incidence_count K U hUniform hGround

/-- The total loss of facet degree when passing from a four-family to a
subfamily is four times the number of deleted edges. -/
theorem rank_four_facet_degree_loss_eq_four_deletions
    (B K : Family α) (U : Edge α)
    (hKB : K ⊆ B)
    (hUniform : Uniform 4 B)
    (hGround : ∀ E ∈ B, E ⊆ U) :
    (∑ T ∈ U.powersetCard 3,
      ((facetCompletions B U T).card -
        (facetCompletions K U T).card)) =
      4 * (B \ K).card := by
  classical
  have hUniformK : Uniform 4 K := by
    intro E hE
    exact hUniform (hKB hE)
  have hGroundK : ∀ E ∈ K, E ⊆ U := by
    intro E hE
    exact hGround E (hKB hE)
  have hDegreeLe (T : Edge α) :
      (facetCompletions K U T).card ≤
        (facetCompletions B U T).card := by
    apply Finset.card_le_card
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hx'.1, hKB hx'.2⟩
  have hPoint :
      (∑ T ∈ U.powersetCard 3,
        ((facetCompletions B U T).card -
          (facetCompletions K U T).card)) +
      (∑ T ∈ U.powersetCard 3,
        (facetCompletions K U T).card) =
      ∑ T ∈ U.powersetCard 3,
        (facetCompletions B U T).card := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro T _
    exact Nat.sub_add_cancel (hDegreeLe T)
  have hBsum := rank_four_facet_completion_degree_sum
    B U hUniform hGround
  have hKsum := rank_four_facet_completion_degree_sum
    K U hUniformK hGroundK
  have hCard := Finset.card_sdiff_add_card_eq_card hKB
  omega

/-- If the cleaned subfamily has facet degree at most half the threshold,
high-degree facets of the parent consume at most eight units per deleted
edge. This is the finite form of (III.B.16). -/
theorem rank_four_high_facet_degree_tail_le_deletions
    (B K : Family α) (U : Edge α) (M : ℕ)
    (hKB : K ⊆ B)
    (hUniform : Uniform 4 B)
    (hGround : ∀ E ∈ B, E ⊆ U)
    (hCap : ∀ T ∈ U.powersetCard 3,
      2 * (facetCompletions K U T).card ≤ M) :
    (∑ T ∈ U.powersetCard 3,
      if M < (facetCompletions B U T).card then
        (facetCompletions B U T).card else 0) ≤
      8 * (B \ K).card := by
  classical
  have hDegreeLe (T : Edge α) :
      (facetCompletions K U T).card ≤
        (facetCompletions B U T).card := by
    apply Finset.card_le_card
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hx'.1, hKB hx'.2⟩
  have hLocal (T : Edge α) (hT : T ∈ U.powersetCard 3) :
      (if M < (facetCompletions B U T).card then
        (facetCompletions B U T).card else 0) ≤
      2 * ((facetCompletions B U T).card -
        (facetCompletions K U T).card) := by
    by_cases hHigh : M < (facetCompletions B U T).card
    · simp only [ite_eq_left hHigh]
      have hCapT := hCap T hT
      have hMono := hDegreeLe T
      omega
    · simp only [ite_eq_right hHigh]
      omega
  calc
    _ ≤ ∑ T ∈ U.powersetCard 3,
        2 * ((facetCompletions B U T).card -
          (facetCompletions K U T).card) := by
      apply Finset.sum_le_sum
      intro T hT
      exact hLocal T hT
    _ = 2 * (∑ T ∈ U.powersetCard 3,
        ((facetCompletions B U T).card -
          (facetCompletions K U T).card)) := by
      rw [Finset.mul_sum]
    _ = 8 * (B \ K).card := by
      rw [rank_four_facet_degree_loss_eq_four_deletions
        B K U hKB hUniform hGround]
      omega

end JSP523.Rank4
