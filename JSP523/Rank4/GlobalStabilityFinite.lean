import JSP523.Rank4.GlobalDegreeTail

/-!
# Finite stability estimate after a degree-tail cleanup

An edge outside the all-private class has a nonprivate facet. Counting
these edges through their facets and using a bounded-degree subfamily
gives the finite estimate behind (III.B.17).
-/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- Actual facets of a four-family with at least two completions. -/
def rankFourNonprivateFacets (K : Family α) (U : Edge α) : Family α :=
  (U.powersetCard 3).filter fun T =>
    2 ≤ (facetCompletions K U T).card

/-- Actual edges whose four triple facets have fewer than two
completions. For a uniform four-family, each of these degrees is one. -/
def rankFourAllPrivateEdges (K : Family α) (U : Edge α) : Family α :=
  K.filter fun E => ∀ T ∈ E.powersetCard 3,
    (facetCompletions K U T).card < 2

/-- Every triple facet of an actual four-edge has a completion in that
edge's own family. -/
theorem rank_four_edge_facet_degree_positive
    (K : Family α) (U E T : Edge α)
    (hUniform : Uniform 4 K)
    (hGround : ∀ F ∈ K, F ⊆ U)
    (hE : E ∈ K) (hT : T ∈ E.powersetCard 3) :
    0 < (facetCompletions K U T).card := by
  classical
  have hT' := Finset.mem_powersetCard.mp hT
  rw [facet_completions_card_eq_parent_edges
    K U T hUniform hGround hT'.2]
  exact Finset.card_pos.mpr
    ⟨E, Finset.mem_filter.mpr ⟨hE, hT'.1⟩⟩

/-- The all-private predicate has exactly the manuscript meaning on
actual four-edges. -/
theorem rank_four_all_private_edge_iff_degree_one
    (K : Family α) (U E : Edge α)
    (hUniform : Uniform 4 K)
    (hGround : ∀ F ∈ K, F ⊆ U) :
    E ∈ rankFourAllPrivateEdges K U ↔
      E ∈ K ∧ ∀ T ∈ E.powersetCard 3,
        (facetCompletions K U T).card = 1 := by
  classical
  constructor
  · intro hE
    have hParts := Finset.mem_filter.mp hE
    refine ⟨hParts.1, ?_⟩
    intro T hT
    have hPos := rank_four_edge_facet_degree_positive
      K U E T hUniform hGround hParts.1 hT
    have hSmall := hParts.2 T hT
    omega
  · rintro ⟨hE, hOne⟩
    exact Finset.mem_filter.mpr
      ⟨hE, fun T hT => by rw [hOne T hT]; omega⟩

/-- Every non-all-private edge is counted by at least one nonprivate
facet, and each facet counts exactly its actual completion degree. -/
theorem rank_four_edges_le_private_plus_nonprivate_degrees
    (K : Family α) (U : Edge α)
    (hUniform : Uniform 4 K)
    (hGround : ∀ E ∈ K, E ⊆ U) :
    K.card ≤ (rankFourAllPrivateEdges K U).card +
      ∑ T ∈ rankFourNonprivateFacets K U,
        (facetCompletions K U T).card := by
  classical
  let P := rankFourAllPrivateEdges K U
  let N := rankFourNonprivateFacets K U
  have hPsub : P ⊆ K := Finset.filter_subset _ _
  have hCover : K \ P ⊆
      N.biUnion (rankFourFacetParents K) := by
    intro E hE
    have hParts := Finset.mem_sdiff.mp hE
    have hWitness : ∃ T ∈ E.powersetCard 3,
        2 ≤ (facetCompletions K U T).card := by
      by_contra hNone
      have hAll : ∀ T ∈ E.powersetCard 3,
          (facetCompletions K U T).card < 2 := by
        intro T hT
        by_contra hNot
        exact hNone ⟨T, hT, by omega⟩
      exact hParts.2 (Finset.mem_filter.mpr ⟨hParts.1, hAll⟩)
    obtain ⟨T, hTE, hDeg⟩ := hWitness
    have hTE' := Finset.mem_powersetCard.mp hTE
    have hTU : T ∈ U.powersetCard 3 :=
      Finset.mem_powersetCard.mpr
        ⟨hTE'.1.trans (hGround E hParts.1), hTE'.2⟩
    have hTN : T ∈ N := Finset.mem_filter.mpr ⟨hTU, hDeg⟩
    exact Finset.mem_biUnion.mpr
      ⟨T, hTN, Finset.mem_filter.mpr ⟨hParts.1, hTE'.1⟩⟩
  have hCardCover : (K \ P).card ≤
      ∑ T ∈ N, (rankFourFacetParents K T).card := by
    calc
      (K \ P).card ≤
          (N.biUnion (rankFourFacetParents K)).card :=
        Finset.card_le_card hCover
      _ ≤ ∑ T ∈ N, (rankFourFacetParents K T).card :=
        Finset.card_biUnion_le
  have hDegreeSum :
      (∑ T ∈ N, (rankFourFacetParents K T).card) =
      ∑ T ∈ N, (facetCompletions K U T).card := by
    apply Finset.sum_congr rfl
    intro T hT
    exact (facet_completions_card_eq_parent_edges
      K U T hUniform hGround
      (Finset.mem_powersetCard.mp
        (Finset.mem_filter.mp hT).1).2).symm
  have hCard := Finset.card_sdiff_add_card_eq_card hPsub
  rw [hDegreeSum] at hCardCover
  change K.card ≤ P.card +
    ∑ T ∈ N, (facetCompletions K U T).card
  omega

/-- The finite core of the stability bound: a bounded-degree subfamily
and the degree tail of its parent pay for every non-all-private edge. -/
theorem rank_four_core_stability_finite
    (B K B₁ : Family α) (U : Edge α) (M : ℕ)
    (hKB : K ⊆ B)
    (hB₁B : B₁ ⊆ B)
    (hUniform : Uniform 4 B)
    (hGround : ∀ E ∈ B, E ⊆ U)
    (hCap : ∀ T ∈ U.powersetCard 3,
      2 * (facetCompletions B₁ U T).card ≤ M) :
    K.card ≤ (rankFourAllPrivateEdges K U).card +
      M * (rankFourNonprivateFacets K U).card +
      8 * (B \ B₁).card := by
  classical
  let N := rankFourNonprivateFacets K U
  have hUniformK : Uniform 4 K := by
    intro E hE
    exact hUniform (hKB hE)
  have hGroundK : ∀ E ∈ K, E ⊆ U := by
    intro E hE
    exact hGround E (hKB hE)
  have hKDegreeLe (T : Edge α) :
      (facetCompletions K U T).card ≤
        (facetCompletions B U T).card := by
    apply Finset.card_le_card
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hx'.1, hKB hx'.2⟩
  have hNsub : N ⊆ U.powersetCard 3 := Finset.filter_subset _ _
  have hPoint (T : Edge α) (hT : T ∈ N) :
      (facetCompletions K U T).card ≤
        M + (if M < (facetCompletions B U T).card then
          (facetCompletions B U T).card else 0) := by
    by_cases hHigh : M < (facetCompletions B U T).card
    · simp only [ite_eq_left hHigh]
      exact Nat.le_add_left_of_le (hKDegreeLe T)
    · simp only [ite_eq_right hHigh, add_zero]
      have hMono := hKDegreeLe T
      omega
  have hNSum :
      (∑ T ∈ N, (facetCompletions K U T).card) ≤
      M * N.card +
        ∑ T ∈ U.powersetCard 3,
          if M < (facetCompletions B U T).card then
            (facetCompletions B U T).card else 0 := by
    have hLocal := Finset.sum_le_sum
      (s := N) (fun T hT => hPoint T hT)
    have hSub :
        (∑ T ∈ N,
          if M < (facetCompletions B U T).card then
            (facetCompletions B U T).card else 0) ≤
        ∑ T ∈ U.powersetCard 3,
          if M < (facetCompletions B U T).card then
            (facetCompletions B U T).card else 0 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hNsub
        (fun _ _ _ => Nat.zero_le _)
    calc
      _ ≤ ∑ T ∈ N,
          (M + (if M < (facetCompletions B U T).card then
            (facetCompletions B U T).card else 0)) := hLocal
      _ = M * N.card +
          ∑ T ∈ N,
            if M < (facetCompletions B U T).card then
              (facetCompletions B U T).card else 0 := by
        rw [Finset.sum_add_distrib]
        simp [mul_comm]
      _ ≤ M * N.card +
          ∑ T ∈ U.powersetCard 3,
            if M < (facetCompletions B U T).card then
              (facetCompletions B U T).card else 0 :=
        Nat.add_le_add_left hSub _
  have hTail := rank_four_high_facet_degree_tail_le_deletions
    B B₁ U M hB₁B hUniform hGround hCap
  have hEdges := rank_four_edges_le_private_plus_nonprivate_degrees
    K U hUniformK hGroundK
  dsimp only [N] at hNSum
  omega

/-- With the finite deficit expressed as a nonnegative surplus, the
two classes of core edges share the same allowance. -/
theorem rank_four_core_stability_from_surplus
    (B K B₁ : Family α) (U : Edge α) (M S : ℕ)
    (hKB : K ⊆ B)
    (hB₁B : B₁ ⊆ B)
    (hUniform : Uniform 4 B)
    (hGround : ∀ E ∈ B, E ⊆ U)
    (hM : 1 ≤ M)
    (hCap : ∀ T ∈ U.powersetCard 3,
      2 * (facetCompletions B₁ U T).card ≤ M)
    (hSurplus :
      (rankFourNonprivateFacets K U).card +
        6 * (rankFourAllPrivateEdges K U).card ≤ 2 * S) :
    K.card ≤ 2 * M * S + 8 * (B \ B₁).card := by
  let b := (rankFourNonprivateFacets K U).card
  let m₀ := (rankFourAllPrivateEdges K U).card
  have hCore := rank_four_core_stability_finite
    B K B₁ U M hKB hB₁B hUniform hGround hCap
  have hSixM : 1 ≤ 6 * M := by omega
  have hm₀ : m₀ ≤ (6 * M) * m₀ := by
    calc
      m₀ = 1 * m₀ := by simp
      _ ≤ (6 * M) * m₀ := Nat.mul_le_mul_right m₀ hSixM
  have hCredit : m₀ + M * b ≤ 2 * M * S := by
    calc
      m₀ + M * b ≤ (6 * M) * m₀ + M * b := by omega
      _ = M * (b + 6 * m₀) := by ring
      _ ≤ M * (2 * S) := Nat.mul_le_mul_left M hSurplus
      _ = 2 * M * S := by ring
  dsimp only [b, m₀] at hCredit
  omega

/-- The fixed parent remainder has the same bound, with the actual
cleanup loss from parent to final core added once. -/
theorem rank_four_parent_stability_from_surplus
    (B K B₁ : Family α) (U : Edge α) (M S : ℕ)
    (hKB : K ⊆ B)
    (hB₁B : B₁ ⊆ B)
    (hUniform : Uniform 4 B)
    (hGround : ∀ E ∈ B, E ⊆ U)
    (hM : 1 ≤ M)
    (hCap : ∀ T ∈ U.powersetCard 3,
      2 * (facetCompletions B₁ U T).card ≤ M)
    (hSurplus :
      (rankFourNonprivateFacets K U).card +
        6 * (rankFourAllPrivateEdges K U).card ≤ 2 * S) :
    B.card ≤ 2 * M * S + 8 * (B \ B₁).card +
      (B \ K).card := by
  have hK := rank_four_core_stability_from_surplus
    B K B₁ U M S hKB hB₁B hUniform hGround hM hCap hSurplus
  have hCard := Finset.card_sdiff_add_card_eq_card hKB
  omega

end JSP523.Rank4
