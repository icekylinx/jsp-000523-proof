import JSP523.Rank4.StarLinkActualBudget

/-!
# The finite rank-four master budget

The cleaned star layer and the core facet shadow both lie in the same
three-subset ground set. Their overlap is precisely the error in the
second budget used with the star/native inequality. This file keeps the
actual finite families in the statement of the resulting master estimate.
-/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- Three-element facets in the ground set that occur in a four-edge of
the core. -/
def rankFourFacetShadow (K : Family α) (U : Edge α) : Family α :=
  (U.powersetCard 3).filter fun T =>
    0 < (facetCompletions K U T).card

theorem mem_rankFourFacetShadow
    (K : Family α) (U T : Edge α) :
    T ∈ rankFourFacetShadow K U ↔
      T ∈ U.powersetCard 3 ∧
        ∃ x ∈ U, insert x T ∈ K := by
  classical
  simp only [rankFourFacetShadow, Finset.mem_filter]
  constructor
  · rintro ⟨hT, hPos⟩
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hPos
    exact ⟨hT, x, (Finset.mem_filter.mp hx).1,
      (Finset.mem_filter.mp hx).2⟩
  · rintro ⟨hT, x, hxU, hxK⟩
    exact ⟨hT, Finset.card_pos.mpr
      ⟨x, Finset.mem_filter.mpr ⟨hxU, hxK⟩⟩⟩

theorem rank_four_facet_shadow_mono
    {K B : Family α} {U : Edge α} (hKB : K ⊆ B) :
    rankFourFacetShadow K U ⊆ rankFourFacetShadow B U := by
  intro T hT
  obtain ⟨hTriple, x, hxU, hxK⟩ :=
    (mem_rankFourFacetShadow K U T).mp hT
  exact (mem_rankFourFacetShadow B U T).mpr
    ⟨hTriple, x, hxU, hKB hxK⟩

/-- The exact shadow-overlap budget from (III.B.1): the union consumes
at most all triples of the fixed ground set. -/
theorem star_shadow_union_budget
    (A K : Family α) (U : Edge α)
    (hA : A ⊆ U.powersetCard 3) :
    A.card + (rankFourFacetShadow K U).card ≤
      U.card.choose 3 +
        (A ∩ rankFourFacetShadow K U).card := by
  classical
  have hShadow : rankFourFacetShadow K U ⊆ U.powersetCard 3 := by
    intro T hT
    exact (Finset.mem_filter.mp hT).1
  have hUnion : A ∪ rankFourFacetShadow K U ⊆
      U.powersetCard 3 := Finset.union_subset hA hShadow
  have hUnionCard := Finset.card_le_card hUnion
  rw [Finset.card_powersetCard] at hUnionCard
  have hInclusion := Finset.card_union_add_card_inter A
    (rankFourFacetShadow K U)
  omega

/-- When the cleaned core lies in its fixed parent, its star-shadow
overlap is bounded by the parent overlap from preprocessing. -/
theorem star_shadow_overlap_mono
    (A K B : Family α) (U : Edge α)
    (hKB : K ⊆ B) :
    (A ∩ rankFourFacetShadow K U).card ≤
      (A ∩ rankFourFacetShadow B U).card := by
  apply Finset.card_le_card
  intro T hT
  have hParts := Finset.mem_inter.mp hT
  exact Finset.mem_inter.mpr
    ⟨hParts.1, rank_four_facet_shadow_mono hKB hParts.2⟩

/-- The finite numerical core of (III.B.15). The deficit premise is
twice (III.B.7), so every quantity stays in natural numbers. -/
theorem rank_four_master_from_deficit
    (A K : Family α) (U : Edge α)
    (nativeVertices nonprivateFacets allPrivateEdges starError : ℕ)
    (hA : A ⊆ U.powersetCard 3)
    (hStar : 3 * A.card + nativeVertices ≤
      3 * U.card.choose 3 + starError)
    (hDeficit :
      10 * K.card + nonprivateFacets + 6 * allPrivateEdges ≤
        2 * nativeVertices + 4 * (rankFourFacetShadow K U).card) :
    10 * (A.card + K.card) + nonprivateFacets +
        6 * allPrivateEdges ≤
      10 * U.card.choose 3 + 2 * starError +
        4 * (A ∩ rankFourFacetShadow K U).card := by
  have hShadow := star_shadow_union_budget A K U hA
  omega

/-- The same finite master estimate, with preprocessing's parent
overlap paid directly. -/
theorem rank_four_master_with_parent_overlap
    (A K B : Family α) (U : Edge α)
    (nativeVertices nonprivateFacets allPrivateEdges starError
      parentOverlap : ℕ)
    (hKB : K ⊆ B)
    (hA : A ⊆ U.powersetCard 3)
    (hOverlap :
      (A ∩ rankFourFacetShadow B U).card ≤ parentOverlap)
    (hStar : 3 * A.card + nativeVertices ≤
      3 * U.card.choose 3 + starError)
    (hDeficit :
      10 * K.card + nonprivateFacets + 6 * allPrivateEdges ≤
        2 * nativeVertices + 4 * (rankFourFacetShadow K U).card) :
    10 * (A.card + K.card) + nonprivateFacets +
        6 * allPrivateEdges ≤
      10 * U.card.choose 3 + 2 * starError +
        4 * parentOverlap := by
  have hMaster := rank_four_master_from_deficit A K U
    nativeVertices nonprivateFacets allPrivateEdges starError
    hA hStar hDeficit
  have hMono := star_shadow_overlap_mono A K B U hKB
  omega

/-- The master estimate with the actual cleaned star union and chosen
native graphs. Only the separate finite-deficit estimate is an input. -/
theorem cleaned_star_chosen_native_master
    [Fintype α]
    {H : Family α} {V U : Edge α}
    (K B : Family α) (L : α → Family α)
    (centers : Finset α) (owner : Edge α → α)
    (fallback : α) (nonprivateFacets allPrivateEdges
      parentOverlap : ℕ)
    (hCenters : UniqueCommonRootCenters K U)
    (hH : Admissible H)
    (hUsubV : U ⊆ V)
    (hCentersV : ∀ c ∈ centers, c ∈ V)
    (hCentersU : ∀ c ∈ centers, c ∉ U)
    (hLayerEdges : ∀ c ∈ centers, ∀ Q ∈ L c, insert c Q ∈ H)
    (hLayerGround : ∀ c ∈ centers, ∀ Q ∈ L c,
      Q ∈ U.powersetCard 3)
    (hU : 3 ≤ U.card)
    (hTails : ∀ a ∈ U, ∀ b ∈ U.erase a,
      ({a, b} : Edge α) ∈ nonemptyCommonRoots K U →
        HasThreeParentTails H V U a b
          (chosenCommonRootLabel K U fallback hCenters
            ({a, b} : Edge α)))
    (hKB : K ⊆ B)
    (hOverlap :
      ((centers.biUnion (pairOwnerCleanedLink L owner)) ∩
        rankFourFacetShadow B U).card ≤ parentOverlap)
    (hDeficit :
      10 * K.card + nonprivateFacets + 6 * allPrivateEdges ≤
        2 * nativeTailVertexTotal K U (nonemptyCommonRoots K U)
          (chosenCommonRootLabel K U fallback hCenters) +
        4 * (rankFourFacetShadow K U).card) :
    10 * ((centers.biUnion (pairOwnerCleanedLink L owner)).card + K.card) +
        nonprivateFacets + 6 * allPrivateEdges ≤
      10 * U.card.choose 3 +
        2 * (U.card ^ 2 * (Nat.sqrt U.card + 1)) +
        4 * parentOverlap := by
  classical
  let A := centers.biUnion (pairOwnerCleanedLink L owner)
  have hA : A ⊆ U.powersetCard 3 := by
    intro T hT
    obtain ⟨c, hc, hTc⟩ := Finset.mem_biUnion.mp hT
    have hTL : T ∈ L c := by
      simp only [pairOwnerCleanedLink, Finset.mem_filter] at hTc
      exact hTc.1
    exact hLayerGround c hc T hTL
  have hStar := cleaned_star_chosen_native_sqrt_budget
    K L centers owner fallback hCenters hH hUsubV
    hCentersV hCentersU hLayerEdges hLayerGround hU hTails
  exact rank_four_master_with_parent_overlap A K B U
    (nativeTailVertexTotal K U (nonemptyCommonRoots K U)
      (chosenCommonRootLabel K U fallback hCenters))
    nonprivateFacets allPrivateEdges
    (U.card ^ 2 * (Nat.sqrt U.card + 1)) parentOverlap
    hKB hA hOverlap hStar hDeficit

end JSP523.Rank4
