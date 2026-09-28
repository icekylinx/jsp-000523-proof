import JSP523.Rank4.PreprocessCrossMoment

/-!
# Fixed core and star decomposition for PART III

The ambient vertex partition is fixed before any layer cleaning.  This file
records its exact finite edge decomposition and composes the already proved
owner cleaning and weak common-cell clearing budgets on those actual pieces.
-/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- The induced core on the fixed ground set. -/
def fixedDecompositionCore (H : Family α) (V : Edge α) : Family α :=
  H.filter fun E => E ⊆ V

/-- Actual rank-four edges meeting the fixed center set once and otherwise
contained in the ground set. -/
def fixedDecompositionStarEdges
    (H : Family α) (V C : Edge α) : Family α :=
  C.biUnion fun c => (rankFourStarLink H V c).image fun T => insert c T

/-- The error part consists of all original edges in neither fixed core nor
the exactly-once star layer. -/
def fixedDecompositionError
    (H : Family α) (V C : Edge α) : Family α :=
  H \ (fixedDecompositionCore H V ∪ fixedDecompositionStarEdges H V C)

private theorem fixed_star_edges_subset
    (H : Family α) (V C : Edge α) :
    fixedDecompositionStarEdges H V C ⊆ H := by
  intro E hE
  obtain ⟨c, hcC, hImage⟩ := Finset.mem_biUnion.mp hE
  obtain ⟨T, hT, hEq⟩ := Finset.mem_image.mp hImage
  have hEdge := (Finset.mem_filter.mp hT).2
  simpa [hEq] using hEdge

private theorem fixed_core_star_disjoint
    (H : Family α) (V C : Edge α)
    (hOutside : ∀ c ∈ C, c ∉ V) :
    Disjoint (fixedDecompositionCore H V)
      (fixedDecompositionStarEdges H V C) := by
  apply Finset.disjoint_left.mpr
  intro E hCore hStar
  obtain ⟨c, hcC, hImage⟩ := Finset.mem_biUnion.mp hStar
  obtain ⟨T, hT, hEq⟩ := Finset.mem_image.mp hImage
  have hcE : c ∈ E := by
    rw [← hEq]
    simp
  exact (hOutside c hcC) ((Finset.mem_filter.mp hCore).2 hcE)

/-- The fixed core, star layer, and remainder partition the original family;
the star layer is charged to the sum of its actual links. -/
theorem fixed_decomposition_card_bound
    (H : Family α) (V C : Edge α)
    (hOutside : ∀ c ∈ C, c ∉ V) :
    H.card ≤ (fixedDecompositionCore H V).card +
      (∑ c ∈ C, (rankFourStarLink H V c).card) +
      (fixedDecompositionError H V C).card := by
  classical
  let B := fixedDecompositionCore H V
  let S := fixedDecompositionStarEdges H V C
  let E := fixedDecompositionError H V C
  have hBS : Disjoint B S := fixed_core_star_disjoint H V C hOutside
  have hSub : B ∪ S ⊆ H := by
    intro F hF
    rcases Finset.mem_union.mp hF with hB | hS
    · exact (Finset.mem_filter.mp hB).1
    · exact fixed_star_edges_subset H V C hS
  have hParts : H = (B ∪ S) ∪ E := by
    ext F
    simp only [E, fixedDecompositionError, Finset.mem_union,
      Finset.mem_sdiff]
    constructor
    · intro hF
      by_cases hPart : F ∈ B ∪ S
      · exact Or.inl (Finset.mem_union.mp hPart)
      · exact Or.inr ⟨hF, by
          intro hUnion
          exact hPart (Finset.mem_union.mpr hUnion)⟩
    · rintro (hPart | ⟨hF, _⟩)
      · exact hSub (Finset.mem_union.mpr hPart)
      · exact hF
  have hDisj : Disjoint (B ∪ S) E := by
    apply Finset.disjoint_left.mpr
    intro F hF hE
    exact (Finset.mem_sdiff.mp hE).2 hF
  have hStarCard : S.card ≤ ∑ c ∈ C, (rankFourStarLink H V c).card := by
    dsimp [S, fixedDecompositionStarEdges]
    calc
      _ ≤ ∑ c ∈ C, ((rankFourStarLink H V c).image fun T => insert c T).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ c ∈ C, (rankFourStarLink H V c).card := by
        apply Finset.sum_le_sum
        intro c hc
        exact Finset.card_image_le
  have hCardParts : H.card = B.card + S.card + E.card := by
    rw [hParts, Finset.card_union_of_disjoint hDisj,
      Finset.card_union_of_disjoint hBS]
  calc
    H.card = B.card + S.card + E.card := hCardParts
    _ ≤ B.card + (∑ c ∈ C, (rankFourStarLink H V c).card) + E.card := by
      exact Nat.add_le_add_right (Nat.add_le_add_left hStarCard B.card) E.card

/-- On the actual fixed core, weak-cell clearing and the actual center star
links can be carried out simultaneously.  The statement returns the core
cleaning budget and unique-cell labels together with disjoint cleaned star
shadows and the explicit owner-loss square bound. -/
theorem fixed_decomposition_preprocess_components
    {H : Family α} (V centers : Edge α) (t D : ℕ)
    (hH : Admissible H)
    (hCap : ∀ T : Edge α, T.card = 3 →
      (facetCompletions H V T).card ≤ D)
    (hLarge : 9 * D < t)
    (hOutside : ∀ c ∈ centers, c ∉ V)
    (hVcard : 6 ≤ V.card)
    [Nonempty {c // c ∈ centers}] :
    ∃ K : Family α,
      K ⊆ fixedDecompositionCore H V ∧
      (fixedDecompositionCore H V \ K).card ≤
        2 * (t - 1) * V.card.choose 2 ∧
      (∀ P ∈ V.powersetCard 2,
        (commonRootCell K V P).card = 0 ∨
          ∃! z : α, ∀ ⦃T : Edge α⦄,
            T ∈ commonRootCell K V P → z ∈ T) ∧
      ((∀ i j : {c // c ∈ centers}, i ≠ j →
        Disjoint
          (starLinkPairShadow
            (pairOwnerCleanedLink
              (fun j : {c // c ∈ centers} => rankFourStarLink H V j.val)
              (maximumDegreePairOwner
                (fun j : {c // c ∈ centers} => rankFourStarLink H V j.val))) V i)
          (starLinkPairShadow
            (pairOwnerCleanedLink
              (fun j : {c // c ∈ centers} => rankFourStarLink H V j.val)
              (maximumDegreePairOwner
                (fun j : {c // c ∈ centers} => rankFourStarLink H V j.val))) V j)) ∧
      (∑ i : {c // c ∈ centers},
        (rankFourStarLink H V i.val \
          pairOwnerCleanedLink
            (fun j : {c // c ∈ centers} => rankFourStarLink H V j.val)
            (maximumDegreePairOwner
              (fun j : {c // c ∈ centers} => rankFourStarLink H V j.val)) i).card) ^ 2 ≤
        (V.powersetCard 2).card *
          (Fintype.card {c // c ∈ centers} *
            (Fintype.card {c // c ∈ centers} - 1) *
            (V.card ^ 3 + 3 * V.card.choose 3))) := by
  classical
  let B := fixedDecompositionCore H V
  have hBH : B ⊆ H := by
    intro E hE
    exact (Finset.mem_filter.mp hE).1
  have hBAdmissible : Admissible B := admissible_mono hBH hH
  have hBCap : ∀ T : Edge α, T.card = 3 →
      (facetCompletions B V T).card ≤ D := by
    intro T hT
    apply (Finset.card_le_card ?_).trans (hCap T hT)
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hx'.1, hBH hx'.2⟩
  obtain ⟨K, hKB, hCellLoss, hLabels⟩ :=
    clear_small_cells_and_get_unique_labels V t D hBAdmissible hBCap hLarge
  have hShadows : ∀ i j : {c // c ∈ centers}, i ≠ j →
      Disjoint
        (starLinkPairShadow
          (pairOwnerCleanedLink
            (fun j : {c // c ∈ centers} => rankFourStarLink H V j.val)
            (maximumDegreePairOwner
              (fun j : {c // c ∈ centers} => rankFourStarLink H V j.val))) V i)
        (starLinkPairShadow
          (pairOwnerCleanedLink
            (fun j : {c // c ∈ centers} => rankFourStarLink H V j.val)
            (maximumDegreePairOwner
              (fun j : {c // c ∈ centers} => rankFourStarLink H V j.val))) V j) := by
    intro i j hij
    exact pair_owner_cleaning_shadows_disjoint
      (fun j : {c // c ∈ centers} => rankFourStarLink H V j.val)
      (maximumDegreePairOwner
        (fun j : {c // c ∈ centers} => rankFourStarLink H V j.val))
      V i j hij
  have hLossSq :=
    rank_four_star_owner_cleaning_loss_sq_bound
      (fun i : {c // c ∈ centers} => i.val) hH
      (fun i j hij => Subtype.ext hij)
      (fun i => hOutside i.val i.property) hVcard
  refine ⟨K, hKB, hCellLoss, hLabels, hShadows, ?_⟩
  simpa using hLossSq

/-! The weak-cell budget on the actual fixed core combines with the fixed
edge decomposition bound without changing the star links or the remainder. -/
theorem fixed_decomposition_core_clearing_card_budget
    {H : Family α} (V centers : Edge α) (t D : ℕ)
    (hH : Admissible H)
    (hCap : ∀ T : Edge α, T.card = 3 →
      (facetCompletions H V T).card ≤ D)
    (hLarge : 9 * D < t)
    (hOutside : ∀ c ∈ centers, c ∉ V) :
    ∃ K : Family α,
      K ⊆ fixedDecompositionCore H V ∧
      (fixedDecompositionCore H V \ K).card ≤
        2 * (t - 1) * V.card.choose 2 ∧
      H.card ≤ K.card + (fixedDecompositionCore H V \ K).card +
        (∑ c ∈ centers, (rankFourStarLink H V c).card) +
        (fixedDecompositionError H V centers).card := by
  classical
  let B := fixedDecompositionCore H V
  have hBH : B ⊆ H := by
    intro E hE
    exact (Finset.mem_filter.mp hE).1
  have hBAdmissible := admissible_mono hBH hH
  have hBCap : ∀ T : Edge α, T.card = 3 →
      (facetCompletions B V T).card ≤ D := by
    intro T hT
    apply (Finset.card_le_card ?_).trans (hCap T hT)
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hx'.1, hBH hx'.2⟩
  obtain ⟨K, hKB, hCellLoss, hLabels⟩ :=
    clear_small_cells_and_get_unique_labels V t D hBAdmissible hBCap hLarge
  have hCoreCard := Finset.card_sdiff_add_card_eq_card hKB
  have hDecomp := fixed_decomposition_card_bound H V centers hOutside
  refine ⟨K, hKB, hCellLoss, ?_⟩
  calc
    H.card ≤ B.card + (∑ c ∈ centers, (rankFourStarLink H V c).card) +
        (fixedDecompositionError H V centers).card := hDecomp
    _ = (B \ K).card + K.card +
        (∑ c ∈ centers, (rankFourStarLink H V c).card) +
        (fixedDecompositionError H V centers).card := by rw [← hCoreCard]
    _ = K.card + (B \ K).card +
        (∑ c ∈ centers, (rankFourStarLink H V c).card) +
        (fixedDecompositionError H V centers).card := by omega


end JSP523.Rank4
