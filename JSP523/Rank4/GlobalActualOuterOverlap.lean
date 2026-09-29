import JSP523.Rank4.GlobalMasterBudget
import JSP523.Rank4.PreprocessFixedDecomposition
import JSP523.Counting.IntersectingTripleCenter

/-! # The actual star and core shadow overlap in §III.A.3 -/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- An intersecting triple system of pair degree at most `D` on `U` has at
most `(U.card + 9) * D` members.  The center case is counted through all
pairs containing its center; the other case uses the nine-pair cover. -/
theorem intersecting_triples_card_le_ground_plus_nine_mul_pair_cap
    (J : Family α) (U : Edge α) (D : ℕ)
    (hGround : ∀ T ∈ J, T ∈ U.powersetCard 3)
    (hIntersect : PairwiseIntersecting J)
    (hPair : ∀ P : Edge α, P.card = 2 → triplePairDegree J P ≤ D) :
    J.card ≤ (U.card + 9) * D := by
  classical
  by_cases hCenter : ∃ z : α, ∀ ⦃T : Edge α⦄, T ∈ J → z ∈ T
  · obtain ⟨z, hz⟩ := hCenter
    have hCover : J ⊆ (U.erase z).biUnion fun x =>
        J.filter fun T => ({z, x} : Edge α) ⊆ T := by
      intro T hT
      have hzT := hz hT
      have hTcard := (Finset.mem_powersetCard.mp (hGround T hT)).2
      have hEraseCard : (T.erase z).card = 2 := by
        rw [Finset.card_erase_of_mem hzT]
        omega

      obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < (T.erase z).card)
      have hxT : x ∈ T := (Finset.mem_erase.mp hx).2
      have hxU : x ∈ U := (Finset.mem_powersetCard.mp (hGround T hT)).1 hxT
      exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_erase.mpr
        ⟨(Finset.mem_erase.mp hx).1, hxU⟩,
        Finset.mem_filter.mpr ⟨hT, by
          intro v hv
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl
          · exact hzT
          · exact hxT⟩⟩
    have hEach : ∀ x ∈ U.erase z,
        (J.filter fun T => ({z, x} : Edge α) ⊆ T).card ≤ D := by
      intro x hxU
      exact hPair {z, x} (Finset.card_pair (Ne.symm (Finset.mem_erase.mp hxU).1))
    have hSum := Finset.card_biUnion_le (s := U.erase z)
      (t := fun x => J.filter fun T => ({z, x} : Edge α) ⊆ T)
    have hCard := (Finset.card_le_card hCover).trans hSum
    have hBound : (∑ x ∈ U.erase z,
        (J.filter fun T => ({z, x} : Edge α) ⊆ T).card) ≤ U.card * D := by
      calc
        _ ≤ ∑ _x ∈ U.erase z, D := Finset.sum_le_sum hEach
        _ = (U.erase z).card * D := by simp
        _ ≤ U.card * D := Nat.mul_le_mul_right D Finset.card_erase_le
    calc
      J.card ≤ U.card * D := hCard.trans hBound
      _ ≤ (U.card + 9) * D := by
        simp only [Nat.add_mul]
        omega
  · have hNoCenter : NoGlobalCenter J := by
      intro z
      by_contra h
      exact hCenter ⟨z, by
        intro T hT
        by_contra hzT
        exact h ⟨T, hT, hzT⟩⟩
    have hNine := intersecting_triples_card_le_nine_mul_pair_degree
      (by intro T hT; exact (Finset.mem_powersetCard.mp (hGround T hT)).2)
      hIntersect hNoCenter hPair
    calc
      J.card ≤ 9 * D := hNine
      _ ≤ (U.card + 9) * D := by
        simp only [Nat.add_mul]
        omega

/-- For a common cell whose first completion vertex lies in `U`, pair
degrees use only facets of the induced core. -/
theorem common_triple_cell_pair_degree_le_induced_facet_cap
    (H : Family α) (U : Edge α) (y c : α) (D : ℕ)
    (hyU : y ∈ U)
    (hFacet : ∀ T : Edge α, T ⊆ U → T.card = 3 →
      (facetCompletions H U T).card ≤ D)
    (P : Edge α) (hPcard : P.card = 2) :
    triplePairDegree (commonTripleCell H U y c) P ≤ D := by
  classical
  by_cases hPU : P ⊆ U
  · by_cases hyP : y ∈ P
    · have hZero : triplePairDegree (commonTripleCell H U y c) P = 0 := by
        unfold triplePairDegree
        apply Finset.card_eq_zero.mpr
        ext T
        constructor
        · intro hT'
          obtain ⟨hT, hPT⟩ := Finset.mem_filter.mp hT'
          have hDisjoint := (mem_common_triple_cell.mp hT).2.2.1
          exact ((Finset.disjoint_left.mp hDisjoint) (hPT hyP) (by simp)).elim
        · simp
      omega
    · have hTsub : insert y P ⊆ U := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxP
        · exact hyU
        · exact hPU hxP
      have hTcard : (insert y P).card = 3 := by
        rw [Finset.card_insert_of_notMem hyP, hPcard]
      exact (common_triple_cell_pair_degree_le_facet_completions H U y c P hPcard).trans
        (hFacet (insert y P) hTsub hTcard)
  · have hZero : triplePairDegree (commonTripleCell H U y c) P = 0 := by
      unfold triplePairDegree
      apply Finset.card_eq_zero.mpr
      ext T
      constructor
      · intro hT'
        obtain ⟨hT, hPT⟩ := Finset.mem_filter.mp hT'
        exact (hPU (hPT.trans (mem_common_triple_cell.mp hT).1)).elim
      · simp
    omega

/-- A facet contained in `U` has the same completions in `H` and in the
induced core on `U`. -/
theorem facet_completions_eq_induced_core_on_ground
    (H : Family α) (U T : Edge α) (hTU : T ⊆ U) :
    facetCompletions H U T =
      facetCompletions (fixedDecompositionCore H U) U T := by
  ext x
  simp only [facetCompletions, fixedDecompositionCore, Finset.mem_filter]
  constructor
  · rintro ⟨hxU, hxH⟩
    exact ⟨hxU, hxH, by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hyT
      · exact hxU
      · exact hTU hyT⟩
  · rintro ⟨hxU, hxH, _⟩
    exact ⟨hxU, hxH⟩

/-- The actual overlap of all original star links with facets of the
induced core.  Its bound uses the core's facet cap and the number of
outside centers; owner cleaning can only reduce this overlap. -/
theorem rank_four_original_star_core_overlap_card_le
    (H : Family α) (U C : Edge α) (D : ℕ)
    (hH : Admissible H) (hUniform : Uniform 4 H)
    (hOutside : ∀ c ∈ C, c ∉ U)
    (hFacet : ∀ T : Edge α, T ⊆ U → T.card = 3 →
      (facetCompletions H U T).card ≤ D) :
    (((C.biUnion fun c => rankFourStarLink H U c) ∩
      rankFourFacetShadow (fixedDecompositionCore H U) U).card) ≤
      C.card * U.card * ((U.card + 9) * D) := by
  classical
  have hCell : ∀ c ∈ C, ∀ y ∈ U,
      (commonTripleCell H U y c).card ≤ (U.card + 9) * D := by
    intro c hc y hy
    apply intersecting_triples_card_le_ground_plus_nine_mul_pair_cap
    · intro T hT
      exact (Finset.mem_filter.mp hT).1
    · exact common_triple_cell_intersecting hH
        (fun hyc => hOutside c hc (hyc ▸ hy))
    · exact common_triple_cell_pair_degree_le_induced_facet_cap
        H U y c D hy hFacet
  have hCover :
      (C.biUnion fun c => rankFourStarLink H U c) ∩
        rankFourFacetShadow (fixedDecompositionCore H U) U ⊆
      C.biUnion fun c => U.biUnion fun y => commonTripleCell H U y c := by
    intro T hT
    obtain ⟨hStar, hShadow⟩ := Finset.mem_inter.mp hT
    obtain ⟨c, hcC, hcLink⟩ := Finset.mem_biUnion.mp hStar
    obtain ⟨hTriple, y, hyU, hyCore⟩ :=
      (mem_rank_four_facet_shadow (fixedDecompositionCore H U) U T).mp hShadow
    have hcEdge : insert c T ∈ H := (Finset.mem_filter.mp hcLink).2
    have hyEdge : insert y T ∈ H :=
      (Finset.mem_filter.mp hyCore).1
    have hyNot : y ∉ T := by
      intro hyT
      have hEq : insert y T = T := Finset.insert_eq_of_mem hyT
      have hFour := hUniform hyEdge
      rw [hEq] at hFour
      have hThree := (Finset.mem_powersetCard.mp hTriple).2
      omega
    have hDisjoint : Disjoint T ({y, c} : Edge α) := by
      apply Finset.disjoint_left.mpr
      intro x hxT hxPair
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxPair
      rcases hxPair with hxc | hxy
      · exact hyNot (hxc ▸ hxT)
      · exact hOutside c hcC ((Finset.mem_powersetCard.mp hTriple).1 (hxy ▸ hxT))
    have hCommon : T ∈ commonTripleCell H U y c :=
      (mem_common_triple_cell).mpr
        ⟨(Finset.mem_powersetCard.mp hTriple).1,
          (Finset.mem_powersetCard.mp hTriple).2,
          hDisjoint, hyEdge, hcEdge⟩
    exact Finset.mem_biUnion.mpr ⟨c, hcC,
      Finset.mem_biUnion.mpr ⟨y, hyU, hCommon⟩⟩
  have hOuterSum :
      (C.biUnion fun c => U.biUnion fun y => commonTripleCell H U y c).card ≤
      ∑ c ∈ C, ∑ y ∈ U, (commonTripleCell H U y c).card := by
    calc
      _ ≤ ∑ c ∈ C, (U.biUnion fun y => commonTripleCell H U y c).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ c ∈ C, ∑ y ∈ U, (commonTripleCell H U y c).card := by
        apply Finset.sum_le_sum
        intro c _
        exact Finset.card_biUnion_le
  have hSum :
      (∑ c ∈ C, ∑ y ∈ U, (commonTripleCell H U y c).card) ≤
      C.card * U.card * ((U.card + 9) * D) := by
    calc
      _ ≤ ∑ c ∈ C, ∑ _y ∈ U, (U.card + 9) * D := by
        apply Finset.sum_le_sum
        intro c hc
        apply Finset.sum_le_sum
        intro y hy
        exact hCell c hc y hy
      _ = C.card * U.card * ((U.card + 9) * D) := by simp [mul_assoc]
  exact (Finset.card_le_card hCover).trans (hOuterSum.trans hSum)

/-- The same overlap estimate applies after pair-owner cleaning and to
any sublink of the original star layer. -/
theorem rank_four_cleaned_star_core_overlap_card_le
    (H : Family α) (U centers : Edge α) (L : α → Family α)
    (owner : Edge α → α) (D : ℕ)
    (hH : Admissible H) (hUniform : Uniform 4 H)
    (hOutside : ∀ c ∈ centers, c ∉ U)
    (hLink : ∀ c ∈ centers, L c ⊆ rankFourStarLink H U c)
    (hFacet : ∀ T : Edge α, T ⊆ U → T.card = 3 →
      (facetCompletions H U T).card ≤ D) :
    (((centers.biUnion fun c => pairOwnerCleanedLink L owner c) ∩
      rankFourFacetShadow (fixedDecompositionCore H U) U).card) ≤
      centers.card * U.card * ((U.card + 9) * D) := by
  have hStar : (centers.biUnion fun c => pairOwnerCleanedLink L owner c) ⊆
      centers.biUnion fun c => rankFourStarLink H U c := by
    intro T hT
    obtain ⟨c, hc, hTc⟩ := Finset.mem_biUnion.mp hT
    exact Finset.mem_biUnion.mpr ⟨c, hc,
      hLink c hc ((Finset.mem_filter.mp hTc).1)⟩
  have hSub :
      (centers.biUnion fun c => pairOwnerCleanedLink L owner c) ∩
        rankFourFacetShadow (fixedDecompositionCore H U) U ⊆
      (centers.biUnion fun c => rankFourStarLink H U c) ∩
        rankFourFacetShadow (fixedDecompositionCore H U) U := by
    intro T hT
    exact Finset.mem_inter.mpr ⟨hStar (Finset.mem_inter.mp hT).1,
      (Finset.mem_inter.mp hT).2⟩
  exact (Finset.card_le_card hSub).trans
    (rank_four_original_star_core_overlap_card_le H U centers D
      hH hUniform hOutside hFacet)

/-- The interface used by the actual master: only the induced core's
facet cap is needed for the original cleaned-star overlap estimate. -/
theorem rank_four_cleaned_star_core_overlap_card_le_of_core_cap
    (H : Family α) (U centers : Edge α) (L : α → Family α)
    (owner : Edge α → α) (D : ℕ)
    (hH : Admissible H) (hUniform : Uniform 4 H)
    (hOutside : ∀ c ∈ centers, c ∉ U)
    (hLink : ∀ c ∈ centers, L c ⊆ rankFourStarLink H U c)
    (hFacet : ∀ T : Edge α, T.card = 3 →
      (facetCompletions (fixedDecompositionCore H U) U T).card ≤ D) :
    (((centers.biUnion fun c => pairOwnerCleanedLink L owner c) ∩
      rankFourFacetShadow (fixedDecompositionCore H U) U).card) ≤
      centers.card * U.card * ((U.card + 9) * D) := by
  apply rank_four_cleaned_star_core_overlap_card_le H U centers L owner D
    hH hUniform hOutside hLink
  intro T hTU hTcard
  rw [facet_completions_eq_induced_core_on_ground H U T hTU]
  exact hFacet T hTcard

end JSP523.Rank4
