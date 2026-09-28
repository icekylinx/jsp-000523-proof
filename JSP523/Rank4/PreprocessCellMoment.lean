import JSP523.Rank4.PreprocessHighCodegree

/-!
# Actual common-cell caps from local degree bounds

With bounded pair codegrees in the four-family and bounded facet degrees,
every actual common triple cell is small.  The center case is charged to a
pair codegree; the no-center case is the finite nine-pair cover lemma.
-/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- Number of four-edges containing a specified pair. -/
def rankFourPairDegree (F : Family α) (P : Edge α) : ℕ :=
  (F.filter fun E => P ⊆ E).card

/-- A centered triple cell is bounded by the degree of the pair consisting
of one endpoint and its common center. -/
private theorem common_triple_cell_card_le_of_center_pair_degree
    {H : Family α} {V : Edge α} {a b z : α} {M : ℕ}
    (hz : ∀ ⦃T : Edge α⦄,
      T ∈ commonTripleCell H V a b → z ∈ T)
    (hPair : ∀ P : Edge α, P.card = 2 → rankFourPairDegree H P ≤ M) :
    (commonTripleCell H V a b).card ≤ M := by
  classical
  let J := commonTripleCell H V a b
  by_cases hJ : J.Nonempty
  · obtain ⟨T₀, hT₀⟩ := hJ
    have hza : z ≠ a := by
      intro h
      have hzT := hz hT₀
      have hDisj := (mem_common_triple_cell.mp hT₀).2.2.1
      have haT : a ∉ T₀ := by
        intro haT
        exact (Finset.disjoint_left.mp hDisj) haT (by simp)
      exact haT (h ▸ hzT)
    let P : Edge α := {a, z}
    have hPcard : P.card = 2 := Finset.card_pair hza.symm
    let f : Edge α → Edge α := fun T => insert a T
    have hMap : Set.MapsTo f (↑J : Set (Edge α))
        (↑(H.filter fun E => P ⊆ E) : Set (Edge α)) := by
      intro T hTJ
      have hCell := mem_common_triple_cell.mp hTJ
      apply Finset.mem_filter.mpr
      refine ⟨hCell.2.2.2.1, ?_⟩
      intro x hx
      have hxP : x = a ∨ x = z := by
        simpa [P, Finset.mem_insert, Finset.mem_singleton] using hx
      rcases hxP with hxa | hxz
      · rw [hxa]
        exact Finset.mem_insert_self a T
      · rw [hxz]
        exact Finset.mem_insert_of_mem (hz hTJ)
    have hInj : (↑J : Set (Edge α)).InjOn f := by
      intro T hT S hS hEq
      change insert a T = insert a S at hEq
      have haT : a ∉ T := by
        intro haT
        have hDisj := (mem_common_triple_cell.mp hT).2.2.1
        exact (Finset.disjoint_left.mp hDisj) haT (by simp)
      have haS : a ∉ S := by
        intro haS
        have hDisj := (mem_common_triple_cell.mp hS).2.2.1
        exact (Finset.disjoint_left.mp hDisj) haS (by simp)
      apply Finset.Subset.antisymm
      · intro x hx
        have hx' : x ∈ insert a S := by
          rw [← hEq]
          exact Finset.mem_insert_of_mem hx
        rcases Finset.mem_insert.mp hx' with hxa | hxS
        · exact (haT (hxa ▸ hx)).elim
        · exact hxS
      · intro x hx
        have hx' : x ∈ insert a T := by
          rw [hEq]
          exact Finset.mem_insert_of_mem hx
        rcases Finset.mem_insert.mp hx' with hxa | hxT
        · exact (haS (hxa ▸ hx)).elim
        · exact hxT
    have hCard := Finset.card_le_card_of_injOn f hMap hInj
    exact hCard.trans (hPair P hPcard)
  · have hEmpty : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    simp [J, hEmpty]

/-- The actual common triple cell is bounded by the larger of the
four-family pair-degree cap and nine times its facet-degree cap. -/
theorem common_triple_cell_card_le_of_degree_caps
    {H : Family α} {V : Edge α} {a b : α} {M D : ℕ}
    (hH : Admissible H) (hab : a ≠ b)
    (hPair : ∀ P : Edge α, P.card = 2 → rankFourPairDegree H P ≤ M)
    (hFacet : ∀ T : Edge α, T.card = 3 →
      (facetCompletions H V T).card ≤ D) :
    (commonTripleCell H V a b).card ≤ max M (9 * D) := by
  classical
  let J := commonTripleCell H V a b
  have hUniform : Uniform 3 J := by
    intro T hT
    exact (Finset.mem_powersetCard.mp
      (Finset.mem_filter.mp hT).1).2
  have hIntersect : PairwiseIntersecting J :=
    common_triple_cell_intersecting hH hab
  have hPairDegree : ∀ P : Edge α, P.card = 2 →
      triplePairDegree J P ≤ D :=
    common_triple_cell_pair_degree_le_of_facet_cap hFacet
  by_cases hCenter : ∃ z : α, ∀ ⦃T : Edge α⦄, T ∈ J → z ∈ T
  · obtain ⟨z, hz⟩ := hCenter
    have hCap := common_triple_cell_card_le_of_center_pair_degree hz hPair
    exact hCap.trans (Nat.le_max_left M (9 * D))
  · have hNoCenter : NoGlobalCenter J := by
      intro z
      by_contra hz
      exact hCenter ⟨z, by
        intro T hT
        by_contra hzT
        exact hz ⟨T, hT, hzT⟩⟩
    have hCover := intersecting_triples_card_le_nine_mul_pair_degree
      hUniform hIntersect hNoCenter hPairDegree
    exact hCover.trans (Nat.le_max_right M (9 * D))

/-- Summing the actual pair-root common cells costs at most their number
times the uniform local cell cap. -/
theorem common_root_cell_sum_le_of_degree_caps
    {H : Family α} {V : Edge α} {M D : ℕ}
    (hH : Admissible H)
    (hFacet : ∀ T : Edge α, T.card = 3 →
      (facetCompletions H V T).card ≤ D)
    (hPair : ∀ P : Edge α, P.card = 2 → rankFourPairDegree H P ≤ M) :
    (∑ P ∈ V.powersetCard 2, (commonRootCell H V P).card) ≤
      (V.powersetCard 2).card * max M (9 * D) := by
  classical
  calc
    _ ≤ ∑ P ∈ V.powersetCard 2, max M (9 * D) := by
      apply Finset.sum_le_sum
      intro P hP
      have hPcard := (Finset.mem_powersetCard.mp hP).2
      let ab := pairRootRep P hPcard
      have hEq : commonRootCell H V P =
          commonTripleCell H V ab.1 ab.2 := by
        simp [commonRootCell, hPcard, ab]
      rw [hEq]
      have hab : ab.1 ≠ ab.2 := (pair_root_rep_spec P hPcard).1
      exact common_triple_cell_card_le_of_degree_caps hH hab hPair hFacet
    _ = (V.powersetCard 2).card * max M (9 * D) := by simp

end JSP523.Rank4
