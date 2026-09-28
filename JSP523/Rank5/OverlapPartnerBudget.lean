import JSP523.Rank5.InheritedCenterLocal
import JSP523.Counting.AssignedPrefixGeometry

/-!
# Actual overlapping parent-link partner budget

This isolates the facet case of the rank-five inheritance argument.  For a
fixed three-core and pair root, every overlapping second root contains one of
the two root vertices.  Mapping that root to its parent edge gives a genuine
four-codegree bound.  This is a coarse upper bound; the pinned witness count
in IV.9 is needed to make inheritance failures sparse.
-/

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α]

/-- Actual pair roots in the same three-core link that intersect `R`. -/
noncomputable def overlappingParentPartners
    (H : Family α) (V B R : Edge α) : Family α := by
  classical
  exact (parentPairLink H V B).filter fun T => ¬ Disjoint R T

/-- Roots in a three-core parent link containing one specified vertex inject
    into the actual parent edges through the resulting four-set. -/
theorem parent_link_roots_containing_vertex_le_codegree
    (H : Family α) (V B : Edge α) (a : α) :
    ((parentPairLink H V B).filter fun T => a ∈ T).card ≤
      (H.filter fun E => B ∪ {a} ⊆ E).card := by
  classical
  let f : Edge α → Edge α := fun T => B ∪ T
  apply Finset.card_le_card_of_injOn f
  · intro T hT
    obtain ⟨hLink, haT⟩ := Finset.mem_filter.mp hT
    have hParts := mem_parent_pair_link.mp hLink
    apply Finset.mem_filter.mpr
    refine ⟨hParts.2.2.2, ?_⟩
    intro x hx
    rcases Finset.mem_union.mp hx with hxB | hxA
    · exact Finset.mem_union_left T hxB
    · have hxa : x = a := Finset.mem_singleton.mp hxA
      exact Finset.mem_union_right B (hxa ▸ haT)
  · intro T hT U hU hEq
    have hTdisj : Disjoint B T :=
      (mem_parent_pair_link.mp (Finset.mem_filter.mp hT).1).2.2.1.symm
    have hUdisj : Disjoint B U :=
      (mem_parent_pair_link.mp (Finset.mem_filter.mp hU).1).2.2.1.symm
    calc
      T = (B ∪ T) \ B := (Finset.union_sdiff_cancel_left hTdisj).symm
      _ = (B ∪ U) \ B := congrArg (· \ B) hEq
      _ = U := Finset.union_sdiff_cancel_left hUdisj

/-- Overlapping partners are covered by the roots containing each vertex of
    `R`, and hence by the sum of the corresponding actual codegrees. -/
theorem overlapping_parent_partners_card_le_codegree_sum
    (H : Family α) (V B R : Edge α) :
    (overlappingParentPartners H V B R).card ≤
      ∑ a ∈ R, (H.filter fun E => B ∪ {a} ⊆ E).card := by
  classical
  let L : α → Family α := fun a =>
    (parentPairLink H V B).filter fun T => a ∈ T
  have hCover : overlappingParentPartners H V B R ⊆ R.biUnion L := by
    intro T hT
    have hParts := Finset.mem_filter.mp hT
    obtain ⟨a, haR, haT⟩ := Finset.not_disjoint_iff.mp hParts.2
    exact Finset.mem_biUnion.mpr
      ⟨a, haR, Finset.mem_filter.mpr ⟨hParts.1, haT⟩⟩
  calc
    (overlappingParentPartners H V B R).card ≤ (R.biUnion L).card :=
      Finset.card_le_card hCover
    _ ≤ ∑ a ∈ R, (L a).card := Finset.card_biUnion_le
    _ ≤ ∑ a ∈ R, (H.filter fun E => B ∪ {a} ⊆ E).card := by
      apply Finset.sum_le_sum
      intro a ha
      exact parent_link_roots_containing_vertex_le_codegree H V B a

/-- The concrete facet case: a pair root has at most twice the four-codegree
    cap many overlapping partners in its three-core parent link. -/
theorem overlapping_pair_partners_card_le_two_four_codegree
    (H : Family α) (V B R : Edge α) (D₄ : ℕ)
    (hRcard : R.card = 2)
    (hD₄ : ∀ a ∈ R, (H.filter fun E => B ∪ {a} ⊆ E).card ≤ D₄) :
    (overlappingParentPartners H V B R).card ≤ 2 * D₄ := by
  have hOverlap := overlapping_parent_partners_card_le_codegree_sum H V B R
  have hSum : (∑ a ∈ R, (H.filter fun E => B ∪ {a} ⊆ E).card) ≤
      ∑ _a ∈ R, D₄ := Finset.sum_le_sum hD₄
  simpa [hRcard, mul_comm] using hOverlap.trans hSum

/-- The IV.9 facet loss is bounded specifically by overlapping parent-link
    pairs.  Choosing the good relation to mean disjointness removes all
    coloring-dependent exceptional pairs from the earlier exposure bound. -/
theorem bad_facet_parent_card_le_overlapping_partner_sum
    {K H : Family α} {V : Edge α}
    (facetCenter tripleLabel : Edge α → α)
    (hKH : K ⊆ H) (hUniform : Uniform 5 K)
    (hAmbient : ∀ G ∈ K, G ⊆ V) :
    (badFacetParentEdges K facetCenter tripleLabel).card ≤
      ∑ B ∈ V.powersetCard 3,
        ∑ R ∈ parentPairLink H V B,
          (overlappingParentPartners H V B R).card := by
  have h := bad_facet_parent_card_le_partner_incidence_sum
    facetCenter tripleLabel hKH hUniform hAmbient
    (fun _ R T => Disjoint R T) (by intros; assumption)
  simpa [overlappingParentPartners, badParentPartners] using h

/-- Exact three-core incidence count for an ambient five-uniform parent. -/
theorem total_three_core_parent_degrees_eq_ten_edges
    (H : Family α) (V : Edge α)
    (hUniform : Uniform 5 H)
    (hAmbient : ∀ E ∈ H, E ⊆ V) :
    (∑ B ∈ V.powersetCard 3,
        (H.filter fun E => B ⊆ E).card) = 10 * H.card := by
  classical
  calc
    (∑ B ∈ V.powersetCard 3,
        (H.filter fun E => B ⊆ E).card) =
        ∑ B ∈ V.powersetCard 3,
          ∑ E ∈ H, if B ⊆ E then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro B hB
      exact Finset.card_filter (fun E : Edge α => B ⊆ E) H
    _ = ∑ E ∈ H, ∑ B ∈ V.powersetCard 3,
          if B ⊆ E then (1 : ℕ) else 0 := Finset.sum_comm
    _ = ∑ E ∈ H, (E.powersetCard 3).card := by
      apply Finset.sum_congr rfl
      intro E hE
      calc
        (∑ B ∈ V.powersetCard 3,
            if B ⊆ E then (1 : ℕ) else 0) =
            ((V.powersetCard 3).filter fun B => B ⊆ E).card :=
          (Finset.card_filter (fun B : Edge α => B ⊆ E) _).symm
        _ = (E.powersetCard 3).card := by
          congr 1
          ext B
          simp only [Finset.mem_filter, Finset.mem_powersetCard]
          constructor
          · rintro ⟨⟨_, hCard⟩, hBE⟩
            exact ⟨hBE, hCard⟩
          · rintro ⟨hBE, hCard⟩
            exact ⟨⟨hBE.trans (hAmbient E hE), hCard⟩, hBE⟩
    _ = ∑ _E ∈ H, 10 := by
      apply Finset.sum_congr rfl
      intro E hE
      rw [Finset.card_powersetCard, hUniform hE]
      decide
    _ = 10 * H.card := by simp [mul_comm]

/-- Each actual five-edge has ten three-cores.  Summing all parent pair-link
    sizes over occurring three-cores counts no more than these incidences. -/
theorem total_three_core_parent_pair_links_le_ten_edges
    (H : Family α) (V : Edge α)
    (hUniform : Uniform 5 H)
    (hAmbient : ∀ E ∈ H, E ⊆ V) :
    (∑ B ∈ V.powersetCard 3, (parentPairLink H V B).card) ≤
      10 * H.card := by
  classical
  have hCodegreeSum := total_three_core_parent_degrees_eq_ten_edges
    H V hUniform hAmbient
  calc
    (∑ B ∈ V.powersetCard 3, (parentPairLink H V B).card) ≤
        ∑ B ∈ V.powersetCard 3,
          (H.filter fun E => B ⊆ E).card := by
      apply Finset.sum_le_sum
      intro B hB
      exact JSP523.Counting.parent_pair_link_card_le_codegree H V B
    _ = 10 * H.card := hCodegreeSum

/-- A coarse but fully actual facet-overlap budget.  It uses only the
    four-codegree cap and the ten three-cores of each five-edge. -/
theorem overlapping_partner_incidence_sum_le_four_codegree_budget
    (H : Family α) (V : Edge α) (D₄ : ℕ)
    (hUniform : Uniform 5 H)
    (hAmbient : ∀ E ∈ H, E ⊆ V)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄) :
    (∑ B ∈ V.powersetCard 3,
      ∑ R ∈ parentPairLink H V B,
        (overlappingParentPartners H V B R).card) ≤
      20 * D₄ * H.card := by
  classical
  have hLocal : ∀ B ∈ V.powersetCard 3,
      ∀ R ∈ parentPairLink H V B,
        (overlappingParentPartners H V B R).card ≤ 2 * D₄ := by
    intro B hB R hR
    have hBcard := (Finset.mem_powersetCard.mp hB).2
    have hParts := mem_parent_pair_link.mp hR
    have hCap : ∀ a ∈ R,
        (H.filter fun E => B ∪ {a} ⊆ E).card ≤ D₄ := by
      intro a haR
      have haNotB : a ∉ B := by
        intro haB
        exact (Finset.disjoint_left.mp hParts.2.2.1) haR haB
      have hCard : (B ∪ {a}).card = 4 := by
        have hDisj : Disjoint B ({a} : Edge α) :=
          Finset.disjoint_singleton_right.mpr haNotB
        rw [Finset.card_union_of_disjoint hDisj]
        simp [hBcard]
      exact hD₄ (B ∪ {a}) hCard
    exact overlapping_pair_partners_card_le_two_four_codegree
      H V B R D₄ hParts.2.1 hCap
  have hCount := total_three_core_parent_pair_links_le_ten_edges
    H V hUniform hAmbient
  calc
    (∑ B ∈ V.powersetCard 3,
        ∑ R ∈ parentPairLink H V B,
          (overlappingParentPartners H V B R).card) ≤
        ∑ B ∈ V.powersetCard 3,
          (2 * D₄) * (parentPairLink H V B).card := by
      apply Finset.sum_le_sum
      intro B hB
      calc
        (∑ R ∈ parentPairLink H V B,
            (overlappingParentPartners H V B R).card) ≤
            ∑ _R ∈ parentPairLink H V B, 2 * D₄ :=
          Finset.sum_le_sum (fun R hR => hLocal B hB R hR)
        _ = (2 * D₄) * (parentPairLink H V B).card := by
          simp [mul_comm]
    _ = (2 * D₄) *
          (∑ B ∈ V.powersetCard 3, (parentPairLink H V B).card) := by
      rw [Finset.mul_sum]
    _ ≤ (2 * D₄) * (10 * H.card) := Nat.mul_le_mul_left _ hCount
    _ = 20 * D₄ * H.card := by ring

/-- The resulting finite IV.9 deletion bound.  The factor `D₄` explains why
    overlap geometry alone does not give the manuscript's small loss. -/
theorem bad_facet_parent_card_le_four_codegree_budget
    {K H : Family α} {V : Edge α}
    (facetCenter tripleLabel : Edge α → α) (D₄ : ℕ)
    (hKH : K ⊆ H) (hUniformK : Uniform 5 K)
    (hUniformH : Uniform 5 H)
    (hAmbient : ∀ E ∈ H, E ⊆ V)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄) :
    (badFacetParentEdges K facetCenter tripleLabel).card ≤
      20 * D₄ * H.card := by
  have hOverlap := bad_facet_parent_card_le_overlapping_partner_sum
    facetCenter tripleLabel hKH hUniformK
    (fun E hE => hAmbient E (hKH hE))
  have hBudget := overlapping_partner_incidence_sum_le_four_codegree_budget
    H V D₄ hUniformH hAmbient hD₄
  exact hOverlap.trans hBudget

end JSP523.Rank5
