import JSP523.Counting.CommonPrefixTails
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Facet energy at arbitrary rank

This file records the exact finite identity (IV.4.6). Every pair of
completions of an `(r-1)`-facet is the same incidence as that facet in the
common cell of the completion pair.
-/

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α]

/-- Vertices in `V` completing a facet to an actual edge. -/
def facetCompletions (H : Family α) (V A : Edge α) : Edge α :=
  V.filter fun x => x ∉ A ∧ insert x A ∈ H

/-- Facets simultaneously completed by both points of a two-set `P`. -/
def commonFacetCell (H : Family α) (V P : Edge α) (r : ℕ) : Family α :=
  (V.powersetCard (r - 1)).filter fun A =>
    Disjoint A P ∧ ∀ x ∈ P, insert x A ∈ H

theorem pair_subset_facetCompletions_iff
    {H : Family α} {V A P : Edge α}
    (hPV : P ⊆ V) :
    P ⊆ facetCompletions H V A ↔
      Disjoint A P ∧ ∀ x ∈ P, insert x A ∈ H := by
  constructor
  · intro hP
    constructor
    · apply Finset.disjoint_left.mpr
      intro x hxA hxP
      exact (Finset.mem_filter.mp (hP hxP)).2.1 hxA
    · intro x hxP
      exact (Finset.mem_filter.mp (hP hxP)).2.2
  · rintro ⟨hDisj, hEdge⟩ x hxP
    apply Finset.mem_filter.mpr
    refine ⟨hPV hxP, ?_, hEdge x hxP⟩
    intro hxA
    exact (Finset.disjoint_left.mp hDisj) hxA hxP

/-- Exact pair-of-completions versus common-facet-cell count (IV.4.6).
No admissibility or codegree assumption is needed for this identity. -/
theorem facet_energy_double_count
    (H : Family α) (V : Edge α) (r : ℕ) :
    (∑ A ∈ V.powersetCard (r - 1),
      (facetCompletions H V A).card.choose 2) =
      ∑ P ∈ V.powersetCard 2,
        (commonFacetCell H V P r).card := by
  classical
  let Facets := V.powersetCard (r - 1)
  let Pairs := V.powersetCard 2
  have hInner : ∀ A ∈ Facets,
      (facetCompletions H V A).card.choose 2 =
      ∑ P ∈ Pairs,
        if P ⊆ facetCompletions H V A then (1 : ℕ) else 0 := by
    intro A _
    have hFilter :
        Pairs.filter (fun P => P ⊆ facetCompletions H V A) =
          (facetCompletions H V A).powersetCard 2 := by
      ext P
      simp only [Pairs, Finset.mem_filter, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨_, hPcard⟩, hPsub⟩
        exact ⟨hPsub, hPcard⟩
      · rintro ⟨hPsub, hPcard⟩
        exact ⟨⟨hPsub.trans (Finset.filter_subset _ _), hPcard⟩, hPsub⟩
    rw [← Finset.card_filter, hFilter, Finset.card_powersetCard]
  have hCell : ∀ P ∈ Pairs,
      (commonFacetCell H V P r).card =
      ∑ A ∈ Facets,
        if P ⊆ facetCompletions H V A then (1 : ℕ) else 0 := by
    intro P hP
    have hPV := (Finset.mem_powersetCard.mp hP).1
    have hEq : commonFacetCell H V P r =
        Facets.filter (fun A => P ⊆ facetCompletions H V A) := by
      ext A
      simp only [commonFacetCell, Finset.mem_filter]
      exact and_congr_right fun _ =>
        (pair_subset_facetCompletions_iff hPV).symm
    rw [hEq, Finset.card_filter]
  calc
    (∑ A ∈ Facets, (facetCompletions H V A).card.choose 2) =
        ∑ A ∈ Facets, ∑ P ∈ Pairs,
          if P ⊆ facetCompletions H V A then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro A hA
      exact hInner A hA
    _ = ∑ P ∈ Pairs, ∑ A ∈ Facets,
          if P ⊆ facetCompletions H V A then (1 : ℕ) else 0 :=
      Finset.sum_comm
    _ = ∑ P ∈ Pairs, (commonFacetCell H V P r).card := by
      apply Finset.sum_congr rfl
      intro P hP
      exact (hCell P hP).symm

/-- A common facet cell of two completion vertices is intersecting by
admissibility. -/
theorem commonFacetCell_intersecting
    {H : Family α} {V : Edge α} {x y : α} {r : ℕ}
    (hH : Admissible H) (hxy : x ≠ y) (hr : 2 ≤ r) :
    PairwiseIntersecting (commonFacetCell H V ({x, y} : Edge α) r) := by
  classical
  have hSub : commonFacetCell H V ({x, y} : Edge α) r ⊆
      commonPrefixTails H V ({x} : Edge α) ({y} : Edge α) (r - 1) := by
    intro A hA
    obtain ⟨hPow, hDisj, hEdges⟩ := Finset.mem_filter.mp hA
    obtain ⟨hAV, hAcard⟩ := Finset.mem_powersetCard.mp hPow
    apply mem_commonPrefixTails.mpr
    refine ⟨hAV, hAcard, ?_, ?_, ?_⟩
    · simpa using hDisj
    · simpa using hEdges x (by simp)
    · simpa using hEdges y (by simp)
  have hI := commonPrefixTails_intersecting (W := V) hH
    (by simp) (by simp) (Finset.disjoint_singleton.mpr hxy)
    (by omega : 1 ≤ r - 1)
  intro A B hA hB hNe
  exact hI (hSub hA) (hSub hB) hNe

/-- The finite common-cell estimate needed after (IV.4.6), expressed
through actual parent two-point degree rather than an abstract cell cap. -/
theorem commonFacetCell_card_le_pair_degree
    {H : Family α} {V : Edge α} {r D : ℕ}
    (hH : Admissible H) (hr : 2 ≤ r)
    (hD : ∀ Q : Edge α, Q.card = 2 →
      (H.filter fun E => Q ⊆ E).card ≤ D)
    {P : Edge α} (hP : P ∈ V.powersetCard 2) :
    (commonFacetCell H V P r).card ≤ (r - 1) * D := by
  classical
  obtain ⟨x, y, hxy, rfl⟩ :=
    Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hP).2
  let C := commonFacetCell H V ({x, y} : Edge α) r
  by_cases hEmpty : C = ∅
  · change C.card ≤ (r - 1) * D
    simp [hEmpty]
  obtain ⟨A, hA⟩ : C.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
  have hU : Uniform (r - 1) C := by
    intro T hT
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).2
  have hI : PairwiseIntersecting C :=
    commonFacetCell_intersecting hH hxy hr
  apply intersecting_card_le_vertex_cap hU hI hA (by omega)
  intro z
  by_cases hzx : z = x
  · subst z
    have hNone : (C.filter fun T => x ∈ T) = ∅ := by
      ext T
      constructor
      · intro hT
        have hDisj := (Finset.mem_filter.mp (Finset.mem_filter.mp hT).1).2.1
        exact False.elim ((Finset.disjoint_left.mp hDisj)
          (Finset.mem_filter.mp hT).2 (by simp))
      · simp
    simp [hNone]
  · let Q : Edge α := {x, z}
    have hQcard : Q.card = 2 := Finset.card_pair (Ne.symm hzx)
    have hMap : ∀ T ∈ C.filter (fun T => z ∈ T),
        insert x T ∈ H.filter (fun E => Q ⊆ E) := by
      intro T hT
      obtain ⟨hTC, hzT⟩ := Finset.mem_filter.mp hT
      have hEdges := (Finset.mem_filter.mp hTC).2.2
      apply Finset.mem_filter.mpr
      refine ⟨hEdges x (by simp), ?_⟩
      intro a ha
      rcases Finset.mem_insert.mp ha with hax | haz
      · exact Finset.mem_insert.mpr (Or.inl hax)
      · exact Finset.mem_insert_of_mem ((Finset.mem_singleton.mp haz) ▸ hzT)
    have hInj : Set.InjOn (fun T : Edge α => insert x T)
        (↑(C.filter fun T => z ∈ T) : Set (Edge α)) := by
      intro T hT U hU hEq
      have hNotX (S : Edge α) (hS : S ∈ C) : x ∉ S := by
        intro hxS
        have hDisj := (Finset.mem_filter.mp hS).2.1
        exact (Finset.disjoint_left.mp hDisj) hxS (by simp)
      have hErase := congrArg (fun E : Edge α => E.erase x) hEq
      simpa [Finset.erase_insert (hNotX T (Finset.mem_filter.mp hT).1),
        Finset.erase_insert (hNotX U (Finset.mem_filter.mp hU).1)] using hErase
    have hBound : (C.filter fun T => z ∈ T).card ≤
        (H.filter fun E => Q ⊆ E).card :=
      Finset.card_le_card_of_injOn (fun T => insert x T) hMap hInj
    exact hBound.trans (hD Q hQcard)

/-- Equation (IV.4.6) with the intersecting-cell bound inserted.
It is the finite energy estimate before substituting codegree scales. -/
theorem facet_energy_le_pair_degree_budget
    {H : Family α} {V : Edge α} {r D : ℕ}
    (hH : Admissible H) (hr : 2 ≤ r)
    (hD : ∀ Q : Edge α, Q.card = 2 →
      (H.filter fun E => Q ⊆ E).card ≤ D) :
    (∑ A ∈ V.powersetCard (r - 1),
      (facetCompletions H V A).card.choose 2) ≤
      V.card.choose 2 * ((r - 1) * D) := by
  rw [facet_energy_double_count]
  have hEach : ∀ P ∈ V.powersetCard 2,
      (commonFacetCell H V P r).card ≤ (r - 1) * D := by
    intro P hP
    exact commonFacetCell_card_le_pair_degree hH hr hD hP
  simpa [nsmul_eq_mul, Finset.card_powersetCard] using
    Finset.sum_le_card_nsmul (V.powersetCard 2)
      (fun P => (commonFacetCell H V P r).card) ((r - 1) * D) hEach

/-- Facets whose actual completion degree exceeds the cutoff. -/
def heavyFacets (H : Family α) (V : Edge α) (r t : ℕ) : Family α :=
  (V.powersetCard (r - 1)).filter fun A => t < (facetCompletions H V A).card

/-- Actual edges deleted because they contain a heavy facet. -/
def edgesMeetingHeavyFacet (H : Family α) (V : Edge α) (r t : ℕ) : Family α :=
  H.filter fun E => ∃ A ∈ heavyFacets H V r t, A ⊆ E

private theorem high_degree_choose_budget (d t : ℕ) (hdt : t < d) :
    (t - 1) * d ≤ 2 * d.choose 2 := by
  have hSub : t - 1 ≤ d - 1 := Nat.sub_le_sub_right hdt.le 1
  have hChoose : d * (d - 1) = 2 * d.choose 2 := by
    rw [mul_comm 2, Nat.choose_two_right,
      Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self d)]
  calc
    (t - 1) * d = d * (t - 1) := mul_comm _ _
    _ ≤ d * (d - 1) := Nat.mul_le_mul_left d hSub
    _ = 2 * d.choose 2 := hChoose

/-- Every deleted edge has a heavy facet and therefore appears among the
completion incidences of that facet. -/
theorem edgesMeetingHeavyFacet_card_le_incidence
    {H : Family α} {V : Edge α} {r t : ℕ}
    (hU : Uniform r H) (hGround : ∀ E ∈ H, E ⊆ V)
    (hr : 1 ≤ r) :
    (edgesMeetingHeavyFacet H V r t).card ≤
      ∑ A ∈ heavyFacets H V r t, (facetCompletions H V A).card := by
  classical
  have hCover : edgesMeetingHeavyFacet H V r t ⊆
      (heavyFacets H V r t).biUnion
        (fun A => (facetCompletions H V A).image (fun x => insert x A)) := by
    intro E hE
    obtain ⟨hEH, A, hA, hAE⟩ := Finset.mem_filter.mp hE
    have hAcard := (Finset.mem_powersetCard.mp
      (Finset.mem_filter.mp hA).1).2
    have hEcard := hU hEH
    have hAdd : A.card + 1 = E.card := by omega
    obtain ⟨x, hxA, hEq⟩ :=
      Finset.exists_eq_insert_iff.mpr ⟨hAE, hAdd⟩
    have hxV : x ∈ V := hGround E hEH (hEq ▸ Finset.mem_insert_self x A)
    have hxComp : x ∈ facetCompletions H V A :=
      Finset.mem_filter.mpr ⟨hxV, hxA, hEq ▸ hEH⟩
    exact Finset.mem_biUnion.mpr
      ⟨A, hA, Finset.mem_image.mpr ⟨x, hxComp, hEq⟩⟩
  have hBi := Finset.card_biUnion_le (s := heavyFacets H V r t)
    (t := fun A => (facetCompletions H V A).image (fun x => insert x A))
  have hImage :
      (∑ A ∈ heavyFacets H V r t,
        ((facetCompletions H V A).image (fun x => insert x A)).card) ≤
      ∑ A ∈ heavyFacets H V r t,
        (facetCompletions H V A).card := by
    apply Finset.sum_le_sum
    intro A _
    exact Finset.card_image_le
  exact (Finset.card_le_card hCover).trans (hBi.trans hImage)

/-- The weighted incidence bound for heavy facets. -/
theorem heavyFacet_incidence_energy_bound
    (H : Family α) (V : Edge α) (r t : ℕ) :
    (t - 1) *
      (∑ A ∈ heavyFacets H V r t,
        (facetCompletions H V A).card) ≤
      2 * (∑ A ∈ V.powersetCard (r - 1),
        (facetCompletions H V A).card.choose 2) := by
  classical
  have hEach : ∀ A ∈ heavyFacets H V r t,
      (t - 1) * (facetCompletions H V A).card ≤
      2 * (facetCompletions H V A).card.choose 2 := by
    intro A hA
    exact high_degree_choose_budget _ _ (Finset.mem_filter.mp hA).2
  have hSum := Finset.sum_le_sum hEach
  have hSub : heavyFacets H V r t ⊆ V.powersetCard (r - 1) :=
    Finset.filter_subset _ _
  have hRest := Finset.sum_le_sum_of_subset hSub
    (f := fun A => 2 * (facetCompletions H V A).card.choose 2)
  simpa only [Finset.mul_sum] using hSum.trans hRest

/-- Finite high-facet deletion cost in (IV.4.7), prior to choosing a
numerical cutoff as a function of the regularization parameter. -/
theorem high_facet_deletion_bound
    {H : Family α} {V : Edge α} {r t D : ℕ}
    (hAdm : Admissible H) (hU : Uniform r H)
    (hGround : ∀ E ∈ H, E ⊆ V) (hr : 2 ≤ r)
    (hD : ∀ Q : Edge α, Q.card = 2 →
      (H.filter fun E => Q ⊆ E).card ≤ D) :
    (t - 1) * (edgesMeetingHeavyFacet H V r t).card ≤
      2 * (V.card.choose 2 * ((r - 1) * D)) := by
  have hInc := edgesMeetingHeavyFacet_card_le_incidence hU hGround
    (t := t) (by omega : 1 ≤ r)
  have hWeighted := Nat.mul_le_mul_left (t - 1) hInc
  have hEnergy := heavyFacet_incidence_energy_bound H V r t
  have hCap := facet_energy_le_pair_degree_budget (V := V) hAdm hr hD
  have hCap' := Nat.mul_le_mul_left 2 hCap
  omega

/-- The survivor after removing all edges incident to a heavy facet. -/
def facetCleanedFamily (H : Family α) (V : Edge α) (r t : ℕ) : Family α :=
  H \ edgesMeetingHeavyFacet H V r t

theorem facetCleanedFamily_subset
    (H : Family α) (V : Edge α) (r t : ℕ) :
    facetCleanedFamily H V r t ⊆ H := Finset.sdiff_subset

theorem facetCleanedFamily_admissible
    {H : Family α} {V : Edge α} {r t : ℕ}
    (hH : Admissible H) :
    Admissible (facetCleanedFamily H V r t) :=
  admissible_mono (facetCleanedFamily_subset H V r t) hH

theorem facetCleanedFamily_uniform
    {H : Family α} {V : Edge α} {r t : ℕ}
    (hH : Uniform r H) :
    Uniform r (facetCleanedFamily H V r t) := by
  intro E hE
  exact hH (facetCleanedFamily_subset H V r t hE)

theorem facetCleanedFamily_codegree_le
    (H : Family α) (V S : Edge α) (r t : ℕ) :
    ((facetCleanedFamily H V r t).filter fun E => S ⊆ E).card ≤
      (H.filter fun E => S ⊆ E).card := by
  apply Finset.card_le_card
  intro E hE
  obtain ⟨hEH, hSE⟩ := Finset.mem_filter.mp hE
  exact Finset.mem_filter.mpr
    ⟨facetCleanedFamily_subset H V r t hEH, hSE⟩

/-- Every retained facet has completion degree at most the cutoff. -/
theorem facetCleanedFamily_facet_degree_le
    (H : Family α) (V : Edge α) (r t : ℕ)
    {A : Edge α} (hA : A ∈ V.powersetCard (r - 1)) :
    (facetCompletions (facetCleanedFamily H V r t) V A).card ≤ t := by
  classical
  by_cases hHeavy : A ∈ heavyFacets H V r t
  · have hEmpty : facetCompletions (facetCleanedFamily H V r t) V A = ∅ := by
      ext x
      constructor
      · intro hx
        have hEdge := (Finset.mem_filter.mp hx).2.2
        have hEdge' := Finset.mem_sdiff.mp hEdge
        have hRemoved : insert x A ∈ edgesMeetingHeavyFacet H V r t := by
          apply Finset.mem_filter.mpr
          exact ⟨hEdge'.1, ⟨A, hHeavy, Finset.subset_insert x A⟩⟩
        exact False.elim (hEdge'.2 hRemoved)
      · simp
    simp [hEmpty]
  · have hParent : (facetCompletions H V A).card ≤ t := by
      have hNot : ¬ t < (facetCompletions H V A).card := by
        intro ht
        exact hHeavy (Finset.mem_filter.mpr ⟨hA, ht⟩)
      omega
    have hSub : facetCompletions (facetCleanedFamily H V r t) V A ⊆
        facetCompletions H V A := by
      intro x hx
      obtain ⟨hxV, hxA, hEdge⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr
        ⟨hxV, hxA, facetCleanedFamily_subset H V r t hEdge⟩
    exact (Finset.card_le_card hSub).trans hParent

/-- The actual number of edges removed by facet cleaning satisfies the
weighted energy budget. -/
theorem facetCleanedFamily_loss_bound
    {H : Family α} {V : Edge α} {r t D : ℕ}
    (hAdm : Admissible H) (hU : Uniform r H)
    (hGround : ∀ E ∈ H, E ⊆ V) (hr : 2 ≤ r)
    (hD : ∀ Q : Edge α, Q.card = 2 →
      (H.filter fun E => Q ⊆ E).card ≤ D) :
    (t - 1) * (H.card - (facetCleanedFamily H V r t).card) ≤
      2 * (V.card.choose 2 * ((r - 1) * D)) := by
  have hDeleted : edgesMeetingHeavyFacet H V r t ⊆ H :=
    Finset.filter_subset _ _
  have hPart := Finset.card_sdiff_add_card_eq_card hDeleted
  have hBudget := high_facet_deletion_bound (t := t)
    hAdm hU hGround hr hD
  have hEq : H.card - (facetCleanedFamily H V r t).card =
      (edgesMeetingHeavyFacet H V r t).card := by
    dsimp [facetCleanedFamily]
    omega
  rw [hEq]
  exact hBudget

end JSP523.Rank5
