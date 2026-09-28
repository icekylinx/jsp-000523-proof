import JSP523.Counting.CommonPrefixTails
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Actual common-prefix cells for distinct star completions

This is the local collision estimate used in the distinct-completion part
of (IV.3.3). A pair of star centers and distinct completions form disjoint
two-point roots; admissibility makes their common `(r-2)`-tails intersect,
and a three-codegree cap bounds the cell by (IV.1.2).
-/

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α]

/-- Number of members of a link containing a fixed shadow set. -/
def starLayerPrefixDegree (A : Family α) (P : Edge α) : ℕ :=
  (A.filter fun T => P ⊆ T).card

/-- Actual `(r-1)`-link at a star center on U. -/
def actualStarLink (H : Family α) (U : Edge α) (z : α) (r : ℕ) : Family α :=
  (U.powersetCard (r - 1)).filter fun T => insert z T ∈ H

/-- Shadow facets shared by two link members. -/
def sharedStarLayerFacets (U T S : Edge α) (k : ℕ) : Family α :=
  (U.powersetCard (k - 1)).filter fun P => P ⊆ T ∧ P ⊆ S

/-- Distinct uniform link members share at most one facet of codimension
one. -/
theorem sharedStarLayerFacets_card_le_one
    (U T S : Edge α) (k : ℕ)
    (hT : T.card = k) (hS : S.card = k) (hTS : T ≠ S) :
    (sharedStarLayerFacets U T S k).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro P hP Q hQ
  have hP' := Finset.mem_filter.mp hP
  have hQ' := Finset.mem_filter.mp hQ
  obtain ⟨hPU, hPk⟩ := Finset.mem_powersetCard.mp hP'.1
  obtain ⟨hQU, hQk⟩ := Finset.mem_powersetCard.mp hQ'.1
  have hIntSub : T ∩ S ⊆ T := Finset.inter_subset_left
  have hIntNe : T ∩ S ≠ T := by
    intro hEq
    have hSubTS : T ⊆ S := Finset.inter_eq_left.mp hEq
    exact hTS (Finset.eq_of_subset_of_card_le hSubTS (by rw [hT, hS]))
  have hIntSsub : T ∩ S ⊂ T :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hIntSub, hIntNe⟩
  have hIntCard : (T ∩ S).card < k := by
    have := Finset.card_lt_card hIntSsub
    simpa [hT] using this
  have hPInt : P ⊆ T ∩ S := Finset.subset_inter hP'.2.1 hP'.2.2
  have hQInt : Q ⊆ T ∩ S := Finset.subset_inter hQ'.2.1 hQ'.2.2
  have hPIntCard : P = T ∩ S :=
    Finset.eq_of_subset_of_card_le hPInt (by omega)
  have hQIntCard : Q = T ∩ S :=
    Finset.eq_of_subset_of_card_le hQInt (by omega)
  exact hPIntCard.trans hQIntCard.symm

/-- If the two link members agree, they contribute exactly k common
`(k-1)`-facets, provided they lie in the link ground set. -/
theorem sharedStarLayerFacets_card_eq_of_eq
    (U T : Edge α) (k : ℕ) (hTU : T ⊆ U) (hT : T.card = k)
    (hk : 1 ≤ k) :
    (sharedStarLayerFacets U T T k).card = k := by
  classical
  have hEq : sharedStarLayerFacets U T T k = T.powersetCard (k - 1) := by
    ext P
    simp only [sharedStarLayerFacets, Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hPU, hPc⟩, hPT, _⟩
      exact ⟨hPT, hPc⟩
    · rintro ⟨hPT, hPc⟩
      exact ⟨⟨hPT.trans hTU, hPc⟩, hPT, hPT⟩
  rw [hEq, Finset.card_powersetCard]
  have hsucc : k - 1 + 1 = k := by omega
  rw [hT]
  simpa [Nat.sub_add_cancel hk] using (Nat.choose_succ_self_right (k - 1))

/-- Exact collision double count: the second moment over shadow prefixes is
the sum, over ordered link-member pairs, of their common shadow facets. -/
theorem starLayerPairwiseCollision_identity
    (U : Edge α) (k : ℕ) (A B : Family α) :
    (∑ P ∈ U.powersetCard (k - 1),
      starLayerPrefixDegree A P * starLayerPrefixDegree B P) =
      ∑ T ∈ A, ∑ S ∈ B,
        ((U.powersetCard (k - 1)).filter fun P => P ⊆ T ∧ P ⊆ S).card := by
  classical
  let Ps := U.powersetCard (k - 1)
  have hProduct : ∀ P ∈ Ps,
      starLayerPrefixDegree A P * starLayerPrefixDegree B P =
        ∑ T ∈ A, ∑ S ∈ B, if P ⊆ T ∧ P ⊆ S then (1 : ℕ) else 0 := by
    intro P hP
    let X := A.filter fun T => P ⊆ T
    let Y := B.filter fun T => P ⊆ T
    have hXY : X ×ˢ Y = (A ×ˢ B).filter fun TS => P ⊆ TS.1 ∧ P ⊆ TS.2 := by
      ext ⟨T, S⟩
      simp [X, Y, Finset.mem_filter, Finset.mem_product]; aesop
    rw [starLayerPrefixDegree, starLayerPrefixDegree]
    change X.card * Y.card = _
    rw [← Finset.card_product, hXY, Finset.card_filter]
    exact Finset.sum_product' A B
      (fun T S => if P ⊆ T ∧ P ⊆ S then (1 : ℕ) else 0)
  calc
    (∑ P ∈ Ps, starLayerPrefixDegree A P * starLayerPrefixDegree B P) =
        ∑ P ∈ Ps, ∑ T ∈ A, ∑ S ∈ B,
          if P ⊆ T ∧ P ⊆ S then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro P hP
      exact hProduct P hP
    _ = ∑ T ∈ A, ∑ S ∈ B, ∑ P ∈ Ps,
          if P ⊆ T ∧ P ⊆ S then (1 : ℕ) else 0 := by
      calc
        (∑ P ∈ Ps, ∑ T ∈ A, ∑ S ∈ B,
            if P ⊆ T ∧ P ⊆ S then (1 : ℕ) else 0) =
          ∑ T ∈ A, ∑ P ∈ Ps, ∑ S ∈ B,
            if P ⊆ T ∧ P ⊆ S then (1 : ℕ) else 0 := Finset.sum_comm
        _ = ∑ T ∈ A, ∑ S ∈ B, ∑ P ∈ Ps,
            if P ⊆ T ∧ P ⊆ S then (1 : ℕ) else 0 := by
          apply Finset.sum_congr rfl
          intro T hT
          exact Finset.sum_comm
    _ = ∑ T ∈ A, ∑ S ∈ B,
          ((U.powersetCard (k - 1)).filter fun P => P ⊆ T ∧ P ⊆ S).card := by
      apply Finset.sum_congr rfl
      intro T hT
      apply Finset.sum_congr rfl
      intro S hS
      exact (Finset.card_filter
        (fun P => P ⊆ T ∧ P ⊆ S) Ps).symm

/-- The IV.1.2 star-fiber argument when codegree control is known only away
from the fixed prefix. Prefix vertices have empty tail fibers by definition. -/
theorem commonPrefixTails_card_le_vertex_degree_off_prefix
    {H : Family α} {W Y Z A : Edge α} {t D : ℕ}
    (hH : Admissible H) (hY : Y.Nonempty) (hZ : Z.Nonempty)
    (hYZ : Disjoint Y Z) (ht : 1 ≤ t)
    (hA : A ∈ commonPrefixTails H W Y Z t)
    (hCap : ∀ x : α, x ∉ Y →
      (H.filter fun E => Y ∪ {x} ⊆ E).card ≤ D) :
    (commonPrefixTails H W Y Z t).card ≤ t * D := by
  have hU : Uniform t (commonPrefixTails H W Y Z t) := by
    intro P hP
    exact (mem_commonPrefixTails.mp hP).2.1
  apply intersecting_card_le_vertex_cap hU
    (commonPrefixTails_intersecting hH hY hZ hYZ ht) hA ht
  intro x
  by_cases hxY : x ∈ Y
  · have hEmpty :
    (commonPrefixTails H W Y Z t).filter (fun P => x ∈ P) = ∅ := by
      ext P
      constructor
      · intro h
        obtain ⟨hP, hxP⟩ := Finset.mem_filter.mp h
        exact False.elim ((Finset.disjoint_left.mp
          (mem_commonPrefixTails.mp hP).2.2.1) hxP
          (Finset.mem_union_left Z hxY))
      · intro h
        simp at h
    simp [hEmpty]
  · simpa only [Finset.singleton_subset_iff] using
      (commonPrefixTails_fiber_le_parent_degree
        (H := H) (W := W) (Y := Y) (Z := Z) (S := ({x} : Edge α))
        (t := t)).trans (hCap x hxY)

/-- The equal-completion cell of two star layers has size at most
`(r-1)D₂`, by the IV.1.2 intersecting-cell bound. -/
theorem starLayerEqualCompletionCell_card_le
    {H : Family α} {U : Edge α} {z w : α} {r D₂ : ℕ}
    (hH : Admissible H) (hzw : z ≠ w)
    (_hzU : z ∉ U) (_hwU : w ∉ U) (hr : 2 ≤ r)
    (hD₂ : ∀ S : Edge α, S.card = 2 →
      (H.filter fun E => S ⊆ E).card ≤ D₂) :
    (commonPrefixTails H U ({z} : Edge α) {w} (r - 1)).card ≤
      (r - 1) * D₂ := by
  classical
  let Y : Edge α := {z}
  let Z : Edge α := {w}
  have hYZ : Disjoint Y Z := by
    exact Finset.disjoint_singleton.mpr hzw
  have hY : Y.Nonempty := by simp [Y]
  have hZ : Z.Nonempty := by simp [Z]
  have ht : 1 ≤ r - 1 := by omega
  let C := commonPrefixTails H U Y Z (r - 1)
  by_cases hEmpty : C = ∅
  · change C.card ≤ (r - 1) * D₂
    simp [hEmpty]
  · obtain ⟨A, hA⟩ : C.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
    have hCap : ∀ a : α, a ∉ Y →
        (H.filter fun E => Y ∪ {a} ⊆ E).card ≤ D₂ := by
      intro a haY
      have hCard : (Y ∪ {a}).card = 2 := by
        rw [Finset.card_union_of_disjoint]
        · simp [Y]
        · exact Finset.disjoint_singleton_right.mpr haY
      exact hD₂ (Y ∪ {a}) hCard
    simpa [C, Y, Z] using
      (commonPrefixTails_card_le_vertex_degree_off_prefix
        hH hY hZ hYZ ht hA hCap)

/-- The common `(r-2)`-tail cell for two star edges with distinct
completions. -/
def starLayerCrossCell (H : Family α) (U : Edge α)
    (z w x y : α) (r : ℕ) : Family α :=
  commonPrefixTails H U ({z, x} : Edge α) ({w, y} : Edge α) (r - 2)

/-- Concrete IV.1.2 bound for a cross-completion cell of two star layers.
The three-codegree bound is required only on three-sets, matching D₃(H). -/
theorem starLayerCrossCell_card_le
    {H : Family α} {U : Edge α} {z w x y : α} {r D₃ : ℕ}
    (hH : Admissible H)
    (hzw : z ≠ w) (hxy : x ≠ y)
    (hzU : z ∉ U) (hwU : w ∉ U)
    (hxU : x ∈ U) (hyU : y ∈ U)
    (hr : 4 ≤ r)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D₃) :
    (starLayerCrossCell H U z w x y r).card ≤ (r - 2) * D₃ := by
  classical
  let Y : Edge α := {z, x}
  let Z : Edge α := {w, y}
  have hzx : z ≠ x := by
    intro heq
    exact hzU (heq ▸ hxU)
  have hwy : w ≠ y := by
    intro heq
    exact hwU (heq ▸ hyU)
  have hYcard : Y.card = 2 := Finset.card_pair hzx
  have hZcard : Z.card = 2 := Finset.card_pair hwy
  have hYZ : Disjoint Y Z := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    simp only [Y, Z, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact hzw rfl
    · exact hzU (by simpa using hyU)
    · exact hwU (by simpa using hxU)
    · exact hxy rfl
  have hY : Y.Nonempty := by simp [Y]
  have hZ : Z.Nonempty := by simp [Z]
  have ht : 1 ≤ r - 2 := by omega
  let C := commonPrefixTails H U Y Z (r - 2)
  by_cases hEmpty : C = ∅
  · change C.card ≤ (r - 2) * D₃
    simp [hEmpty]
  · obtain ⟨A, hA⟩ : C.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
    have hCap : ∀ a : α, a ∉ Y →
        (H.filter fun E => Y ∪ {a} ⊆ E).card ≤ D₃ := by
      intro a haY
      have hCard : (Y ∪ {a}).card = 3 := by
        rw [Finset.card_union_of_disjoint]
        · simp [hYcard]
        · exact Finset.disjoint_singleton_right.mpr haY
      exact hD₃ (Y ∪ {a}) hCard
    exact commonPrefixTails_card_le_vertex_degree_off_prefix
      hH hY hZ hYZ ht hA hCap

/-- Two distinct actual star-link members sharing an `(r-2)`-facet have
unique completions outside that facet, and the facet lies in the fixed
cross-completion common-prefix cell. -/
theorem distinct_star_link_members_land_in_cross_cell
    {H : Family α} {U T S P : Edge α} {z w : α} {r : ℕ}
    (hzU : z ∉ U) (hwU : w ∉ U)
    (hT : T ∈ actualStarLink H U z r)
    (hS : S ∈ actualStarLink H U w r)
    (hr : 4 ≤ r)
    (hP : P ∈ U.powersetCard (r - 2))
    (hPT : P ⊆ T) (hPS : P ⊆ S) (hTS : T ≠ S) :
    ∃ x y : α, x ∈ T \ P ∧ y ∈ S \ P ∧ x ≠ y ∧
      P ∈ starLayerCrossCell H U z w x y r := by
  classical
  have hTcard : T.card = r - 1 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).2
  have hScard : S.card = r - 1 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1).2
  have hPcard : P.card = r - 2 := (Finset.mem_powersetCard.mp hP).2
  have hTdiff : (T \ P).card = 1 := by
    rw [Finset.card_sdiff_of_subset hPT, hTcard, hPcard]
    omega
  have hSdiff : (S \ P).card = 1 := by
    rw [Finset.card_sdiff_of_subset hPS, hScard, hPcard]
    omega
  obtain ⟨x, hxEq⟩ := Finset.card_eq_one.mp hTdiff
  obtain ⟨y, hyEq⟩ := Finset.card_eq_one.mp hSdiff
  have hx : x ∈ T \ P := by rw [hxEq]; simp
  have hy : y ∈ S \ P := by rw [hyEq]; simp
  have hTrep : T = P ∪ {x} := by
    have h := Finset.union_sdiff_of_subset hPT
    rw [hxEq] at h
    exact h.symm
  have hSrep : S = P ∪ {y} := by
    have h := Finset.union_sdiff_of_subset hPS
    rw [hyEq] at h
    exact h.symm
  have hxy : x ≠ y := by
    intro hEq
    apply hTS
    rw [hTrep, hSrep, hEq]
  have hxU : x ∈ U :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).1
      ((Finset.mem_sdiff.mp hx).1)
  have hyU : y ∈ U :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1).1
      ((Finset.mem_sdiff.mp hy).1)
  have hxNotP : x ∉ P := (Finset.mem_sdiff.mp hx).2
  have hyNotP : y ∉ P := (Finset.mem_sdiff.mp hy).2
  have hYedge : ({z, x} : Edge α) ∪ P = insert z T := by
    ext a
    simp [hTrep]
  have hZedge : ({w, y} : Edge α) ∪ P = insert w S := by
    ext a
    simp [hSrep]
  have hPdata := Finset.mem_powersetCard.mp hP
  have hzNotP : z ∉ P := fun hzP => hzU (hPdata.1 hzP)
  have hwNotP : w ∉ P := fun hwP => hwU (hPdata.1 hwP)
  have hcell : P ∈ commonPrefixTails H U
      ({z, x} : Edge α) ({w, y} : Edge α) (r - 2) := by
    apply mem_commonPrefixTails.mpr
    refine ⟨hPdata.1, hPcard, ?_, ?_, ?_⟩
    · apply Finset.disjoint_left.mpr
      intro a haP haRoot
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at haRoot
      rcases haRoot with (rfl | rfl) | (rfl | rfl)
      · exact hzNotP haP
      · exact hxNotP haP
      · exact hwNotP haP
      · exact hyNotP haP
    · rw [hYedge]
      exact (Finset.mem_filter.mp hT).2
    · rw [hZedge]
      exact (Finset.mem_filter.mp hS).2
  exact ⟨x, y, hx, hy, hxy, by simpa [starLayerCrossCell] using hcell⟩

end JSP523.Rank5
