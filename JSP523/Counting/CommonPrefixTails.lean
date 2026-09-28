import JSP523.Counting.IntersectingCovers
import JSP523.Counting.PrefixCommonSystem
import Mathlib.Data.Finset.SDiff

/-!
# Common tails of disjoint prefixes at arbitrary rank

This module proves the intersecting-cell statement preceding Lemma IV.1.1
and the codegree consequences (IV.1.2)–(IV.1.3) of
`paper/proof.pdf`.
The degree bounds below are expressed through the actual parent family,
with `D` supplied as a uniform upper bound on its indicated fibers.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

/-- Tails of size `t` completing two disjoint prefixes in the same parent. -/
def commonPrefixTails (H : Family α) (W Y Z : Edge α) (t : ℕ) : Family α :=
  (W.powersetCard t).filter fun P =>
    Disjoint P (Y ∪ Z) ∧ Y ∪ P ∈ H ∧ Z ∪ P ∈ H

theorem mem_commonPrefixTails
    {H : Family α} {W Y Z P : Edge α} {t : ℕ} :
    P ∈ commonPrefixTails H W Y Z t ↔
      P ⊆ W ∧ P.card = t ∧ Disjoint P (Y ∪ Z) ∧
        Y ∪ P ∈ H ∧ Z ∪ P ∈ H := by
  simp only [commonPrefixTails, Finset.mem_filter,
    Finset.mem_powersetCard]
  tauto

/-- The all-rank common-tail cell is intersecting by the four-piece
forbidden switch. -/
theorem commonPrefixTails_intersecting
    {H : Family α} {W Y Z : Edge α} {t : ℕ}
    (hH : Admissible H) (hY : Y.Nonempty) (hZ : Z.Nonempty)
    (hYZ : Disjoint Y Z) (ht : 1 ≤ t) :
    PairwiseIntersecting (commonPrefixTails H W Y Z t) := by
  intro P Q hP hQ _hNe
  by_contra hEmpty
  have hPQ : Disjoint P Q := Finset.disjoint_iff_inter_eq_empty.mpr
    (Finset.not_nonempty_iff_eq_empty.mp hEmpty)
  obtain ⟨_, hPcard, hPdisj, hYP, hZP⟩ :=
    mem_commonPrefixTails.mp hP
  obtain ⟨_, hQcard, hQdisj, hYQ, hZQ⟩ :=
    mem_commonPrefixTails.mp hQ
  have hPnon : P.Nonempty := Finset.card_pos.mp (by omega)
  have hQnon : Q.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨hPY, hPZ⟩ := Finset.disjoint_union_right.mp hPdisj
  obtain ⟨hQY, hQZ⟩ := Finset.disjoint_union_right.mp hQdisj
  exact hH hYP hZQ hYQ hZP
    (prefix_switch_forbidden hY hZ hPnon hQnon hYZ
      hPY hPZ hQY hQZ hPQ)

/-- A tail fiber maps injectively to the actual parent edges containing
its fixed prefix and local set `S`. This justifies replacing cell degrees
by parent codegrees in (IV.1.2)–(IV.1.3). -/
theorem commonPrefixTails_fiber_le_parent_degree
    {H : Family α} {W Y Z S : Edge α} {t : ℕ} :
    ((commonPrefixTails H W Y Z t).filter fun P => S ⊆ P).card ≤
      (H.filter fun E => Y ∪ S ⊆ E).card := by
  classical
  let C := (commonPrefixTails H W Y Z t).filter fun P => S ⊆ P
  let D := H.filter fun E => Y ∪ S ⊆ E
  let f : Edge α → Edge α := fun P => Y ∪ P
  have hmap : ∀ P ∈ C, f P ∈ D := by
    intro P hP
    obtain ⟨hCell, hSP⟩ := Finset.mem_filter.mp hP
    have hYP := (mem_commonPrefixTails.mp hCell).2.2.2.1
    exact Finset.mem_filter.mpr ⟨hYP, by
      intro x hx
      rcases Finset.mem_union.mp hx with hxY | hxS
      · exact Finset.mem_union_left P hxY
      · exact Finset.mem_union_right Y (hSP hxS)⟩
  have hinj : Set.InjOn f (↑C : Set (Edge α)) := by
    intro P hP Q hQ hEq
    have hYP := (mem_commonPrefixTails.mp (Finset.mem_filter.mp hP).1).2.2.1
    have hYQ := (mem_commonPrefixTails.mp (Finset.mem_filter.mp hQ).1).2.2.1
    have hDisjP : Disjoint Y P :=
      (Finset.disjoint_union_right.mp hYP).1.symm
    have hDisjQ : Disjoint Y Q :=
      (Finset.disjoint_union_right.mp hYQ).1.symm
    calc
      P = (Y ∪ P) \ Y := (Finset.union_sdiff_cancel_left hDisjP).symm
      _ = (Y ∪ Q) \ Y := by
        change Y ∪ P = Y ∪ Q at hEq
        rw [hEq]
      _ = Q := Finset.union_sdiff_cancel_left hDisjQ
  exact Finset.card_le_card_of_injOn f hmap hinj

/-- Vertex-codegree form of (IV.1.2), with the actual parent family in
the codegree fibers. -/
theorem commonPrefixTails_card_le_vertex_degree
    {H : Family α} {W Y Z A : Edge α} {t D : ℕ}
    (hH : Admissible H) (hY : Y.Nonempty) (hZ : Z.Nonempty)
    (hYZ : Disjoint Y Z) (ht : 1 ≤ t)
    (hA : A ∈ commonPrefixTails H W Y Z t)
    (hCap : ∀ x : α,
      (H.filter fun E => Y ∪ {x} ⊆ E).card ≤ D) :
    (commonPrefixTails H W Y Z t).card ≤ t * D := by
  apply intersecting_card_le_vertex_cap
    (fun P hP => (mem_commonPrefixTails.mp hP).2.1)
    (commonPrefixTails_intersecting hH hY hZ hYZ ht) hA ht
  intro x
  simpa only [Finset.singleton_subset_iff] using
    (commonPrefixTails_fiber_le_parent_degree
    (H := H) (W := W) (Y := Y) (Z := Z) (S := ({x} : Edge α))
    (t := t)).trans (hCap x)

/-- Pair-codegree form of (IV.1.3) when the common-tail cell has empty
total intersection. -/
theorem commonPrefixTails_card_le_pair_degree_no_center
    {H : Family α} {W Y Z A : Edge α} {t D : ℕ}
    (hH : Admissible H) (hY : Y.Nonempty) (hZ : Z.Nonempty)
    (hYZ : Disjoint Y Z) (ht : 1 ≤ t)
    (hA : A ∈ commonPrefixTails H W Y Z t)
    (hN : NoGlobalCenter (commonPrefixTails H W Y Z t))
    (hCap : ∀ Q : Edge α, Q.card = 2 →
      (H.filter fun E => Y ∪ Q ⊆ E).card ≤ D) :
    (commonPrefixTails H W Y Z t).card ≤ t * t * D := by
  apply intersecting_card_le_pair_cap
    (fun P hP => (mem_commonPrefixTails.mp hP).2.1)
    (commonPrefixTails_intersecting hH hY hZ hYZ ht) hN hA ht
  intro Q hQ
  exact (commonPrefixTails_fiber_le_parent_degree
    (H := H) (W := W) (Y := Y) (Z := Z) (S := Q) (t := t)).trans
      (hCap Q hQ)

/-- Pair-codegree form of (IV.1.3) when two vertices belong to every
common tail. One pair fiber covers the cell. -/
theorem commonPrefixTails_card_le_pair_degree_common_pair
    {H : Family α} {W Y Z : Edge α} {t D : ℕ} {x y : α}
    (hxy : x ≠ y)
    (hx : ∀ P ∈ commonPrefixTails H W Y Z t, x ∈ P)
    (hy : ∀ P ∈ commonPrefixTails H W Y Z t, y ∈ P)
    (hCap : ∀ Q : Edge α, Q.card = 2 →
      (H.filter fun E => Y ∪ Q ⊆ E).card ≤ D) :
    (commonPrefixTails H W Y Z t).card ≤ D := by
  apply intersecting_card_le_common_pair_cap hxy hx hy
  intro Q hQ
  exact (commonPrefixTails_fiber_le_parent_degree
    (H := H) (W := W) (Y := Y) (Z := Z) (S := Q) (t := t)).trans
      (hCap Q hQ)

end JSP523
