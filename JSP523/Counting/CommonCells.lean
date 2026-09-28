import JSP523.Counting.IntersectingCovers
import JSP523.Counting.PrefixCommonSystem

/-!
# Common completion cells at arbitrary rank

The family `commonCell` is the finite version of `C_s(P,Q;F)` in
`paper/proof.pdf`, equation (IV.1.1), with completion size recorded as
`k = r - s`. The crossed-completion argument proves that it is
intersecting. The following bounds apply Lemma IV.1.1 to the actual
cell and are the finite covering counts behind (IV.1.2)–(IV.1.3).
The fiber injection identifies each completion with its edge through
the first root, giving the corresponding parent-codegree comparison.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

/-- Common `k`-element completions of two disjoint roots inside `U`.
The members are disjoint from both roots and complete each root to an
edge of `H`, as in (IV.1.1). -/
def commonCell (H : Family α) (U P Q : Edge α) (k : ℕ) : Family α :=
  (U.powersetCard k).filter fun A =>
    Disjoint A (P ∪ Q) ∧ P ∪ A ∈ H ∧ Q ∪ A ∈ H

/-- Membership in the common completion cell of (IV.1.1). -/
theorem mem_commonCell {H : Family α} {U P Q A : Edge α} {k : ℕ} :
    A ∈ commonCell H U P Q k ↔
      A ⊆ U ∧ A.card = k ∧ Disjoint A (P ∪ Q) ∧
        P ∪ A ∈ H ∧ Q ∪ A ∈ H := by
  simp only [commonCell, Finset.mem_filter, Finset.mem_powersetCard]
  tauto

/-- The common cell has completion uniformity `k`. -/
theorem commonCell_uniform (H : Family α) (U P Q : Edge α) (k : ℕ) :
    Uniform k (commonCell H U P Q k) := by
  intro A hA
  exact (mem_commonCell.mp hA).2.1

/-- The crossed-completion assertion following (IV.1.1): a common
cell of two disjoint nonempty roots is intersecting in an admissible
parent family. -/
theorem commonCell_intersecting
    {H : Family α} {U P Q : Edge α} {k : ℕ}
    (hH : Admissible H)
    (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hPQ : Disjoint P Q) (hk : 0 < k) :
    PairwiseIntersecting (commonCell H U P Q k) := by
  intro A B hA hB _hNe
  by_contra hEmpty
  have hAB : Disjoint A B := Finset.disjoint_iff_inter_eq_empty.mpr
    (Finset.not_nonempty_iff_eq_empty.mp hEmpty)
  obtain ⟨_, hAcard, hAavoid, hPA, hQA⟩ := mem_commonCell.mp hA
  obtain ⟨_, hBcard, hBavoid, hPB, hQB⟩ := mem_commonCell.mp hB
  have hAnon : A.Nonempty := Finset.card_pos.mp (by omega)
  have hBnon : B.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨hAP, hAQ⟩ := Finset.disjoint_union_right.mp hAavoid
  obtain ⟨hBP, hBQ⟩ := Finset.disjoint_union_right.mp hBavoid
  exact hH hPA hQB hPB hQA
    (prefix_switch_forbidden hP hQ hAnon hBnon hPQ
      hAP hAQ hBP hBQ hAB)

/-- The injection used after Lemma IV.1.1: every cell member containing
`R` determines a distinct parent edge containing `P ∪ R`. This is the
finite bridge from a cell fiber to the codegrees in (IV.1.2)–(IV.1.3). -/
theorem commonCell_fiber_le_parent_codegree
    (H : Family α) (U P Q R : Edge α) (k : ℕ) :
    ((commonCell H U P Q k).filter fun A => R ⊆ A).card ≤
      (H.filter fun E => P ∪ R ⊆ E).card := by
  classical
  let C := (commonCell H U P Q k).filter fun A => R ⊆ A
  let f : Edge α → Edge α := fun A => P ∪ A
  have hMap : ∀ A ∈ C, f A ∈ H.filter (fun E => P ∪ R ⊆ E) := by
    intro A hA
    obtain ⟨hAC, hRA⟩ := Finset.mem_filter.mp hA
    obtain ⟨_, _, _, hPA, _⟩ := mem_commonCell.mp hAC
    apply Finset.mem_filter.mpr
    refine ⟨hPA, ?_⟩
    intro x hx
    rcases Finset.mem_union.mp hx with hxP | hxR
    · exact Finset.mem_union_left A hxP
    · exact Finset.mem_union_right P (hRA hxR)
  have hInj : Set.InjOn f (↑C : Set (Edge α)) := by
    intro A hA B hB hEq
    have hAC : A ∈ commonCell H U P Q k := (Finset.mem_filter.mp hA).1
    have hBC : B ∈ commonCell H U P Q k := (Finset.mem_filter.mp hB).1
    have hAavoid : Disjoint A P :=
      (Finset.disjoint_union_right.mp (mem_commonCell.mp hAC).2.2.1).1
    have hBavoid : Disjoint B P :=
      (Finset.disjoint_union_right.mp (mem_commonCell.mp hBC).2.2.1).1
    change P ∪ A = P ∪ B at hEq
    ext x
    constructor
    · intro hxA
      have hxNotP : x ∉ P := fun hxP =>
        (Finset.disjoint_left.mp hAavoid) hxA hxP
      have hxUnion : x ∈ P ∪ B := hEq ▸ Finset.mem_union_right P hxA
      rcases Finset.mem_union.mp hxUnion with hxP | hxB
      · exact False.elim (hxNotP hxP)
      · exact hxB
    · intro hxB
      have hxNotP : x ∉ P := fun hxP =>
        (Finset.disjoint_left.mp hBavoid) hxB hxP
      have hxUnion : x ∈ P ∪ A := hEq.symm ▸ Finset.mem_union_right P hxB
      rcases Finset.mem_union.mp hxUnion with hxP | hxA
      · exact False.elim (hxNotP hxP)
      · exact hxA
  exact Finset.card_le_card_of_injOn f hMap hInj

/-- A codegree cap is needed only for sets disjoint from the first root:
if `R` meets `P`, no common completion can contain `R`. -/
theorem commonCell_fiber_le_disjoint_parent_cap
    (H : Family α) (U P Q R : Edge α) (k D : ℕ)
    (hD : Disjoint R P →
      (H.filter fun E => P ∪ R ⊆ E).card ≤ D) :
    ((commonCell H U P Q k).filter fun A => R ⊆ A).card ≤ D := by
  by_cases hRP : Disjoint R P
  · exact (commonCell_fiber_le_parent_codegree H U P Q R k).trans
      (hD hRP)
  · have hEmpty :
        (commonCell H U P Q k).filter (fun A => R ⊆ A) = ∅ := by
      ext A
      constructor
      · intro hA
        obtain ⟨hAC, hRA⟩ := Finset.mem_filter.mp hA
        have hAP : Disjoint A P :=
          (Finset.disjoint_union_right.mp (mem_commonCell.mp hAC).2.2.1).1
        have hRP' : Disjoint R P :=
          Finset.disjoint_left.mpr (fun x hxR hxP =>
            (Finset.disjoint_left.mp hAP) (hRA hxR) hxP)
        exact False.elim (hRP hRP')
      · intro hA
        simp at hA
    simp [hEmpty]

/-- Cell-level form of (IV.1.2): a vertex-fiber bound `D` gives
`|C_s(P,Q;F)| ≤ k D`. -/
theorem commonCell_card_le_vertex_fiber
    {H : Family α} {U P Q : Edge α} {k D : ℕ}
    (hH : Admissible H)
    (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hPQ : Disjoint P Q) (hk : 0 < k)
    (hD : ∀ x : α,
      ((commonCell H U P Q k).filter fun A => x ∈ A).card ≤ D) :
    (commonCell H U P Q k).card ≤ k * D :=
  intersecting_card_le_vertex_degree
    (commonCell_uniform H U P Q k)
    (commonCell_intersecting hH hP hQ hPQ hk) hk hD

/-- Equation (IV.1.2), expressed with an explicit parent codegree cap
for each `(P ∪ {x})` with `x ∉ P`. -/
theorem commonCell_card_le_parent_vertex_codegree
    {H : Family α} {U P Q : Edge α} {k D : ℕ}
    (hH : Admissible H)
    (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hPQ : Disjoint P Q) (hk : 0 < k)
    (hD : ∀ x : α, x ∉ P →
      (H.filter fun E => P ∪ {x} ⊆ E).card ≤ D) :
    (commonCell H U P Q k).card ≤ k * D := by
  apply commonCell_card_le_vertex_fiber hH hP hQ hPQ hk
  intro x
  have hCap : Disjoint ({x} : Edge α) P →
      (H.filter fun E => P ∪ {x} ⊆ E).card ≤ D := by
    intro hDisj
    apply hD x
    intro hxP
    exact (Finset.disjoint_left.mp hDisj) (by simp) hxP
  simpa only [Finset.singleton_subset_iff] using
    (commonCell_fiber_le_disjoint_parent_cap H U P Q {x} k D hCap)

/-- Cell-level form of the empty-total-intersection case of
(IV.1.3): a pair-fiber bound `D` gives `|C_s(P,Q;F)| ≤ k² D`. -/
theorem commonCell_card_le_pair_fiber
    {H : Family α} {U P Q : Edge α} {k D : ℕ}
    (hH : Admissible H)
    (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hPQ : Disjoint P Q) (hk : 2 ≤ k)
    (hNoCenter : NoGlobalCenter (commonCell H U P Q k))
    (hD : ∀ R : Edge α, R.card = 2 →
      ((commonCell H U P Q k).filter fun A => R ⊆ A).card ≤ D) :
    (commonCell H U P Q k).card ≤ k * k * D :=
  intersecting_card_le_pair_degree
    (commonCell_uniform H U P Q k)
    (commonCell_intersecting hH hP hQ hPQ (by omega))
    hNoCenter hk hD

/-- Empty-total-intersection case of (IV.1.3), with the parent
`(s+2)`-codegree cap written for each pair disjoint from `P`. -/
theorem commonCell_card_le_parent_pair_codegree
    {H : Family α} {U P Q : Edge α} {k D : ℕ}
    (hH : Admissible H)
    (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hPQ : Disjoint P Q) (hk : 2 ≤ k)
    (hNoCenter : NoGlobalCenter (commonCell H U P Q k))
    (hD : ∀ R : Edge α, R.card = 2 → Disjoint R P →
      (H.filter fun E => P ∪ R ⊆ E).card ≤ D) :
    (commonCell H U P Q k).card ≤ k * k * D := by
  apply commonCell_card_le_pair_fiber hH hP hQ hPQ hk hNoCenter
  intro R hR
  exact commonCell_fiber_le_disjoint_parent_cap H U P Q R k D
    (hD R hR)

/-- Two-common-vertex case of (IV.1.3): one pair star suffices, so the
same parent pair-codegree cap bounds the entire cell by `D`. -/
theorem commonCell_card_le_parent_pair_codegree_of_two_centers
    {H : Family α} {U P Q : Edge α} {k D : ℕ} {x y : α}
    (hxy : x ≠ y)
    (hCenters : ∀ A ∈ commonCell H U P Q k, x ∈ A ∧ y ∈ A)
    (hD : ∀ R : Edge α, R.card = 2 → Disjoint R P →
      (H.filter fun E => P ∪ R ⊆ E).card ≤ D) :
    (commonCell H U P Q k).card ≤ D := by
  apply intersecting_card_le_pair_degree_of_two_centers hxy hCenters
  intro R hR
  exact commonCell_fiber_le_disjoint_parent_cap H U P Q R k D
    (hD R hR)

end JSP523
