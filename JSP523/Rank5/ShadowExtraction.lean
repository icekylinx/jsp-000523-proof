import JSP523.Counting.IntersectingCovers
import JSP523.Counting.CommonPrefixTails
import JSP523.Counting.StarDecomposition
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite shadow allocation for Part IV

The elementary ledger in §IV.5.2 counts links of deleted vertices while
retaining the shadow of the surviving family.  The first lemmas below are
finite union-and-overlap statements, with no asymptotic notation.
-/

namespace JSP523.Rank5

variable {ι β : Type*} [DecidableEq ι] [DecidableEq β]

/-- Ordered overlap budget. It is deliberately allowed to count each
unordered collision twice, which is harmless for the asymptotic ledger. -/
def orderedOverlap (X : Finset ι) (A : ι → Finset β) : ℕ :=
  ∑ x ∈ X, ∑ y ∈ X.erase x, (A x ∩ A y).card

omit [DecidableEq ι] in
private theorem intersection_biUnion_card_le_sum
    (S : Finset ι) (A : ι → Finset β) (B : Finset β) :
    (B ∩ S.biUnion A).card ≤ ∑ y ∈ S, (B ∩ A y).card := by
  have hEq : B ∩ S.biUnion A = S.biUnion (fun y => B ∩ A y) := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_biUnion]
    tauto
  rw [hEq]
  exact Finset.card_biUnion_le

private theorem orderedOverlap_insert
    (S : Finset ι) (A : ι → Finset β) (a : ι) (ha : a ∉ S) :
    orderedOverlap (insert a S) A = orderedOverlap S A +
      2 * (∑ y ∈ S, (A a ∩ A y).card) := by
  classical
  unfold orderedOverlap
  simp only [Finset.sum_insert ha, Finset.erase_insert ha]
  have hInner : ∀ x ∈ S,
      ((insert a S).erase x).sum (fun y => (A x ∩ A y).card) =
        (S.erase x).sum (fun y => (A x ∩ A y).card) +
          (A x ∩ A a).card := by
    intro x hx
    have hax : a ≠ x := by
      intro h
      exact ha (h ▸ hx)
    rw [Finset.erase_insert_of_ne hax]
    rw [Finset.sum_insert (by simp [ha])]
    omega
  have hS :
      (∑ x ∈ S, ∑ y ∈ (insert a S).erase x, (A x ∩ A y).card) =
      (∑ x ∈ S, ∑ y ∈ S.erase x, (A x ∩ A y).card) +
        ∑ x ∈ S, (A a ∩ A x).card := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [hInner x hx, Finset.inter_comm]
  rw [hS]
  omega

/-- The total sizes of finite fibers are controlled by their union and
their ordered pairwise overlaps. -/
theorem sum_card_le_union_add_orderedOverlap
    (X : Finset ι) (A : ι → Finset β) :
    (∑ x ∈ X, (A x).card) ≤
      (X.biUnion A).card + orderedOverlap X A := by
  classical
  induction X using Finset.induction_on with
  | empty => simp [orderedOverlap]
  | @insert a S ha ih =>
    have hInt := intersection_biUnion_card_le_sum S A (A a)
    have hUnion := Finset.card_union_add_card_inter (A a) (S.biUnion A)
    have hOverlap := orderedOverlap_insert S A a ha
    simp only [Finset.sum_insert ha, Finset.biUnion_insert] at *
    rw [hOverlap]
    omega

/-- An ambient family can hold the union of the vertex links and a
distinguished shadow. Every repeated link use and every link-shadow
collision appears explicitly on the right. -/
theorem shadow_allocation_ledger
    (X : Finset ι) (U S : Finset β) (A : ι → Finset β)
    (hS : S ⊆ U) (hA : ∀ x ∈ X, A x ⊆ U) :
    (∑ x ∈ X, (A x).card) + S.card ≤
      U.card + (∑ x ∈ X, (A x ∩ S).card) +
        orderedOverlap X A := by
  classical
  have hUnionSub : X.biUnion A ∪ S ⊆ U := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨x, hx, hzx⟩ := Finset.mem_biUnion.mp hz
      exact hA x hx hzx
    · exact hS hz
  have hInt := intersection_biUnion_card_le_sum X A S
  have hUnion := Finset.card_union_add_card_inter (X.biUnion A) S
  have hFibers := sum_card_le_union_add_orderedOverlap X A
  have hCap := Finset.card_le_card hUnionSub
  have hInt' : (X.biUnion A ∩ S).card ≤
      ∑ x ∈ X, (A x ∩ S).card := by
    simpa only [Finset.inter_comm S] using hInt
  omega

/-- A direct finite vertex-cover estimate for an intersecting uniform
family on `W`. The slightly coarse `|W| choose (k-1)` fiber size keeps the
bound convenient for finite extraction estimates. -/
theorem intersecting_card_le_ground_choose
    {T : Family β} {W : Edge β} {k : ℕ}
    (hTW : T ⊆ W.powersetCard k)
    (hI : PairwiseIntersecting T) (hk : 1 ≤ k) :
    T.card ≤ k * W.card.choose (k - 1) := by
  classical
  by_cases hEmpty : T = ∅
  · simp [hEmpty]
  obtain ⟨A, hA⟩ : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
  have hU : Uniform k T := by
    intro E hE
    exact (Finset.mem_powersetCard.mp (hTW hE)).2
  apply intersecting_card_le_vertex_cap hU hI hA hk
  intro z
  have hMap : ∀ E ∈ T.filter (fun E => z ∈ E),
      E.erase z ∈ W.powersetCard (k - 1) := by
    intro E hE
    obtain ⟨hET, hzE⟩ := Finset.mem_filter.mp hE
    obtain ⟨hEW, hEcard⟩ := Finset.mem_powersetCard.mp (hTW hET)
    apply Finset.mem_powersetCard.mpr
    refine ⟨(Finset.erase_subset z E).trans hEW, ?_⟩
    have hErase := Finset.card_erase_add_one hzE
    omega
  have hInj : Set.InjOn (fun E : Edge β => E.erase z)
      (↑(T.filter fun E => z ∈ E) : Set (Edge β)) := by
    intro E hE E' hE' hEq
    have hzE := (Finset.mem_filter.mp hE).2
    have hzE' := (Finset.mem_filter.mp hE').2
    have hInsert := congrArg (insert z) hEq
    simpa only [Finset.insert_erase hzE, Finset.insert_erase hzE'] using hInsert
  have hBound : (T.filter fun E => z ∈ E).card ≤
      (W.powersetCard (k - 1)).card :=
    Finset.card_le_card_of_injOn (fun E => E.erase z) hMap hInj
  simpa only [Finset.card_powersetCard] using hBound

section EdgeLayers

variable {α : Type*} [DecidableEq α]

/-- Edges meeting the removed vertex set at least twice. -/
def multipleRemovedEdges (F : Family α) (X : Edge α) : Family α :=
  F.filter fun E => 2 ≤ (E ∩ X).card

/-- The fiber of edges whose only possible removed vertex is `x`. -/
def oneRemovedFiber (F : Family α) (W : Edge α) (x : α) : Family α :=
  F.filter fun E => x ∈ E ∧ E.erase x ⊆ W

/-- The link of the one-removed-vertex fiber, recorded as facets on `W`. -/
def oneRemovedLink (F : Family α) (W : Edge α) (x : α) : Family α :=
  (oneRemovedFiber F W x).image fun E => E.erase x

/-- The actual `(r-1)`-shadow of `K` inside `W`. -/
def shadowOn (K : Family α) (W : Edge α) (r : ℕ) : Family α :=
  (W.powersetCard (r - 1)).filter fun T => ∃ E ∈ K, T ⊆ E

/-- A cross-link between the removed center `x` and a retained parent edge
through `y`. Its members are facets on `W`. -/
def mixedCommonCell (F K : Family α) (W : Edge α) (x y : α)
    (r : ℕ) : Family α :=
  (W.powersetCard (r - 1)).filter fun T =>
    insert x T ∈ F ∧ insert y T ∈ K

private theorem mixed_cell_y_not_mem
    {F K : Family α} {W T : Edge α} {x y : α} {r : ℕ}
    (hr : 1 ≤ r) (hK : Uniform r K)
    (hT : T ∈ mixedCommonCell F K W x y r) : y ∉ T := by
  obtain ⟨hPow, _hx, hyK⟩ := Finset.mem_filter.mp hT
  have hTcard := (Finset.mem_powersetCard.mp hPow).2
  intro hy
  have hEq : insert y T = T := Finset.insert_eq_of_mem hy
  have hCard := hK hyK
  rw [hEq] at hCard
  omega

/-- The mixed cell is an intersecting subfamily of the actual common-link
cell in the admissible parent. -/
theorem mixed_common_cell_intersecting
    {F K : Family α} {W : Edge α} {x y : α} {r : ℕ}
    (hF : Admissible F) (hK : K ⊆ F) (hKU : Uniform r K)
    (hxW : x ∉ W) (hyW : y ∈ W) (hr : 2 ≤ r) :
    PairwiseIntersecting (mixedCommonCell F K W x y r) := by
  classical
  have hxy : x ≠ y := by
    intro h
    exact hxW (h ▸ hyW)
  have hSub : mixedCommonCell F K W x y r ⊆
      commonPrefixTails F W ({x} : Edge α) ({y} : Edge α) (r - 1) := by
    intro T hT
    obtain ⟨hPow, hxF, hyK⟩ := Finset.mem_filter.mp hT
    obtain ⟨hTW, hTcard⟩ := Finset.mem_powersetCard.mp hPow
    have hxT : x ∉ T := fun h => hxW (hTW h)
    have hyT := mixed_cell_y_not_mem (r := r) (by omega) hKU hT
    apply mem_commonPrefixTails.mpr
    refine ⟨hTW, hTcard, ?_, hxF, hK hyK⟩
    apply Finset.disjoint_union_right.mpr
    constructor
    · exact Finset.disjoint_singleton_right.mpr hxT
    · exact Finset.disjoint_singleton_right.mpr hyT
  have hCommon := commonPrefixTails_intersecting (W := W) hF
    (by simp) (by simp)
    (Finset.disjoint_singleton.mpr hxy) (by omega : 1 ≤ r - 1)
  intro T U hT hU hNe
  exact hCommon (hSub hT) (hSub hU) hNe

/-- The cross-link through a retained parent edge is bounded by its
actual two-point codegree. This is the local estimate in (IV.5.5). -/
theorem mixed_common_cell_card_le_pair_degree
    {F K : Family α} {W : Edge α} {x y : α} {r D : ℕ}
    (hF : Admissible F) (hK : K ⊆ F) (hKU : Uniform r K)
    (hxW : x ∉ W) (hyW : y ∈ W) (hr : 2 ≤ r)
    (hD : ∀ Q : Edge α, Q.card = 2 →
      (K.filter fun E => Q ⊆ E).card ≤ D) :
    (mixedCommonCell F K W x y r).card ≤ (r - 1) * D := by
  classical
  let C := mixedCommonCell F K W x y r
  by_cases hEmpty : C = ∅
  · change C.card ≤ (r - 1) * D
    simp [hEmpty]
  obtain ⟨A, hA⟩ : C.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
  have hU : Uniform (r - 1) C := by
    intro T hT
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).2
  have hI : PairwiseIntersecting C :=
    mixed_common_cell_intersecting hF hK hKU hxW hyW hr
  apply intersecting_card_le_vertex_cap hU hI hA (by omega)
  intro z
  by_cases hzy : z = y
  · subst z
    have hNone : (C.filter fun T => y ∈ T) = ∅ := by
      ext T
      constructor
      · intro hT
        exact False.elim ((mixed_cell_y_not_mem (r := r)
          (by omega) hKU (Finset.mem_filter.mp hT).1)
          (Finset.mem_filter.mp hT).2)
      · simp
    simp [hNone]
  · let Q : Edge α := {y, z}
    have hQcard : Q.card = 2 := Finset.card_pair (Ne.symm hzy)
    have hMap : ∀ T ∈ C.filter (fun T => z ∈ T),
        insert y T ∈ K.filter (fun E => Q ⊆ E) := by
      intro T hT
      obtain ⟨hTC, hzT⟩ := Finset.mem_filter.mp hT
      have hyK := (Finset.mem_filter.mp hTC).2.2
      apply Finset.mem_filter.mpr
      refine ⟨hyK, ?_⟩
      intro a ha
      rcases Finset.mem_insert.mp ha with hay | ha
      · exact Finset.mem_insert.mpr (Or.inl hay)
      · have haz : a = z := Finset.mem_singleton.mp ha
        exact Finset.mem_insert_of_mem (haz ▸ hzT)
    have hInj : Set.InjOn (fun T : Edge α => insert y T)
        (↑(C.filter fun T => z ∈ T) : Set (Edge α)) := by
      intro T hT U hU hEq
      have hyT := mixed_cell_y_not_mem (r := r) (by omega) hKU
        (Finset.mem_filter.mp hT).1
      have hyU := mixed_cell_y_not_mem (r := r) (by omega) hKU
        (Finset.mem_filter.mp hU).1
      have hErase := congrArg (fun E : Edge α => E.erase y) hEq
      simpa [Finset.erase_insert hyT, Finset.erase_insert hyU] using hErase
    exact (Finset.card_le_card_of_injOn (fun T => insert y T)
      hMap hInj).trans (hD Q hQcard)

theorem oneRemovedLink_subset_facets
    {F : Family α} {W : Edge α} {x : α} {r : ℕ}
    (hF : Uniform r F) :
    oneRemovedLink F W x ⊆ W.powersetCard (r - 1) := by
  intro T hT
  obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hT
  obtain ⟨hEF, hx, hErase⟩ := Finset.mem_filter.mp hE
  apply Finset.mem_powersetCard.mpr
  constructor
  · exact hErase
  · have hCard := Finset.card_erase_add_one hx
    have hUniform := hF hEF
    omega

theorem oneRemovedLink_card_eq_fiber
    (F : Family α) (W : Edge α) (x : α) :
    (oneRemovedLink F W x).card = (oneRemovedFiber F W x).card := by
  unfold oneRemovedLink
  apply Finset.card_image_iff.mpr
  intro E hE E' hE' hEq
  have hx : x ∈ E := (Finset.mem_filter.mp hE).2.1
  have hx' : x ∈ E' := (Finset.mem_filter.mp hE').2.1
  have hInsert := congrArg (insert x) hEq
  simpa only [Finset.insert_erase hx, Finset.insert_erase hx'] using hInsert

theorem oneRemovedLink_insert_mem
    {F : Family α} {W T : Edge α} {x : α}
    (hT : T ∈ oneRemovedLink F W x) : insert x T ∈ F := by
  obtain ⟨E, hE, hErase⟩ := Finset.mem_image.mp hT
  have hEF := (Finset.mem_filter.mp hE).1
  have hxE := (Finset.mem_filter.mp hE).2.1
  have hEq : insert x T = E := by
    calc
      insert x T = insert x (E.erase x) := congrArg (insert x) hErase.symm
      _ = E := Finset.insert_erase hxE
  rw [hEq]
  exact hEF

/-- Two distinct deleted centers have only an intersecting common facet
system. The finite cap is the repeated-link term in §IV.5.2. -/
theorem two_one_removed_links_overlap_bound
    {F : Family α} {W : Edge α} {x y : α} {r : ℕ}
    (hAdm : Admissible F) (hU : Uniform r F)
    (hxW : x ∉ W) (hyW : y ∉ W) (hxy : x ≠ y)
    (hr : 2 ≤ r) :
    (oneRemovedLink F W x ∩ oneRemovedLink F W y).card ≤
      (r - 1) * W.card.choose (r - 2) := by
  classical
  let C := commonPrefixTails F W ({x} : Edge α) ({y} : Edge α) (r - 1)
  have hSub : oneRemovedLink F W x ∩ oneRemovedLink F W y ⊆ C := by
    intro T hT
    obtain ⟨hxT, hyT⟩ := Finset.mem_inter.mp hT
    obtain ⟨hTW, hTcard⟩ :=
      Finset.mem_powersetCard.mp (oneRemovedLink_subset_facets hU hxT)
    have hnoX : x ∉ T := fun h => hxW (hTW h)
    have hnoY : y ∉ T := fun h => hyW (hTW h)
    apply mem_commonPrefixTails.mpr
    refine ⟨hTW, hTcard, ?_, oneRemovedLink_insert_mem hxT,
      oneRemovedLink_insert_mem hyT⟩
    exact Finset.disjoint_union_right.mpr
      ⟨Finset.disjoint_singleton_right.mpr hnoX,
        Finset.disjoint_singleton_right.mpr hnoY⟩
  have hCSub : C ⊆ W.powersetCard (r - 1) := by
    intro T hT
    have hMem := mem_commonPrefixTails.mp hT
    exact Finset.mem_powersetCard.mpr ⟨hMem.1, hMem.2.1⟩
  have hI : PairwiseIntersecting C :=
    commonPrefixTails_intersecting (W := W) hAdm
      (by simp) (by simp) (Finset.disjoint_singleton.mpr hxy)
      (by omega)
  exact (Finset.card_le_card hSub).trans
    (intersecting_card_le_ground_choose hCSub hI (by omega))

/-- The ordered collision budget of all removed-center links has the
expected quadratic dependence on the number of removed vertices. -/
theorem ordered_one_removed_overlap_bound
    {F : Family α} {W X : Edge α} {r : ℕ}
    (hAdm : Admissible F) (hU : Uniform r F)
    (hXW : ∀ x ∈ X, x ∉ W) (hr : 2 ≤ r) :
    orderedOverlap X (oneRemovedLink F W) ≤
      X.card * X.card * ((r - 1) * W.card.choose (r - 2)) := by
  classical
  let C := (r - 1) * W.card.choose (r - 2)
  have hInner : ∀ x ∈ X,
      (∑ y ∈ X.erase x,
        (oneRemovedLink F W x ∩ oneRemovedLink F W y).card) ≤
      X.card * C := by
    intro x hx
    have hEach : ∀ y ∈ X.erase x,
        (oneRemovedLink F W x ∩ oneRemovedLink F W y).card ≤ C := by
      intro y hy
      have hyX := (Finset.mem_erase.mp hy).2
      have hxy : x ≠ y := (Finset.mem_erase.mp hy).1.symm
      exact two_one_removed_links_overlap_bound hAdm hU
        (hXW x hx) (hXW y hyX) hxy hr
    have hSum := Finset.sum_le_card_nsmul (X.erase x)
      (fun y => (oneRemovedLink F W x ∩ oneRemovedLink F W y).card)
      C hEach
    have hCard : (X.erase x).card ≤ X.card :=
      Finset.card_le_card (Finset.erase_subset x X)
    calc
      _ ≤ (X.erase x).card * C := by simpa [nsmul_eq_mul] using hSum
      _ ≤ X.card * C := Nat.mul_le_mul_right C hCard
  have hSum := Finset.sum_le_card_nsmul X
    (fun x => ∑ y ∈ X.erase x,
      (oneRemovedLink F W x ∩ oneRemovedLink F W y).card)
    (X.card * C) hInner
  unfold orderedOverlap
  calc
    _ ≤ X.card * (X.card * C) := by simpa [nsmul_eq_mul] using hSum
    _ = X.card * X.card * C := by simp only [mul_assoc]

/-- The elementary codegree bound by all completions inside the ground set. -/
theorem uniform_pair_degree_le_choose
    {F : Family α} {V P : Edge α} {r : ℕ}
    (hU : Uniform r F) (hSupport : ∀ E ∈ F, E ⊆ V)
    (hPV : P ⊆ V) (hPcard : P.card = 2) :
    (F.filter fun E => P ⊆ E).card ≤
      (V.card - 2).choose (r - 2) := by
  classical
  let C := F.filter fun E => P ⊆ E
  have hMap : ∀ E ∈ C, E \ P ∈ (V \ P).powersetCard (r - 2) := by
    intro E hE
    obtain ⟨hEF, hPE⟩ := Finset.mem_filter.mp hE
    apply Finset.mem_powersetCard.mpr
    constructor
    · exact Finset.sdiff_subset_sdiff_left P (hSupport E hEF)
    · rw [Finset.card_sdiff_of_subset hPE, hU hEF, hPcard]
  have hInj : Set.InjOn (fun E : Edge α => E \ P) (↑C : Set (Edge α)) := by
    intro E hE E' hE' hEq
    have hPE := (Finset.mem_filter.mp hE).2
    have hPE' := (Finset.mem_filter.mp hE').2
    have hUnion := congrArg (fun T : Edge α => P ∪ T) hEq
    simpa only [Finset.union_sdiff_of_subset hPE,
      Finset.union_sdiff_of_subset hPE'] using hUnion
  have hBound : C.card ≤ ((V \ P).powersetCard (r - 2)).card :=
    Finset.card_le_card_of_injOn (fun E => E \ P) hMap hInj
  simpa only [C, Finset.card_powersetCard,
    Finset.card_sdiff_of_subset hPV, hPcard] using hBound

/-- Edges containing at least two removed vertices are covered by their
removed-vertex pairs. This is the final error term of (IV.5.4). -/
theorem multiple_removed_edges_bound
    {F : Family α} {W X : Edge α} {r : ℕ}
    (hU : Uniform r F)
    (hSupport : ∀ E ∈ F, E ⊆ W ∪ X) :
    (multipleRemovedEdges F X).card ≤
      X.card.choose 2 * ((W ∪ X).card - 2).choose (r - 2) := by
  classical
  let Pairs := X.powersetCard 2
  have hCover : multipleRemovedEdges F X ⊆
      Pairs.biUnion (fun P => F.filter fun E => P ⊆ E) := by
    intro E hE
    obtain ⟨hEF, hTwo⟩ := Finset.mem_filter.mp hE
    obtain ⟨P, hPsub, hPcard⟩ :=
      Finset.exists_subset_card_eq hTwo
    have hPX : P ⊆ X := hPsub.trans Finset.inter_subset_right
    have hPE : P ⊆ E := hPsub.trans Finset.inter_subset_left
    exact Finset.mem_biUnion.mpr
      ⟨P, Finset.mem_powersetCard.mpr ⟨hPX, hPcard⟩,
        Finset.mem_filter.mpr ⟨hEF, hPE⟩⟩
  have hEach : ∀ P ∈ Pairs,
      (F.filter fun E => P ⊆ E).card ≤
      ((W ∪ X).card - 2).choose (r - 2) := by
    intro P hP
    obtain ⟨hPX, hPcard⟩ := Finset.mem_powersetCard.mp hP
    exact uniform_pair_degree_le_choose hU hSupport
      (hPX.trans Finset.subset_union_right) hPcard
  have hBi := Finset.card_biUnion_le_card_mul Pairs
    (fun P => F.filter (fun E => P ⊆ E))
    (((W ∪ X).card - 2).choose (r - 2)) hEach
  exact (Finset.card_le_card hCover).trans
    (by simpa [Pairs, Finset.card_powersetCard] using hBi)

/-- Equation (IV.5.5) with the actual retained-family pair degree as its
input. Each shadow facet chooses a retained parent and its last vertex;
the common-link cell for that vertex is intersecting. -/
theorem one_removed_link_shadow_overlap_bound
    {F K : Family α} {W : Edge α} {x : α} {r D : ℕ}
    (hAdm : Admissible F) (hU : Uniform r F)
    (hK : K ⊆ outsideFamily F W)
    (hxW : x ∉ W) (hr : 2 ≤ r)
    (hD : ∀ Q : Edge α, Q.card = 2 →
      (K.filter fun E => Q ⊆ E).card ≤ D) :
    (oneRemovedLink F W x ∩ shadowOn K W r).card ≤
      W.card * ((r - 1) * D) := by
  classical
  have hKF : K ⊆ F := by
    intro E hE
    exact (Finset.mem_filter.mp (hK hE)).1
  have hKU : Uniform r K := by
    intro E hE
    exact hU (hKF hE)
  have hCover : oneRemovedLink F W x ∩ shadowOn K W r ⊆
      W.biUnion (fun y => mixedCommonCell F K W x y r) := by
    intro T hT
    obtain ⟨hTL, hTS⟩ := Finset.mem_inter.mp hT
    have hPow := oneRemovedLink_subset_facets hU hTL
    have hTcard := (Finset.mem_powersetCard.mp hPow).2
    obtain ⟨_hPow, E, hE, hTE⟩ := Finset.mem_filter.mp hTS
    have hEcard := hKU hE
    have hAdd : T.card + 1 = E.card := by omega
    obtain ⟨y, hyT, hIns⟩ :=
      Finset.exists_eq_insert_iff.mpr ⟨hTE, hAdd⟩
    have hEW := (Finset.mem_filter.mp (hK hE)).2
    have hyW : y ∈ W := hEW (hIns ▸ Finset.mem_insert_self y T)
    obtain ⟨E₀, hE₀, hErase⟩ := Finset.mem_image.mp hTL
    have hE₀F := (Finset.mem_filter.mp hE₀).1
    have hxE₀ := (Finset.mem_filter.mp hE₀).2.1
    have hxF : insert x T ∈ F := by
      have hEq : insert x T = E₀ := by
        calc
          insert x T = insert x (E₀.erase x) := congrArg (insert x) hErase.symm
          _ = E₀ := Finset.insert_erase hxE₀
      rw [hEq]
      exact hE₀F
    exact Finset.mem_biUnion.mpr ⟨y, hyW,
      Finset.mem_filter.mpr ⟨hPow, hxF, by simpa [hIns] using hE⟩⟩
  have hCells : ∀ y ∈ W,
      (mixedCommonCell F K W x y r).card ≤ (r - 1) * D := by
    intro y hy
    exact mixed_common_cell_card_le_pair_degree hAdm hKF hKU
      hxW hy hr hD
  exact (Finset.card_le_card hCover).trans
    (Finset.card_biUnion_le_card_mul W
      (fun y => mixedCommonCell F K W x y r) ((r - 1) * D) hCells)

/-- Every edge is inside `W`, meets `X` once, or meets `X` at least twice.
The inequality allows the one-vertex fibers to overlap, so no ordering of
the removed vertices is needed. -/
theorem edge_layer_card_le
    {F : Family α} {W X : Edge α}
    (hSupport : ∀ E ∈ F, E ⊆ W ∪ X) :
    F.card ≤ (outsideFamily F W).card +
      (∑ x ∈ X, (oneRemovedLink F W x).card) +
        (multipleRemovedEdges F X).card := by
  classical
  have hCover : F ⊆ outsideFamily F W ∪
      X.biUnion (oneRemovedFiber F W) ∪ multipleRemovedEdges F X := by
    intro E hE
    by_cases hZero : (E ∩ X).card = 0
    · have hEW : E ⊆ W := by
        intro y hy
        rcases Finset.mem_union.mp (hSupport E hE hy) with hyW | hyX
        · exact hyW
        · have : y ∈ E ∩ X := Finset.mem_inter.mpr ⟨hy, hyX⟩
          have hEmpty : E ∩ X = ∅ := Finset.card_eq_zero.mp hZero
          simp [hEmpty] at this
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hE, hEW⟩))
    · by_cases hOne : (E ∩ X).card = 1
      · obtain ⟨x, hxEq⟩ := Finset.card_eq_one.mp hOne
        have hxBoth : x ∈ E ∩ X := hxEq.symm ▸ Finset.mem_singleton_self x
        have hxE : x ∈ E := (Finset.mem_inter.mp hxBoth).1
        have hxX : x ∈ X := (Finset.mem_inter.mp hxBoth).2
        have hErase : E.erase x ⊆ W := by
          intro y hy
          have hyE := Finset.mem_of_mem_erase hy
          rcases Finset.mem_union.mp (hSupport E hE hyE) with hyW | hyX
          · exact hyW
          · have hyBoth : y ∈ E ∩ X := Finset.mem_inter.mpr ⟨hyE, hyX⟩
            have hyEq : y = x := by simpa [hxEq] using hyBoth
            exact False.elim ((Finset.ne_of_mem_erase hy) hyEq)
        exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨x, hxX,
            Finset.mem_filter.mpr ⟨hE, hxE, hErase⟩⟩))
      · have hTwo : 2 ≤ (E ∩ X).card := by omega
        exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hE, hTwo⟩)
  have hCard := Finset.card_le_card hCover
  have hUnion₁ := Finset.card_union_le
    (outsideFamily F W ∪ X.biUnion (oneRemovedFiber F W))
    (multipleRemovedEdges F X)
  have hUnion₂ := Finset.card_union_le (outsideFamily F W)
    (X.biUnion (oneRemovedFiber F W))
  have hFibers : (X.biUnion (oneRemovedFiber F W)).card ≤
      ∑ x ∈ X, (oneRemovedFiber F W x).card :=
    Finset.card_biUnion_le
  have hLink : (∑ x ∈ X, (oneRemovedFiber F W x).card) =
      ∑ x ∈ X, (oneRemovedLink F W x).card := by
    apply Finset.sum_congr rfl
    intro x _
    exact (oneRemovedLink_card_eq_fiber F W x).symm
  omega

/-- Finite coefficient-preserving shadow ledger, before bounding the three
explicit error terms. It is valid at every rank. The repeated-link term
uses ordered pairs, so it is at most twice the unordered term in (IV.5.4). -/
theorem actual_shadow_ledger
    {F K : Family α} {W X : Edge α} {r : ℕ}
    (hF : Uniform r F)
    (hSupport : ∀ E ∈ F, E ⊆ W ∪ X)
    (hK : K ⊆ outsideFamily F W) :
    F.card + (shadowOn K W r).card ≤
      W.card.choose (r - 1) + K.card +
        ((outsideFamily F W) \ K).card +
        (multipleRemovedEdges F X).card +
        (∑ x ∈ X,
          (oneRemovedLink F W x ∩ shadowOn K W r).card) +
        orderedOverlap X (oneRemovedLink F W) := by
  classical
  have hAlloc := shadow_allocation_ledger X
    (W.powersetCard (r - 1)) (shadowOn K W r)
    (oneRemovedLink F W)
    (Finset.filter_subset _ _)
    (fun x _ => oneRemovedLink_subset_facets hF)
  have hLayers := edge_layer_card_le hSupport
  have hInside := Finset.card_sdiff_add_card_eq_card hK
  rw [Finset.card_powersetCard] at hAlloc
  omega

/-- The shadow ledger with both link-error terms bounded by the actual
codegree of the retained family and by the finite common-link cover.
The multi-removed-vertex and discarded-family terms remain explicit. -/
theorem actual_shadow_ledger_with_codegree
    {F K : Family α} {W X : Edge α} {r D : ℕ}
    (hAdm : Admissible F) (hU : Uniform r F)
    (hSupport : ∀ E ∈ F, E ⊆ W ∪ X)
    (hXW : ∀ x ∈ X, x ∉ W)
    (hK : K ⊆ outsideFamily F W) (hr : 2 ≤ r)
    (hD : ∀ Q : Edge α, Q.card = 2 →
      (K.filter fun E => Q ⊆ E).card ≤ D) :
    F.card + (shadowOn K W r).card ≤
      W.card.choose (r - 1) + K.card +
        ((outsideFamily F W) \ K).card +
        (multipleRemovedEdges F X).card +
        X.card * (W.card * ((r - 1) * D)) +
        X.card * X.card * ((r - 1) * W.card.choose (r - 2)) := by
  classical
  have hLedger := actual_shadow_ledger hU hSupport hK
  have hLink :
      (∑ x ∈ X,
        (oneRemovedLink F W x ∩ shadowOn K W r).card) ≤
      X.card * (W.card * ((r - 1) * D)) := by
    have hEach : ∀ x ∈ X,
        (oneRemovedLink F W x ∩ shadowOn K W r).card ≤
        W.card * ((r - 1) * D) := by
      intro x hx
      exact one_removed_link_shadow_overlap_bound hAdm hU hK
        (hXW x hx) hr hD
    simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul X
      (fun x => (oneRemovedLink F W x ∩ shadowOn K W r).card)
      (W.card * ((r - 1) * D)) hEach
  have hPairs := ordered_one_removed_overlap_bound hAdm hU hXW hr
  omega

/-- Fully numerical finite version of the shadow ledger in §IV.5.2.
Only the actual discarded-family size and retained-family pair codegree
remain as external numerical inputs. The constants are slightly looser
than (IV.5.4) because ordered link collisions are counted twice. -/
theorem finite_shadow_extraction_bound
    {F K : Family α} {W X : Edge α} {r D : ℕ}
    (hAdm : Admissible F) (hU : Uniform r F)
    (hSupport : ∀ E ∈ F, E ⊆ W ∪ X)
    (hXW : ∀ x ∈ X, x ∉ W)
    (hK : K ⊆ outsideFamily F W) (hr : 2 ≤ r)
    (hD : ∀ Q : Edge α, Q.card = 2 →
      (K.filter fun E => Q ⊆ E).card ≤ D) :
    F.card + (shadowOn K W r).card ≤
      W.card.choose (r - 1) + K.card +
        ((outsideFamily F W) \ K).card +
        X.card.choose 2 * ((W ∪ X).card - 2).choose (r - 2) +
        X.card * (W.card * ((r - 1) * D)) +
        X.card * X.card * ((r - 1) * W.card.choose (r - 2)) := by
  have hLedger := actual_shadow_ledger_with_codegree
    hAdm hU hSupport hXW hK hr hD
  have hMulti := multiple_removed_edges_bound hU hSupport
  omega

/-- Signed integer form of the coefficient-preserving extraction ledger.
This is the finite precursor of (IV.5.7): any later deletion estimate can
be substituted directly into the right-hand error. -/
theorem finite_shadow_surplus_retention
    {F K : Family α} {W X : Edge α} {r D : ℕ}
    (hAdm : Admissible F) (hU : Uniform r F)
    (hSupport : ∀ E ∈ F, E ⊆ W ∪ X)
    (hXW : ∀ x ∈ X, x ∉ W)
    (hK : K ⊆ outsideFamily F W) (hr : 2 ≤ r)
    (hD : ∀ Q : Edge α, Q.card = 2 →
      (K.filter fun E => Q ⊆ E).card ≤ D) :
    (F.card : ℤ) - (W.card.choose (r - 1) : ℤ) ≤
      (K.card : ℤ) - ((shadowOn K W r).card : ℤ) +
        (((outsideFamily F W) \ K).card : ℤ) +
        (X.card.choose 2 * ((W ∪ X).card - 2).choose (r - 2) : ℕ) +
        (X.card * (W.card * ((r - 1) * D)) : ℕ) +
        (X.card * X.card * ((r - 1) * W.card.choose (r - 2)) : ℕ) := by
  have h := finite_shadow_extraction_bound
    hAdm hU hSupport hXW hK hr hD
  omega

/-- Deleting edges cannot create shadow facets. -/
theorem shadowOn_mono
    {K H : Family α} {V : Edge α} {r : ℕ} (hKH : K ⊆ H) :
    shadowOn K V r ⊆ shadowOn H V r := by
  intro A hA
  obtain ⟨hPow, E, hE, hAE⟩ := Finset.mem_filter.mp hA
  exact Finset.mem_filter.mpr ⟨hPow, E, hKH hE, hAE⟩

/-- Exact deletion stability of the signed edge-minus-shadow surplus,
the final observation in (IV.9.7). -/
theorem shadow_surplus_loss_le_deleted_edges
    {K H : Family α} {V : Edge α} {r : ℕ} (hKH : K ⊆ H) :
    (H.card : ℤ) - ((shadowOn H V r).card : ℤ) -
        ((H \ K).card : ℤ) ≤
      (K.card : ℤ) - ((shadowOn K V r).card : ℤ) := by
  have hPart := Finset.card_sdiff_add_card_eq_card hKH
  have hShadow := Finset.card_le_card (shadowOn_mono (V := V) (r := r) hKH)
  omega

end EdgeLayers

end JSP523.Rank5
