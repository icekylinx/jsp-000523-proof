import JSP523.Rank5.ShadowExtraction

/-!
# Coefficient preserving extraction with subsequent deletions

This file composes the finite shadow ledger with the exact stability of
edge-minus-shadow surplus under deletion.  It keeps the original family,
the discarded part, all removed-vertex errors, and a later extraction cost
visible in one actual-family inequality.
-/

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α]

/-- The number of unordered link collisions. It is half the ordered sum;
the proof below records the evenness rather than assuming it. -/
def unorderedLinkOverlap {ι β : Type*} [DecidableEq ι] [DecidableEq β]
    (X : Finset ι) (A : ι → Finset β) : ℕ := orderedOverlap X A / 2

private theorem orderedOverlap_insert_local
    {ι β : Type*} [DecidableEq ι] [DecidableEq β]
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
    have hax : a ≠ x := fun h => ha (h ▸ hx)
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

private theorem orderedOverlap_even_local
    {ι β : Type*} [DecidableEq ι] [DecidableEq β]
    (X : Finset ι) (A : ι → Finset β) : 2 ∣ orderedOverlap X A := by
  classical
  induction X using Finset.induction_on with
  | empty => simp [orderedOverlap]
  | @insert a S ha ih =>
      rw [orderedOverlap_insert_local S A a ha]
      exact dvd_add ih (dvd_mul_right 2 _)

private theorem unorderedLinkOverlap_insert
    {ι β : Type*} [DecidableEq ι] [DecidableEq β]
    (S : Finset ι) (A : ι → Finset β) (a : ι) (ha : a ∉ S) :
    unorderedLinkOverlap (insert a S) A = unorderedLinkOverlap S A +
      (∑ y ∈ S, (A a ∩ A y).card) := by
  have hEven := orderedOverlap_even_local S A
  have hIns := orderedOverlap_insert_local S A a ha
  unfold unorderedLinkOverlap
  rw [hIns]
  have heq : orderedOverlap S A % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hEven
  omega

/-- Unordered Bonferroni for finite fibers. A repeated point in `m`
fibers is paid once by the union and then by each of its `choose(m,2)`
colliding pairs. -/
theorem sum_card_le_union_add_unorderedOverlap
    {ι β : Type*} [DecidableEq ι] [DecidableEq β]
    (X : Finset ι) (A : ι → Finset β) :
    (∑ x ∈ X, (A x).card) ≤ (X.biUnion A).card + unorderedLinkOverlap X A := by
  classical
  have hIntersect : ∀ (S : Finset ι) (A : ι → Finset β) (B : Finset β),
      (B ∩ S.biUnion A).card ≤ ∑ y ∈ S, (B ∩ A y).card := by
    intro S A B
    have hEq : B ∩ S.biUnion A = S.biUnion (fun y => B ∩ A y) := by
      ext z
      simp only [Finset.mem_inter, Finset.mem_biUnion]
      tauto
    rw [hEq]
    exact Finset.card_biUnion_le
  induction X using Finset.induction_on with
  | empty => simp [unorderedLinkOverlap, orderedOverlap]
  | @insert a S ha ih =>
      have hCap := hIntersect S A (A a)
      have hUnion := Finset.card_union_add_card_inter (A a) (S.biUnion A)
      have hPair := unorderedLinkOverlap_insert S A a ha
      simp only [Finset.sum_insert ha, Finset.biUnion_insert] at *
      rw [hPair]
      omega

/-- Sharp elementary cover bound for a uniform intersecting family: fix
one member and cover every member by the stars through its vertices. -/
theorem intersecting_card_le_sharp_ground_choose
    {T : Family α} {W : Edge α} {k : ℕ}
    (hTW : T ⊆ W.powersetCard k)
    (hI : PairwiseIntersecting T) (hk : 1 ≤ k) :
    T.card ≤ k * (W.card - 1).choose (k - 1) := by
  classical
  by_cases hEmpty : T = ∅
  · simp [hEmpty]
  obtain ⟨A, hA⟩ : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
  have hAc : A.card = k := (Finset.mem_powersetCard.mp (hTW hA)).2
  have hCover : T ⊆ A.biUnion (fun z => T.filter fun E => z ∈ E) := by
    intro B hB
    have hInter : (A ∩ B).Nonempty := by
      by_cases hAB : A = B
      · subst B
        have : A.Nonempty := by
          have hkA := (Finset.mem_powersetCard.mp (hTW hA)).2
          exact Finset.card_pos.mp (by omega)
        exact ⟨this.choose, Finset.mem_inter.mpr
          ⟨this.choose_spec, this.choose_spec⟩⟩
      · exact hI hA hB hAB
    obtain ⟨z, hz⟩ := hInter
    have hz' := Finset.mem_inter.mp hz
    exact Finset.mem_biUnion.mpr ⟨z, hz'.1, Finset.mem_filter.mpr ⟨hB, hz'.2⟩⟩
  have hEach : ∀ z ∈ A, (T.filter fun E => z ∈ E).card ≤
      (W.card - 1).choose (k - 1) := by
    intro z hz
    let C := T.filter fun E => z ∈ E
    have hMap : ∀ E ∈ C, E.erase z ∈ (W.erase z).powersetCard (k - 1) := by
      intro E hE
      obtain ⟨hET, hzE⟩ := Finset.mem_filter.mp hE
      obtain ⟨hEW, hEc⟩ := Finset.mem_powersetCard.mp (hTW hET)
      apply Finset.mem_powersetCard.mpr
      refine ⟨?_, ?_⟩
      · intro a ha
        have haE := Finset.mem_of_mem_erase ha
        have haW := hEW haE
        exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase ha, haW⟩
      have hc := Finset.card_erase_add_one hzE
      omega
    have hInj : Set.InjOn (fun E : Edge α => E.erase z) (↑C : Set (Edge α)) := by
      intro E hE E' hE' hEq
      have hzE := (Finset.mem_filter.mp hE).2
      have hzE' := (Finset.mem_filter.mp hE').2
      have hIns := congrArg (insert z) hEq
      simpa only [Finset.insert_erase hzE, Finset.insert_erase hzE'] using hIns
    have hBound : C.card ≤ ((W.erase z).powersetCard (k - 1)).card :=
      Finset.card_le_card_of_injOn (fun E => E.erase z) hMap hInj
    have hzW : z ∈ W := (Finset.mem_powersetCard.mp (hTW hA)).1 hz
    simpa only [C, Finset.card_powersetCard, Finset.card_erase_of_mem hzW] using hBound
  have hBi := Finset.card_biUnion_le_card_mul A
    (fun z => T.filter fun E => z ∈ E)
    ((W.card - 1).choose (k - 1)) hEach
  calc
    T.card ≤ (A.biUnion fun z => T.filter fun E => z ∈ E).card :=
      Finset.card_le_card hCover
    _ ≤ A.card * (W.card - 1).choose (k - 1) := hBi
    _ = k * (W.card - 1).choose (k - 1) := by rw [hAc]

/-- Repeated links of two deleted vertices have the manuscript's sharp
cover size, with the ambient ground set reduced by one. -/
theorem two_one_removed_links_overlap_bound_sharp
    {F : Family α} {W : Edge α} {x y : α} {r : ℕ}
    (hAdm : Admissible F) (hU : Uniform r F)
    (hxW : x ∉ W) (hyW : y ∉ W) (hxy : x ≠ y)
    (hr : 2 ≤ r) :
    (oneRemovedLink F W x ∩ oneRemovedLink F W y).card ≤
      (r - 1) * (W.card - 1).choose (r - 2) := by
  classical
  let C := commonPrefixTails F W ({x} : Edge α) ({y} : Edge α) (r - 1)
  have hSub : oneRemovedLink F W x ∩ oneRemovedLink F W y ⊆ C := by
    intro T hT
    obtain ⟨hxT, hyT⟩ := Finset.mem_inter.mp hT
    obtain ⟨hTW, hTc⟩ := Finset.mem_powersetCard.mp
      (oneRemovedLink_subset_facets hU hxT)
    have hnx : x ∉ T := fun h => hxW (hTW h)
    have hny : y ∉ T := fun h => hyW (hTW h)
    apply mem_commonPrefixTails.mpr
    refine ⟨hTW, hTc, ?_, oneRemovedLink_insert_mem hxT,
      oneRemovedLink_insert_mem hyT⟩
    exact Finset.disjoint_union_right.mpr
      ⟨Finset.disjoint_singleton_right.mpr hnx,
       Finset.disjoint_singleton_right.mpr hny⟩
  have hCW : C ⊆ W.powersetCard (r - 1) := by
    intro T hT
    obtain ⟨hTW, hTc, _, _, _⟩ := mem_commonPrefixTails.mp hT
    exact Finset.mem_powersetCard.mpr ⟨hTW, hTc⟩
  have hI : PairwiseIntersecting C := commonPrefixTails_intersecting
    (W := W) hAdm (by simp) (by simp)
    (Finset.disjoint_singleton.mpr hxy) (by omega)
  exact (Finset.card_le_card hSub).trans
    (intersecting_card_le_sharp_ground_choose hCW hI (by omega))

/-- Sharp total unordered collision budget for the actual links of removed
vertices. The second-order term is exactly `choose(|X|,2)` times the
sharp common-link cap. -/
theorem unordered_one_removed_overlap_bound_sharp
    {F : Family α} {W X : Edge α} {r : ℕ}
    (hAdm : Admissible F) (hU : Uniform r F)
    (hXW : ∀ x ∈ X, x ∉ W) (hr : 2 ≤ r) :
    unorderedLinkOverlap X (oneRemovedLink F W) ≤
      X.card.choose 2 * ((r - 1) * (W.card - 1).choose (r - 2)) := by
  classical
  let C := (r - 1) * (W.card - 1).choose (r - 2)
  induction X using Finset.induction_on with
  | empty => simp [unorderedLinkOverlap, orderedOverlap]
  | @insert a S ha ih =>
      rw [unorderedLinkOverlap_insert]
      · have hEach : ∀ y ∈ S,
            (oneRemovedLink F W a ∩ oneRemovedLink F W y).card ≤ C := by
          intro y hy
          have hxy : a ≠ y := by
            intro heq
            exact ha (heq ▸ hy)
          exact two_one_removed_links_overlap_bound_sharp hAdm hU
            (hXW a (Finset.mem_insert_self a S))
            (hXW y (Finset.mem_insert_of_mem hy)) hxy hr
        have hSum := Finset.sum_le_card_nsmul S
          (fun y => (oneRemovedLink F W a ∩ oneRemovedLink F W y).card)
          C hEach
        have hCard : (∑ y ∈ S,
            (oneRemovedLink F W a ∩ oneRemovedLink F W y).card) ≤ S.card * C := by
          simpa [nsmul_eq_mul] using hSum
        have hIh := ih (by
          intro x hx
          exact hXW x (Finset.mem_insert_of_mem hx))
        dsimp [C] at hCard ⊢
        rw [Finset.card_insert_of_notMem ha, Nat.choose_succ_succ',
          Nat.choose_one_right]
        calc
          _ ≤ S.card.choose 2 * ((r - 1) * (W.card - 1).choose (r - 2)) +
              S.card * ((r - 1) * (W.card - 1).choose (r - 2)) :=
            Nat.add_le_add hIh hCard
          _ = (S.card + S.card.choose 2) *
              ((r - 1) * (W.card - 1).choose (r - 2)) := by
            rw [Nat.add_mul]
            omega
      · exact ha

/-- Unordered Bonferroni allocation with an additional distinguished
shadow `S` inside an ambient universe `U`. -/
theorem shadow_allocation_ledger_unordered
    {ι β : Type*} [DecidableEq ι] [DecidableEq β]
    (X : Finset ι) (U S : Finset β) (A : ι → Finset β)
    (hS : S ⊆ U) (hA : ∀ x ∈ X, A x ⊆ U) :
    (∑ x ∈ X, (A x).card) + S.card ≤
      U.card + (∑ x ∈ X, (A x ∩ S).card) + unorderedLinkOverlap X A := by
  classical
  have hUnionSub : X.biUnion A ∪ S ⊆ U := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨x, hx, hzx⟩ := Finset.mem_biUnion.mp hz
      exact hA x hx hzx
    · exact hS hz
  have hInt : (X.biUnion A ∩ S).card ≤ ∑ x ∈ X, (A x ∩ S).card := by
    have hEq : X.biUnion A ∩ S = X.biUnion (fun x => A x ∩ S) := by
      ext z
      simp only [Finset.mem_inter, Finset.mem_biUnion]
      tauto
    rw [hEq]
    exact Finset.card_biUnion_le
  have hUnion := Finset.card_union_add_card_inter (X.biUnion A) S
  have hFibers := sum_card_le_union_add_unorderedOverlap X A
  have hCap := Finset.card_le_card hUnionSub
  omega

/-- Exact unordered shadow allocation for the actual removed-center links. -/
theorem actual_shadow_ledger_unordered
    {F K : Family α} {W X : Edge α} {r : ℕ}
    (hU : Uniform r F)
    (hSupport : ∀ E ∈ F, E ⊆ W ∪ X)
    (hK : K ⊆ outsideFamily F W) :
    F.card + (shadowOn K W r).card ≤
      W.card.choose (r - 1) + K.card +
        ((outsideFamily F W) \ K).card +
        (multipleRemovedEdges F X).card +
        (∑ x ∈ X,
          (oneRemovedLink F W x ∩ shadowOn K W r).card) +
        unorderedLinkOverlap X (oneRemovedLink F W) := by
  classical
  have hAlloc := shadow_allocation_ledger_unordered X
    (W.powersetCard (r - 1)) (shadowOn K W r)
    (oneRemovedLink F W)
    (Finset.filter_subset _ _)
    (fun x _ => oneRemovedLink_subset_facets hU)
  have hLayers := edge_layer_card_le hSupport
  have hInside := Finset.card_sdiff_add_card_eq_card hK
  rw [Finset.card_powersetCard] at hAlloc
  omega

/-- Exact unordered finite shadow ledger with the retained-family pair
codegree and all edge layers bounded. Its two link terms have precisely
the coefficients of (IV.5.4). -/
theorem actual_shadow_ledger_with_codegree_sharp
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
        X.card.choose 2 * ((r - 1) * (W.card - 1).choose (r - 2)) := by
  have hLedger := actual_shadow_ledger_unordered hU hSupport hK
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
  have hPairs := unordered_one_removed_overlap_bound_sharp hAdm hU hXW hr
  omega

/-- Signed, manuscript-coefficient version of the coefficient-preserving
finite extraction inequality. The family `H` may be a further subfamily of
`K`; its deletion is charged explicitly. -/
theorem finite_shadow_surplus_retention_sharp
    {F K H : Family α} {W X : Edge α} {r D : ℕ}
    (hAdm : Admissible F) (hU : Uniform r F)
    (hSupport : ∀ E ∈ F, E ⊆ W ∪ X)
    (hXW : ∀ x ∈ X, x ∉ W)
    (hK : K ⊆ outsideFamily F W) (hHK : H ⊆ K)
    (hr : 2 ≤ r)
    (hD : ∀ Q : Edge α, Q.card = 2 →
      (K.filter fun E => Q ⊆ E).card ≤ D) :
    (F.card : ℤ) - (W.card.choose (r - 1) : ℤ) ≤
      (H.card : ℤ) - ((shadowOn H W r).card : ℤ) +
        ((K \ H).card : ℤ) +
        (((outsideFamily F W) \ K).card : ℤ) +
        ((multipleRemovedEdges F X).card : ℤ) +
        (X.card * (W.card * ((r - 1) * D)) : ℕ) +
        (X.card.choose 2 * ((r - 1) * (W.card - 1).choose (r - 2)) : ℕ) := by
  have hLedger := actual_shadow_ledger_with_codegree_sharp
    hAdm hU hSupport hXW hK hr hD
  have hStability := shadow_surplus_loss_le_deleted_edges
    (V := W) (r := r) hHK
  omega

/-- Fully numerical IV.5.3/IV.5.4 finite form. For `H = K`, this is the
coefficient-preserving extraction ledger with explicit `D₂(K) ≤ D` and
ambient support `W ∪ X`; no asymptotic assumptions are built in. -/
theorem finite_shadow_surplus_retention_numeric_sharp
    {F K H : Family α} {W X : Edge α} {r D : ℕ}
    (hAdm : Admissible F) (hU : Uniform r F)
    (hSupport : ∀ E ∈ F, E ⊆ W ∪ X)
    (hXW : ∀ x ∈ X, x ∉ W)
    (hK : K ⊆ outsideFamily F W) (hHK : H ⊆ K)
    (hr : 2 ≤ r)
    (hD : ∀ Q : Edge α, Q.card = 2 →
      (K.filter fun E => Q ⊆ E).card ≤ D) :
    (F.card : ℤ) - (W.card.choose (r - 1) : ℤ) ≤
      (H.card : ℤ) - ((shadowOn H W r).card : ℤ) +
        ((K \ H).card : ℤ) +
        (((outsideFamily F W) \ K).card : ℤ) +
        (X.card.choose 2 * ((W ∪ X).card - 2).choose (r - 2) : ℕ) +
        (X.card * (W.card * ((r - 1) * D)) : ℕ) +
        (X.card.choose 2 * ((r - 1) * (W.card - 1).choose (r - 2)) : ℕ) := by
  have hLedger := finite_shadow_surplus_retention_sharp
    hAdm hU hSupport hXW hK hHK hr hD
  have hMulti := multiple_removed_edges_bound hU hSupport
  omega

/-- Star-baseline form of the finite coefficient-one inequality. The
nonempty removed set supplies a vertex omitted by `W`, so the shadow
baseline `choose(|W|,r-1)` is at most the star baseline
`choose(|W∪X|-1,r-1)`. All finite extraction costs remain explicit. -/
theorem finite_shadow_surplus_star_baseline
    {F K H : Family α} {W X V : Edge α} {r D : ℕ}
    (hAdm : Admissible F) (hU : Uniform r F)
    (hSupport : ∀ E ∈ F, E ⊆ W ∪ X)
    (hXW : ∀ x ∈ X, x ∉ W)
    (hK : K ⊆ outsideFamily F W) (hHK : H ⊆ K)
    (hr : 2 ≤ r)
    (hD : ∀ Q : Edge α, Q.card = 2 →
      (K.filter fun E => Q ⊆ E).card ≤ D)
    (hV : V = W ∪ X) (hDisj : Disjoint W X) (hX : X.Nonempty) :
    (F.card : ℤ) - ((V.card - 1).choose (r - 1) : ℤ) ≤
      (H.card : ℤ) - ((shadowOn H W r).card : ℤ) +
        ((K \ H).card : ℤ) +
        (((outsideFamily F W) \ K).card : ℤ) +
        (X.card.choose 2 * ((V.card - 2).choose (r - 2)) : ℕ) +
        (X.card * (W.card * ((r - 1) * D)) : ℕ) +
        (X.card.choose 2 * ((r - 1) * (W.card - 1).choose (r - 2)) : ℕ) := by
  have hFinite := finite_shadow_surplus_retention_numeric_sharp
    hAdm hU hSupport hXW hK hHK hr hD
  obtain ⟨x, hx⟩ := hX
  have hxV : x ∈ V := by rw [hV]; exact Finset.mem_union_right W hx
  have hWsub : W ⊆ V.erase x := by
    intro y hy
    have hyV : y ∈ V := by rw [hV]; exact Finset.mem_union_left X hy
    have hyx : y ≠ x := by
      intro hEq
      have : x ∈ W := hEq ▸ hy
      exact (Finset.disjoint_left.mp hDisj) this hx
    exact Finset.mem_erase.mpr ⟨hyx, hyV⟩
  have hWcard : W.card ≤ V.card - 1 := by
    have hCard := Finset.card_le_card hWsub
    simpa [Finset.card_erase_of_mem hxV] using hCard
  have hBase : W.card.choose (r - 1) ≤ (V.card - 1).choose (r - 1) :=
    Nat.choose_le_choose (r - 1) hWcard
  have hAmbient : (W ∪ X).card = V.card := by rw [← hV]
  rw [hAmbient] at hFinite
  omega

/-- The coefficient-one ledger survives a second extraction step.  Here
`K` is the first retained family outside `W`, and `H` is any further
subfamily.  The term `|K \ H|` pays for this second deletion exactly;
all other errors are the explicit finite terms from the shadow ledger.

In particular, this theorem does not assert that the error terms are
asymptotically small: that requires the parameter estimates in the
manuscript's regularization argument. -/
theorem finite_extraction_surplus_after_deletion
    {F K H : Family α} {W X : Edge α} {r D : ℕ}
    (hAdm : Admissible F) (hU : Uniform r F)
    (hSupport : ∀ E ∈ F, E ⊆ W ∪ X)
    (hXW : ∀ x ∈ X, x ∉ W)
    (hK : K ⊆ outsideFamily F W) (hHK : H ⊆ K)
    (hr : 2 ≤ r)
    (hD : ∀ Q : Edge α, Q.card = 2 →
      (K.filter fun E => Q ⊆ E).card ≤ D) :
    (F.card : ℤ) - (W.card.choose (r - 1) : ℤ) ≤
      (H.card : ℤ) - ((shadowOn H W r).card : ℤ) +
        ((K \ H).card : ℤ) +
        (((outsideFamily F W) \ K).card : ℤ) +
        (X.card.choose 2 * ((W ∪ X).card - 2).choose (r - 2) : ℕ) +
        (X.card * (W.card * ((r - 1) * D)) : ℕ) +
        (X.card * X.card * ((r - 1) * W.card.choose (r - 2)) : ℕ) := by
  have hLedger := finite_shadow_surplus_retention
    hAdm hU hSupport hXW hK hr hD
  have hStability := shadow_surplus_loss_le_deleted_edges
    (V := W) (r := r) hHK
  omega

end JSP523.Rank5
