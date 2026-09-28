import JSP523.Counting.PrefixAssignment

/-!
# The geometric prefix bound for the actual assigned subfamilies

A prefix condition need hold only for edges assigned that prefix, not for
all parent edges through it.  The distinction is essential when applying
center inheritance.  This module restricts both common systems and label
hypotheses accordingly, proves the geometric cap, and combines it with
the complete finite double count.  Cleanup/center hypotheses remain
explicit; construction of those data is not asserted here.
-/

namespace JSP523.Counting

open Finset

variable {α : Type*} [DecidableEq α]

/-- Common tails in two actual chosen-prefix fibers. -/
def assignedCommonTriples (K : Family α) (V : Edge α) (p : ℕ)
    (chosenPrefix : Edge α → Edge α) (Y Z : Edge α) : Family α :=
  (V.powersetCard 3).filter (fun P =>
    Y ∈ chosenPrefixesAt K V p chosenPrefix P ∧ Z ∈ chosenPrefixesAt K V p chosenPrefix P)

/-- Assigned common tails are actual common tails, but need not exhaust them. -/
theorem assignedCommonTriples_subset
    (K : Family α) (V : Edge α) (p : ℕ)
    (chosenPrefix : Edge α → Edge α) (Y Z : Edge α) :
    assignedCommonTriples K V p chosenPrefix Y Z ⊆ commonPrefixTriples K V Y Z := by
  intro P hP
  obtain ⟨hPV, hPY, hPZ⟩ := Finset.mem_filter.mp hP
  have hy := mem_chosenPrefixesAt.mp hPY
  have hz := mem_chosenPrefixesAt.mp hPZ
  have hp := Finset.mem_powersetCard.mp hPV
  exact mem_commonPrefixTriples.mpr ⟨hp.1, hp.2,
    Finset.disjoint_union_right.mpr ⟨hy.2.1.symm, hz.2.1.symm⟩,
    hy.2.2.1, hz.2.2.1⟩

/-- The two pair-label tests apply to the two assigned edge fibers only. -/
theorem assigned_common_triples_linear
    (K : Family α) (V : Edge α) (p : ℕ)
    (chosenPrefix : Edge α → Edge α) (Y Z : Edge α)
    (pairLabel : Edge α → α)
    (hYlabel : PairCompletionLabelInPrefix
      (K.filter (fun E => chosenPrefix E = Y)) pairLabel Y)
    (hZlabel : PairCompletionLabelInPrefix
      (K.filter (fun E => chosenPrefix E = Z)) pairLabel Z)
    (hYZ : Disjoint Y Z) :
    LinearFamily (assignedCommonTriples K V p chosenPrefix Y Z) := by
  intro P Q hP hQ hNe
  by_contra hNotLe
  obtain ⟨hPpow, hPY, hPZ⟩ := Finset.mem_filter.mp hP
  obtain ⟨hQpow, hQY, hQZ⟩ := Finset.mem_filter.mp hQ
  have hp := Finset.mem_powersetCard.mp hPpow
  have hq := Finset.mem_powersetCard.mp hQpow
  obtain ⟨S, x, y, hSc, hxy, hPeq, hQeq⟩ :=
    triple_shared_pair_completions hp.2 hq.2 hNe (by omega)
  have hYP : Y ∪ P ∈ K.filter (fun E => chosenPrefix E = Y) := by
    have hd := mem_chosenPrefixesAt.mp hPY
    exact Finset.mem_filter.mpr ⟨hd.2.2.1, hd.2.2.2⟩
  have hYQ : Y ∪ Q ∈ K.filter (fun E => chosenPrefix E = Y) := by
    have hd := mem_chosenPrefixesAt.mp hQY
    exact Finset.mem_filter.mpr ⟨hd.2.2.1, hd.2.2.2⟩
  have hZP : Z ∪ P ∈ K.filter (fun E => chosenPrefix E = Z) := by
    have hd := mem_chosenPrefixesAt.mp hPZ
    exact Finset.mem_filter.mpr ⟨hd.2.2.1, hd.2.2.2⟩
  have hZQ : Z ∪ Q ∈ K.filter (fun E => chosenPrefix E = Z) := by
    have hd := mem_chosenPrefixesAt.mp hQZ
    exact Finset.mem_filter.mpr ⟨hd.2.2.1, hd.2.2.2⟩
  rw [hPeq] at hYP hZP
  rw [hQeq] at hYQ hZQ
  exact (Finset.disjoint_left.mp hYZ)
    (hYlabel S x y hSc hxy hYP hYQ) (hZlabel S x y hSc hxy hZP hZQ)

/-- The star/bad-partner argument is hereditary in the common triple
family; it does not require every possible common tail to be assigned. -/
theorem common_substar_card_le_one_add_bad_partners
    {K H C : Family α} {V Y Z P₀ : Edge α} {x : α}
    (hKH : K ⊆ H) (hYZ : Disjoint Y Z)
    (hC : C ⊆ commonPrefixTriples K V Y Z) (hP₀ : P₀ ∈ C)
    (hStar : ∀ ⦃P : Edge α⦄, P ∈ C → x ∈ P)
    (center : Edge α → α) (hCenter : center (Y ∪ {x}) ∈ Y)
    (good : Edge α → Edge α → Edge α → Prop)
    (label : Edge α → Edge α → α)
    (hGoodCenter : ∀ A S T, good A S T → label S T = center A)
    (hLabel : GoodPairLabelValid H V good label) :
    C.card ≤ 1 + (badParentPartners H V (Y ∪ {x}) (P₀.erase x) good).card := by
  classical
  have hMap : ∀ P ∈ C.erase P₀,
      P.erase x ∈ badParentPartners H V (Y ∪ {x}) (P₀.erase x) good := by
    intro P hP
    have hPC := Finset.mem_of_mem_erase hP
    exact common_star_other_tail_is_bad hKH hYZ (hC hP₀) (hC hPC)
      (hStar hP₀) (hStar hPC) center hCenter good label hGoodCenter hLabel
  have hInj : Set.InjOn (fun P : Edge α => P.erase x)
      (C.erase P₀ : Set (Edge α)) := by
    intro P hP Q hQ hEq
    have hxP := hStar (Finset.mem_of_mem_erase hP)
    have hxQ := hStar (Finset.mem_of_mem_erase hQ)
    have h := congrArg (fun S : Edge α => insert x S) hEq
    simpa only [Finset.insert_erase hxP, Finset.insert_erase hxQ] using h
  have hCount := Finset.card_le_card_of_injOn (fun P : Edge α => P.erase x) hMap hInj
  have hErase := Finset.card_erase_add_one hP₀
  omega

/-- Actual parent two-tail links inject into the corresponding codegree. -/
theorem parent_pair_link_card_le_codegree (H : Family α) (V A : Edge α) :
    (parentPairLink H V A).card ≤ (H.filter (fun E => A ⊆ E)).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun P => A ∪ P)
  · intro P hP
    have hp := mem_parentPairLink.mp hP
    exact Finset.mem_filter.mpr ⟨hp.2.2.2, Finset.subset_union_left⟩
  · intro P hP Q hQ hEq
    have hp := (mem_parentPairLink.mp hP).2.2.1
    have hq := (mem_parentPairLink.mp hQ).2.2.1
    have h := congrArg (fun E : Edge α => E \ A) hEq
    simpa only [Finset.union_sdiff_cancel_left hp.symm,
      Finset.union_sdiff_cancel_left hq.symm] using h

/-- (IV.B.2) for the assigned common system, with retained-edge partner
bounds rather than partner bounds on every vertex of every parent link. -/
theorem assigned_prefix_common_system_bound
    {K H : Family α} {V : Edge α} {r : ℕ}
    (chosenPrefix : Edge α → Edge α) (Y Z : Edge α)
    (hr : 5 ≤ r) (hH : Admissible H) (hKH : K ⊆ H)
    (hY : Y ∈ V.powersetCard (r - 3))
    (hZ : Z ∈ V.powersetCard (r - 3)) (hYZ : Disjoint Y Z)
    (pairLabel : Edge α → α)
    (hYlabel : PairCompletionLabelInPrefix
      (K.filter (fun E => chosenPrefix E = Y)) pairLabel Y)
    (hZlabel : PairCompletionLabelInPrefix
      (K.filter (fun E => chosenPrefix E = Z)) pairLabel Z)
    (center : Edge α → α)
    (hCenter : ∀ P ∈ assignedCommonTriples K V (r - 3) chosenPrefix Y Z,
      ∀ x ∈ P, center (Y ∪ {x}) ∈ Y)
    (good : Edge α → Edge α → Edge α → Prop)
    (label : Edge α → Edge α → α)
    (hGoodCenter : ∀ A S T, good A S T → label S T = center A)
    (hLabel : GoodPairLabelValid H V good label)
    (ε : ℝ) (hε : 0 ≤ ε) (D : ℕ)
    (hBad : ∀ P ∈ assignedCommonTriples K V (r - 3) chosenPrefix Y Z,
      ∀ x ∈ P,
        ((badParentPartners H V (Y ∪ {x}) (P.erase x) good).card : ℝ) ≤
          ε * ((parentPairLink H V (Y ∪ {x})).card : ℝ))
    (hD : ∀ A : Edge α, A.card = r - 2 →
      (H.filter (fun E => A ⊆ E)).card ≤ D) :
    ((assignedCommonTriples K V (r - 3) chosenPrefix Y Z).card : ℝ) ≤
      max 7 (1 + ε * (D : ℝ)) := by
  classical
  let C := assignedCommonTriples K V (r - 3) chosenPrefix Y Z
  have hC : C ⊆ commonPrefixTriples K V Y Z :=
    assignedCommonTriples_subset K V (r - 3) chosenPrefix Y Z
  have hYpos : Y.Nonempty := by
    have hyc := (Finset.mem_powersetCard.mp hY).2
    exact Finset.card_pos.mp (by omega)
  have hZpos : Z.Nonempty := by
    have hzc := (Finset.mem_powersetCard.mp hZ).2
    exact Finset.card_pos.mp (by omega)
  have hInt : PairwiseIntersecting C := by
    intro P Q hP hQ hNe
    exact common_prefix_triples_intersecting (admissible_mono hKH hH)
      hYpos hZpos hYZ (hC hP) (hC hQ) hNe
  have hLin : LinearFamily C :=
    assigned_common_triples_linear K V (r - 3) chosenPrefix Y Z
      pairLabel hYlabel hZlabel hYZ
  have hUnif : Uniform 3 C := by
    intro P hP
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hP).1).2
  rcases linear_intersecting_triples_star_or_small hUnif hInt hLin with hStar | hSmall
  · obtain ⟨x, hxStar⟩ := hStar
    by_cases hNonempty : C.Nonempty
    · obtain ⟨P₀, hP₀⟩ := hNonempty
      have hxP₀ := hxStar hP₀
      have hCount := common_substar_card_le_one_add_bad_partners
        hKH hYZ hC hP₀ hxStar center (hCenter P₀ hP₀ x hxP₀)
        good label hGoodCenter hLabel
      have hBad₀ := hBad P₀ hP₀ x hxP₀
      have hxY : x ∉ Y := by
        have hp := mem_commonPrefixTriples.mp (hC hP₀)
        exact (Finset.disjoint_left.mp
          (Finset.disjoint_union_right.mp hp.2.2.1).1) hxP₀
      have hAc : (Y ∪ {x}).card = r - 2 := by
        rw [Finset.union_singleton, Finset.card_insert_of_notMem hxY,
          (Finset.mem_powersetCard.mp hY).2]
        omega
      have hDegNat := (parent_pair_link_card_le_codegree H V (Y ∪ {x})).trans
        (hD _ hAc)
      have hDeg : ((parentPairLink H V (Y ∪ {x})).card : ℝ) ≤ (D : ℝ) := by
        exact_mod_cast hDegNat
      have hScaled := mul_le_mul_of_nonneg_left hDeg hε
      have hCountReal : (C.card : ℝ) ≤
          1 + ((badParentPartners H V (Y ∪ {x}) (P₀.erase x) good).card : ℝ) := by
        exact_mod_cast hCount
      exact (show (C.card : ℝ) ≤ 1 + ε * (D : ℝ) by linarith).trans
        (le_max_right _ _)
    · have hEmpty : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hNonempty
      have hZero : (C.card : ℝ) = 0 := by simp only [hEmpty, Finset.card_empty, Nat.cast_zero]
      change (C.card : ℝ) ≤ _
      rw [hZero]
      exact (by norm_num : (0 : ℝ) ≤ 7).trans (le_max_left _ _)
  · exact (show (C.card : ℝ) ≤ 7 by exact_mod_cast hSmall).trans (le_max_left _ _)

/-- The finite prefix inequality with its geometric common-system estimate
discharged.  The hypotheses are the actual assigned-prefix structure and
parent-partner guarantee supplied by the cleanup/center part of the proof;
no collision-count or common-system-cardinality inequality is assumed. -/
theorem actual_prefix_bound_from_parent_structure
    (K H : Family α) (V : Edge α) (r D D₄ : ℕ) (ε : ℝ)
    (chosenPrefix : Edge α → Edge α)
    (hr : 5 ≤ r) (hD₄pos : 1 ≤ D₄) (hε : 0 ≤ ε)
    (hH : Admissible H) (hKH : K ⊆ H) (hUniform : Uniform r K)
    (hGround : ∀ E ∈ K, E ⊆ V)
    (hPrefixSub : ∀ E ∈ K, chosenPrefix E ⊆ E)
    (hPrefixCard : ∀ E ∈ K, (chosenPrefix E).card = r - 3)
    (pairLabel : Edge α → α)
    (hPair : ∀ Y ∈ V.powersetCard (r - 3),
      PairCompletionLabelInPrefix (K.filter (fun E => chosenPrefix E = Y)) pairLabel Y)
    (center : Edge α → α)
    (hCenter : ∀ P ∈ V.powersetCard 3,
      ∀ Y ∈ chosenPrefixesAt K V (r - 3) chosenPrefix P,
      ∀ x ∈ P, center (Y ∪ {x}) ∈ Y)
    (good : Edge α → Edge α → Edge α → Prop)
    (label : Edge α → Edge α → α)
    (hGoodCenter : ∀ A S T, good A S T → label S T = center A)
    (hLabel : GoodPairLabelValid H V good label)
    (hBad : ∀ P ∈ V.powersetCard 3,
      ∀ Y ∈ chosenPrefixesAt K V (r - 3) chosenPrefix P, ∀ x ∈ P,
      ((badParentPartners H V (Y ∪ {x}) (P.erase x) good).card : ℝ) ≤
        ε * ((parentPairLink H V (Y ∪ {x})).card : ℝ))
    (hD : ∀ A : Edge α, A.card = r - 2 →
      (H.filter (fun E => A ⊆ E)).card ≤ D)
    (hD₄ : ∀ Q : Edge α, Q.card = 4 →
      (K.filter (fun E => Q ⊆ E)).card ≤ D₄) :
    (K.card : ℝ) ^ 2 ≤ (V.card.choose 3 : ℝ) *
      (((1 + (r - 3) * (D₄ - 1) : ℕ) : ℝ) * (K.card : ℝ) +
        ((V.card.choose (r - 3) *
          (V.card - (r - 3)).choose (r - 3) : ℕ) : ℝ) *
            max 7 (1 + ε * (D : ℝ))) := by
  apply actual_prefix_collision_bound_real K V r D₄
    (max 7 (1 + ε * (D : ℝ))) chosenPrefix (by omega) hD₄pos hUniform hGround
    hPrefixSub hPrefixCard hD₄
  intro Y hY Z hZ hYZ
  apply assigned_prefix_common_system_bound chosenPrefix Y Z hr hH hKH hY hZ hYZ
    pairLabel (hPair Y hY) (hPair Z hZ) center ?_
    good label hGoodCenter hLabel ε hε D ?_ hD
  · intro P hP x hx
    obtain ⟨hPpow, hPY, _⟩ := Finset.mem_filter.mp hP
    exact hCenter P hPpow Y hPY x hx
  · intro P hP x hx
    obtain ⟨hPpow, hPY, _⟩ := Finset.mem_filter.mp hP
    exact hBad P hPpow Y hPY x hx

end JSP523.Counting
