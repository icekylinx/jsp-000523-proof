import JSP523.Counting.LinearTriple
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Common triple systems of disjoint prefixes

The first step of the fixed-rank prefix-collision argument is a genuine
forbidden-switch statement.  A triple in the common system completes both
prefixes to edges of the retained family.  If two such triples were disjoint,
the four crossed completions would be a forbidden quadruple.
-/

namespace JSP523

section PrefixCommonSystem

variable {α : Type*} [DecidableEq α]

/-- Triples outside both prefixes that complete both prefixes to edges of `K`.
    This includes the common system of two chosen-prefix fibers. -/
def commonPrefixTriples (K : Family α) (V Y Z : Edge α) : Family α :=
  (V.powersetCard 3).filter fun P =>
    Disjoint P (Y ∪ Z) ∧ Y ∪ P ∈ K ∧ Z ∪ P ∈ K

theorem mem_commonPrefixTriples {K : Family α} {V Y Z P : Edge α} :
    P ∈ commonPrefixTriples K V Y Z ↔
      P ⊆ V ∧ P.card = 3 ∧ Disjoint P (Y ∪ Z) ∧
        Y ∪ P ∈ K ∧ Z ∪ P ∈ K := by
  simp only [commonPrefixTriples, Finset.mem_filter,
    Finset.mem_powersetCard]
  tauto

/-- Four pairwise disjoint nonempty pieces give the repeated-union switch. -/
theorem prefix_switch_forbidden
    {Y Z P Q : Edge α}
    (hY : Y.Nonempty) (hZ : Z.Nonempty)
    (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hYZ : Disjoint Y Z)
    (hPY : Disjoint P Y) (hPZ : Disjoint P Z)
    (hQY : Disjoint Q Y) (hQZ : Disjoint Q Z)
    (hPQ : Disjoint P Q) :
    ForbiddenQuad (Y ∪ P) (Z ∪ Q) (Y ∪ Q) (Z ∪ P) := by
  obtain ⟨y, hy⟩ := hY
  obtain ⟨z, hz⟩ := hZ
  obtain ⟨p, hp⟩ := hP
  obtain ⟨q, hq⟩ := hQ
  have hyZ : y ∉ Z := (Finset.disjoint_left.mp hYZ) hy
  have hyP : y ∉ P := (Finset.disjoint_left.mp hPY.symm) hy
  have hyQ : y ∉ Q := (Finset.disjoint_left.mp hQY.symm) hy
  have hzY : z ∉ Y := (Finset.disjoint_left.mp hYZ.symm) hz
  have hzP : z ∉ P := (Finset.disjoint_left.mp hPZ.symm) hz
  have hzQ : z ∉ Q := (Finset.disjoint_left.mp hQZ.symm) hz
  have hpY : p ∉ Y := (Finset.disjoint_left.mp hPY) hp
  have hpQ : p ∉ Q := (Finset.disjoint_left.mp hPQ) hp
  have hqZ : q ∉ Z := (Finset.disjoint_left.mp hQZ) hq
  have hqP : q ∉ P := (Finset.disjoint_left.mp hPQ.symm) hq
  have hAB : Y ∪ P ≠ Z ∪ Q := by
    intro h
    have : y ∈ Z ∪ Q := h ▸ Finset.mem_union_left P hy
    simp [hyZ, hyQ] at this
  have hAC : Y ∪ P ≠ Y ∪ Q := by
    intro h
    have : p ∈ Y ∪ Q := h ▸ Finset.mem_union_right Y hp
    simp [hpY, hpQ] at this
  have hAD : Y ∪ P ≠ Z ∪ P := by
    intro h
    have : y ∈ Z ∪ P := h ▸ Finset.mem_union_left P hy
    simp [hyZ, hyP] at this
  have hBC : Z ∪ Q ≠ Y ∪ Q := by
    intro h
    have : z ∈ Y ∪ Q := h ▸ Finset.mem_union_left Q hz
    simp [hzY, hzQ] at this
  have hBD : Z ∪ Q ≠ Z ∪ P := by
    intro h
    have : q ∈ Z ∪ P := h ▸ Finset.mem_union_right Z hq
    simp [hqZ, hqP] at this
  have hCD : Y ∪ Q ≠ Z ∪ P := by
    intro h
    have : y ∈ Z ∪ P := h ▸ Finset.mem_union_left Q hy
    simp [hyZ, hyP] at this
  refine ⟨⟨hAB, hAC, hAD, hBC, hBD, hCD⟩, ?_, ?_, ?_⟩
  · simpa [Finset.disjoint_union_left, Finset.disjoint_union_right] using
      (show (Disjoint Y Z ∧ Disjoint P Z) ∧
        Disjoint Y Q ∧ Disjoint P Q from
        ⟨⟨hYZ, hPZ⟩, hQY.symm, hPQ⟩)
  · simpa [Finset.disjoint_union_left, Finset.disjoint_union_right] using
      (show (Disjoint Y Z ∧ Disjoint Q Z) ∧
        Disjoint Y P ∧ Disjoint Q P from
        ⟨⟨hYZ, hQZ⟩, hPY.symm, hPQ.symm⟩)
  · ac_rfl

/-- The actual common triple system of two disjoint nonempty prefixes is
    intersecting in an admissible parent family. -/
theorem common_prefix_triples_intersecting
    {K : Family α} {V Y Z : Edge α}
    (hK : Admissible K)
    (hY : Y.Nonempty) (hZ : Z.Nonempty)
    (hYZ : Disjoint Y Z) :
    PairwiseIntersecting (commonPrefixTriples K V Y Z) := by
  intro P Q hP hQ _hNe
  by_contra hEmpty
  have hPQ : Disjoint P Q := Finset.disjoint_iff_inter_eq_empty.mpr
    (Finset.not_nonempty_iff_eq_empty.mp hEmpty)
  obtain ⟨_, hPcard, hPdisj, hYP, hZP⟩ :=
    mem_commonPrefixTriples.mp hP
  obtain ⟨_, hQcard, hQdisj, hYQ, hZQ⟩ :=
    mem_commonPrefixTriples.mp hQ
  have hPnon : P.Nonempty := Finset.card_pos.mp (by omega)
  have hQnon : Q.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨hPY, hPZ⟩ := Finset.disjoint_union_right.mp hPdisj
  obtain ⟨hQY, hQZ⟩ := Finset.disjoint_union_right.mp hQdisj
  exact hK hYP hZQ hYQ hZP
    (prefix_switch_forbidden hY hZ hPnon hQnon hYZ
      hPY hPZ hQY hQZ hPQ)

/-- The exact pair-label interface used in the manuscript's linearity
    argument.  If `Y ∪ S` has two retained completions `x,y`, its single
    parent completion-pair label lies in the prefix `Y`. -/
def PairCompletionLabelInPrefix
    (K : Family α) (label : Edge α → α) (Y : Edge α) : Prop :=
  ∀ (S : Edge α) (x y : α), S.card = 2 → x ≠ y →
    Y ∪ (S ∪ {x}) ∈ K → Y ∪ (S ∪ {y}) ∈ K →
    label {x, y} ∈ Y

/-- Two different triples of size three that share at least two vertices
    have a two-vertex intersection and one distinct completion each. -/
theorem triple_shared_pair_completions
    {P Q : Edge α}
    (hPcard : P.card = 3) (hQcard : Q.card = 3)
    (hNe : P ≠ Q) (hTwo : 2 ≤ (P ∩ Q).card) :
    ∃ (S : Edge α) (x y : α),
      S.card = 2 ∧ x ≠ y ∧
        P = S ∪ {x} ∧ Q = S ∪ {y} := by
  let S := P ∩ Q
  have hSTwo : 2 ≤ S.card := hTwo
  have hSP : S ⊆ P := Finset.inter_subset_left
  have hSQ : S ⊆ Q := Finset.inter_subset_right
  have hSle : S.card ≤ 3 := by
    exact (Finset.card_le_card hSP).trans_eq hPcard
  have hSne : S.card ≠ 3 := by
    intro hScard
    have hPeq : S = P := Finset.eq_of_subset_of_card_le hSP (by omega)
    have hQeq : S = Q := Finset.eq_of_subset_of_card_le hSQ (by omega)
    exact hNe (hPeq.symm.trans hQeq)
  have hScard : S.card = 2 := by omega
  have hPdiff : (P \ S).card = 1 := by
    rw [Finset.card_sdiff_of_subset hSP]
    omega
  have hQdiff : (Q \ S).card = 1 := by
    rw [Finset.card_sdiff_of_subset hSQ]
    omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hPdiff
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hQdiff
  have hxPdiff : x ∈ P \ S := by simp [hx]
  have hyQdiff : y ∈ Q \ S := by simp [hy]
  have hxP : x ∈ P := (Finset.mem_sdiff.mp hxPdiff).1
  have hxQ : x ∉ Q := by
    intro hxQ
    exact (Finset.mem_sdiff.mp hxPdiff).2
      (Finset.mem_inter.mpr ⟨hxP, hxQ⟩)
  have hyQ : y ∈ Q := (Finset.mem_sdiff.mp hyQdiff).1
  have hxy : x ≠ y := by
    intro h
    exact hxQ (h ▸ hyQ)
  have hPeq : P = S ∪ {x} := by
    have h := Finset.union_sdiff_of_subset hSP
    rw [hx] at h
    exact h.symm
  have hQeq : Q = S ∪ {y} := by
    have h := Finset.union_sdiff_of_subset hSQ
    rw [hy] at h
    exact h.symm
  exact ⟨S, x, y, hScard, hxy, hPeq, hQeq⟩

/-- A single-valued parent pair label satisfying the local prefix-center
    condition at both prefixes makes their common triple system linear. -/
theorem common_prefix_triples_linear
    {K : Family α} {V Y Z : Edge α}
    (label : Edge α → α)
    (hYlabel : PairCompletionLabelInPrefix K label Y)
    (hZlabel : PairCompletionLabelInPrefix K label Z)
    (hYZ : Disjoint Y Z) :
    LinearFamily (commonPrefixTriples K V Y Z) := by
  intro P Q hP hQ hNe
  by_contra hNotLe
  have hTwo : 2 ≤ (P ∩ Q).card := by omega
  obtain ⟨_, hPcard, _, hYP, hZP⟩ :=
    mem_commonPrefixTriples.mp hP
  obtain ⟨_, hQcard, _, hYQ, hZQ⟩ :=
    mem_commonPrefixTriples.mp hQ
  obtain ⟨S, x, y, hScard, hxy, hPeq, hQeq⟩ :=
    triple_shared_pair_completions hPcard hQcard hNe hTwo
  rw [hPeq] at hYP hZP
  rw [hQeq] at hYQ hZQ
  have hcenterY : label {x, y} ∈ Y :=
    hYlabel S x y hScard hxy hYP hYQ
  have hcenterZ : label {x, y} ∈ Z :=
    hZlabel S x y hScard hxy hZP hZQ
  exact (Finset.disjoint_left.mp hYZ) hcenterY hcenterZ

/-- The non-star common system has at most seven triples.  The remaining
    star branch is the parent bad-partner argument of §IV.B in the all-rank manuscript. -/
theorem common_prefix_triples_star_or_small
    {K : Family α} {V Y Z : Edge α}
    (hK : Admissible K)
    (hY : Y.Nonempty) (hZ : Z.Nonempty)
    (hYZ : Disjoint Y Z)
    (label : Edge α → α)
    (hYlabel : PairCompletionLabelInPrefix K label Y)
    (hZlabel : PairCompletionLabelInPrefix K label Z) :
    (∃ x : α, ∀ ⦃P : Edge α⦄,
      P ∈ commonPrefixTriples K V Y Z → x ∈ P) ∨
      (commonPrefixTriples K V Y Z).card ≤ 7 := by
  have hU : Uniform 3 (commonPrefixTriples K V Y Z) := by
    intro P hP
    exact (mem_commonPrefixTriples.mp hP).2.1
  exact linear_intersecting_triples_star_or_small hU
    (common_prefix_triples_intersecting hK hY hZ hYZ)
    (common_prefix_triples_linear label hYlabel hZlabel hYZ)

/-- The parent's actual two-point link of a core. -/
def parentPairLink (H : Family α) (V A : Edge α) : Family α :=
  (V.powersetCard 2).filter fun S => Disjoint S A ∧ A ∪ S ∈ H

theorem mem_parentPairLink {H : Family α} {V A S : Edge α} :
    S ∈ parentPairLink H V A ↔
      S ⊆ V ∧ S.card = 2 ∧ Disjoint S A ∧ A ∪ S ∈ H := by
  simp only [parentPairLink, Finset.mem_filter, Finset.mem_powersetCard]
  tauto

/-- Removing the center from a common triple gives an actual parent-link
    pair at either extended prefix. -/
theorem common_tail_erase_mem_parent_link
    {K H : Family α} {V Y Z P : Edge α} {x : α}
    (hKH : K ⊆ H)
    (hP : P ∈ commonPrefixTriples K V Y Z)
    (hx : x ∈ P) :
    P.erase x ∈ parentPairLink H V (Y ∪ {x}) ∧
      P.erase x ∈ parentPairLink H V (Z ∪ {x}) := by
  obtain ⟨hPV, hPcard, hPdisj, hYP, hZP⟩ :=
    mem_commonPrefixTriples.mp hP
  have hEraseCard : (P.erase x).card = 2 := by
    have h := Finset.card_erase_add_one hx
    omega
  have hEraseV : P.erase x ⊆ V :=
    (Finset.erase_subset x P).trans hPV
  have hDisjY : Disjoint (P.erase x) (Y ∪ {x}) := by
    apply Finset.disjoint_left.mpr
    intro a ha hAY
    have haP : a ∈ P := Finset.mem_of_mem_erase ha
    have haNe : a ≠ x := Finset.ne_of_mem_erase ha
    rcases Finset.mem_union.mp hAY with haY | haX
    · exact (Finset.disjoint_left.mp
        (Finset.disjoint_union_right.mp hPdisj).1) haP haY
    · exact haNe (Finset.mem_singleton.mp haX)
  have hDisjZ : Disjoint (P.erase x) (Z ∪ {x}) := by
    apply Finset.disjoint_left.mpr
    intro a ha hAZ
    have haP : a ∈ P := Finset.mem_of_mem_erase ha
    have haNe : a ≠ x := Finset.ne_of_mem_erase ha
    rcases Finset.mem_union.mp hAZ with haZ | haX
    · exact (Finset.disjoint_left.mp
        (Finset.disjoint_union_right.mp hPdisj).2) haP haZ
    · exact haNe (Finset.mem_singleton.mp haX)
  have hReconstruct : ({x} : Edge α) ∪ P.erase x = P := by
    ext a
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_erase]
    constructor
    · rintro (rfl | ⟨_, haP⟩)
      · exact hx
      · exact haP
    · intro haP
      by_cases hax : a = x
      · exact Or.inl hax
      · exact Or.inr ⟨hax, haP⟩
  have hYedge : (Y ∪ {x}) ∪ P.erase x ∈ H := by
    rw [Finset.union_assoc, hReconstruct]
    exact hKH hYP
  have hZedge : (Z ∪ {x}) ∪ P.erase x ∈ H := by
    rw [Finset.union_assoc, hReconstruct]
    exact hKH hZP
  exact ⟨mem_parentPairLink.mpr ⟨hEraseV, hEraseCard, hDisjY, hYedge⟩,
    mem_parentPairLink.mpr ⟨hEraseV, hEraseCard, hDisjZ, hZedge⟩⟩

/-- Different members of a linear star have disjoint pairs after removing
    their common vertex. -/
theorem disjoint_erased_tails_of_linear_star
    {C : Family α} {P Q : Edge α} {x : α}
    (hL : LinearFamily C)
    (hP : P ∈ C) (hQ : Q ∈ C) (hNe : P ≠ Q)
    (hxP : x ∈ P) (hxQ : x ∈ Q) :
    Disjoint (P.erase x) (Q.erase x) := by
  have hOne : (P ∩ Q).card ≤ 1 := hL hP hQ hNe
  have hxInter : x ∈ P ∩ Q := Finset.mem_inter.mpr ⟨hxP, hxQ⟩
  have hSingleton : ({x} : Edge α) ⊆ P ∩ Q := by
    simpa using hxInter
  have hInterEq : ({x} : Edge α) = P ∩ Q :=
    Finset.eq_of_subset_of_card_le hSingleton (by simpa using hOne)
  apply Finset.disjoint_left.mpr
  intro a haP haQ
  have haInter : a ∈ P ∩ Q := Finset.mem_inter.mpr
    ⟨Finset.mem_of_mem_erase haP, Finset.mem_of_mem_erase haQ⟩
  have hax : a = x := Finset.mem_singleton.mp (hInterEq ▸ haInter)
  exact (Finset.ne_of_mem_erase haP) hax

/-- Bad parent-link pairs for one retained tail pair. -/
noncomputable def badParentPartners
    (H : Family α) (V A S : Edge α)
    (good : Edge α → Edge α → Edge α → Prop) : Family α := by
  classical
  exact (parentPairLink H V A).filter fun T => ¬ good A S T

/-- The global parent label requirement used in the star branch: a good
    partner's label belongs to every actual parent common core. -/
def GoodPairLabelValid
    (H : Family α) (V : Edge α)
    (good : Edge α → Edge α → Edge α → Prop)
    (label : Edge α → Edge α → α) : Prop :=
  ∀ (A A' S T : Edge α),
    good A S T →
    S ∈ parentPairLink H V A' →
    T ∈ parentPairLink H V A' →
    label S T ∈ A'

/-- Each other tail pair in a linear common star is an actual bad parent
    partner.  The witness at the second prefix is retained in `K`. -/
theorem common_star_other_tail_is_bad
    {K H : Family α} {V Y Z P₀ P : Edge α} {x : α}
    (hKH : K ⊆ H) (hYZ : Disjoint Y Z)
    (hP₀ : P₀ ∈ commonPrefixTriples K V Y Z)
    (hP : P ∈ commonPrefixTriples K V Y Z)
    (hx₀ : x ∈ P₀) (hx : x ∈ P)
    (center : Edge α → α)
    (hCenterY : center (Y ∪ {x}) ∈ Y)
    (good : Edge α → Edge α → Edge α → Prop)
    (label : Edge α → Edge α → α)
    (hGoodCenter : ∀ A S T, good A S T → label S T = center A)
    (hLabel : GoodPairLabelValid H V good label) :
    P.erase x ∈ badParentPartners H V (Y ∪ {x}) (P₀.erase x) good := by
  classical
  have hLinkY := (common_tail_erase_mem_parent_link hKH hP hx).1
  have hLinkZ₀ := (common_tail_erase_mem_parent_link hKH hP₀ hx₀).2
  have hLinkZ := (common_tail_erase_mem_parent_link hKH hP hx).2
  change P.erase x ∈
    (parentPairLink H V (Y ∪ {x})).filter
      (fun T => ¬ good (Y ∪ {x}) (P₀.erase x) T)
  apply Finset.mem_filter.mpr
  refine ⟨hLinkY, ?_⟩
  intro hGood
  have hLabelZ : label (P₀.erase x) (P.erase x) ∈ Z ∪ {x} :=
    hLabel (Y ∪ {x}) (Z ∪ {x}) (P₀.erase x) (P.erase x)
      hGood hLinkZ₀ hLinkZ
  rw [hGoodCenter _ _ _ hGood] at hLabelZ
  have hxOut : x ∉ Y := by
    have hP₀disj := (mem_commonPrefixTriples.mp hP₀).2.2.1
    exact (Finset.disjoint_left.mp
      (Finset.disjoint_union_right.mp hP₀disj).1) hx₀
  rcases Finset.mem_union.mp hLabelZ with hZ | hX
  · exact (Finset.disjoint_left.mp hYZ) hCenterY hZ
  · exact hxOut ((Finset.mem_singleton.mp hX) ▸ hCenterY)

/-- The star branch counts distinct actual bad partner pairs, with the
    distinguished base triple contributing the sole additive one. -/
theorem common_star_card_le_one_add_bad_partners
    {K H : Family α} {V Y Z P₀ : Edge α} {x : α}
    (hKH : K ⊆ H) (hYZ : Disjoint Y Z)
    (hP₀ : P₀ ∈ commonPrefixTriples K V Y Z)
    (hStar : ∀ ⦃P : Edge α⦄,
      P ∈ commonPrefixTriples K V Y Z → x ∈ P)
    (center : Edge α → α)
    (hCenterY : center (Y ∪ {x}) ∈ Y)
    (good : Edge α → Edge α → Edge α → Prop)
    (label : Edge α → Edge α → α)
    (hGoodCenter : ∀ A S T, good A S T → label S T = center A)
    (hLabel : GoodPairLabelValid H V good label) :
    (commonPrefixTriples K V Y Z).card ≤
      1 + (badParentPartners H V (Y ∪ {x}) (P₀.erase x) good).card := by
  let C := commonPrefixTriples K V Y Z
  let B := badParentPartners H V (Y ∪ {x}) (P₀.erase x) good
  let f : Edge α → Edge α := fun P => P.erase x
  have hmap : Set.MapsTo f (↑(C.erase P₀) : Set (Edge α))
      (↑B : Set (Edge α)) := by
    intro P hP
    have hPC : P ∈ C := Finset.mem_of_mem_erase hP
    exact common_star_other_tail_is_bad hKH hYZ hP₀ hPC
      (hStar hP₀) (hStar hPC) center hCenterY good label
      hGoodCenter hLabel
  have hinj : Set.InjOn f (↑(C.erase P₀) : Set (Edge α)) := by
    intro P hP Q hQ hEq
    change P.erase x = Q.erase x at hEq
    have hxP : x ∈ P := hStar (Finset.mem_of_mem_erase hP)
    have hxQ : x ∈ Q := hStar (Finset.mem_of_mem_erase hQ)
    have hRestoreP : ({x} : Edge α) ∪ P.erase x = P := by
      ext a
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_erase]
      constructor
      · rintro (rfl | ⟨_, haP⟩)
        · exact hxP
        · exact haP
      · intro haP
        by_cases hax : a = x
        · exact Or.inl hax
        · exact Or.inr ⟨hax, haP⟩
    have hRestoreQ : ({x} : Edge α) ∪ Q.erase x = Q := by
      ext a
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_erase]
      constructor
      · rintro (rfl | ⟨_, haQ⟩)
        · exact hxQ
        · exact haQ
      · intro haQ
        by_cases hax : a = x
        · exact Or.inl hax
        · exact Or.inr ⟨hax, haQ⟩
    calc
      P = ({x} : Edge α) ∪ P.erase x := hRestoreP.symm
      _ = ({x} : Edge α) ∪ Q.erase x := by rw [hEq]
      _ = Q := hRestoreQ
  have hBound : (C.erase P₀).card ≤ B.card :=
    Finset.card_le_card_of_injOn f hmap hinj
  have hErase : (C.erase P₀).card + 1 = C.card :=
    Finset.card_erase_add_one hP₀
  change C.card ≤ 1 + B.card
  omega

/-- The manuscript's uniform disjoint-prefix common-system bound (IV.B.2),
    expressed with the actual parent pair-link degree.  The local pair-label,
    center, and bad-partner estimates are explicit inputs; neither the star
    nor non-star conclusion is assumed. -/
theorem disjoint_prefix_common_system_bound
    {K H : Family α} {V Y Z : Edge α}
    (hH : Admissible H) (hKH : K ⊆ H)
    (hY : Y.Nonempty) (hZ : Z.Nonempty)
    (hYZ : Disjoint Y Z)
    (pairLabel : Edge α → α)
    (hYpair : PairCompletionLabelInPrefix K pairLabel Y)
    (hZpair : PairCompletionLabelInPrefix K pairLabel Z)
    (center : Edge α → α)
    (hPrefixCenter : ∀ P ∈ commonPrefixTriples K V Y Z,
      ∀ x ∈ P, center (Y ∪ {x}) ∈ Y)
    (good : Edge α → Edge α → Edge α → Prop)
    (strongLabel : Edge α → Edge α → α)
    (hGoodCenter : ∀ A S T, good A S T →
      strongLabel S T = center A)
    (hStrongLabel : GoodPairLabelValid H V good strongLabel)
    (ε : ℝ) (hε : 0 ≤ ε) (D : ℕ)
    (hBadFraction : ∀ A S,
      S ∈ parentPairLink H V A →
      ((badParentPartners H V A S good).card : ℝ) ≤
        ε * ((parentPairLink H V A).card : ℝ))
    (hMaxDegree : ∀ A, (parentPairLink H V A).card ≤ D) :
    ((commonPrefixTriples K V Y Z).card : ℝ) ≤
      max 7 (1 + ε * (D : ℝ)) := by
  let C := commonPrefixTriples K V Y Z
  have hK : Admissible K := admissible_mono hKH hH
  rcases common_prefix_triples_star_or_small hK hY hZ hYZ
      pairLabel hYpair hZpair with hStar | hSmall
  · obtain ⟨x, hxStar⟩ := hStar
    by_cases hEmpty : C = ∅
    · simp [C, hEmpty]
    · have hNonempty : C.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
      obtain ⟨P₀, hP₀⟩ := hNonempty
      have hxP₀ : x ∈ P₀ := hxStar hP₀
      have hCenterY : center (Y ∪ {x}) ∈ Y :=
        hPrefixCenter P₀ hP₀ x hxP₀
      have hCard := common_star_card_le_one_add_bad_partners
        hKH hYZ hP₀ hxStar center hCenterY good strongLabel
        hGoodCenter hStrongLabel
      have hLink := (common_tail_erase_mem_parent_link
        hKH hP₀ hxP₀).1
      have hBad := hBadFraction (Y ∪ {x}) (P₀.erase x) hLink
      have hDegNat := hMaxDegree (Y ∪ {x})
      have hDeg : ((parentPairLink H V (Y ∪ {x})).card : ℝ) ≤ D := by
        exact_mod_cast hDegNat
      have hScaled : ε * ((parentPairLink H V (Y ∪ {x})).card : ℝ) ≤
          ε * (D : ℝ) := mul_le_mul_of_nonneg_left hDeg hε
      have hCardReal : (C.card : ℝ) ≤
          1 + ((badParentPartners H V (Y ∪ {x})
            (P₀.erase x) good).card : ℝ) := by
        exact_mod_cast hCard
      exact hCardReal.trans (by
        calc
          1 + ((badParentPartners H V (Y ∪ {x})
              (P₀.erase x) good).card : ℝ)
              ≤ 1 + ε * ((parentPairLink H V (Y ∪ {x})).card : ℝ) := by
                  linarith
          _ ≤ 1 + ε * (D : ℝ) := by linarith
          _ ≤ max 7 (1 + ε * (D : ℝ)) := le_max_right _ _)
  · exact (by exact_mod_cast hSmall : (C.card : ℝ) ≤ 7).trans
      (le_max_left _ _)

end PrefixCommonSystem

end JSP523
