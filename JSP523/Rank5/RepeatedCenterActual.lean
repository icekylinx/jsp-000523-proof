import JSP523.Rank5.RepeatedCenterDegree

/-!
# Actual repeated-center codegree count (IV.7.1)--(IV.7.2)

All strong partners and common cells below are computed in one fixed parent
family.  The left projection of the incidence set is bounded through edges
containing `P ∪ {z}`; each right fiber is bounded through edges containing
`A ∪ U`.  These are the two actual parent codegrees used in the manuscript.
-/

namespace JSP523.Rank5

open JSP523

variable {α : Type*} [DecidableEq α]

/-- Incidences between strong partners with center `z` and their actual
common-prefix tails. -/
noncomputable def repeatedCenterIncidences
    (H : Family α) (W P : Edge α) (s k t : ℕ) (z : α) (U : Edge α) :
    Finset (Edge α × Edge α) := by
  classical
  exact (actualCenterPartners H W P s k t z U ×ˢ W.powersetCard k).filter
    fun qa => qa.2 ∈ commonPrefixTails H W P qa.1 k

theorem mem_repeated_center_incidences
    {H : Family α} {W P Q A : Edge α} {s k t : ℕ} {z : α} {U : Edge α} :
    (Q, A) ∈ repeatedCenterIncidences H W P s k t z U ↔
      Q ∈ actualCenterPartners H W P s k t z U ∧
      A ∈ W.powersetCard k ∧ A ∈ commonPrefixTails H W P Q k := by
  simp only [repeatedCenterIncidences, Finset.mem_filter, Finset.mem_product]
  tauto

/-- For each strong partner `Q`, its incidence fiber is precisely the actual
common-prefix cell. -/
theorem repeated_center_left_fiber_eq
    (H : Family α) (W P Q : Edge α) (s k t : ℕ) (z : α) (U : Edge α)
    (hQ : Q ∈ actualCenterPartners H W P s k t z U) :
    ((repeatedCenterIncidences H W P s k t z U).filter
      fun qa => qa.1 = Q).card =
      (commonPrefixTails H W P Q k).card := by
  classical
  let C := commonPrefixTails H W P Q k
  have hEq : ((repeatedCenterIncidences H W P s k t z U).filter
      fun qa => qa.1 = Q) = C.image (fun A => (Q, A)) := by
    ext ⟨Q', A⟩
    simp only [Finset.mem_filter, mem_repeated_center_incidences,
      Finset.mem_image]
    constructor
    · rintro ⟨⟨hQ', hA, hCell⟩, rfl⟩
      exact ⟨A, hCell, rfl⟩
    · rintro ⟨B, hB, hEq⟩
      cases hEq
      exact ⟨⟨hQ, (Finset.mem_filter.mp hB).1, hB⟩, rfl⟩
  rw [hEq, Finset.card_image_of_injective]
  intro A B h
  exact congrArg Prod.snd h

/-- The set of tails appearing in a repeated-center incidence injects into
the actual parent edges through `P ∪ {z}`. -/
theorem repeated_center_tail_projection_le_codegree
    (H : Family α) (W P : Edge α) (s k t : ℕ) (z : α) (U : Edge α) :
    ((repeatedCenterIncidences H W P s k t z U).image Prod.snd).card ≤
      (H.filter fun E => P ∪ {z} ⊆ E).card := by
  classical
  let I := repeatedCenterIncidences H W P s k t z U
  let tails := I.image Prod.snd
  let f : Edge α → Edge α := fun A => P ∪ A
  apply Finset.card_le_card_of_injOn f
  · intro A hA
    obtain ⟨⟨Q, B⟩, hI, hBA⟩ := Finset.mem_image.mp hA
    have hBA' : B = A := hBA
    subst B
    obtain ⟨hQ, _, hCell⟩ := mem_repeated_center_incidences.mp hI
    have hC := mem_common_prefix_tails.mp hCell
    have hStrong : ActualStrongPartner H W P Q s k t z :=
      (Finset.mem_filter.mp hQ).2.1
    have hzA : z ∈ A := hStrong.2.2.2.1 A hCell
    apply Finset.mem_filter.mpr
    refine ⟨hC.2.2.2.1, ?_⟩
    intro x hx
    rcases Finset.mem_union.mp hx with hxP | hxz
    · exact Finset.mem_union_left A hxP
    · exact Finset.mem_union_right P (Finset.mem_singleton.mp hxz ▸ hzA)
  · intro A hA B hB hEq
    obtain ⟨⟨Q, C⟩, hI, hCA⟩ := Finset.mem_image.mp hA
    obtain ⟨⟨Q', D⟩, hI', hDB⟩ := Finset.mem_image.mp hB
    have hDisjA : Disjoint P A := by
      have hCell := (mem_repeated_center_incidences.mp hI).2.2
      have hDisj := (mem_common_prefix_tails.mp hCell).2.2.1
      change C = A at hCA
      rw [hCA] at hDisj
      exact (Finset.disjoint_union_right.mp hDisj).1.symm
    have hDisjB : Disjoint P B := by
      have hCell := (mem_repeated_center_incidences.mp hI').2.2
      have hDisj := (mem_common_prefix_tails.mp hCell).2.2.1
      change D = B at hDB
      rw [hDB] at hDisj
      exact (Finset.disjoint_union_right.mp hDisj).1.symm
    calc
      A = (P ∪ A) \ P := (Finset.union_sdiff_cancel_left hDisjA).symm
      _ = (P ∪ B) \ P := by exact congrArg (· \ P) hEq
      _ = B := Finset.union_sdiff_cancel_left hDisjB

/-- Fixing a tail `A`, its strong partners inject into parent edges through
`A ∪ U`.  The disjointness needed for injection is part of the actual cell. -/
theorem repeated_center_fixed_tail_le_codegree
    (H : Family α) (W P A : Edge α) (s k t : ℕ) (z : α) (U : Edge α) :
    ((repeatedCenterIncidences H W P s k t z U).filter
      fun qa => qa.2 = A).card ≤
      (H.filter fun E => A ∪ U ⊆ E).card := by
  classical
  let I := (repeatedCenterIncidences H W P s k t z U).filter
      fun qa => qa.2 = A
  let f : Edge α × Edge α → Edge α := fun qa => A ∪ qa.1
  apply Finset.card_le_card_of_injOn f
  · intro qa hqa
    obtain ⟨hI, hEq⟩ := Finset.mem_filter.mp hqa
    obtain ⟨hQ, _, hCell⟩ := mem_repeated_center_incidences.mp hI
    have hC := mem_common_prefix_tails.mp hCell
    have hUQ : U ⊆ qa.1 := (Finset.mem_filter.mp hQ).2.2
    have hEdge : A ∪ qa.1 ∈ H := by
      simpa [hEq, Finset.union_comm] using hC.2.2.2.2
    refine Finset.mem_filter.mpr ⟨hEdge, ?_⟩
    intro x hx
    rcases Finset.mem_union.mp hx with hxA | hxU
    · exact Finset.mem_union_left _ hxA
    · exact Finset.mem_union_right _ (hUQ hxU)
  · intro qa hqa qb hqb hEq
    have hAqa : Disjoint A qa.1 := by
      obtain ⟨hI, hTailEq⟩ := Finset.mem_filter.mp hqa
      have hC := mem_common_prefix_tails.mp (mem_repeated_center_incidences.mp hI).2.2
      have hDisj := (Finset.disjoint_union_right.mp hC.2.2.1).2
      rw [hTailEq] at hDisj
      exact hDisj
    have hAqb : Disjoint A qb.1 := by
      obtain ⟨hI, hTailEq⟩ := Finset.mem_filter.mp hqb
      have hC := mem_common_prefix_tails.mp (mem_repeated_center_incidences.mp hI).2.2
      have hDisj := (Finset.disjoint_union_right.mp hC.2.2.1).2
      rw [hTailEq] at hDisj
      exact hDisj
    have hQeq : qa.1 = qb.1 := by
      calc
        qa.1 = (A ∪ qa.1) \ A :=
          (Finset.union_sdiff_cancel_left hAqa).symm
        _ = (A ∪ qb.1) \ A := congrArg (· \ A) hEq
        _ = qb.1 := Finset.union_sdiff_cancel_left hAqb
    have hTaq : qa.2 = A := (Finset.mem_filter.mp hqa).2
    have hTbq : qb.2 = A := (Finset.mem_filter.mp hqb).2
    exact Prod.ext hQeq (hTaq.trans hTbq.symm)

/-- The actual parent-family version of the repeated-center bound.  Both
codegree hypotheses are on the fixed parent `H`, including the prescribed
set `U`; putting `U = ∅` gives (IV.7.1), and a `p`-set `U` gives (IV.7.2). -/
theorem repeated_center_partner_degree_bound
    (H : Family α) (W P : Edge α) (s k t : ℕ) (z : α) (U : Edge α)
    (Dleft Dright : ℕ)
    (hLeftCap : (H.filter fun E => P ∪ {z} ⊆ E).card ≤ Dleft)
    (hRightCap : ∀ A ∈
      (repeatedCenterIncidences H W P s k t z U).image Prod.snd,
      (H.filter fun E => A ∪ U ⊆ E).card ≤ Dright) :
    t * (actualCenterPartners H W P s k t z U).card ≤ Dleft * Dright := by
  classical
  let partners := actualCenterPartners H W P s k t z U
  let I := repeatedCenterIncidences H W P s k t z U
  apply finite_incidence_degree_bound I partners t Dleft Dright
  · intro qa hqa
    exact (mem_repeated_center_incidences.mp hqa).1
  · intro Q hQ
    rw [repeated_center_left_fiber_eq H W P Q s k t z U hQ]
    have hStrong : ActualStrongPartner H W P Q s k t z :=
      (Finset.mem_filter.mp hQ).2.1
    exact hStrong.2.2.1
  · exact (repeated_center_tail_projection_le_codegree H W P s k t z U).trans hLeftCap
  · intro A
    have hBase := repeated_center_fixed_tail_le_codegree H W P A s k t z U
    by_cases hA : A ∈ I.image Prod.snd
    · exact hBase.trans (hRightCap A hA)
    · have hEmpty : (I.filter fun qa => qa.2 = A) = ∅ := by
        ext qa
        constructor
        · intro hqa
          have hI := (Finset.mem_filter.mp hqa).1
          exact False.elim (hA (Finset.mem_image.mpr
            ⟨qa, hI, (Finset.mem_filter.mp hqa).2⟩))
        · simp
      simp [hEmpty]

/-- Uniform actual codegree caps imply the prescribed-set repeated-center
bound (IV.7.2).  The empty prescribed set is (IV.7.1). -/
theorem repeated_center_partner_bound_from_codegrees
    (H : Family α) (W P : Edge α) (s k t : ℕ) (z : α)
    (U : Edge α) (p Dleft Dright : ℕ)
    (hPsize : P.card = s) (hzP : z ∉ P) (hUsize : U.card = p)
    (hLeftCap : ∀ S : Edge α, S.card = s + 1 →
      (H.filter fun E => S ⊆ E).card ≤ Dleft)
    (hRightCap : ∀ S : Edge α, S.card = k + p →
      (H.filter fun E => S ⊆ E).card ≤ Dright) :
    t * (actualCenterPartners H W P s k t z U).card ≤ Dleft * Dright := by
  classical
  apply repeated_center_partner_degree_bound H W P s k t z U Dleft Dright
  · apply hLeftCap
    rw [Finset.card_union_of_disjoint]
    · simp [hPsize]
    · exact Finset.disjoint_singleton_right.mpr hzP
  · intro A hA
    obtain ⟨⟨Q, B⟩, hI, hBA⟩ := Finset.mem_image.mp hA
    have hCell := (mem_repeated_center_incidences.mp hI).2.2
    have hC := mem_common_prefix_tails.mp hCell
    have hQ := (mem_repeated_center_incidences.mp hI).1
    have hUQ : U ⊆ Q := (Finset.mem_filter.mp hQ).2.2
    have hAQ : Disjoint B Q :=
      (Finset.disjoint_union_right.mp hC.2.2.1).2
    have hBU : Disjoint B U := Finset.disjoint_left.mpr
      (fun x hxB hxU => (Finset.disjoint_left.mp hAQ) hxB (hUQ hxU))
    have hBA' : B = A := hBA
    rw [hBA'] at hBU
    apply hRightCap
    rw [Finset.card_union_of_disjoint hBU]
    have hAsize : A.card = k := by simpa [hBA'] using hC.2.1
    omega

end JSP523.Rank5
