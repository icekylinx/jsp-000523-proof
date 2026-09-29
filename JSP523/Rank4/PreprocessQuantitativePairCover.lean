import JSP523.Rank4.PreprocessHeavyPairMoment

/-! # Actual quantitative cover of heavy pairs -/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- Select the actual maximal matching and its endpoint cover.  All
second-moment premises are discharged from the original family and its
facet cap.  The surviving induced family has pair degree at most `T|U|`. -/
theorem exists_quantitative_heavy_pair_cover
    (F : Family α) (U : Edge α) (T R : ℕ)
    (hSupport : F ⊆ U.powersetCard 4) (hAdm : Admissible F)
    (hTripleCap : ∀ S ∈ U.powersetCard 3,
      (tripleCompletionVertices F U S).card ≤ R)
    (hR : 3 ≤ R) (hT : 0 < T) (hU : 0 < U.card) (hGap : 2 * R ≤ T ^ 2) :
    ∃ X : Edge α,
      X ⊆ U ∧ X.card * T ≤ 8 * U.card ∧
      (∀ P ∈ U.powersetCard 2, Disjoint P X → rankFourPairDegree F P ≤ T * U.card) ∧
      (∀ P : Edge α, P.card = 2 →
        rankFourPairDegree (F.filter fun E => Disjoint E X) P ≤ T * U.card) := by
  classical
  obtain ⟨M, hHeavy, hMatching, hCover, hCard⟩ :=
    actual_heavy_pair_roots_maximal_matching_cover F U (T * U.card)
  let X := M.biUnion fun P => P
  have hMpair : ∀ P ∈ M, P ∈ U.powersetCard 2 := by
    intro P hP
    exact (Finset.mem_filter.mp (hHeavy hP)).1
  have hXU : X ⊆ U := by
    intro x hx
    obtain ⟨P, hP, hxP⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_powersetCard.mp (hMpair P hP)).1 hxP
  have hTail : ∀ P ∈ M, T * U.card ≤ (actualPairRootTails F U P).card := by
    intro P hP
    rw [actual_pair_root_tails_card_eq_rank_four_pair_degree F U P hSupport (hMpair P hP)]
    exact Nat.le_of_lt (Finset.mem_filter.mp (hHeavy hP)).2
  have hPairs : (U.powersetCard 2).card ≤ U.card * U.card := by
    simpa [pow_two] using Nat.choose_le_pow U.card 2
  have hDenom : 2 * (U.powersetCard 2).card * R ≤ (T * U.card) ^ 2 := by
    calc
      _ ≤ 2 * (U.card * U.card) * R := Nat.mul_le_mul_right R (Nat.mul_le_mul_left 2 hPairs)
      _ = (2 * R) * U.card ^ 2 := by ring
      _ ≤ T ^ 2 * U.card ^ 2 := Nat.mul_le_mul_right _ hGap
      _ = (T * U.card) ^ 2 := by ring
  have hMT : M.card * T ≤ 4 * U.card := by
    by_cases hM : M.card = 0
    · simp [hM]
    · let A := chooseActualPairTailSelection F M U (T * U.card) hTail
      have hSelection : uniformActualPairTailSelection F M U (T * U.card) A :=
        choose_actual_pair_tail_selection_spec F M U (T * U.card) hTail
      have hMoment := actual_pair_tail_selection_square_moment_of_caps
        F M U A (T * U.card) R hSelection hMpair hMatching hAdm hTripleCap hR
      exact heavy_matching_card_le_four_mul_n_div_t hMoment (Nat.pos_of_ne_zero hM)
        (Nat.le_refl _) (Nat.mul_pos hT hU) hPairs (by simpa [pow_two] using hDenom)
  have hLow : ∀ P ∈ U.powersetCard 2, Disjoint P X → rankFourPairDegree F P ≤ T * U.card := by
    intro P hP hDisj
    by_contra h
    have hHeavyP : P ∈ actualHeavyPairRoots F U (T * U.card) := Finset.mem_filter.mpr ⟨hP, by omega⟩
    obtain ⟨x, hxP, hxX⟩ := hCover P hHeavyP
    exact Finset.disjoint_left.mp hDisj hxP hxX
  refine ⟨X, hXU, ?_, hLow, ?_⟩
  · change (M.biUnion fun P => P).card * T ≤ _
    nlinarith [Nat.mul_le_mul_right T hCard]
  · intro P hPcard
    let K := F.filter fun E => Disjoint E X
    by_cases hParents : (K.filter fun E => P ⊆ E).Nonempty
    · obtain ⟨E, hE⟩ := hParents
      have hEK := (Finset.mem_filter.mp hE).1
      have hPE := (Finset.mem_filter.mp hE).2
      have hEF := (Finset.mem_filter.mp hEK).1
      have hEX := (Finset.mem_filter.mp hEK).2
      have hPU : P ⊆ U := hPE.trans (Finset.mem_powersetCard.mp (hSupport hEF)).1
      have hPX : Disjoint P X := hEX.mono_left hPE
      have hBound := hLow P (Finset.mem_powersetCard.mpr ⟨hPU, hPcard⟩) hPX
      apply le_trans (b := rankFourPairDegree F P) ?_ hBound
      apply Finset.card_le_card
      intro Q hQ
      have hs := Finset.mem_filter.mp hQ
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hs.1).1, hs.2⟩
    · have hEmpty := Finset.not_nonempty_iff_eq_empty.mp hParents
      change (K.filter fun E => P ⊆ E).card ≤ _
      simp [hEmpty]

end JSP523.Rank4
