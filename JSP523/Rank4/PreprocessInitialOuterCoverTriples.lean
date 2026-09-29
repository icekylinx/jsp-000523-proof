import JSP523.Rank4.PreprocessHeavyPairMoment
import JSP523.Rank4.GlobalDegreeTail
import JSP523.Counting.CommonPrefixTails

/-! # Actual heavy-triple cover in the initial rank-four decomposition -/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- Disjoint triple roots have at most one common completion vertex. -/
theorem disjoint_triple_completions_inter_card_le_one
    (H : Family α) (W P Q : Edge α)
    (hAdm : Admissible H) (hUniform : Uniform 4 H)
    (hP : P.card = 3) (hQ : Q.card = 3) (hPQ : Disjoint P Q) :
    (tripleCompletionVertices H W P ∩ tripleCompletionVertices H W Q).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro x hx y hy
  by_contra hxy
  have hTail (z : α) (hz : z ∈ tripleCompletionVertices H W P ∩ tripleCompletionVertices H W Q) :
      ({z} : Edge α) ∈ commonPrefixTails H W P Q 1 := by
    have hzP := Finset.mem_filter.mp (Finset.mem_inter.mp hz).1
    have hzQ := Finset.mem_filter.mp (Finset.mem_inter.mp hz).2
    have hzNotP : z ∉ P := by
      intro hzIn
      have h := hUniform hzP.2
      simp [Finset.insert_eq_of_mem hzIn, hP] at h
    have hzNotQ : z ∉ Q := by
      intro hzIn
      have h := hUniform hzQ.2
      simp [Finset.insert_eq_of_mem hzIn, hQ] at h
    apply mem_common_prefix_tails.mpr
    refine ⟨Finset.singleton_subset_iff.mpr hzP.1, Finset.card_singleton _, ?_, ?_, ?_⟩
    · exact Finset.disjoint_singleton_left.mpr (by simpa using And.intro hzNotP hzNotQ)
    · simpa only [Finset.union_singleton] using hzP.2
    · simpa only [Finset.union_singleton] using hzQ.2
  have hIntersect := common_prefix_tails_intersecting (W := W) hAdm
    (Finset.card_pos.mp (by omega : 0 < P.card))
    (Finset.card_pos.mp (by omega : 0 < Q.card)) hPQ (by decide : 1 ≤ 1)
  have h := hIntersect (hTail x hx) (hTail y hy) (by simpa using hxy)
  simp [hxy] at h

noncomputable def initialHeavyTriples (H : Family α) (W : Edge α) (t : ℕ) : Family α :=
  (W.powersetCard 3).filter fun T => t ≤ (tripleCompletionVertices H W T).card

/-- The exact multiplicity estimate in III.A.3 controls a disjoint
matching of actual heavy triples. -/
theorem initial_heavy_triple_matching_bound
    (H M : Family α) (W : Edge α) (t : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform 4 H)
    (hHeavy : M ⊆ initialHeavyTriples H W t) (hMatching : pairRootMatching M)
    (ht : 0 < t) (hGap : 2 * W.card ≤ t ^ 2) :
    M.card * t ≤ 2 * W.card := by
  classical
  have hTail (P : Edge α) (hP : P ∈ M) : t ≤ (tripleCompletionVertices H W P).card :=
    (Finset.mem_filter.mp (hHeavy hP)).2
  let A : Edge α → Edge α := fun P =>
    if hP : P ∈ M then Classical.choose (Finset.exists_subset_card_eq (hTail P hP)) else ∅
  have hSelection (P : Edge α) (hP : P ∈ M) :
      A P ⊆ tripleCompletionVertices H W P ∧ (A P).card = t := by
    simpa only [A, dite_eq_left hP] using
      Classical.choose_spec (Finset.exists_subset_card_eq (hTail P hP))
  have hSubset (P : Edge α) (hP : P ∈ M) : A P ⊆ W :=
    (hSelection P hP).1.trans (Finset.filter_subset _ _)
  have hCross (P : Edge α) (hP : P ∈ M) (Q : Edge α) (hQ : Q ∈ M) (hPQ : P ≠ Q) :
      ((A P ∩ A Q) ∩ W).card ≤ 1 := by
    apply (Finset.card_le_card (show (A P ∩ A Q) ∩ W ⊆
      tripleCompletionVertices H W P ∩ tripleCompletionVertices H W Q from
        Finset.inter_subset_left.trans (Finset.inter_subset_inter (hSelection P hP).1 (hSelection Q hQ).1))).trans
    exact disjoint_triple_completions_inter_card_le_one H W P Q hAdm hUniform
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp (hHeavy hP)).1).2
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp (hHeavy hQ)).1).2
      (hMatching P hP Q hQ hPQ)
  have hMoment := selected_tail_square_moment_bound M W A t 1 hSubset
    (fun P hP => (hSelection P hP).2) hCross
  by_cases hZero : M.card = 0
  · simp [hZero]
  have hMpos : 0 < M.card := Nat.pos_of_ne_zero hZero
  have hCancel : M.card * t ^ 2 ≤ W.card * (t + (M.card - 1)) := by
    apply Nat.le_of_mul_le_mul_left (c := M.card) _ hMpos
    nlinarith only [hMoment]
  have hOne : M.card - 1 + 1 = M.card := by omega
  have hScaledGap := Nat.mul_le_mul_left M.card hGap
  have hSmall : M.card * t ^ 2 ≤ 2 * W.card * t := by
    nlinarith only [hCancel, hOne, hScaledGap]
  exact Nat.le_of_mul_le_mul_right (by nlinarith only [hSmall]) ht

/-- A concrete vertex cover of the actual heavy triples. Removing it
leaves every triple degree strictly below the threshold. -/
theorem exists_initial_heavy_triple_cover
    (H : Family α) (W : Edge α) (t : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform 4 H)
    (ht : 0 < t) (hGap : 2 * W.card ≤ t ^ 2) :
    ∃ X : Edge α, X ⊆ W ∧ X.card * t ≤ 6 * W.card ∧
      ∀ T ∈ W.powersetCard 3, Disjoint T X → (tripleCompletionVertices H W T).card < t := by
  classical
  let S := initialHeavyTriples H W t
  let M := maximalDisjointPairRoots S
  have hMem : M ∈ pairRootMatchingCandidates S := (maximal_disjoint_pair_roots_spec S).1
  have hSub : M ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp hMem).1
  have hMatch : pairRootMatching M := (Finset.mem_filter.mp hMem).2
  let X := M.biUnion fun P => P
  have hXW : X ⊆ W := by
    intro x hx
    obtain ⟨P,hP,hxP⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp (hSub hP)).1).1 hxP
  have hCard : X.card ≤ 3 * M.card := by
    calc
      _ ≤ ∑ P ∈ M, P.card := Finset.card_biUnion_le
      _ = ∑ _P ∈ M, 3 := Finset.sum_congr rfl (fun P hP =>
        (Finset.mem_powersetCard.mp (Finset.mem_filter.mp (hSub hP)).1).2)
      _ = _ := by simp [Nat.mul_comm]
  have hMT := initial_heavy_triple_matching_bound H M W t hAdm hUniform hSub hMatch ht hGap
  refine ⟨X,hXW, by nlinarith [Nat.mul_le_mul_right t hCard], ?_⟩
  intro T hT hDisj
  by_contra hLow
  have hHeavy : T ∈ S := Finset.mem_filter.mpr ⟨hT, by omega⟩
  by_cases hTM : T ∈ M
  · obtain ⟨x,hx⟩ := Finset.card_pos.mp (by have := (Finset.mem_powersetCard.mp hT).2; omega : 0 < T.card)
    exact Finset.disjoint_left.mp hDisj hx (Finset.mem_biUnion.mpr ⟨T,hTM,hx⟩)
  · obtain ⟨P,hP,hNot⟩ := maximal_disjoint_pair_roots_maximal S T hHeavy hTM
    obtain ⟨x,hxT,hxP⟩ := Finset.not_disjoint_iff.mp hNot
    exact Finset.disjoint_left.mp hDisj hxT (Finset.mem_biUnion.mpr ⟨P,hP,hxP⟩)

end JSP523.Rank4
