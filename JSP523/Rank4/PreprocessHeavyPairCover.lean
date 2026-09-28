import JSP523.Basic
import JSP523.Rank4.PreprocessCellMoment
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Finite maximal disjoint cover for heavy pair roots

The maximal matching step in §III.A.4 is represented by an actual finite
family of pair roots.  A cardinality-maximal disjoint subfamily covers every
root in the heavy family by one of its endpoints.
-/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- Pairwise disjointness for a family of distinct pair roots. -/
def pairRootMatching (M : Family α) : Prop :=
  ∀ P ∈ M, ∀ Q ∈ M, P ≠ Q → Disjoint P Q

/-- Candidate disjoint subfamilies of `S`. -/
noncomputable def pairRootMatchingCandidates (S : Family α) : Finset (Family α) := by
  classical
  exact S.powerset.filter pairRootMatching

omit [DecidableEq α] in
theorem pair_root_matching_candidates_nonempty (S : Family α) :
    (pairRootMatchingCandidates S).Nonempty := by
  classical
  refine ⟨∅, ?_⟩
  simp [pairRootMatchingCandidates, pairRootMatching]

/-- A maximum-cardinality matching of the finite pair-root family. -/
noncomputable def maximalDisjointPairRoots (S : Family α) : Family α :=
  Classical.choose (Finset.exists_max_image (pairRootMatchingCandidates S)
    Finset.card (pair_root_matching_candidates_nonempty S))

omit [DecidableEq α] in
theorem maximal_disjoint_pair_roots_spec (S : Family α) :
    maximalDisjointPairRoots S ∈ pairRootMatchingCandidates S ∧
      ∀ M ∈ pairRootMatchingCandidates S,
        M.card ≤ (maximalDisjointPairRoots S).card := by
  exact Classical.choose_spec (Finset.exists_max_image
    (pairRootMatchingCandidates S) Finset.card
    (pair_root_matching_candidates_nonempty S))

/-- Any heavy root disjoint from every selected root could be added to the
matching, contradicting maximum cardinality. -/
theorem maximal_disjoint_pair_roots_maximal
    (S : Family α) (P : Edge α) (hP : P ∈ S)
    (hNotM : P ∉ maximalDisjointPairRoots S) :
    ∃ Q ∈ maximalDisjointPairRoots S, ¬ Disjoint P Q := by
  classical
  by_contra h
  push Not at h
  let M := maximalDisjointPairRoots S
  have hSpec := maximal_disjoint_pair_roots_spec S
  have hSpecMem : M ∈ S.powerset.filter pairRootMatching := by
    simpa [M, pairRootMatchingCandidates] using hSpec.1
  have hM : pairRootMatching M := by
    exact (Finset.mem_filter.mp hSpecMem).2
  have hMsub : M ⊆ S := Finset.mem_powerset.mp
    (Finset.mem_filter.mp hSpecMem).1
  have hInsSub : insert P M ⊆ S := by
    intro Q hQ
    rcases Finset.mem_insert.mp hQ with hEq | hQM
    · exact hEq ▸ hP
    · exact hMsub hQM
  have hInsMatch : pairRootMatching (insert P M) := by
    intro A hA B hB hAB
    rcases Finset.mem_insert.mp hA with hAP | hAM
    · subst A
      rcases Finset.mem_insert.mp hB with hBP | hBM
      · exact False.elim (hAB hBP.symm)
      · exact h B hBM
    · rcases Finset.mem_insert.mp hB with hBP | hBM
      · subst B
        exact (h A hAM).symm
      · exact hM A hAM B hBM hAB
  have hInsMem : insert P M ∈ pairRootMatchingCandidates S :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hInsSub, hInsMatch⟩
  have hMax := (maximal_disjoint_pair_roots_spec S).2 (insert P M) hInsMem
  have hCard : (insert P M).card = M.card + 1 :=
    Finset.card_insert_of_notMem hNotM
  rw [hCard] at hMax
  change M.card + 1 ≤ M.card at hMax
  omega

/-- The selected roots cover the entire heavy pair-root family by endpoints. -/
theorem maximal_disjoint_pair_roots_endpoint_cover
    (S : Family α)
    (hPair : ∀ P ∈ S, P.card = 2) :
    ∀ P ∈ S, ∃ a ∈ P, a ∈ (maximalDisjointPairRoots S).biUnion fun Q => Q := by
  classical
  intro P hP
  let M := maximalDisjointPairRoots S
  by_cases hPM : P ∈ M
  · have hPcard := hPair P hP
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < P.card)
    refine ⟨a, ha, Finset.mem_biUnion.mpr ⟨P, hPM, ha⟩⟩
  · obtain ⟨Q, hQM, hNotDisj⟩ :=
      maximal_disjoint_pair_roots_maximal S P hP hPM
    obtain ⟨a, ha⟩ := Finset.not_disjoint_iff_nonempty_inter.mp hNotDisj
    exact ⟨a, (Finset.mem_inter.mp ha).1,
      Finset.mem_biUnion.mpr ⟨Q, hQM, (Finset.mem_inter.mp ha).2⟩⟩

/-- Actual heavy pair roots in a rank-four family. -/
def actualHeavyPairRoots (F : Family α) (U : Edge α) (T : ℕ) : Family α :=
  (U.powersetCard 2).filter fun P => T < rankFourPairDegree F P

/-- The maximum matching cover applies directly to the actual high-codegree
pairs in the fixed ground set. -/
theorem actual_heavy_pair_roots_maximal_matching_cover
    (F : Family α) (U : Edge α) (T : ℕ) :
    ∃ M : Family α,
      M ⊆ actualHeavyPairRoots F U T ∧
      pairRootMatching M ∧
      (∀ P ∈ actualHeavyPairRoots F U T,
        ∃ a ∈ P, a ∈ M.biUnion fun Q => Q) ∧
      (M.biUnion fun Q => Q).card ≤ 2 * M.card := by
  classical
  let S := actualHeavyPairRoots F U T
  let M := maximalDisjointPairRoots S
  have hSpec := maximal_disjoint_pair_roots_spec S
  have hMmem : M ∈ pairRootMatchingCandidates S := by
    simpa [M] using hSpec.1
  have hMsub : M ⊆ S := Finset.mem_powerset.mp
    (Finset.mem_filter.mp hMmem).1
  have hMmatch : pairRootMatching M := (Finset.mem_filter.mp hMmem).2
  refine ⟨M, hMsub, hMmatch, ?_, ?_⟩
  · intro P hP
    exact maximal_disjoint_pair_roots_endpoint_cover S
      (fun P hP => (Finset.mem_powersetCard.mp
        (Finset.mem_filter.mp hP).1).2) P hP
  · calc
      _ ≤ ∑ P ∈ M, P.card := Finset.card_biUnion_le
      _ = ∑ _P ∈ M, 2 := by
        apply Finset.sum_congr rfl
        intro P hP
        have hPH : P ∈ S := hMsub hP
        exact (Finset.mem_powersetCard.mp
          (Finset.mem_filter.mp hPH).1).2
      _ = 2 * M.card := by simp [Nat.mul_comm]

end JSP523.Rank4
