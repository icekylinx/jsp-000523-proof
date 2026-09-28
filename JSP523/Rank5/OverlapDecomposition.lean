import JSP523.Rank5.FacetIncidence
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Multiple-parent four-faces and the refined rank-five surplus

Every one-parent face contributes zero to the previously established
overlap ledger.  A shared face contributes one initial collision, with
the remaining parent incidences recorded by an additional nonnegative
sum.  The resulting three-term identity feeds the shared-face slack into
the real surplus bound used later in the high-rank argument.
-/

namespace JSP523.Rank5

section OverlapDecomposition

variable {α : Type*} [DecidableEq α]

theorem shared_four_shadow_subset_four_shadow (all : Family α) :
    sharedFourShadow all ⊆ fourShadow all := by
  intro A hA
  exact (Finset.mem_filter.mp hA).1

/-- The overlap excess is supported exactly on faces with at least two
    parent edges. -/
theorem facet_overlap_excess_eq_shared_sum (all : Family α) :
    facetOverlapExcess all =
      (sharedFourShadow all).sum
        (fun A => (facetParents all A).card - 1) := by
  unfold facetOverlapExcess
  symm
  apply Finset.sum_subset (shared_four_shadow_subset_four_shadow all)
  intro A hA hnot
  have hpos : 0 < (facetParents all A).card :=
    Finset.card_pos.mpr (facet_parents_nonempty_of_shadow all A hA)
  have hlt : ¬ 2 ≤ (facetParents all A).card := by
    intro htwo
    exact hnot (Finset.mem_filter.mpr ⟨hA, htwo⟩)
  have hone : (facetParents all A).card = 1 := by omega
  simp [hone]

/-- Parent incidences beyond the second at each shared four-face. -/
def higherFacetOverlapExcess (all : Family α) : ℕ :=
  (sharedFourShadow all).sum
    (fun A => (facetParents all A).card - 2)

/-- Each shared face contributes one overlap, and any further parents
    contribute to the higher overlap excess. -/
theorem facet_overlap_excess_eq_shared_card_add_higher
    (all : Family α) :
    facetOverlapExcess all =
      (sharedFourShadow all).card + higherFacetOverlapExcess all := by
  calc
    facetOverlapExcess all =
        (sharedFourShadow all).sum
          (fun A => (facetParents all A).card - 1) :=
      facet_overlap_excess_eq_shared_sum all
    _ = (sharedFourShadow all).sum
          (fun A => 1 + ((facetParents all A).card - 2)) := by
      apply Finset.sum_congr rfl
      intro A hA
      have htwo : 2 ≤ (facetParents all A).card :=
        (Finset.mem_filter.mp hA).2
      omega
    _ = (sharedFourShadow all).card +
          higherFacetOverlapExcess all := by
      simp [higherFacetOverlapExcess, Finset.sum_add_distrib]

theorem shared_four_shadow_card_le_overlap_excess (all : Family α) :
    (sharedFourShadow all).card ≤ facetOverlapExcess all := by
  have hledger := facet_overlap_excess_eq_shared_card_add_higher all
  omega

/-- The exact parent multiplicity spectrum: private faces count once,
    shared faces count twice, and parents after the second are residual. -/
theorem four_shadow_parent_spectrum
    (all : Family α) (hUniform : Uniform 5 all) :
    5 * all.card =
      (privateFourShadow all).card +
        2 * (sharedFourShadow all).card +
          higherFacetOverlapExcess all := by
  have hledger := four_shadow_overlap_ledger all hUniform
  have hpartition := four_shadow_private_shared_card_partition all
  have hexcess := facet_overlap_excess_eq_shared_card_add_higher all
  omega

/-- Real signed surplus with the actual multiple-parent shadow retained
    on the left side. -/
theorem four_shadow_real_surplus_with_shared_slack
    (all : Family α) (z : Edge α → α)
    (hUniform : Uniform 5 all)
    (hshared : ∀ E ∈ unrootedEdges all z, ∀ a ∈ E,
      (∃ F ∈ all, F ≠ E ∧ E.erase a ⊆ F) →
      CoherentDeletedFace E z a) :
    (all.card : ℝ) - ((fourShadow all).card : ℝ) +
      ((sharedFourShadow all).card : ℝ) ≤
      -(all.card : ℝ) + 2 * ((rootedEdges all z).card : ℝ) := by
  have hnat := four_shadow_bound_with_shared_slack all z hUniform hshared
  have hcast :
      ((2 * all.card + (sharedFourShadow all).card : ℕ) : ℝ) ≤
      (((fourShadow all).card + 2 * (rootedEdges all z).card : ℕ) : ℝ) :=
    Nat.cast_le.mpr hnat
  have hreal :
      (2 : ℝ) * (all.card : ℝ) +
        ((sharedFourShadow all).card : ℝ) ≤
      ((fourShadow all).card : ℝ) +
        2 * ((rootedEdges all z).card : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hcast
  linarith

/-- Insert a separate real upper bound on the rooted error, while
    retaining the additional shared-face slack. -/
theorem four_shadow_real_surplus_with_error_and_shared_slack
    (all : Family α) (z : Edge α → α) (ε : ℝ)
    (hUniform : Uniform 5 all)
    (hshared : ∀ E ∈ unrootedEdges all z, ∀ a ∈ E,
      (∃ F ∈ all, F ≠ E ∧ E.erase a ⊆ F) →
      CoherentDeletedFace E z a)
    (hroot : ((rootedEdges all z).card : ℝ) ≤ ε) :
    (all.card : ℝ) - ((fourShadow all).card : ℝ) +
      ((sharedFourShadow all).card : ℝ) ≤
      -(all.card : ℝ) + 2 * ε := by
  have hsurplus :=
    four_shadow_real_surplus_with_shared_slack all z hUniform hshared
  linarith

end OverlapDecomposition

end JSP523.Rank5
