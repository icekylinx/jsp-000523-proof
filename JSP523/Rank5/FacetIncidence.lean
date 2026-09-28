import JSP523.Rank5.RootedFacetCenters
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Lean.Elab.Tactic.Omega

/-!
# Exact incidence count for the genuine four-shadow

For each four-face we count its parent five-edges.  Every five-edge has
five four-faces, including repeated faces whose parent multiplicity is
greater than one.  The resulting excess ledger records exactly how much
the shadow is smaller than the total face incidence count.
-/

namespace JSP523.Rank5

section FacetIncidence

variable {α : Type*} [DecidableEq α]

/-- Five-edges containing a specified four-face. -/
def facetParents (all : Family α) (A : Edge α) : Family α :=
  all.filter (fun E => A ⊆ E)

/-- Membership in the actual four-shadow supplies an actual parent. -/
theorem mem_four_shadow_iff_parent
    (all : Family α) (A : Edge α) :
    A ∈ fourShadow all ↔
      ∃ E ∈ all, A ⊆ E ∧ A.card = 4 := by
  constructor
  · intro hA
    obtain ⟨E, hE, hface⟩ := Finset.mem_biUnion.mp hA
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hface
    exact ⟨E, hE, hsub, hcard⟩
  · rintro ⟨E, hE, hsub, hcard⟩
    exact Finset.mem_biUnion.mpr
      ⟨E, hE, Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩⟩

/-- A four-face in the shadow has at least one parent edge. -/
theorem facet_parents_nonempty_of_shadow
    (all : Family α) (A : Edge α)
    (hA : A ∈ fourShadow all) :
    (facetParents all A).Nonempty := by
  obtain ⟨E, hE, hsub, _⟩ :=
    (mem_four_shadow_iff_parent all A).mp hA
  exact ⟨E, Finset.mem_filter.mpr ⟨hE, hsub⟩⟩

/-- Filtering the actual shadow by containment in one member recovers
    exactly the four-faces of that member. -/
theorem shadow_faces_inside_edge
    (all : Family α) (E : Edge α) (hE : E ∈ all) :
    (fourShadow all).filter (fun A => A ⊆ E) =
      E.powersetCard 4 := by
  ext A
  constructor
  · intro hA
    obtain ⟨hshadow, hsub⟩ := Finset.mem_filter.mp hA
    obtain ⟨_, _, _, hcard⟩ :=
      (mem_four_shadow_iff_parent all A).mp hshadow
    exact Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩
  · intro hA
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hA
    exact Finset.mem_filter.mpr
      ⟨(mem_four_shadow_iff_parent all A).mpr
        ⟨E, hE, hsub, hcard⟩, hsub⟩

/-- Count all shadow-parent incidences in a five-uniform family. -/
theorem four_shadow_parent_incidence_count
    (all : Family α) (hUniform : Uniform 5 all) :
    (∑ A ∈ fourShadow all, (facetParents all A).card) =
      5 * all.card := by
  classical
  let S : Family α := fourShadow all
  calc
    (∑ A ∈ S, (facetParents all A).card) =
        ∑ A ∈ S, ∑ E ∈ all,
          if A ⊆ E then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro A _
      exact Finset.card_filter (fun E : Edge α => A ⊆ E) all
    _ = ∑ E ∈ all, ∑ A ∈ S,
          if A ⊆ E then (1 : ℕ) else 0 := Finset.sum_comm
    _ = ∑ E ∈ all, (E.powersetCard 4).card := by
      apply Finset.sum_congr rfl
      intro E hE
      calc
        (∑ A ∈ S, if A ⊆ E then (1 : ℕ) else 0) =
            (S.filter (fun A => A ⊆ E)).card :=
          (Finset.card_filter (fun A => A ⊆ E) S).symm
        _ = (E.powersetCard 4).card :=
          congrArg Finset.card (shadow_faces_inside_edge all E hE)
    _ = ∑ E ∈ all, (5 : ℕ) := by
      apply Finset.sum_congr rfl
      intro E hE
      rw [Finset.card_powersetCard, hUniform hE]
      decide
    _ = 5 * all.card := by simp [mul_comm]

/-- The excess number of parents beyond the first, summed over genuine
    four-faces.  Each summand is defined because the face has a parent. -/
def facetOverlapExcess (all : Family α) : ℕ :=
  (fourShadow all).sum (fun A => (facetParents all A).card - 1)

/-- Exact rank-five shadow ledger: each five-edge contributes five facets,
    and every additional parent of an already seen facet accounts for one
    overlap. -/
theorem four_shadow_overlap_ledger
    (all : Family α) (hUniform : Uniform 5 all) :
    5 * all.card = (fourShadow all).card +
      facetOverlapExcess all := by
  have hlocal : ∀ A ∈ fourShadow all,
      (facetParents all A).card =
        1 + ((facetParents all A).card - 1) := by
    intro A hA
    have hpos : 0 < (facetParents all A).card :=
      Finset.card_pos.mpr (facet_parents_nonempty_of_shadow all A hA)
    omega
  calc
    5 * all.card =
        ∑ A ∈ fourShadow all, (facetParents all A).card :=
      (four_shadow_parent_incidence_count all hUniform).symm
    _ = ∑ A ∈ fourShadow all,
          (1 + ((facetParents all A).card - 1)) := by
      apply Finset.sum_congr rfl
      intro A hA
      exact hlocal A hA
    _ = (fourShadow all).card + facetOverlapExcess all := by
      simp [facetOverlapExcess, Finset.sum_add_distrib]

/-- The ordinary shadow bound is the nonnegative part of the exact
    overlap identity. -/
theorem four_shadow_card_le_five_edges
    (all : Family α) (hUniform : Uniform 5 all) :
    (fourShadow all).card ≤ 5 * all.card := by
  have hledger := four_shadow_overlap_ledger all hUniform
  omega

/-- A private four-face has precisely one parent, the edge which owns it. -/
theorem private_deleted_face_one_parent
    (all : Family α) (E : Edge α) (a : α)
    (hE : E ∈ all)
    (hprivate : PrivateDeletedFace all E a) :
    (facetParents all (E.erase a)).card = 1 := by
  have hsingle : facetParents all (E.erase a) = {E} := by
    ext F
    constructor
    · intro hF
      obtain ⟨hFall, hsub⟩ := Finset.mem_filter.mp hF
      exact Finset.mem_singleton.mpr (hprivate F hFall hsub)
    · intro hF
      have hFE : F = E := Finset.mem_singleton.mp hF
      subst F
      exact Finset.mem_filter.mpr
        ⟨hE, Finset.erase_subset a E⟩
  rw [hsingle]
  simp

/-- The four-shadow faces with exactly one parent five-edge. -/
def privateFourShadow (all : Family α) : Family α :=
  (fourShadow all).filter (fun A => (facetParents all A).card = 1)

/-- The complementary four-faces with at least two parent five-edges. -/
def sharedFourShadow (all : Family α) : Family α :=
  (fourShadow all).filter (fun A => 2 ≤ (facetParents all A).card)

theorem private_four_shadow_subset_four_shadow (all : Family α) :
    privateFourShadow all ⊆ fourShadow all := by
  intro A hA
  exact (Finset.mem_filter.mp hA).1

/-- Every actual four-face has a parent, so it has either exactly one
    parent or at least two. -/
theorem four_shadow_private_shared_union (all : Family α) :
    privateFourShadow all ∪ sharedFourShadow all = fourShadow all := by
  ext A
  constructor
  · intro hA
    rcases Finset.mem_union.mp hA with hp | hs
    · exact (Finset.mem_filter.mp hp).1
    · exact (Finset.mem_filter.mp hs).1
  · intro hA
    have hpos : 0 < (facetParents all A).card :=
      Finset.card_pos.mpr (facet_parents_nonempty_of_shadow all A hA)
    by_cases hsingle : (facetParents all A).card = 1
    · exact Finset.mem_union.mpr (Or.inl
        (Finset.mem_filter.mpr ⟨hA, hsingle⟩))
    · have hlarge : 2 ≤ (facetParents all A).card := by omega
      exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_filter.mpr ⟨hA, hlarge⟩))

theorem private_shared_four_shadow_disjoint (all : Family α) :
    Disjoint (privateFourShadow all) (sharedFourShadow all) := by
  apply Finset.disjoint_left.mpr
  intro A hp hs
  have hone := (Finset.mem_filter.mp hp).2
  have htwo := (Finset.mem_filter.mp hs).2
  omega

/-- Exact partition of the four-shadow by parent multiplicity. -/
theorem four_shadow_private_shared_card_partition (all : Family α) :
    (fourShadow all).card =
      (privateFourShadow all).card + (sharedFourShadow all).card := by
  have hcard := Finset.card_union_of_disjoint
    (private_shared_four_shadow_disjoint all)
  rw [four_shadow_private_shared_union all] at hcard
  exact hcard

/-- Every unrooted five-edge contributes two distinct faces of unique
    parentage to the actual shadow.  Shared-face coherence is the same
    explicit structural hypothesis as in the earlier shadow bound. -/
theorem private_four_shadow_bound_of_shared_coherence
    (all : Family α) (z : Edge α → α)
    (hUniform : Uniform 5 all)
    (hshared : ∀ E ∈ unrootedEdges all z, ∀ a ∈ E,
      (∃ F ∈ all, F ≠ E ∧ E.erase a ⊆ F) →
      CoherentDeletedFace E z a) :
    2 * (unrootedEdges all z).card ≤
      (privateFourShadow all).card := by
  have hbound : 2 * all.card ≤
      (privateFourShadow all).card +
        2 * (rootedEdges all z).card := by
    apply shadow_bound_of_private_pairs
      (rooted_unrooted_card_partition all z)
      (unrooted_edges_subset all z)
    intro E hE
    have hAll : E ∈ all := unrooted_edges_subset all z hE
    obtain ⟨a, ha, b, hb, _, hne, _, _, hprivA, hprivB⟩ :=
      two_private_facets_of_rootless_edge (hUniform hAll)
        (unrooted_has_no_triple_root all z hE)
        (hshared E hE)
    refine ⟨⟨E.erase a, E.erase b⟩, ?_⟩
    refine ⟨?_, ?_, Finset.erase_subset a E,
      Finset.erase_subset b E, hne, hprivA, hprivB⟩
    · exact Finset.mem_filter.mpr
        ⟨erase_mem_four_shadow hAll (hUniform hAll) ha,
          private_deleted_face_one_parent all E a hAll hprivA⟩
    · exact Finset.mem_filter.mpr
        ⟨erase_mem_four_shadow hAll (hUniform hAll) hb,
          private_deleted_face_one_parent all E b hAll hprivB⟩
  have hpartition := rooted_unrooted_card_partition all z
  omega

/-- Shared four-faces remain as an explicit nonnegative slack term in the
    conditional five-edge shadow estimate. -/
theorem four_shadow_bound_with_shared_slack
    (all : Family α) (z : Edge α → α)
    (hUniform : Uniform 5 all)
    (hshared : ∀ E ∈ unrootedEdges all z, ∀ a ∈ E,
      (∃ F ∈ all, F ≠ E ∧ E.erase a ⊆ F) →
      CoherentDeletedFace E z a) :
    2 * all.card + (sharedFourShadow all).card ≤
      (fourShadow all).card + 2 * (rootedEdges all z).card := by
  have hprivate :=
    private_four_shadow_bound_of_shared_coherence all z hUniform hshared
  have hpartition := rooted_unrooted_card_partition all z
  have hshadow := four_shadow_private_shared_card_partition all
  omega

end FacetIncidence

end JSP523.Rank5
