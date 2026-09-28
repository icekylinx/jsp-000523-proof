import JSP523.Rank5.FacetIncidence
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Rank-five shadow bound with an explicit coherence defect

The rank-five branch of §IV.A in the all-rank manuscript uses coherence of
every shared four-face after the center-inheritance repair in §§IV.8–IV.9.
Here edges where that property fails
are counted explicitly.  The ordinary conditional shadow bound is recovered
when this exceptional set is empty; a later cleanup theorem can instead
bound its size quantitatively.
-/

namespace JSP523.Rank5

section CoherenceDefect

variable {α : Type*} [DecidableEq α]

/-- The local shared-face condition needed for private-facet extraction. -/
def SharedFacesCoherent (all : Family α) (z : Edge α → α)
    (E : Edge α) : Prop :=
  ∀ a ∈ E,
    (∃ F ∈ all, F ≠ E ∧ E.erase a ⊆ F) →
      CoherentDeletedFace E z a

/-- The global shared-facet center and exact triple inheritance supplied
    by the repaired-family step in §§IV.8–IV.9 of the all-rank manuscript. -/
def SharedFacetCenterInheritance
    (all : Family α) (z : Edge α → α) (center : Edge α → α) : Prop :=
  ∀ A ∈ sharedFourShadow all,
    center A ∈ A ∧
      ∀ S : Edge α, S ⊆ A → S.card = 3 →
        center A ∈ S → z S = center A

/-- A deleted face with two distinct parents belongs to the actual shared
    four-shadow. -/
theorem second_parent_deleted_face_shared
    {all : Family α} {E F : Edge α} {a : α}
    (hUniform : Uniform 5 all)
    (hE : E ∈ all) (ha : a ∈ E)
    (hF : F ∈ all) (hFE : F ≠ E)
    (hface : E.erase a ⊆ F) :
    E.erase a ∈ sharedFourShadow all := by
  have hshadow : E.erase a ∈ fourShadow all :=
    erase_mem_fourShadow hE (hUniform hE) ha
  have hpair : ({E, F} : Family α) ⊆ facetParents all (E.erase a) := by
    intro G hG
    rcases Finset.mem_insert.mp hG with hGE | hGF
    · subst G
      exact Finset.mem_filter.mpr ⟨hE, Finset.erase_subset a E⟩
    · have hGF' : G = F := Finset.mem_singleton.mp hGF
      subst G
      exact Finset.mem_filter.mpr ⟨hF, hface⟩
  have htwo : 2 ≤ (facetParents all (E.erase a)).card := by
    have hbound := Finset.card_le_card hpair
    have hcard : ({E, F} : Family α).card = 2 :=
      Finset.card_pair (Ne.symm hFE)
    omega
  exact Finset.mem_filter.mpr ⟨hshadow, htwo⟩

/-- A single inherited center on each shared facet makes every unrooted
    edge good in the exact sense needed for private-facet counting. -/
theorem shared_facet_inheritance_implies_coherence
    (all : Family α) (z : Edge α → α) (center : Edge α → α)
    (hUniform : Uniform 5 all)
    (hcenter : SharedFacetCenterInheritance all z center) :
    ∀ E ∈ unrootedEdges all z, SharedFacesCoherent all z E := by
  intro E hE a ha hsecond
  obtain ⟨F, hF, hFE, hface⟩ := hsecond
  have hAll : E ∈ all := unrootedEdges_subset all z hE
  have hshared : E.erase a ∈ sharedFourShadow all :=
    second_parent_deleted_face_shared hUniform hAll ha hF hFE hface
  obtain ⟨hw, htriples⟩ := hcenter (E.erase a) hshared
  exact ⟨center (E.erase a), hw, htriples⟩

noncomputable def goodUnrootedEdges (all : Family α) (z : Edge α → α) : Family α := by
  classical
  exact (unrootedEdges all z).filter (SharedFacesCoherent all z)

noncomputable def badUnrootedEdges (all : Family α) (z : Edge α → α) : Family α := by
  classical
  exact (unrootedEdges all z).filter (fun E => ¬ SharedFacesCoherent all z E)

theorem good_unrooted_edges_subset_unrooted (all : Family α) (z : Edge α → α) :
    goodUnrootedEdges all z ⊆ unrootedEdges all z := by
  classical
  intro E hE
  exact (Finset.mem_filter.mp hE).1

theorem bad_unrooted_edges_subset_unrooted (all : Family α) (z : Edge α → α) :
    badUnrootedEdges all z ⊆ unrootedEdges all z := by
  classical
  intro E hE
  exact (Finset.mem_filter.mp hE).1

theorem good_bad_unrooted_union (all : Family α) (z : Edge α → α) :
    goodUnrootedEdges all z ∪ badUnrootedEdges all z =
      unrootedEdges all z := by
  classical
  ext E
  constructor
  · intro hE
    rcases Finset.mem_union.mp hE with hg | hb
    · exact good_unrooted_edges_subset_unrooted all z hg
    · exact bad_unrooted_edges_subset_unrooted all z hb
  · intro hE
    by_cases hgood : SharedFacesCoherent all z E
    · exact Finset.mem_union.mpr (Or.inl
        (Finset.mem_filter.mpr ⟨hE, hgood⟩))
    · exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_filter.mpr ⟨hE, hgood⟩))

theorem good_bad_unrooted_disjoint (all : Family α) (z : Edge α → α) :
    Disjoint (goodUnrootedEdges all z) (badUnrootedEdges all z) := by
  classical
  apply Finset.disjoint_left.mpr
  intro E hg hb
  exact (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp hg).2

theorem unrooted_good_bad_card_partition (all : Family α) (z : Edge α → α) :
    (unrootedEdges all z).card =
      (goodUnrootedEdges all z).card +
        (badUnrootedEdges all z).card := by
  have hcard := Finset.card_union_of_disjoint
    (good_bad_unrooted_disjoint all z)
  rw [good_bad_unrooted_union all z] at hcard
  exact hcard

theorem bad_unrooted_edges_eq_empty_of_shared_facet_inheritance
    (all : Family α) (z : Edge α → α) (center : Edge α → α)
    (hUniform : Uniform 5 all)
    (hcenter : SharedFacetCenterInheritance all z center) :
    badUnrootedEdges all z = ∅ := by
  classical
  ext E
  constructor
  · intro hE
    have hU : E ∈ unrootedEdges all z := (Finset.mem_filter.mp hE).1
    have hbad : ¬ SharedFacesCoherent all z E := (Finset.mem_filter.mp hE).2
    exact False.elim (hbad
      (shared_facet_inheritance_implies_coherence all z center hUniform hcenter E hU))
  · intro hE
    simp at hE

/-- Every good unrooted edge contributes two private faces to the actual
    shadow, even when other edges fail the coherence condition. -/
theorem private_four_shadow_bound_of_good_unrooted
    (all : Family α) (z : Edge α → α)
    (hUniform : Uniform 5 all) :
    2 * (goodUnrootedEdges all z).card ≤
      (privateFourShadow all).card := by
  classical
  let good := goodUnrootedEdges all z
  have hsub : good ⊆ all := by
    intro E hE
    exact unrootedEdges_subset all z
      (good_unrooted_edges_subset_unrooted all z hE)
  have hbound :
      2 * good.card ≤ (privateFourShadow all).card := by
    have hraw := shadow_bound_of_private_pairs
      (all := good) (rooted := (∅ : Family α))
      (unrooted := good) (shadow := privateFourShadow all)
      (by simp) (Finset.Subset.rfl) (by
        intro E hE
        have hU : E ∈ unrootedEdges all z :=
          good_unrooted_edges_subset_unrooted all z hE
        have hcoh : SharedFacesCoherent all z E :=
          (Finset.mem_filter.mp hE).2
        obtain ⟨a, ha, b, hb, _, hne, _, _, hprivA, hprivB⟩ :=
          two_private_facets_of_rootless_edge
            (hUniform (hsub hE))
            (unrooted_has_no_triple_root all z hU) hcoh
        refine ⟨⟨E.erase a, E.erase b⟩, ?_⟩
        refine ⟨?_, ?_, Finset.erase_subset a E,
          Finset.erase_subset b E, hne, ?_, ?_⟩
        · exact Finset.mem_filter.mpr
            ⟨erase_mem_fourShadow (hsub hE) (hUniform (hsub hE)) ha,
              private_deleted_face_one_parent all E a (hsub hE) hprivA⟩
        · exact Finset.mem_filter.mpr
            ⟨erase_mem_fourShadow (hsub hE) (hUniform (hsub hE)) hb,
              private_deleted_face_one_parent all E b (hsub hE) hprivB⟩
        · intro F hF hface
          exact hprivA F (hsub hF) hface
        · intro F hF hface
          exact hprivB F (hsub hF) hface)
    simpa using hraw
  exact hbound

/-- A finite error-budget version of the rank-five shadow inequality.
    Each bad unrooted edge is charged at most two lost private faces. -/
theorem four_shadow_bound_with_coherence_defect
    (all : Family α) (z : Edge α → α)
    (hUniform : Uniform 5 all) :
    2 * all.card + (sharedFourShadow all).card ≤
      (fourShadow all).card +
        2 * (rootedEdges all z).card +
        2 * (badUnrootedEdges all z).card := by
  have hgood := private_four_shadow_bound_of_good_unrooted all z hUniform
  have hroot := rooted_unrooted_card_partition all z
  have hsplit := unrooted_good_bad_card_partition all z
  have hshadow := fourShadow_private_shared_card_partition all
  omega

/-- The original conditional shadow bound follows directly from one
    inherited center on each actual shared facet. -/
theorem four_shadow_bound_of_shared_facet_inheritance
    (all : Family α) (z : Edge α → α) (center : Edge α → α)
    (hUniform : Uniform 5 all)
    (hcenter : SharedFacetCenterInheritance all z center) :
    2 * all.card + (sharedFourShadow all).card ≤
      (fourShadow all).card + 2 * (rootedEdges all z).card := by
  have h := four_shadow_bound_with_coherence_defect all z hUniform
  rw [bad_unrooted_edges_eq_empty_of_shared_facet_inheritance
    all z center hUniform hcenter] at h
  simpa using h

/-- The same defect bound in the signed real-surplus form used by the
    rank-five endpoint. -/
theorem four_shadow_real_surplus_with_coherence_defect
    (all : Family α) (z : Edge α → α)
    (hUniform : Uniform 5 all) :
    (all.card : ℝ) - ((fourShadow all).card : ℝ) +
      ((sharedFourShadow all).card : ℝ) ≤
      -(all.card : ℝ) +
        2 * ((rootedEdges all z).card : ℝ) +
        2 * ((badUnrootedEdges all z).card : ℝ) := by
  have hnat := four_shadow_bound_with_coherence_defect all z hUniform
  have hreal :
      2 * (all.card : ℝ) + ((sharedFourShadow all).card : ℝ) ≤
        ((fourShadow all).card : ℝ) +
          2 * ((rootedEdges all z).card : ℝ) +
          2 * ((badUnrootedEdges all z).card : ℝ) := by
    exact_mod_cast hnat
  linarith

end CoherenceDefect

end JSP523.Rank5
