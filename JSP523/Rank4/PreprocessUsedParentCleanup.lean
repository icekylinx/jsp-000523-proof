import JSP523.Rank4.PreprocessUsedParentSeparation
import JSP523.Rank4.PreprocessActualLinkColor

/-!
# Cleaning the actual used parent-label pair system

This module deletes precisely the four-edges whose pair roots have a
common completion in the fixed, used-pair parent label system. The
separation property is inherited by the remaining completion data.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Original edges violating pairwise separation in the fixed actual
used-pair parent label system. -/
noncomputable def usedParentPairSeparationBadEdges
    (D : FiniteCompletionCliqueData α) : Family α := by
  classical
  exact D.K.filter fun E => ∃ R ∈ E.powersetCard 2,
    ∃ S ∈ E.powersetCard 2, R ≠ S ∧
      ¬ Disjoint
        (JSP523.Rank3.completionVertices
          (reciprocalUsedParentLabelTriples D) D.ground R)
        (JSP523.Rank3.completionVertices
          (reciprocalUsedParentLabelTriples D) D.ground S)

/-- Removing the actual separation violations preserves the finite
completion data and its original pair labels. -/
noncomputable def clearUsedParentPairSeparation
    (D : FiniteCompletionCliqueData α) : FiniteCompletionCliqueData α := by
  classical
  let K' := D.K \ usedParentPairSeparationBadEdges D
  have h_sub : K' ⊆ D.K := Finset.sdiff_subset
  refine ⟨D.ground, K', ?_, ?_, D.label, D.label_symm, ?_, ?_⟩
  · intro E hE
    exact D.uniform_four (h_sub hE)
  · exact admissible_mono h_sub D.admissible
  · intro x y hxy P hP
    have hCell := mem_common_triple_cell.mp hP
    exact D.label_center x y hxy P (mem_common_triple_cell.mpr
      ⟨hCell.1, hCell.2.1, hCell.2.2.1,
        h_sub hCell.2.2.2.1, h_sub hCell.2.2.2.2⟩)
  · intro T hTcard x hx y hy z hz hxy hxz hyz
    have hx' : x ∈ graphFacetCompletions D.K D.ground T := by
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hx).1,
          h_sub (Finset.mem_filter.mp hx).2⟩
    have hy' : y ∈ graphFacetCompletions D.K D.ground T := by
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hy).1,
          h_sub (Finset.mem_filter.mp hy).2⟩
    have hz' : z ∈ graphFacetCompletions D.K D.ground T := by
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hz).1,
          h_sub (Finset.mem_filter.mp hz).2⟩
    exact D.no_bicolored_triangle T hTcard x hx' y hy' z hz' hxy hxz hyz

omit [Fintype α] in
theorem clear_used_parent_pair_separation_sub
    (D : FiniteCompletionCliqueData α) :
    (clearUsedParentPairSeparation D).K ⊆ D.K := by
  classical
  change (D.K \ usedParentPairSeparationBadEdges D) ⊆ D.K
  exact Finset.sdiff_subset

omit [Fintype α] in
theorem clear_used_parent_pair_separation_loss_card_le
    (D : FiniteCompletionCliqueData α) :
    (D.K \ (clearUsedParentPairSeparation D).K).card ≤
      (usedParentPairSeparationBadEdges D).card := by
  classical
  apply Finset.card_le_card
  intro E hE
  have hParts := Finset.mem_sdiff.mp hE
  by_contra hNotBad
  have hClean : E ∈ (clearUsedParentPairSeparation D).K := by
    change E ∈ D.K \ usedParentPairSeparationBadEdges D
    exact Finset.mem_sdiff.mpr ⟨hParts.1, hNotBad⟩
  exact hParts.2 hClean

omit [Fintype α] in
/-- The surviving edges are pair-root separated with respect to the
fixed parent's used label triples. -/
theorem clear_used_parent_pair_separation_fixed
    (D : FiniteCompletionCliqueData α) :
    ∀ E ∈ (clearUsedParentPairSeparation D).K,
      ∀ R ∈ E.powersetCard 2, ∀ S ∈ E.powersetCard 2,
        R ≠ S →
        Disjoint
          (JSP523.Rank3.completionVertices
            (reciprocalUsedParentLabelTriples D) D.ground R)
          (JSP523.Rank3.completionVertices
            (reciprocalUsedParentLabelTriples D) D.ground S) := by
  classical
  intro E hE R hR S hS hRS
  by_contra hBad
  have hEK : E ∈ D.K :=
    clear_used_parent_pair_separation_sub D hE
  have hDelete : E ∈ usedParentPairSeparationBadEdges D :=
    Finset.mem_filter.mpr
      ⟨hEK, ⟨R, hR, S, hS, hRS, hBad⟩⟩
  have hClean : E ∈ D.K \ usedParentPairSeparationBadEdges D := hE
  exact (Finset.mem_sdiff.mp hClean).2 hDelete

omit [Fintype α] in
/-- The deletion yields separation for the survivor's own used-pair
label system, since that system is a subfamily of the fixed parent's. -/
theorem clear_used_parent_pair_separation_actual
    (D : FiniteCompletionCliqueData α) :
    ReciprocalUsedParentPairSeparation
      (clearUsedParentPairSeparation D) := by
  classical
  let D' := clearUsedParentPairSeparation D
  have h_sub : D'.K ⊆ D.K :=
    clear_used_parent_pair_separation_sub D
  have h_q_sub : reciprocalUsedParentLabelTriples D' ⊆
      reciprocalUsedParentLabelTriples D :=
    reciprocal_used_parent_label_triples_mono_data
      D' D rfl rfl h_sub
  have h_completion_sub (R : Edge α) :
      JSP523.Rank3.completionVertices
          (reciprocalUsedParentLabelTriples D') D'.ground R ⊆
        JSP523.Rank3.completionVertices
          (reciprocalUsedParentLabelTriples D) D.ground R := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr
      ⟨hx'.1, hx'.2.1, h_q_sub hx'.2.2⟩
  intro E hE R hR S hS hRS
  have h_fixed := clear_used_parent_pair_separation_fixed
    D E hE R hR S hS hRS
  exact h_fixed.mono (h_completion_sub R) (h_completion_sub S)

omit [Fintype α] in
/-- Used-parent pair separation is hereditary under edge deletion with
the same ground set and pair-label function. -/
theorem reciprocal_used_parent_pair_separation_mono_data
    (D' D : FiniteCompletionCliqueData α)
    (h_ground : D'.ground = D.ground)
    (h_label : D'.label = D.label)
    (h_sub : D'.K ⊆ D.K)
    (h_sep : ReciprocalUsedParentPairSeparation D) :
    ReciprocalUsedParentPairSeparation D' := by
  classical
  have h_q_sub := reciprocal_used_parent_label_triples_mono_data
    D' D h_ground h_label h_sub
  have h_completion_sub (R : Edge α) :
      JSP523.Rank3.completionVertices
          (reciprocalUsedParentLabelTriples D') D'.ground R ⊆
        JSP523.Rank3.completionVertices
          (reciprocalUsedParentLabelTriples D) D.ground R := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr
      ⟨h_ground ▸ hx'.1, hx'.2.1, h_q_sub hx'.2.2⟩
  intro E hE R hR S hS hRS
  have h := h_sep E (h_sub hE) R hR S hS hRS
  exact h.mono (h_completion_sub R) (h_completion_sub S)

omit [Fintype α] in
/-- A separation collision between disjoint pair roots of an actual
four-edge is exactly an edge represented in the existing fixed-center
pair-node deletion family. -/
theorem used_parent_disjoint_collision_in_fixed_center_deletion
    (D : FiniteCompletionCliqueData α)
    (E R S : Edge α) (x : α)
    (h_ground : E ⊆ D.ground)
    (h_edge : E ∈ D.K)
    (h_r : R ∈ E.powersetCard 2)
    (h_s : S ∈ E.powersetCard 2)
    (h_disjoint : Disjoint R S)
    (h_xr : x ∈ JSP523.Rank3.completionVertices
      (reciprocalUsedParentLabelTriples D) D.ground R)
    (h_xs : x ∈ JSP523.Rank3.completionVertices
      (reciprocalUsedParentLabelTriples D) D.ground S) :
    E ∈ fixedCenterPairNodeDeletion D.K
      (reciprocalUsedParentLabelTriples D) D.ground x := by
  classical
  have h_r_parts := Finset.mem_powersetCard.mp h_r
  have h_s_parts := Finset.mem_powersetCard.mp h_s
  have h_xr_parts := Finset.mem_filter.mp h_xr
  have h_xs_parts := Finset.mem_filter.mp h_xs
  have h_r_node : R ∈ (D.ground.powersetCard 2).filter
      (fun P => insert x P ∈ reciprocalUsedParentLabelTriples D) :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr
        ⟨h_r_parts.1.trans h_ground, h_r_parts.2⟩,
        by simpa only [Finset.union_singleton] using h_xr_parts.2.2⟩
  have h_s_node : S ∈ (D.ground.powersetCard 2).filter
      (fun P => insert x P ∈ reciprocalUsedParentLabelTriples D) :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr
        ⟨h_s_parts.1.trans h_ground, h_s_parts.2⟩,
        by simpa only [Finset.union_singleton] using h_xs_parts.2.2⟩
  let r_node : fixedCenterPairNodes
      (reciprocalUsedParentLabelTriples D) D.ground x :=
    ⟨R, h_r_node⟩
  let s_node : fixedCenterPairNodes
      (reciprocalUsedParentLabelTriples D) D.ground x :=
    ⟨S, h_s_node⟩
  have h_union_sub : R ∪ S ⊆ E :=
    Finset.union_subset h_r_parts.1 h_s_parts.1
  have h_union_card : (R ∪ S).card = 4 := by
    rw [Finset.card_union_of_disjoint h_disjoint,
      h_r_parts.2, h_s_parts.2]
  have h_union_eq : R ∪ S = E :=
    Finset.eq_of_subset_of_card_le h_union_sub
      (by rw [h_union_card, D.uniform_four h_edge])
  exact Finset.mem_filter.mpr
    ⟨h_edge, ⟨r_node, s_node, h_disjoint, h_union_eq⟩⟩

/-- The disjoint-root portion of actual parent-label separation failures. -/
noncomputable def usedParentDisjointCollisionEdges
    (D : FiniteCompletionCliqueData α) : Family α := by
  classical
  exact D.K.filter fun E => ∃ R ∈ E.powersetCard 2,
    ∃ S ∈ E.powersetCard 2,
      Disjoint R S ∧
        ∃ x ∈ JSP523.Rank3.completionVertices
          (reciprocalUsedParentLabelTriples D) D.ground R,
          x ∈ JSP523.Rank3.completionVertices
            (reciprocalUsedParentLabelTriples D) D.ground S

omit [Fintype α] in
/-- Every disjoint-root separation failure is charged by one of the
already bounded fixed-center pair-node deletion families. -/
theorem used_parent_disjoint_collisions_subset_fixed_center_union
    (D : FiniteCompletionCliqueData α)
    (h_ground : ∀ E ∈ D.K, E ⊆ D.ground) :
    usedParentDisjointCollisionEdges D ⊆
      D.ground.biUnion (fun x =>
        fixedCenterPairNodeDeletion D.K
          (reciprocalUsedParentLabelTriples D) D.ground x) := by
  classical
  intro E hE
  obtain ⟨hEK, R, hR, S, hS, hRS, x, hxR, hxS⟩ :=
    Finset.mem_filter.mp hE
  have hxGround := (Finset.mem_filter.mp hxR).1
  exact Finset.mem_biUnion.mpr
    ⟨x, hxGround,
      used_parent_disjoint_collision_in_fixed_center_deletion
        D E R S x (h_ground E hEK) hEK hR hS hRS hxR hxS⟩

omit [Fintype α] in
/-- The disjoint-root deletion cost is bounded by the sum of the fixed
center costs, which are covered by the existing C4 argument. -/
theorem used_parent_disjoint_collisions_card_le_fixed_center_sum
    (D : FiniteCompletionCliqueData α)
    (h_ground : ∀ E ∈ D.K, E ⊆ D.ground) :
    (usedParentDisjointCollisionEdges D).card ≤
      ∑ x ∈ D.ground,
        (fixedCenterPairNodeDeletion D.K
          (reciprocalUsedParentLabelTriples D) D.ground x).card := by
  calc
    _ ≤ (D.ground.biUnion (fun x =>
          fixedCenterPairNodeDeletion D.K
            (reciprocalUsedParentLabelTriples D) D.ground x)).card :=
      Finset.card_le_card
        (used_parent_disjoint_collisions_subset_fixed_center_union
          D h_ground)
    _ ≤ _ := Finset.card_biUnion_le

/-- The remaining separation failures have intersecting pair roots. -/
noncomputable def usedParentOverlappingCollisionEdges
    (D : FiniteCompletionCliqueData α) : Family α := by
  classical
  exact D.K.filter fun E => ∃ R ∈ E.powersetCard 2,
    ∃ S ∈ E.powersetCard 2,
      R ≠ S ∧ ¬ Disjoint R S ∧
        ∃ x ∈ JSP523.Rank3.completionVertices
          (reciprocalUsedParentLabelTriples D) D.ground R,
          x ∈ JSP523.Rank3.completionVertices
            (reciprocalUsedParentLabelTriples D) D.ground S

omit [Fintype α] in
/-- All actual separation failures split into the disjoint-root class
charged by fixed-center C4 graphs and the overlapping-root class. -/
theorem used_parent_separation_bad_subset_collision_union
    (D : FiniteCompletionCliqueData α) :
    usedParentPairSeparationBadEdges D ⊆
      usedParentDisjointCollisionEdges D ∪
        usedParentOverlappingCollisionEdges D := by
  classical
  intro E hE
  obtain ⟨hEK, R, hR, S, hS, hRS, hNotDisj⟩ :=
    Finset.mem_filter.mp hE
  have hWitness : ∃ x,
      x ∈ JSP523.Rank3.completionVertices
        (reciprocalUsedParentLabelTriples D) D.ground R ∧
      x ∈ JSP523.Rank3.completionVertices
        (reciprocalUsedParentLabelTriples D) D.ground S := by
    by_contra hNone
    apply hNotDisj
    apply Finset.disjoint_left.mpr
    intro x hxR hxS
    exact hNone ⟨x, hxR, hxS⟩
  obtain ⟨x, hxR, hxS⟩ := hWitness
  by_cases hDisj : Disjoint R S
  · exact Finset.mem_union.mpr (Or.inl
      (Finset.mem_filter.mpr
        ⟨hEK, ⟨R, hR, S, hS, hDisj, x, hxR, hxS⟩⟩))
  · exact Finset.mem_union.mpr (Or.inr
      (Finset.mem_filter.mpr
        ⟨hEK, ⟨R, hR, S, hS, hRS, hDisj, x, hxR, hxS⟩⟩))

omit [Fintype α] in
theorem used_parent_separation_bad_card_le_collision_sum
    (D : FiniteCompletionCliqueData α) :
    (usedParentPairSeparationBadEdges D).card ≤
      (usedParentDisjointCollisionEdges D).card +
        (usedParentOverlappingCollisionEdges D).card := by
  calc
    _ ≤ (usedParentDisjointCollisionEdges D ∪
          usedParentOverlappingCollisionEdges D).card :=
      Finset.card_le_card
        (used_parent_separation_bad_subset_collision_union D)
    _ ≤ _ := Finset.card_union_le _ _

end JSP523.Rank4
