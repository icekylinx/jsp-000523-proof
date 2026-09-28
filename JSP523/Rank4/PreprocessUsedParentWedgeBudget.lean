import JSP523.Rank4.PreprocessUsedParentCleanup
import JSP523.Rank4.PreprocessLabelExceptions

/-! # Overlapping used-parent roots charged to existing link wedges -/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- Every used parent-label triple lies in the original ground set. -/
theorem reciprocal_used_parent_label_triples_ground
    (D : FiniteCompletionCliqueData α) :
    ∀ T ∈ reciprocalUsedParentLabelTriples D, T ⊆ D.ground := by
  classical
  intro T hT
  obtain ⟨xy, hxy, rfl⟩ := Finset.mem_image.mp hT
  have hPair := (Finset.mem_filter.mp hxy).1
  obtain ⟨P, hP⟩ := (Finset.mem_filter.mp hxy).2.2
  have hCenter : D.label xy.1 xy.2 ∈ P :=
    D.label_center xy.1 xy.2
      (Finset.mem_filter.mp hxy).2.1 P hP
  have hPGround := (mem_common_triple_cell.mp hP).1
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl
  · exact hPGround hCenter
  · exact (Finset.mem_product.mp hPair).1
  · exact (Finset.mem_product.mp hPair).2

theorem used_parent_overlapping_collision_subset_shared_endpoint_core
    (D : FiniteCompletionCliqueData α)
    (h_ground : ∀ E ∈ D.K, E ⊆ D.ground) :
    usedParentOverlappingCollisionEdges D ⊆
      sharedEndpointCoreEdges D.K
        (reciprocalUsedParentLabelTriples D) D.ground := by
  classical
  intro E hE
  obtain ⟨hEK, R, hR, S, hS, hRS, hNotDisj, x, hxR, hxS⟩ :=
    Finset.mem_filter.mp hE
  obtain ⟨a, haR, haS⟩ := Finset.not_disjoint_iff.mp hNotDisj
  have hRparts := Finset.mem_powersetCard.mp hR
  have hSparts := Finset.mem_powersetCard.mp hS
  obtain ⟨b, hbR, hba⟩ := Finset.exists_mem_ne (by omega : 1 < R.card) a
  obtain ⟨c, hcS, hca⟩ := Finset.exists_mem_ne (by omega : 1 < S.card) a
  have hab : a ≠ b := hba.symm
  have hac : a ≠ c := hca.symm
  have hReq : R = ({a, b} : Edge α) := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      have : z = a ∨ z = b := by
        by_contra hn
        have hsub : ({a, b, z} : Edge α) ⊆ R := by
          intro t ht
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl | rfl <;> assumption
        have hcard := Finset.card_le_card hsub
        have hthree : ({a, b, z} : Edge α).card = 3 := by
          have hza : z ≠ a := fun h => hn (Or.inl h)
          have hzb : z ≠ b := fun h => hn (Or.inr h)
          have hnotA : a ∉ ({b, z} : Edge α) := by
            simp [hab, hza.symm]
          have hnotB : b ∉ ({z} : Edge α) := by simp [hzb.symm]
          rw [Finset.card_insert_of_notMem hnotA,
            Finset.card_insert_of_notMem hnotB]
          simp
        omega
      simpa only [Finset.mem_insert, Finset.mem_singleton] using this
    · rw [hRparts.2, Finset.card_pair hab]
  have hSeq : S = ({a, c} : Edge α) := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      have : z = a ∨ z = c := by
        by_contra hn
        have hsub : ({a, c, z} : Edge α) ⊆ S := by
          intro t ht
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl | rfl <;> assumption
        have hcard := Finset.card_le_card hsub
        have hthree : ({a, c, z} : Edge α).card = 3 := by
          have hza : z ≠ a := fun h => hn (Or.inl h)
          have hzc : z ≠ c := fun h => hn (Or.inr h)
          have hnotA : a ∉ ({c, z} : Edge α) := by
            simp [hac, hza.symm]
          have hnotC : c ∉ ({z} : Edge α) := by simp [hzc.symm]
          rw [Finset.card_insert_of_notMem hnotA,
            Finset.card_insert_of_notMem hnotC]
          simp
        omega
      simpa only [Finset.mem_insert, Finset.mem_singleton] using this
    · rw [hSparts.2, Finset.card_pair hac]
  have hbc : b ≠ c := by
    intro h
    apply hRS
    calc
      R = {a, b} := hReq
      _ = {a, c} := by rw [h]
      _ = S := hSeq.symm
  let Q := reciprocalUsedParentLabelTriples D
  have hxGround : x ∈ D.ground := (Finset.mem_filter.mp hxR).1
  have haGround : a ∈ D.ground := h_ground E hEK (hRparts.1 haR)
  have hbGround : b ∈ D.ground := h_ground E hEK (hRparts.1 hbR)
  have hcGround : c ∈ D.ground := h_ground E hEK (hSparts.1 hcS)
  have hxa : x ≠ a := by
    intro h
    exact (Finset.mem_filter.mp hxR).2.1 (h ▸ haR)
  have hxb : x ≠ b := by
    intro h
    exact (Finset.mem_filter.mp hxR).2.1 (h ▸ hbR)
  have hxc : x ≠ c := by
    intro h
    exact (Finset.mem_filter.mp hxS).2.1 (h ▸ hcS)
  have hbCompletion : b ∈ JSP523.Rank3.completionVertices Q D.ground {x, a} := by
    apply Finset.mem_filter.mpr
    refine ⟨hbGround, ?_, ?_⟩
    · simp [hxb.symm, hab.symm]
    · have hQ := (Finset.mem_filter.mp hxR).2.2
      simpa [Q, hReq, Finset.union_comm, Finset.insert_comm] using hQ
  have hcCompletion : c ∈ JSP523.Rank3.completionVertices Q D.ground {x, a} := by
    apply Finset.mem_filter.mpr
    refine ⟨hcGround, ?_, ?_⟩
    · simp [hxc.symm, hac.symm]
    · have hQ := (Finset.mem_filter.mp hxS).2.2
      simpa [Q, hSeq, Finset.union_comm, Finset.insert_comm] using hQ
  let w : Σ _x : α, Σ _a : α, α × α := ⟨x, a, (b, c)⟩
  have hw : w ∈ qLinkWedgeIndices Q D.ground := by
    apply Finset.mem_sigma.mpr
    refine ⟨hxGround, Finset.mem_sigma.mpr ?_⟩
    refine ⟨Finset.mem_erase.mpr ⟨hxa.symm, haGround⟩, ?_⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨hbCompletion, hcCompletion⟩, hbc⟩
  apply Finset.mem_filter.mpr
  refine ⟨hEK, w, hw, ?_⟩
  have hcore : qLinkWedgeCore w = R ∪ S := by
    ext z
    simp [qLinkWedgeCore, w, hReq, hSeq]
    tauto
  rw [hcore]
  exact Finset.union_subset hRparts.1 hSparts.1

/-- The overlapping part of the actual used-parent separation deletion
has the manuscript's finite `D κ² |V|²` bound. -/
theorem used_parent_overlapping_collision_card_le_degree_caps
    (D : FiniteCompletionCliqueData α) (Dcap κ : ℕ)
    (h_ground : ∀ E ∈ D.K, E ⊆ D.ground)
    (h_pair : ∀ P ∈ D.ground.powersetCard 2,
      qPairDegree (reciprocalUsedParentLabelTriples D) P ≤ κ)
    (h_facet : ∀ T : Edge α, T.card = 3 →
      (D.K.filter fun E => T ⊆ E).card ≤ Dcap) :
    (usedParentOverlappingCollisionEdges D).card ≤
      Dcap * D.ground.card ^ 2 * κ ^ 2 := by
  calc
    _ ≤ (sharedEndpointCoreEdges D.K
          (reciprocalUsedParentLabelTriples D) D.ground).card :=
      Finset.card_le_card
        (used_parent_overlapping_collision_subset_shared_endpoint_core
          D h_ground)
    _ ≤ Dcap * D.ground.card ^ 2 * κ ^ 2 :=
      shared_endpoint_core_edges_card_le_degree_caps
        D.K (reciprocalUsedParentLabelTriples D) D.ground Dcap κ
        (reciprocal_used_parent_label_triples_uniform_three D)
        (reciprocal_used_parent_label_triples_ground D)
        h_pair h_facet

/-- The actual used-parent separation deletion has precisely the paper's
disjoint-root C4 term plus the intersecting-root wedge term. -/
theorem used_parent_separation_bad_card_le_actual_budget
    (D : FiniteCompletionCliqueData α) (Dcap κ : ℕ)
    (h_ground : ∀ E ∈ D.K, E ⊆ D.ground)
    (h_pair : ∀ P ∈ D.ground.powersetCard 2,
      qPairDegree (reciprocalUsedParentLabelTriples D) P ≤ κ)
    (h_facet : ∀ T : Edge α, T.card = 3 →
      (D.K.filter fun E => T ⊆ E).card ≤ Dcap) :
    (usedParentPairSeparationBadEdges D).card ≤
      (∑ x ∈ D.ground,
        (fixedCenterPairNodeDeletion D.K
          (reciprocalUsedParentLabelTriples D) D.ground x).card) +
        Dcap * D.ground.card ^ 2 * κ ^ 2 := by
  have hSplit := used_parent_separation_bad_card_le_collision_sum D
  have hDisjoint :=
    used_parent_disjoint_collisions_card_le_fixed_center_sum D h_ground
  have hOverlap :=
    used_parent_overlapping_collision_card_le_degree_caps
      D Dcap κ h_ground h_pair h_facet
  omega

end JSP523.Rank4
