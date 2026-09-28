import JSP523.Rank4.PreprocessReciprocalWrongWitness

/-!
# Parent label triples from actual used completion pairs

Only pairs with a nonempty common triple cell belong to the parent's
label system. This is the triple system to which bounded-label separation
can apply in §III.A.5; arbitrary labels on unused pairs carry no geometry.
-/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- The actual parent label system, restricted to used completion pairs. -/
noncomputable def reciprocalUsedParentLabelTriples
    (D : FiniteCompletionCliqueData α) : Family α := by
  classical
  exact ((D.ground.product D.ground).filter fun xy =>
    xy.1 ≠ xy.2 ∧
      (commonTripleCell D.K D.ground xy.1 xy.2).Nonempty).image
        fun xy => insert (D.label xy.1 xy.2) ({xy.1, xy.2} : Edge α)

/-- A used completion pair contributes its actual three-element label
triple to the parent system. -/
theorem mem_reciprocal_used_parent_label_triples
    (D : FiniteCompletionCliqueData α) (x y : α)
    (hx : x ∈ D.ground) (hy : y ∈ D.ground)
    (hxy : x ≠ y)
    (h_cell : (commonTripleCell D.K D.ground x y).Nonempty) :
    insert (D.label x y) ({x, y} : Edge α) ∈
      reciprocalUsedParentLabelTriples D := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨(x, y), Finset.mem_filter.mpr ?_, rfl⟩
  exact ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hxy, h_cell⟩

/-- The corrected actual parent label system is genuinely 3-uniform.
The label of a used pair lies in a common triple disjoint from that pair. -/
theorem reciprocal_used_parent_label_triples_uniform_three
    (D : FiniteCompletionCliqueData α) :
    Uniform 3 (reciprocalUsedParentLabelTriples D) := by
  classical
  intro E hE
  obtain ⟨xy, hxy, rfl⟩ := Finset.mem_image.mp hE
  have h_parts := Finset.mem_filter.mp hxy
  obtain ⟨T, hT⟩ := h_parts.2.2
  have h_label : D.label xy.1 xy.2 ∈ T :=
    D.label_center xy.1 xy.2 h_parts.2.1 T hT
  have h_disjoint := (mem_common_triple_cell.mp hT).2.2.1
  have h_label_not_pair : D.label xy.1 xy.2 ∉
      ({xy.1, xy.2} : Edge α) :=
    (Finset.disjoint_left.mp h_disjoint) h_label
  rw [Finset.card_insert_of_notMem h_label_not_pair,
    Finset.card_pair h_parts.2.1]

/-- Every actual parent label triple is also in the older all-pairs
system. This records the relationship without changing existing theorems. -/
theorem reciprocal_used_parent_label_triples_subset_all
    (D : FiniteCompletionCliqueData α) :
    reciprocalUsedParentLabelTriples D ⊆
      reciprocalParentLabelTriples D D.ground := by
  classical
  intro E hE
  obtain ⟨xy, hxy, rfl⟩ := Finset.mem_image.mp hE
  have hxy' := (Finset.mem_filter.mp hxy).1
  have hmem := Finset.mem_product.mp hxy'
  exact mem_reciprocal_parent_label_triples D D.ground
    xy.1 xy.2 hmem.1 hmem.2

/-- Separation for the corrected parent label system. This is the
condition supplied by bounded-label cleanup in the manuscript. -/
def ReciprocalUsedParentPairSeparation
    (D : FiniteCompletionCliqueData α) : Prop :=
  ∀ E ∈ D.K, ∀ R ∈ E.powersetCard 2, ∀ S ∈ E.powersetCard 2,
    R ≠ S →
      Disjoint
        (JSP523.Rank3.completionVertices
          (reciprocalUsedParentLabelTriples D) D.ground R)
        (JSP523.Rank3.completionVertices
          (reciprocalUsedParentLabelTriples D) D.ground S)

/-- Two actual edges sharing the triple `xP` make their completion
pair used, so its parent label triple lies in the corrected system. -/
theorem mem_used_parent_label_of_shared_pair_root
    (D : FiniteCompletionCliqueData α) (P : Edge α)
    (x a b : α)
    (h_p_card : P.card = 2) (h_p_ground : P ⊆ D.ground)
    (hx_ground : x ∈ D.ground) (hx_not_p : x ∉ P)
    (ha_ground : a ∈ D.ground) (hb_ground : b ∈ D.ground)
    (hab : a ≠ b)
    (h_a : insert a (insert x P) ∈ D.K)
    (h_b : insert b (insert x P) ∈ D.K) :
    insert (D.label a b) ({a, b} : Edge α) ∈
      reciprocalUsedParentLabelTriples D := by
  classical
  let T := insert x P
  have h_t_card : T.card = 3 := by
    dsimp [T]
    rw [Finset.card_insert_of_notMem hx_not_p, h_p_card]
  have h_t_ground : T ⊆ D.ground :=
    Finset.insert_subset hx_ground h_p_ground
  have h_raw : T ∈ rawCommonTripleCell D.K D.ground a b :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨h_t_ground, h_t_card⟩,
        h_a, h_b⟩
  have h_cell : (commonTripleCell D.K D.ground a b).Nonempty := by
    refine ⟨T, ?_⟩
    exact (raw_common_triple_cell_eq_common_triple_cell
      D.uniform_four) ▸ h_raw
  exact mem_reciprocal_used_parent_label_triples D a b
    ha_ground hb_ground hab h_cell

/-- Used parent label triples can only disappear when the four-family is
shrunk with its ground set and label function fixed. -/
theorem reciprocal_used_parent_label_triples_mono_data
    (D' D : FiniteCompletionCliqueData α)
    (h_ground : D'.ground = D.ground)
    (h_label : D'.label = D.label)
    (h_sub : D'.K ⊆ D.K) :
    reciprocalUsedParentLabelTriples D' ⊆
      reciprocalUsedParentLabelTriples D := by
  classical
  intro E hE
  obtain ⟨xy, hxy, rfl⟩ := Finset.mem_image.mp hE
  have hParts := Finset.mem_filter.mp hxy
  obtain ⟨T, hT⟩ := hParts.2.2
  have hCell' := mem_common_triple_cell.mp hT
  have hCell : T ∈ commonTripleCell D.K D.ground xy.1 xy.2 :=
    mem_common_triple_cell.mpr
      ⟨h_ground ▸ hCell'.1, hCell'.2.1,
        hCell'.2.2.1, h_sub hCell'.2.2.2.1,
          h_sub hCell'.2.2.2.2⟩
  have hPair : xy ∈ D.ground.product D.ground := by
    simpa only [h_ground] using hParts.1
  have hSource : xy ∈ (D.ground.product D.ground).filter
      (fun xy => xy.1 ≠ xy.2 ∧
        (commonTripleCell D.K D.ground xy.1 xy.2).Nonempty) :=
    Finset.mem_filter.mpr
      ⟨hPair, hParts.2.1, ⟨T, hCell⟩⟩
  have hImage : insert (D.label xy.1 xy.2)
      ({xy.1, xy.2} : Edge α) ∈
      reciprocalUsedParentLabelTriples D :=
    Finset.mem_image.mpr ⟨xy, hSource, rfl⟩
  simpa only [h_label] using hImage

end JSP523.Rank4
