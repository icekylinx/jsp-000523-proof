import JSP523.Rank4.PreprocessReciprocalDeletion
import JSP523.Rank4.PreprocessReciprocalTriangle
import JSP523.Rank4.GraphReciprocalAccounting

/-!
# Removing reciprocal triangles with the wrong common witness

The distinct-witness cleanup does not remove a reciprocal pair whose two
witnesses coincide at `w` while the pair label is different from `w`.
The manuscript removes this second pattern separately in §III.A.6.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
/-- Three actual pair-link edges at a common root force the completion-pair
label into `P ∪ {w}`. If the label is not the common witness, it lies in
the root pair, exactly as in §III.A.6. -/
theorem reciprocal_wrong_common_witness_label_in_root
    (D : FiniteCompletionCliqueData α) (P : Edge α)
    (a b w : α)
    (h_p_card : P.card = 2) (h_p_ground : P ⊆ D.ground)
    (h_ab : (completionPairLinkGraph D P).Adj a b)
    (h_aw : (completionPairLinkGraph D P).Adj a w)
    (h_bw : (completionPairLinkGraph D P).Adj b w)
    (h_wrong : D.label a b ≠ w) :
    D.label a b ∈ P := by
  classical
  have h_ab' := h_ab
  have h_aw' := h_aw
  have h_bw' := h_bw
  change a ∉ P ∧ b ∉ P ∧ a ∈ D.ground ∧ b ∈ D.ground ∧
    a ≠ b ∧ insert a (insert b P) ∈ D.K at h_ab'
  change a ∉ P ∧ w ∉ P ∧ a ∈ D.ground ∧ w ∈ D.ground ∧
    a ≠ w ∧ insert a (insert w P) ∈ D.K at h_aw'
  change b ∉ P ∧ w ∉ P ∧ b ∈ D.ground ∧ w ∈ D.ground ∧
    b ≠ w ∧ insert b (insert w P) ∈ D.K at h_bw'
  let T := insert w P
  have h_t_card : T.card = 3 := by
    dsimp [T]
    rw [Finset.card_insert_of_notMem h_aw'.2.1, h_p_card]
  have h_t_ground : T ⊆ D.ground :=
    Finset.insert_subset h_aw'.2.2.2.1 h_p_ground
  have h_a : a ∈ graphFacetCompletions D.K D.ground T := by
    apply Finset.mem_filter.mpr
    exact ⟨h_aw'.2.2.1, by
      simpa [T] using h_aw'.2.2.2.2.2⟩
  have h_b : b ∈ graphFacetCompletions D.K D.ground T := by
    apply Finset.mem_filter.mpr
    exact ⟨h_bw'.2.2.1, by
      simpa [T] using h_bw'.2.2.2.2.2⟩
  have h_label := completion_pair_label_mem_facet D T
    h_t_card h_t_ground a b h_a h_b h_ab'.2.2.2.2.1
  rcases Finset.mem_insert.mp h_label with h_eq | h_root
  · exact False.elim (h_wrong h_eq)
  · exact h_root

/-- Target edges carrying the remaining common-witness reciprocal pattern
at a fixed pair root. -/
noncomputable def reciprocalWrongCommonWitnessDeletionSet
    (D : FiniteCompletionCliqueData α) (P : Edge α) : Family α := by
  classical
  exact D.K.filter fun E => ∃ a b w : α,
    E = insert a (insert b P) ∧
    (completionPairLinkGraph D P).Adj a b ∧
    (completionPairLinkGraph D P).Adj a w ∧
    (completionPairLinkGraph D P).Adj b w ∧
    D.label a w = b ∧ D.label b w = a ∧
    D.label a b ≠ w

/-- Delete the wrong-common-witness targets at every pair root. -/
noncomputable def reciprocalWrongCommonWitnessDeletionSetAll
    (D : FiniteCompletionCliqueData α) : Family α := by
  classical
  exact (D.ground.powersetCard 2).biUnion fun P =>
    reciprocalWrongCommonWitnessDeletionSet D P

/-- The second reciprocal cleanup preserves the completion data fields
needed by all subsequent selected-graph lemmas. -/
noncomputable def clearReciprocalWrongCommonWitnesses
    (D : FiniteCompletionCliqueData α) : FiniteCompletionCliqueData α := by
  classical
  let K' := D.K \ reciprocalWrongCommonWitnessDeletionSetAll D
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
  · intro T x hx y hy z hz hxy hxz hyz
    have hx' : x ∈ graphFacetCompletions D.K D.ground T := by
      apply Finset.mem_filter.mpr
      exact ⟨(Finset.mem_filter.mp hx).1,
        h_sub (Finset.mem_filter.mp hx).2⟩
    have hy' : y ∈ graphFacetCompletions D.K D.ground T := by
      apply Finset.mem_filter.mpr
      exact ⟨(Finset.mem_filter.mp hy).1,
        h_sub (Finset.mem_filter.mp hy).2⟩
    have hz' : z ∈ graphFacetCompletions D.K D.ground T := by
      apply Finset.mem_filter.mpr
      exact ⟨(Finset.mem_filter.mp hz).1,
        h_sub (Finset.mem_filter.mp hz).2⟩
    exact D.no_bicolored_triangle T x hx' y hy' z hz' hxy hxz hyz

theorem clear_reciprocal_wrong_common_witnesses_sub
    (D : FiniteCompletionCliqueData α) :
    (clearReciprocalWrongCommonWitnesses D).K ⊆ D.K := by
  classical
  change (D.K \ reciprocalWrongCommonWitnessDeletionSetAll D) ⊆ D.K
  exact Finset.sdiff_subset

/-- No wrong-common-witness reciprocal survives the explicit second
cleanup. -/
theorem clear_reciprocal_wrong_common_witnesses_no_wrong
    (D : FiniteCompletionCliqueData α) (P : Edge α)
    (h_p_card : P.card = 2) (h_p_ground : P ⊆ D.ground)
    (a b w : α)
    (h_ab : (completionPairLinkGraph
      (clearReciprocalWrongCommonWitnesses D) P).Adj a b)
    (h_aw : (completionPairLinkGraph
      (clearReciprocalWrongCommonWitnesses D) P).Adj a w)
    (h_bw : (completionPairLinkGraph
      (clearReciprocalWrongCommonWitnesses D) P).Adj b w)
    (h_aw_label : D.label a w = b)
    (h_bw_label : D.label b w = a) :
    D.label a b = w := by
  classical
  by_contra h_wrong
  let D' := clearReciprocalWrongCommonWitnesses D
  have h_sub := clear_reciprocal_wrong_common_witnesses_sub D
  have h_ab_parent := completion_pair_link_graph_adj_mono
    D D' P rfl h_sub h_ab
  have h_aw_parent := completion_pair_link_graph_adj_mono
    D D' P rfl h_sub h_aw
  have h_bw_parent := completion_pair_link_graph_adj_mono
    D D' P rfl h_sub h_bw
  have h_edge : insert a (insert b P) ∈ D'.K := by
    change a ∉ P ∧ b ∉ P ∧ a ∈ D'.ground ∧ b ∈ D'.ground ∧
      a ≠ b ∧ insert a (insert b P) ∈ D'.K at h_ab
    exact h_ab.2.2.2.2.2
  have h_bad_root : insert a (insert b P) ∈
      reciprocalWrongCommonWitnessDeletionSet D P := by
    exact Finset.mem_filter.mpr
      ⟨h_sub h_edge,
        ⟨a, b, w, rfl, h_ab_parent, h_aw_parent, h_bw_parent,
          h_aw_label, h_bw_label, h_wrong⟩⟩
  have h_bad_all : insert a (insert b P) ∈
      reciprocalWrongCommonWitnessDeletionSetAll D :=
    Finset.mem_biUnion.mpr
      ⟨P, Finset.mem_powersetCard.mpr ⟨h_p_ground, h_p_card⟩,
        h_bad_root⟩
  have h_clean : insert a (insert b P) ∈
      D.K \ reciprocalWrongCommonWitnessDeletionSetAll D := h_edge
  exact (Finset.mem_sdiff.mp h_clean).2 h_bad_all

/-- A charging superset for wrong-common-witness deletions. The witness
lies in a bounded label fiber, while the target edge contains the fixed
triple `abℓ(ab)` and so lies in one facet-parent fiber. -/
noncomputable def reciprocalWrongCommonWitnessBudgetEdges
    (D : FiniteCompletionCliqueData α) : Family α := by
  classical
  exact (D.ground.product D.ground).biUnion fun ab =>
    (reciprocalLabelFiber D ab.1 ab.2).biUnion fun _w =>
      rankFourFacetParents D.K
        ({ab.1, ab.2, D.label ab.1 ab.2} : Edge α)

/-- Every wrong-common-witness target charges a bounded label fiber and a
triple-facet parent of the original family. -/
theorem reciprocal_wrong_common_witness_deletion_subset_budget
    (D : FiniteCompletionCliqueData α) :
    reciprocalWrongCommonWitnessDeletionSetAll D ⊆
      reciprocalWrongCommonWitnessBudgetEdges D := by
  classical
  intro E hE
  obtain ⟨P, hP, hRoot⟩ := Finset.mem_biUnion.mp hE
  have hP' := Finset.mem_powersetCard.mp hP
  obtain ⟨hEK, a, b, w, hEeq, hAB, hAW, hBW,
    hAWlabel, _, hWrong⟩ := Finset.mem_filter.mp hRoot
  have hzP : D.label a b ∈ P :=
    reciprocal_wrong_common_witness_label_in_root D P a b w
      hP'.2 hP'.1 hAB hAW hBW hWrong
  have hAB' := hAB
  have hAW' := hAW
  change a ∉ P ∧ b ∉ P ∧ a ∈ D.ground ∧ b ∈ D.ground ∧
    a ≠ b ∧ insert a (insert b P) ∈ D.K at hAB'
  change a ∉ P ∧ w ∉ P ∧ a ∈ D.ground ∧ w ∈ D.ground ∧
    a ≠ w ∧ insert a (insert w P) ∈ D.K at hAW'
  have hwFiber : w ∈ reciprocalLabelFiber D a b :=
    Finset.mem_filter.mpr
      ⟨hAW'.2.2.2.1, hAW'.2.2.2.2.1, hAWlabel⟩
  have hTripleSub : ({a, b, D.label a b} : Edge α) ⊆ E := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | hx
    · simp [hEeq]
    · simp [hEeq]
    · have hx' : x ∈ P := hx ▸ hzP
      simp [hEeq, hx']
  have hParent : E ∈ rankFourFacetParents D.K
      ({a, b, D.label a b} : Edge α) :=
    Finset.mem_filter.mpr ⟨hEK, hTripleSub⟩
  exact Finset.mem_biUnion.mpr
    ⟨(a, b), Finset.mem_product.mpr
      ⟨hAB'.2.2.1, hAB'.2.2.2.1⟩,
      Finset.mem_biUnion.mpr ⟨w, hwFiber, hParent⟩⟩

/-- Only valid three-element label facets can support an actual
wrong-common-witness target. -/
noncomputable def reciprocalWrongCommonWitnessTripleBudget
    (D : FiniteCompletionCliqueData α) : Family α := by
  classical
  exact ((D.ground.product D.ground).filter fun ab =>
    ab.1 ≠ ab.2 ∧ D.label ab.1 ab.2 ≠ ab.1 ∧
      D.label ab.1 ab.2 ≠ ab.2).biUnion fun ab =>
        rankFourFacetParents D.K
          ({ab.1, ab.2, D.label ab.1 ab.2} : Edge α)

theorem reciprocal_wrong_common_witness_deletion_subset_triple_budget
    (D : FiniteCompletionCliqueData α) :
    reciprocalWrongCommonWitnessDeletionSetAll D ⊆
      reciprocalWrongCommonWitnessTripleBudget D := by
  classical
  intro E hE
  obtain ⟨P, hP, hRoot⟩ := Finset.mem_biUnion.mp hE
  have hP' := Finset.mem_powersetCard.mp hP
  obtain ⟨hEK, a, b, w, hEeq, hAB, hAW, hBW,
    _, _, hWrong⟩ := Finset.mem_filter.mp hRoot
  have hzP : D.label a b ∈ P :=
    reciprocal_wrong_common_witness_label_in_root D P a b w
      hP'.2 hP'.1 hAB hAW hBW hWrong
  have hAB' := hAB
  change a ∉ P ∧ b ∉ P ∧ a ∈ D.ground ∧ b ∈ D.ground ∧
    a ≠ b ∧ insert a (insert b P) ∈ D.K at hAB'
  have hla : D.label a b ≠ a := by
    intro h
    exact hAB'.1 (h ▸ hzP)
  have hlb : D.label a b ≠ b := by
    intro h
    exact hAB'.2.1 (h ▸ hzP)
  have hPair : (a, b) ∈ (D.ground.product D.ground).filter
      (fun ab => ab.1 ≠ ab.2 ∧
        D.label ab.1 ab.2 ≠ ab.1 ∧
        D.label ab.1 ab.2 ≠ ab.2) :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr
        ⟨hAB'.2.2.1, hAB'.2.2.2.1⟩,
        hAB'.2.2.2.2.1, hla, hlb⟩
  have hTripleSub : ({a, b, D.label a b} : Edge α) ⊆ E := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | hx
    · simp [hEeq]
    · simp [hEeq]
    · have hx' : x ∈ P := hx ▸ hzP
      simp [hEeq, hx']
  exact Finset.mem_biUnion.mpr
    ⟨(a, b), hPair, Finset.mem_filter.mpr ⟨hEK, hTripleSub⟩⟩

/-- The realistic triple-degree assumption alone gives a stronger
D times ground-card squared bound for actual wrong-common-witness targets. -/
theorem reciprocal_wrong_common_witness_deletion_card_le_triple_cap
    (D : FiniteCompletionCliqueData α) (Dcap : ℕ)
    (h_facet : ∀ T : Edge α, T.card = 3 →
      (D.K.filter fun E => T ⊆ E).card ≤ Dcap) :
    (reciprocalWrongCommonWitnessDeletionSetAll D).card ≤
      D.ground.card * D.ground.card * Dcap := by
  classical
  let pairs := (D.ground.product D.ground).filter fun ab =>
    ab.1 ≠ ab.2 ∧ D.label ab.1 ab.2 ≠ ab.1 ∧
      D.label ab.1 ab.2 ≠ ab.2
  have hPerPair : ∀ ab ∈ pairs,
      (rankFourFacetParents D.K
        ({ab.1, ab.2, D.label ab.1 ab.2} : Edge α)).card ≤ Dcap := by
    intro ab hab
    have hParts := (Finset.mem_filter.mp hab).2
    apply h_facet
    have hnot : D.label ab.1 ab.2 ∉ ({ab.1, ab.2} : Edge α) := by
      simp [hParts.2.1, hParts.2.2]
    have hset : ({ab.1, ab.2, D.label ab.1 ab.2} : Edge α) =
        insert (D.label ab.1 ab.2) ({ab.1, ab.2} : Edge α) := by
      ext z
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [hset, Finset.card_insert_of_notMem hnot,
      Finset.card_pair hParts.1]
  calc
    _ ≤ (reciprocalWrongCommonWitnessTripleBudget D).card :=
      Finset.card_le_card
        (reciprocal_wrong_common_witness_deletion_subset_triple_budget D)
    _ ≤ pairs.card * Dcap := by
      exact Finset.card_biUnion_le_card_mul pairs _ Dcap hPerPair
    _ ≤ (D.ground.product D.ground).card * Dcap :=
      Nat.mul_le_mul_right Dcap (Finset.card_filter_le _ _)
    _ = D.ground.card * D.ground.card * Dcap := by
      simp [Finset.card_product, Nat.mul_assoc]

/-- Explicit `u² K_* D` budget for the missing §III.A.6 deletion,
under the actual label-fiber and triple-degree caps. -/
theorem reciprocal_wrong_common_witness_deletion_card_le
    (D : FiniteCompletionCliqueData α) (Kstar Dcap : ℕ)
    (h_label_cap : ∀ a b : α,
      (reciprocalLabelFiber D a b).card ≤ Kstar)
    (h_facet_cap : ∀ a ∈ D.ground, ∀ b ∈ D.ground,
      (rankFourFacetParents D.K
        ({a, b, D.label a b} : Edge α)).card ≤ Dcap) :
    (reciprocalWrongCommonWitnessDeletionSetAll D).card ≤
      D.ground.card * D.ground.card * Kstar * Dcap := by
  classical
  have hSub := reciprocal_wrong_common_witness_deletion_subset_budget D
  have hPerPair : ∀ ab ∈ D.ground.product D.ground,
      ((reciprocalLabelFiber D ab.1 ab.2).biUnion fun _w =>
        rankFourFacetParents D.K
          ({ab.1, ab.2, D.label ab.1 ab.2} : Edge α)).card ≤
      Kstar * Dcap := by
    intro ab hab
    have h := Finset.card_biUnion_le_card_mul
      (reciprocalLabelFiber D ab.1 ab.2)
      (fun _w => rankFourFacetParents D.K
        ({ab.1, ab.2, D.label ab.1 ab.2} : Edge α))
      Dcap (by
        intro w hw
        exact h_facet_cap ab.1 (Finset.mem_product.mp hab).1
          ab.2 (Finset.mem_product.mp hab).2)
    exact h.trans (Nat.mul_le_mul_right Dcap (h_label_cap ab.1 ab.2))
  have hBudget := Finset.card_biUnion_le_card_mul
    (D.ground.product D.ground)
    (fun ab => (reciprocalLabelFiber D ab.1 ab.2).biUnion fun _w =>
      rankFourFacetParents D.K
        ({ab.1, ab.2, D.label ab.1 ab.2} : Edge α))
    (Kstar * Dcap) hPerPair
  have hBudget' :
      (reciprocalWrongCommonWitnessBudgetEdges D).card ≤
        D.ground.card * D.ground.card * Kstar * Dcap := by
    simpa [reciprocalWrongCommonWitnessBudgetEdges,
      Finset.card_product, Nat.mul_assoc] using hBudget
  exact (Finset.card_le_card hSub).trans hBudget'

/-- The actual loss of the second reciprocal cleanup is no larger than
its explicit wrong-common-witness deletion set. -/
theorem clear_reciprocal_wrong_common_witnesses_loss_card_le
    (D : FiniteCompletionCliqueData α) :
    (D.K \ (clearReciprocalWrongCommonWitnesses D).K).card ≤
      (reciprocalWrongCommonWitnessDeletionSetAll D).card := by
  classical
  apply Finset.card_le_card
  intro E hE
  have hParts := Finset.mem_sdiff.mp hE
  by_contra hNotBad
  have hClean : E ∈ (clearReciprocalWrongCommonWitnesses D).K := by
    change E ∈ D.K \ reciprocalWrongCommonWitnessDeletionSetAll D
    exact Finset.mem_sdiff.mpr ⟨hParts.1, hNotBad⟩
  exact hParts.2 hClean

/-- Both reciprocal deletion rounds, with the wrong-common-witness round
applied to the distinct-witness survivor. -/
noncomputable def clearReciprocalFully
    (D : FiniteCompletionCliqueData α) : FiniteCompletionCliqueData α :=
  clearReciprocalWrongCommonWitnesses
    (clearReciprocalDifferentWitnesses D)

/-- The two cleanup losses add, with the second deletion measured on the
survivor of the first. -/
theorem clear_reciprocal_fully_loss_card_le
    (D : FiniteCompletionCliqueData α) :
    (D.K \ (clearReciprocalFully D).K).card ≤
      (reciprocalDifferentWitnessDeletionSetAll D).card +
      (reciprocalWrongCommonWitnessDeletionSetAll
        (clearReciprocalDifferentWitnesses D)).card := by
  classical
  let D₁ := clearReciprocalDifferentWitnesses D
  let D₂ := clearReciprocalFully D
  have h_sub_1 : D₁.K ⊆ D.K :=
    clear_reciprocal_different_witnesses_sub D
  have h_sub_2 : D₂.K ⊆ D₁.K :=
    clear_reciprocal_wrong_common_witnesses_sub D₁
  have h_sub : D₂.K ⊆ D.K := h_sub_2.trans h_sub_1
  have h_card_1 := Finset.card_sdiff_add_card_eq_card h_sub_1
  have h_card_2 := Finset.card_sdiff_add_card_eq_card h_sub_2
  have h_card := Finset.card_sdiff_add_card_eq_card h_sub
  have h_loss_1 := clear_reciprocal_different_witnesses_loss_card_le D
  have h_loss_2 := clear_reciprocal_wrong_common_witnesses_loss_card_le D₁
  change (D.K \ D₁.K).card ≤
    (reciprocalDifferentWitnessDeletionSetAll D).card at h_loss_1
  change (D₁.K \ D₂.K).card ≤
    (reciprocalWrongCommonWitnessDeletionSetAll D₁).card at h_loss_2
  change (D.K \ D₂.K).card ≤
    (reciprocalDifferentWitnessDeletionSetAll D).card +
      (reciprocalWrongCommonWitnessDeletionSetAll D₁).card
  omega

/-- The second cleanup cannot restore an edge deleted in the first round.
Thus the full survivor still has no distinct reciprocal witnesses. -/
theorem clear_reciprocal_fully_no_second
    (D : FiniteCompletionCliqueData α) (P : Edge α)
    (h_p_card : P.card = 2) (h_p_ground : P ⊆ D.ground) :
    ∀ a b r s : α,
      (completionPairLinkGraph (clearReciprocalFully D) P).Adj a b →
      (completionPairLinkGraph (clearReciprocalFully D) P).Adj b r →
      (completionPairLinkGraph (clearReciprocalFully D) P).Adj a s →
      a ≠ b → a ≠ r → a ≠ s → b ≠ r → b ≠ s → r ≠ s →
      (clearReciprocalFully D).label a r = b →
      (clearReciprocalFully D).label b s = a → r = s := by
  classical
  let D₁ := clearReciprocalDifferentWitnesses D
  let D₂ := clearReciprocalFully D
  have h_sub_1 : D₁.K ⊆ D.K :=
    clear_reciprocal_different_witnesses_sub D
  have h_sub_2 : D₂.K ⊆ D₁.K :=
    clear_reciprocal_wrong_common_witnesses_sub D₁
  have h_sub : D₂.K ⊆ D.K := h_sub_2.trans h_sub_1
  have h_avoid : ∀ E ∈ reciprocalDifferentWitnessDeletionSet D P,
      E ∉ D₂.K := by
    intro E hE hD₂
    exact clear_reciprocal_different_witnesses_avoids_root
      D P h_p_card h_p_ground E hE (h_sub_2 hD₂)
  intro a b r s hAB hBR hAS _hab hAR _hAS hBR' hBS _hRS hLabAR hLabBS
  exact no_second_reciprocal_witness_of_deletion
    D D₂ P rfl rfl h_sub h_avoid
    a b r s hAB hBR hAS hAR hBS hLabAR hLabBS

/-- In the fully cleaned family, a reciprocal pair's common witness is
its own completion-pair label. -/
theorem clear_reciprocal_fully_common_witness_eq_label
    (D : FiniteCompletionCliqueData α) (P : Edge α)
    (h_p_card : P.card = 2) (h_p_ground : P ⊆ D.ground)
    (a b w : α)
    (h_ab : (completionPairLinkGraph (clearReciprocalFully D) P).Adj a b)
    (h_aw : (completionPairLinkGraph (clearReciprocalFully D) P).Adj a w)
    (h_bw : (completionPairLinkGraph (clearReciprocalFully D) P).Adj b w)
    (h_aw_label : (clearReciprocalFully D).label a w = b)
    (h_bw_label : (clearReciprocalFully D).label b w = a) :
    (clearReciprocalFully D).label a b = w := by
  let D₁ := clearReciprocalDifferentWitnesses D
  exact clear_reciprocal_wrong_common_witnesses_no_wrong
    D₁ P h_p_card h_p_ground a b w
    h_ab h_aw h_bw h_aw_label h_bw_label

/-- Both deletion rounds and parent pair-label separation isolate every
surviving reciprocal triangle, without assuming `ℓ(ab)=w` separately. -/
theorem reciprocal_triangle_isolated_after_full_cleanup
    (D : FiniteCompletionCliqueData α) (P : Edge α)
    (a b w : α)
    [DecidableRel (completionPairLinkGraph (clearReciprocalFully D) P).Adj]
    (h_p_card : P.card = 2) (h_p_ground : P ⊆ D.ground)
    (hab : a ≠ b) (haw : a ≠ w) (hbw : b ≠ w)
    (h_ab : (completionPairLinkGraph (clearReciprocalFully D) P).Adj a b)
    (h_aw : (completionPairLinkGraph (clearReciprocalFully D) P).Adj a w)
    (h_bw : (completionPairLinkGraph (clearReciprocalFully D) P).Adj b w)
    (h_aw_label : (clearReciprocalFully D).label a w = b)
    (h_bw_label : (clearReciprocalFully D).label b w = a)
    (h_separated : ReciprocalParentPairSeparation
      (clearReciprocalFully D)) :
    ∀ x ∈ ({a, b, w} : Edge α), ∀ t : α,
      t ∉ ({a, b, w} : Edge α) →
      ¬ (completionPairLinkGraph (clearReciprocalFully D) P).Adj x t := by
  have h_ab_label := clear_reciprocal_fully_common_witness_eq_label
    D P h_p_card h_p_ground a b w h_ab h_aw h_bw
    h_aw_label h_bw_label
  exact reciprocal_triangle_isolated_of_parent_separation
    (clearReciprocalFully D) P a b w h_p_card h_p_ground
    hab haw hbw h_ab h_aw h_bw h_ab_label h_aw_label h_bw_label
    (clear_reciprocal_fully_no_second D P h_p_card h_p_ground)
    h_separated

end JSP523.Rank4
