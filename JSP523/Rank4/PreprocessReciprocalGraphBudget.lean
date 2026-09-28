import JSP523.Rank4.PreprocessReciprocalAssembly
import JSP523.Rank4.PreprocessUsedParentPairDegree
import JSP523.Rank4.PreprocessReciprocalTailCap

/-! # Finite C4 graph budget for the actual reciprocal cleanup -/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Sum of the established C4-free edge bounds over the actual colored
fixed-center parent-label pair-node graphs. -/
noncomputable def reciprocalActualC4GraphBudget
    (D : FiniteCompletionCliqueData α) (κ : ℕ)
    (color : ∀ x : α,
      fixedCenterPairNodes (reciprocalUsedParentLabelTriples D)
        D.ground x → Fin (2 * κ - 1)) : ℝ :=
  ∑ x ∈ D.ground,
    ∑ ij ∈ (Finset.univ : Finset
      (Fin (2 * κ - 1) × Fin (2 * κ - 1))),
      2 * ((Real.sqrt ((Fintype.card (Sum
        {P : fixedCenterPairNodes
          (reciprocalUsedParentLabelTriples D) D.ground x //
            (color x P).val = ij.1.val}
        {P : fixedCenterPairNodes
          (reciprocalUsedParentLabelTriples D) D.ground x //
            (color x P).val = ij.2.val}) : ℝ) ^ 3) +
          (Fintype.card (Sum
            {P : fixedCenterPairNodes
              (reciprocalUsedParentLabelTriples D) D.ground x //
                (color x P).val = ij.1.val}
            {P : fixedCenterPairNodes
              (reciprocalUsedParentLabelTriples D) D.ground x //
                (color x P).val = ij.2.val}) : ℝ) / 2) / 2)

/-- The actual disjoint-root deletion sum is bounded by C4-free graphs
with a proper coloring chosen from the verified greedy coloring lemma. -/
theorem reciprocal_actual_c4_graph_budget_exists
    (D : FiniteCompletionCliqueData α) (κ : ℕ)
    (hκ : 1 ≤ κ)
    (h_pair : ∀ P ∈ D.ground.powersetCard 2,
      qPairDegree (reciprocalUsedParentLabelTriples D) P ≤ κ) :
    ∃ color : ∀ x : α,
        fixedCenterPairNodes (reciprocalUsedParentLabelTriples D)
          D.ground x → Fin (2 * κ - 1),
      ((∑ x ∈ D.ground,
        (fixedCenterPairNodeDeletion D.K
          (reciprocalUsedParentLabelTriples D) D.ground x).card : ℕ) : ℝ) ≤
        reciprocalActualC4GraphBudget D κ color := by
  classical
  let Q := reciprocalUsedParentLabelTriples D
  have hExist (x : α) (hx : x ∈ D.ground) :
      ∃ c : fixedCenterPairNodes Q D.ground x → Fin (2 * κ - 1),
        ((fixedCenterPairNodeDeletion D.K Q D.ground x).card : ℝ) ≤
          ∑ ij ∈ (Finset.univ : Finset
            (Fin (2 * κ - 1) × Fin (2 * κ - 1))),
            2 * ((Real.sqrt ((Fintype.card (Sum
              {P : fixedCenterPairNodes Q D.ground x //
                (c P).val = ij.1.val}
              {P : fixedCenterPairNodes Q D.ground x //
                (c P).val = ij.2.val}) : ℝ) ^ 3) +
              (Fintype.card (Sum
                {P : fixedCenterPairNodes Q D.ground x //
                  (c P).val = ij.1.val}
                {P : fixedCenterPairNodes Q D.ground x //
                  (c P).val = ij.2.val}) : ℝ) / 2) / 2) :=
    actual_fixed_center_separation_explicit_bound D.K Q D.ground x κ
      hκ (reciprocal_used_parent_label_triples_uniform_three D)
      hx h_pair D.admissible
  let color (x : α) :
      fixedCenterPairNodes Q D.ground x → Fin (2 * κ - 1) :=
    if hx : x ∈ D.ground then Classical.choose (hExist x hx)
    else fun _ => ⟨0, by omega⟩
  refine ⟨color, ?_⟩
  rw [Nat.cast_sum]
  change (∑ x ∈ D.ground,
      ((fixedCenterPairNodeDeletion D.K Q D.ground x).card : ℝ)) ≤
    reciprocalActualC4GraphBudget D κ color
  unfold reciprocalActualC4GraphBudget
  apply Finset.sum_le_sum
  intro x hx
  have hBound := Classical.choose_spec (hExist x hx)
  have hColor : color x = Classical.choose (hExist x hx) := by
    simp [color, hx]
  rw [hColor]
  exact hBound

/-- All three actual reciprocal cleanup losses are paid by the existing
C4-free pair-node graphs and explicit quadratic wedge/witness terms. -/
theorem clear_used_parent_then_reciprocal_loss_le_c4_graph_budget
    (D : FiniteCompletionCliqueData α) (Dcap κ Kstar C_D : ℕ)
    (hκ : 1 ≤ κ)
    (h_ground : ∀ E ∈ D.K, E ⊆ D.ground)
    (h_pair : ∀ P ∈ D.ground.powersetCard 2,
      qPairDegree (reciprocalUsedParentLabelTriples D) P ≤ κ)
    (h_facet : ∀ T : Edge α, T.card = 3 →
      (D.K.filter fun E => T ⊆ E).card ≤ Dcap)
    (h_label : ∀ a b : α,
      (reciprocalLabelFiber D a b).card ≤ Kstar)
    (h_tail : ∀ a b r s : α,
      (reciprocalWitnessTailFiber D a b r s).card ≤ C_D) :
    ∃ color : ∀ x : α,
        fixedCenterPairNodes (reciprocalUsedParentLabelTriples D)
          D.ground x → Fin (2 * κ - 1),
      (((D.K \ (clearUsedParentThenReciprocal D).K).card : ℕ) : ℝ) ≤
        reciprocalActualC4GraphBudget D κ color +
        (Dcap * D.ground.card ^ 2 * κ ^ 2 +
          D.ground.card ^ 2 * Kstar ^ 2 * C_D +
          D.ground.card ^ 2 * Dcap : ℕ) := by
  obtain ⟨color, hC4⟩ :=
    reciprocal_actual_c4_graph_budget_exists D κ hκ h_pair
  refine ⟨color, ?_⟩
  have hFinite :=
    clear_used_parent_then_reciprocal_loss_card_le_degree_caps
      D Dcap κ Kstar C_D h_ground h_pair h_facet h_label h_tail
  have hFiniteR :
      (((D.K \ (clearUsedParentThenReciprocal D).K).card : ℕ) : ℝ) ≤
        ((∑ x ∈ D.ground,
          (fixedCenterPairNodeDeletion D.K
            (reciprocalUsedParentLabelTriples D) D.ground x).card : ℕ) : ℝ) +
        (Dcap * D.ground.card ^ 2 * κ ^ 2 +
          D.ground.card ^ 2 * Kstar ^ 2 * C_D +
          D.ground.card ^ 2 * Dcap : ℕ) := by
    have hNat :
        (D.K \ (clearUsedParentThenReciprocal D).K).card ≤
          (∑ x ∈ D.ground,
            (fixedCenterPairNodeDeletion D.K
              (reciprocalUsedParentLabelTriples D) D.ground x).card) +
          (Dcap * D.ground.card ^ 2 * κ ^ 2 +
            D.ground.card ^ 2 * Kstar ^ 2 * C_D +
            D.ground.card ^ 2 * Dcap) := by omega
    exact_mod_cast hNat
  linarith

/-- The corrected parent-label pair-degree input is supplied by the
original label-fiber cap, leaving no independent Q-degree premise. -/
theorem clear_used_parent_then_reciprocal_loss_le_c4_graph_budget_of_label_fibers
    (D : FiniteCompletionCliqueData α) (Dcap Kstar C_D : ℕ)
    (h_ground : ∀ E ∈ D.K, E ⊆ D.ground)
    (h_facet : ∀ T : Edge α, T.card = 3 →
      (D.K.filter fun E => T ⊆ E).card ≤ Dcap)
    (h_label : ∀ a b : α,
      (reciprocalLabelFiber D a b).card ≤ Kstar)
    (h_tail : ∀ a b r s : α,
      (reciprocalWitnessTailFiber D a b r s).card ≤ C_D) :
    ∃ color : ∀ x : α,
        fixedCenterPairNodes (reciprocalUsedParentLabelTriples D)
          D.ground x → Fin (2 * (2 + 4 * Kstar) - 1),
      (((D.K \ (clearUsedParentThenReciprocal D).K).card : ℕ) : ℝ) ≤
        reciprocalActualC4GraphBudget D (2 + 4 * Kstar) color +
        (Dcap * D.ground.card ^ 2 * (2 + 4 * Kstar) ^ 2 +
          D.ground.card ^ 2 * Kstar ^ 2 * C_D +
          D.ground.card ^ 2 * Dcap : ℕ) := by
  have hκ : 1 ≤ 2 + 4 * Kstar := by omega
  have hPair :=
    reciprocal_used_parent_pair_degree_cap_of_label_fibers D Kstar h_label
  exact clear_used_parent_then_reciprocal_loss_le_c4_graph_budget
    D Dcap (2 + 4 * Kstar) Kstar C_D hκ h_ground hPair
      h_facet h_label h_tail

/-- The actual three-round cleanup now needs only the initial label-fiber
and triple-degree caps; Q pair-degree and reciprocal tail caps are derived. -/
theorem clear_used_parent_then_reciprocal_loss_le_c4_graph_budget_of_degree_caps
    (D : FiniteCompletionCliqueData α) (Dcap Kstar : ℕ)
    (h_ground : ∀ E ∈ D.K, E ⊆ D.ground)
    (h_facet : ∀ T : Edge α, T.card = 3 →
      (D.K.filter fun E => T ⊆ E).card ≤ Dcap)
    (h_label : ∀ a b : α,
      (reciprocalLabelFiber D a b).card ≤ Kstar) :
    ∃ color : ∀ x : α,
        fixedCenterPairNodes (reciprocalUsedParentLabelTriples D)
          D.ground x → Fin (2 * (2 + 4 * Kstar) - 1),
      (((D.K \ (clearUsedParentThenReciprocal D).K).card : ℕ) : ℝ) ≤
        reciprocalActualC4GraphBudget D (2 + 4 * Kstar) color +
        (Dcap * D.ground.card ^ 2 * (2 + 4 * Kstar) ^ 2 +
          D.ground.card ^ 2 * Kstar ^ 2 * max Dcap 3 +
          D.ground.card ^ 2 * Dcap : ℕ) := by
  have hTail : ∀ a b r s : α,
      (reciprocalWitnessTailFiber D a b r s).card ≤
        max Dcap 3 :=
    reciprocal_witness_tail_fiber_card_le_max_facet_three D Dcap h_facet
  exact
    clear_used_parent_then_reciprocal_loss_le_c4_graph_budget_of_label_fibers
      D Dcap Kstar (max Dcap 3) h_ground h_facet h_label hTail

end JSP523.Rank4
