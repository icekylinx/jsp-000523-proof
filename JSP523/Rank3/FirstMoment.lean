import JSP523.Rank3.PositiveSupports
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Lean.Elab.Tactic.Omega

/-!
# The two exact rank-three incidence moments

The first moment counts each triple once for each of its three pairs.
The second identity restricts the previously proved common-link double
count to its genuinely used cell support.  Both sums refer to the actual
finite family rather than independent ledger parameters.
-/

namespace JSP523.Rank3

section FirstMoment

variable {α : Type*} [DecidableEq α]

/-- Edges of `H` containing one pair. -/
def containingEdges (H : Family α) (p : Edge α) : Family α :=
  H.filter (fun E => p ⊆ E)

/-- Completing vertices and containing triples are in bijection. -/
theorem completion_vertices_card_eq_containing_edges
    (H : Family α) (V p : Edge α)
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hp : p ∈ V.powersetCard 2) :
    (completionVertices H V p).card = (containingEdges H p).card := by
  apply Finset.card_bij (fun x _ => p ∪ {x})
  · intro x hx
    obtain ⟨_, _, hxH⟩ := Finset.mem_filter.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨hxH, ?_⟩
    intro y hy
    exact Finset.mem_union.mpr (Or.inl hy)
  · intro x hx y hy heq
    have hxp : x ∉ p := (Finset.mem_filter.mp hx).2.1
    have hxUnion : x ∈ p ∪ ({x} : Edge α) := by simp
    have hxY : x ∈ p ∪ ({y} : Edge α) := heq ▸ hxUnion
    rcases Finset.mem_union.mp hxY with hxP | hxSingle
    · exact False.elim (hxp hxP)
    · exact Finset.mem_singleton.mp hxSingle
  · intro E hE
    obtain ⟨hEH, hpE⟩ := Finset.mem_filter.mp hE
    have hp2 : p.card = 2 := (Finset.mem_powersetCard.mp hp).2
    have hE3 : E.card = 3 := hUniform hEH
    obtain ⟨x, hxE, hxp⟩ :=
      pair_subset_triple_has_extra hp2 hE3 hpE
    have heq : p ∪ {x} = E :=
      pair_extension_eq_triple hp2 hE3 hpE hxE hxp
    refine ⟨x, Finset.mem_filter.mpr ⟨hground E hEH hxE, hxp, ?_⟩, heq⟩
    exact heq.symm ▸ hEH

/-- Every triple contributes exactly three incidences with ambient pairs. -/
theorem containing_edges_first_moment
    (H : Family α) (V : Edge α)
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V) :
    (∑ p ∈ V.powersetCard 2, (containingEdges H p).card) =
      3 * H.card := by
  classical
  let P : Family α := V.powersetCard 2
  calc
    (∑ p ∈ P, (containingEdges H p).card) =
        ∑ p ∈ P, ∑ E ∈ H, if p ⊆ E then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      exact Finset.card_filter (fun E : Edge α => p ⊆ E) H
    _ = ∑ E ∈ H, ∑ p ∈ P,
          if p ⊆ E then (1 : ℕ) else 0 := Finset.sum_comm
    _ = ∑ E ∈ H, (E.powersetCard 2).card := by
      apply Finset.sum_congr rfl
      intro E hEH
      have hfilter : P.filter (fun p => p ⊆ E) =
          E.powersetCard 2 := by
        ext p
        constructor
        · intro hp
          obtain ⟨hpP, hpE⟩ := Finset.mem_filter.mp hp
          exact Finset.mem_powersetCard.mpr
            ⟨hpE, (Finset.mem_powersetCard.mp hpP).2⟩
        · intro hp
          obtain ⟨hpE, hp2⟩ := Finset.mem_powersetCard.mp hp
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_powersetCard.mpr
            ⟨hpE.trans (hground E hEH), hp2⟩, hpE⟩
      calc
        (∑ p ∈ P, if p ⊆ E then (1 : ℕ) else 0) =
            (P.filter (fun p => p ⊆ E)).card :=
          (Finset.card_filter (fun p => p ⊆ E) P).symm
        _ = (E.powersetCard 2).card := congrArg Finset.card hfilter
    _ = ∑ E ∈ H, (3 : ℕ) := by
      apply Finset.sum_congr rfl
      intro E hEH
      rw [Finset.card_powersetCard, hUniform hEH]
      decide
    _ = 3 * H.card := by simp [mul_comm]

/-- The genuine completion degrees, summed over all ambient pairs. -/
theorem completion_vertices_first_moment
    (H : Family α) (V : Edge α)
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V) :
    (∑ p ∈ V.powersetCard 2,
        (completionVertices H V p).card) = 3 * H.card := by
  calc
    (∑ p ∈ V.powersetCard 2,
        (completionVertices H V p).card) =
      ∑ p ∈ V.powersetCard 2, (containingEdges H p).card := by
        apply Finset.sum_congr rfl
        intro p hp
        exact completion_vertices_card_eq_containing_edges
          H V p hUniform hground hp
    _ = 3 * H.card := containing_edges_first_moment H V hUniform hground

/-- Unused pairs contribute zero to the first moment. -/
theorem used_pairs_completion_first_moment
    (H : Family α) (V : Edge α)
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V) :
    (∑ p ∈ usedPairs H V,
        (completionVertices H V p).card) = 3 * H.card := by
  calc
    (∑ p ∈ usedPairs H V,
        (completionVertices H V p).card) =
      ∑ p ∈ V.powersetCard 2,
        (completionVertices H V p).card := by
        apply Finset.sum_subset (used_pairs_subset H V)
        intro p hp hnot
        by_cases hz : (completionVertices H V p).card = 0
        · exact hz
        · have hpos : 0 < (completionVertices H V p).card :=
            Nat.pos_of_ne_zero hz
          have hnon : (completionVertices H V p).Nonempty :=
            Finset.card_pos.mp hpos
          exact False.elim (hnot
            ((mem_used_pairs_iff_completion_nonempty H V p
              hUniform hground hp).mpr hnon))
    _ = 3 * H.card := completion_vertices_first_moment H V hUniform hground

/-- The number of completions beyond the first, summed over actual used
    ambient pairs. -/
def pairDegreeExcess (H : Family α) (V : Edge α) : ℕ :=
  (usedPairs H V).sum (fun p => (completionVertices H V p).card - 1)

/-- The exact first-moment surplus: each used pair accounts for its first
    triple, and the remaining triple incidences form `pairDegreeExcess`. -/
theorem used_pairs_completion_excess_ledger
    (H : Family α) (V : Edge α)
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V) :
    3 * H.card = (usedPairs H V).card +
      pairDegreeExcess H V := by
  have hlocal : ∀ p ∈ usedPairs H V,
      (completionVertices H V p).card =
        1 + ((completionVertices H V p).card - 1) := by
    intro p hp
    have hpos : 0 < (completionVertices H V p).card :=
      Finset.card_pos.mpr
        (used_pair_has_completion H V p hUniform hground hp)
    omega
  calc
    3 * H.card =
        ∑ p ∈ usedPairs H V,
          (completionVertices H V p).card :=
      (used_pairs_completion_first_moment H V hUniform hground).symm
    _ = ∑ p ∈ usedPairs H V,
          (1 + ((completionVertices H V p).card - 1)) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact hlocal p hp
    _ = (usedPairs H V).card + pairDegreeExcess H V := by
      simp [pairDegreeExcess, Finset.sum_add_distrib]

/-- Every used pair receives at least one of the three incidences
    contributed by each triple. -/
theorem used_pairs_card_le_three_edges
    (H : Family α) (V : Edge α)
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V) :
    (usedPairs H V).card ≤ 3 * H.card := by
  have hledger := used_pairs_completion_excess_ledger H V hUniform hground
  omega

/-- The second moment is likewise supported on the actual used cells. -/
theorem used_cells_common_link_double_count
    (H : Family α) (V : Edge α) :
    (∑ q ∈ usedCells H V, (commonLink H V q).card) =
      ∑ p ∈ V.powersetCard 2,
        (completionVertices H V p).card.choose 2 := by
  calc
    (∑ q ∈ usedCells H V, (commonLink H V q).card) =
      ∑ q ∈ V.powersetCard 2, (commonLink H V q).card := by
        apply Finset.sum_subset (used_cells_subset H V)
        intro q hq hnot
        by_cases hz : (commonLink H V q).card = 0
        · exact hz
        · have hpos : 0 < (commonLink H V q).card :=
            Nat.pos_of_ne_zero hz
          have hnon : (commonLink H V q).Nonempty :=
            Finset.card_pos.mp hpos
          exact False.elim (hnot
            ((mem_used_cells_iff_common_link_nonempty H V q).mpr ⟨hq, hnon⟩))
    _ = ∑ p ∈ V.powersetCard 2,
          (completionVertices H V p).card.choose 2 :=
      actual_common_link_double_count H V

end FirstMoment

end JSP523.Rank3
