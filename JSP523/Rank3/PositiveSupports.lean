import JSP523.Rank3.IncidenceDoubleCount
import Lean.Elab.Tactic.Omega

/-!
# Identify the actual rank-three supports with positive local degrees

The support ledger uses pairs with positive completion degree and cells
with positive common-link size.  The existing finite supports were defined
through edge witnesses.  This module proves those two descriptions agree
for a three-uniform family carried by the chosen ground set.
-/

namespace JSP523.Rank3

section PositiveSupports

variable {α : Type*} [DecidableEq α]

/-- A two-element subset of a three-element edge plus any third point is
    exactly that edge. -/
theorem pair_extension_eq_triple
    {p E : Edge α} {x : α}
    (hp2 : p.card = 2) (hE3 : E.card = 3)
    (hpE : p ⊆ E) (hxE : x ∈ E) (hxp : x ∉ p) :
    p ∪ {x} = E := by
  have hsub : p ∪ {x} ⊆ E := by
    intro y hy
    rcases Finset.mem_union.mp hy with hyp | hyx
    · exact hpE hyp
    · exact (Finset.mem_singleton.mp hyx) ▸ hxE
  have hUnion : p ∪ {x} = insert x p := by
    ext y
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
    constructor
    · intro hy
      rcases hy with hyp | hyx
      · exact Or.inr hyp
      · exact Or.inl hyx
    · intro hy
      rcases hy with hyx | hyp
      · exact Or.inr hyx
      · exact Or.inl hyp
  have hcard : (p ∪ {x}).card = 3 := by
    rw [hUnion, Finset.card_insert_of_notMem hxp, hp2]
  exact Finset.eq_of_subset_of_card_le hsub (by rw [hE3, hcard])

/-- A triple containing a pair has a vertex outside that pair. -/
theorem pair_subset_triple_has_extra
    {p E : Edge α}
    (hp2 : p.card = 2) (hE3 : E.card = 3)
    (_hpE : p ⊆ E) :
    ∃ x ∈ E, x ∉ p := by
  by_contra h
  have hsub : E ⊆ p := by
    intro x hx
    by_contra hxp
    exact h ⟨x, hx, hxp⟩
  have hbound := Finset.card_le_card hsub
  omega

/-- A positive completion degree always produces an actually used pair. -/
theorem completion_nonempty_implies_used_pair
    (H : Family α) (V p : Edge α)
    (hp : p ∈ V.powersetCard 2)
    (hnon : (completionVertices H V p).Nonempty) :
    p ∈ usedPairs H V := by
  obtain ⟨x, hx⟩ := hnon
  obtain ⟨_, _, hpx⟩ := Finset.mem_filter.mp hx
  apply Finset.mem_filter.mpr
  refine ⟨hp, ⟨p ∪ {x}, hpx, ?_⟩⟩
  intro y hy
  exact Finset.mem_union.mpr (Or.inl hy)

/-- In a three-uniform family on `V`, every actually used ambient pair
    has a completing vertex: its containing triple has one point beyond
    the two vertices of the pair. -/
theorem used_pair_has_completion
    (H : Family α) (V p : Edge α)
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hp : p ∈ usedPairs H V) :
    (completionVertices H V p).Nonempty := by
  obtain ⟨hpV, E, hEH, hpE⟩ := Finset.mem_filter.mp hp
  have hp2 : p.card = 2 := (Finset.mem_powersetCard.mp hpV).2
  have hE3 : E.card = 3 := hUniform hEH
  have hthird : ∃ x ∈ E, x ∉ p :=
    pair_subset_triple_has_extra hp2 hE3 hpE
  obtain ⟨x, hxE, hxp⟩ := hthird
  have hEq : p ∪ {x} = E :=
    pair_extension_eq_triple hp2 hE3 hpE hxE hxp
  refine ⟨x, Finset.mem_filter.mpr ⟨hground E hEH hxE, hxp, ?_⟩⟩
  exact hEq.symm ▸ hEH

/-- A used ambient pair is exactly an ambient pair of positive completion
    degree when the family is three-uniform and supported on `V`. -/
theorem mem_used_pairs_iff_completion_nonempty
    (H : Family α) (V p : Edge α)
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hp : p ∈ V.powersetCard 2) :
    p ∈ usedPairs H V ↔ (completionVertices H V p).Nonempty := by
  constructor
  · exact used_pair_has_completion H V p hUniform hground
  · exact completion_nonempty_implies_used_pair H V p hp

/-- Actual ambient pairs with strictly positive completion degree. -/
def positiveCompletionPairs (H : Family α) (V : Edge α) : Family α :=
  (V.powersetCard 2).filter (fun p => 0 < (completionVertices H V p).card)

/-- The edge-witness pair support agrees with the positive-degree support. -/
theorem used_pairs_eq_positive_completion_pairs
    (H : Family α) (V : Edge α)
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V) :
    usedPairs H V = positiveCompletionPairs H V := by
  ext p
  constructor
  · intro hp
    have hpV : p ∈ V.powersetCard 2 := (Finset.mem_filter.mp hp).1
    have hnon : (completionVertices H V p).Nonempty :=
      (mem_used_pairs_iff_completion_nonempty H V p hUniform hground hpV).mp hp
    exact Finset.mem_filter.mpr ⟨hpV, Finset.card_pos.mpr hnon⟩
  · intro hp
    obtain ⟨hpV, hpos⟩ := Finset.mem_filter.mp hp
    exact (mem_used_pairs_iff_completion_nonempty H V p
      hUniform hground hpV).mpr (Finset.card_pos.mp hpos)

/-- Actual cells with a strictly positive common-link size. -/
def positiveCommonLinkCells (H : Family α) (V : Edge α) : Family α :=
  (V.powersetCard 2).filter (fun q => 0 < (commonLink H V q).card)

/-- The common-link witness definition of used cells equals positive
    common-link size, with no uniformity hypothesis. -/
theorem used_cells_eq_positive_common_link_cells
    (H : Family α) (V : Edge α) :
    usedCells H V = positiveCommonLinkCells H V := by
  ext q
  constructor
  · intro hq
    obtain ⟨hqV, hnon⟩ :=
      (mem_used_cells_iff_common_link_nonempty H V q).mp hq
    exact Finset.mem_filter.mpr ⟨hqV, Finset.card_pos.mpr hnon⟩
  · intro hq
    obtain ⟨hqV, hpos⟩ := Finset.mem_filter.mp hq
    exact (mem_used_cells_iff_common_link_nonempty H V q).mpr
      ⟨hqV, Finset.card_pos.mp hpos⟩

end PositiveSupports

end JSP523.Rank3
