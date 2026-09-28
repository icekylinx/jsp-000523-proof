import JSP523.Rank5.RealShadowSurplus

set_option linter.unusedSectionVars false

/-!
# The actual rooted/unrooted partition of a five-uniform family

The earlier shadow assembly accepted three separate sets with a cardinal
partition and a no-root condition.  Here the two pieces are defined from
the assigned triple centers themselves.  The shadow and real surplus
theorems consequently need only five-uniformity and the explicit local
shared-face coherence input.
-/

namespace JSP523.Rank5

section RootedPartition

variable {α : Type*} [DecidableEq α]

/-- A vertex which centers every triple of `E` containing it. -/
def TripleRoot (E : Edge α) (z : Edge α → α) (v : α) : Prop :=
  v ∈ E ∧ ∀ S : Edge α, S ⊆ E → S.card = 3 → v ∈ S → z S = v

/-- The actual rooted part of a finite family. -/
noncomputable def rootedEdges (all : Family α) (z : Edge α → α) : Family α := by
  classical
  exact all.filter (fun E => ∃ v : α, TripleRoot E z v)

/-- The actual unrooted part of the same family. -/
noncomputable def unrootedEdges (all : Family α) (z : Edge α → α) : Family α := by
  classical
  exact all.filter (fun E => ¬ ∃ v : α, TripleRoot E z v)

theorem mem_rootedEdges_iff
    (all : Family α) (z : Edge α → α) (E : Edge α) :
    E ∈ rootedEdges all z ↔
      E ∈ all ∧ ∃ v : α, TripleRoot E z v := by
  classical
  exact Finset.mem_filter

theorem mem_unrootedEdges_iff
    (all : Family α) (z : Edge α → α) (E : Edge α) :
    E ∈ unrootedEdges all z ↔
      E ∈ all ∧ ¬ ∃ v : α, TripleRoot E z v := by
  classical
  exact Finset.mem_filter

theorem rootedEdges_subset
    (all : Family α) (z : Edge α → α) :
    rootedEdges all z ⊆ all := by
  intro E hE
  exact ((mem_rootedEdges_iff all z E).mp hE).1

theorem unrootedEdges_subset
    (all : Family α) (z : Edge α → α) :
    unrootedEdges all z ⊆ all := by
  intro E hE
  exact ((mem_unrootedEdges_iff all z E).mp hE).1

theorem rooted_unrooted_disjoint
    (all : Family α) (z : Edge α → α) :
    Disjoint (rootedEdges all z) (unrootedEdges all z) := by
  apply Finset.disjoint_left.mpr
  intro E hr hu
  have hroot := ((mem_rootedEdges_iff all z E).mp hr).2
  have hnroot := ((mem_unrootedEdges_iff all z E).mp hu).2
  exact hnroot hroot

theorem rooted_unrooted_union
    (all : Family α) (z : Edge α → α) :
    rootedEdges all z ∪ unrootedEdges all z = all := by
  classical
  ext E
  constructor
  · intro hE
    rcases Finset.mem_union.mp hE with hr | hu
    · exact rootedEdges_subset all z hr
    · exact unrootedEdges_subset all z hu
  · intro hE
    by_cases hr : ∃ v : α, TripleRoot E z v
    · exact Finset.mem_union.mpr (Or.inl
        ((mem_rootedEdges_iff all z E).mpr ⟨hE, hr⟩))
    · exact Finset.mem_union.mpr (Or.inr
        ((mem_unrootedEdges_iff all z E).mpr ⟨hE, hr⟩))

theorem rooted_unrooted_card_partition
    (all : Family α) (z : Edge α → α) :
    all.card = (rootedEdges all z).card +
      (unrootedEdges all z).card := by
  classical
  have hcard := Finset.card_union_of_disjoint
    (rooted_unrooted_disjoint all z)
  rw [rooted_unrooted_union all z] at hcard
  exact hcard

theorem unrooted_has_no_triple_root
    (all : Family α) (z : Edge α → α)
    {E : Edge α} (hE : E ∈ unrootedEdges all z) :
    ¬ ∃ v ∈ E, ∀ S : Edge α,
      S ⊆ E → S.card = 3 → v ∈ S → z S = v := by
  exact ((mem_unrootedEdges_iff all z E).mp hE).2

/-- The actual finite shadow inequality no longer asks for an abstract
    partition or a separate rootlessness proof. -/
theorem actual_four_shadow_bound_of_shared_coherence
    (all : Family α) (z : Edge α → α)
    (hUniform : Uniform 5 all)
    (hshared : ∀ E ∈ unrootedEdges all z, ∀ a ∈ E,
      (∃ F ∈ all, F ≠ E ∧ E.erase a ⊆ F) →
      CoherentDeletedFace E z a) :
    2 * all.card ≤ (fourShadow all).card +
      2 * (rootedEdges all z).card := by
  apply actual_four_shadow_bound_of_rootless_coherence z
    (rooted_unrooted_card_partition all z)
    (unrootedEdges_subset all z)
  · intro E hE
    exact hUniform (unrootedEdges_subset all z hE)
  · intro E hE
    exact unrooted_has_no_triple_root all z hE
  · exact hshared

/-- The same concrete partition enters the real signed-surplus interface,
    with an independent real upper bound on the rooted error. -/
theorem actual_four_shadow_real_surplus_of_shared_coherence
    (all : Family α) (z : Edge α → α) (ε : ℝ)
    (hUniform : Uniform 5 all)
    (hshared : ∀ E ∈ unrootedEdges all z, ∀ a ∈ E,
      (∃ F ∈ all, F ≠ E ∧ E.erase a ⊆ F) →
      CoherentDeletedFace E z a)
    (hroot : ((rootedEdges all z).card : ℝ) ≤ ε) :
    (all.card : ℝ) - ((fourShadow all).card : ℝ) ≤
      -(all.card : ℝ) + 2 * ε := by
  apply actual_four_shadow_real_surplus_with_error z ε
    (rooted_unrooted_card_partition all z)
    (unrootedEdges_subset all z)
  · intro E hE
    exact hUniform (unrootedEdges_subset all z hE)
  · intro E hE
    exact unrooted_has_no_triple_root all z hE
  · exact hshared
  · exact hroot

end RootedPartition

end JSP523.Rank5
