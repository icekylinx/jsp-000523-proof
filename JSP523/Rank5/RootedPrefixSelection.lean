import JSP523.Rank5.RootedPartition
import JSP523.Counting.PrefixAssignment

/-!
# Actual prefixes of repaired rooted five-edges

Each rooted five-edge has a two-vertex prefix containing its triple root.
The resulting deterministic choice supplies the prefix-size and
triple-center conditions in the assigned-prefix bound.
-/

namespace JSP523.Rank5

open JSP523.Counting

variable {α : Type*} [DecidableEq α]

theorem rooted_edge_has_pair_prefix
    {E : Edge α} {z : Edge α → α}
    (hEcard : E.card = 5)
    (hRoot : ∃ v : α, TripleRoot E z v) :
    ∃ Y : Edge α, Y ⊆ E ∧ Y.card = 2 ∧
      ∃ v ∈ Y, TripleRoot E z v := by
  obtain ⟨v, hv⟩ := hRoot
  obtain ⟨w, hwE, hwv⟩ := Finset.exists_mem_ne (by omega : 1 < E.card) v
  refine ⟨{v, w}, ?_, ?_, v, by simp, hv⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hv.1
    · exact (Finset.mem_singleton.mp hx) ▸ hwE
  · exact Finset.card_pair hwv.symm

/-- A total choice of the rooted pair prefix. Values on unrooted edges are
    irrelevant because they are never passed to the rooted fiber count. -/
noncomputable def rootedChosenPairPrefix
    (z : Edge α → α) (E : Edge α) : Edge α := by
  classical
  if h : ∃ Y : Edge α, Y ⊆ E ∧ Y.card = 2 ∧
      ∃ v ∈ Y, TripleRoot E z v then
    exact Classical.choose h
  else
    exact ∅

theorem rooted_chosen_pair_prefix_spec
    (K : Family α) (z : Edge α → α)
    (hUniform : Uniform 5 K)
    {E : Edge α} (hE : E ∈ rootedEdges K z) :
    rootedChosenPairPrefix z E ⊆ E ∧
      (rootedChosenPairPrefix z E).card = 2 ∧
      ∃ v ∈ rootedChosenPairPrefix z E, TripleRoot E z v := by
  classical
  have hRoot := ((mem_rooted_edges_iff K z E).mp hE).2
  have hCard := hUniform ((mem_rooted_edges_iff K z E).mp hE).1
  have h := rooted_edge_has_pair_prefix hCard hRoot
  unfold rootedChosenPairPrefix
  rw [dite_eq_left h]
  exact Classical.choose_spec h

/-- The selected pair on every rooted edge satisfies the mass-counting
    prefix interface at rank five. -/
theorem rooted_chosen_pair_prefix_sub_card
    (K : Family α) (z : Edge α → α)
    (hUniform : Uniform 5 K) :
    (∀ E ∈ rootedEdges K z, rootedChosenPairPrefix z E ⊆ E) ∧
    (∀ E ∈ rootedEdges K z, (rootedChosenPairPrefix z E).card = 2) := by
  constructor
  · intro E hE
    exact (rooted_chosen_pair_prefix_spec K z hUniform hE).1
  · intro E hE
    exact (rooted_chosen_pair_prefix_spec K z hUniform hE).2.1

/-- Every triple obtained by adding one tail vertex to an assigned rooted
    pair has center in that pair. This discharges the rank-five `hCenter`
    premise of the assigned-prefix collision theorem. -/
theorem rooted_chosen_pair_prefix_triple_centers
    (K : Family α) (V : Edge α) (z : Edge α → α)
    (hUniform : Uniform 5 K) :
    ∀ P ∈ V.powersetCard 3,
      ∀ Y ∈ chosenPrefixesAt (rootedEdges K z) V 2
        (rootedChosenPairPrefix z) P,
        ∀ x ∈ P, z (Y ∪ {x}) ∈ Y := by
  intro P hP Y hY x hxP
  have hParts := mem_chosen_prefixes_at.mp hY
  have hE : Y ∪ P ∈ rootedEdges K z := hParts.2.2.1
  have hYeq : rootedChosenPairPrefix z (Y ∪ P) = Y := hParts.2.2.2
  obtain ⟨_, hYcard, v, hvY, hv⟩ :=
    rooted_chosen_pair_prefix_spec K z hUniform hE
  rw [hYeq] at hYcard hvY
  have hxY : x ∉ Y := by
    intro hxY
    exact (Finset.disjoint_left.mp hParts.2.1) hxY hxP
  have hSCard : (Y ∪ {x}).card = 3 := by
    rw [Finset.union_singleton, Finset.card_insert_of_notMem hxY]
    omega
  have hSSub : Y ∪ {x} ⊆ Y ∪ P := by
    intro a ha
    rcases Finset.mem_union.mp ha with haY | hax
    · exact Finset.mem_union_left P haY
    · exact Finset.mem_union_right Y ((Finset.mem_singleton.mp hax) ▸ hxP)
  have hvS : v ∈ Y ∪ {x} := Finset.mem_union_left _ hvY
  rw [hv.2 (Y ∪ {x}) hSSub hSCard hvS]
  exact hvY

end JSP523.Rank5
