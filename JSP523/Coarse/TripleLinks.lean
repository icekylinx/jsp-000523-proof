import JSP523.Coarse.GraphDeletion
import JSP523.Rank3.FirstMoment
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Ordinary links of a finite triple system

This module connects Part I's graph deletion lemma to the actual triples
used in the rank-three incidence ledgers.  The link at `z` has an edge `uv`
exactly when `zuv` is a triple of the parent family.
-/

namespace JSP523.Coarse

open Finset
open scoped Sym2

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The ordinary graph link of a triple family at `z`. -/
def tripleLinkGraph (T : Family α) (z : α) : SimpleGraph α where
  Adj u v := u ≠ v ∧ ({z, u, v} : Edge α) ∈ T
  symm.symm u v := by
    intro h
    refine ⟨h.1.symm, ?_⟩
    simpa only [Finset.pair_comm u v] using h.2
  loopless.irrefl u := by
    intro h
    exact h.1 rfl

omit [Fintype α] in
@[simp] theorem triple_link_graph_adj (T : Family α) (z u v : α) :
    (tripleLinkGraph T z).Adj u v ↔
      u ≠ v ∧ ({z, u, v} : Edge α) ∈ T := Iff.rfl

instance (T : Family α) (z : α) : DecidableRel (tripleLinkGraph T z).Adj :=
  inferInstanceAs (DecidableRel (fun u v : α =>
    u ≠ v ∧ ({z, u, v} : Edge α) ∈ T))

omit [Fintype α] in
theorem triple_link_graph_mono {S T : Family α}
    (hST : S ⊆ T) (z : α) :
    tripleLinkGraph S z ≤ tripleLinkGraph T z := by
  intro u v h
  exact ⟨h.1, hST h.2⟩

/-- Triple members represented by a selected set of graph edges at `z`.
The image may have fewer members than `R`, which is sufficient for the
deletion budget in Lemma I.3. -/
def linkDeletedTriples (z : α) (R : Finset (Sym2 α)) : Family α :=
  R.image (fun e => insert z e.toFinset)

omit [Fintype α] in
theorem link_deleted_triples_card_le (z : α) (R : Finset (Sym2 α)) :
    (linkDeletedTriples z R).card ≤ R.card := by
  exact Finset.card_image_le

omit [Fintype α] in
theorem triple_of_link_edge_mem_deleted (z u v : α)
    (R : Finset (Sym2 α)) (h : s(u, v) ∈ R) :
    ({z, u, v} : Edge α) ∈ linkDeletedTriples z R := by
  apply Finset.mem_image.mpr
  refine ⟨s(u, v), h, ?_⟩
  simp [Sym2.toFinset_mk_eq]

omit [Fintype α] in
theorem link_graph_after_delete_le (T : Family α) (z : α)
    (R : Finset (Sym2 α)) :
    tripleLinkGraph (T \ linkDeletedTriples z R) z ≤
      (tripleLinkGraph T z).deleteEdges R := by
  intro u v h
  have hT : ({z, u, v} : Edge α) ∈ T :=
    (Finset.mem_sdiff.mp h.2).1
  have hnot : ({z, u, v} : Edge α) ∉ linkDeletedTriples z R :=
    (Finset.mem_sdiff.mp h.2).2
  apply SimpleGraph.deleteEdges_adj.mpr
  refine ⟨⟨h.1, hT⟩, ?_⟩
  intro he
  exact hnot (triple_of_link_edge_mem_deleted z u v R he)

/-- A deletion set supplied by Lemma I.2 for each original vertex link. -/
noncomputable def linkRemovalEdges (T : Family α) (z : α) :
    Finset (Sym2 α) :=
  (graph_delete_four_cycles (tripleLinkGraph T z)).choose

theorem link_removal_edges_card_le (T : Family α) (z : α) :
    (linkRemovalEdges T z).card ≤
      (graphDiagonals (tripleLinkGraph T z)).card := by
  exact (graph_delete_four_cycles (tripleLinkGraph T z)).choose_spec.2.1

theorem link_removal_edges_four_cycle_free (T : Family α) (z : α) :
    FourCycleFree
      ((tripleLinkGraph T z).deleteEdges (linkRemovalEdges T z)) := by
  exact (graph_delete_four_cycles (tripleLinkGraph T z)).choose_spec.2.2

/-- All triples selected by the original-link graph deletions.  Choices
for different links may overlap, which only improves the cardinal bound. -/
noncomputable def allLinkDeletedTriples (T : Family α) : Family α :=
  Finset.univ.biUnion fun z : α =>
    linkDeletedTriples z (linkRemovalEdges T z)

/-- The triple system left after deleting the selected original-link
triples. -/
noncomputable def cleanTripleSystem (T : Family α) : Family α :=
  T \ allLinkDeletedTriples T

theorem all_link_deleted_triples_card_le (T : Family α) :
    (allLinkDeletedTriples T).card ≤
      ∑ z : α, (graphDiagonals (tripleLinkGraph T z)).card := by
  classical
  calc
    (allLinkDeletedTriples T).card ≤
        ∑ z : α, (linkDeletedTriples z (linkRemovalEdges T z)).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ z : α, (linkRemovalEdges T z).card := by
      apply Finset.sum_le_sum
      intro z _
      exact link_deleted_triples_card_le z (linkRemovalEdges T z)
    _ ≤ ∑ z : α,
          (graphDiagonals (tripleLinkGraph T z)).card := by
      apply Finset.sum_le_sum
      intro z _
      exact link_removal_edges_card_le T z

theorem clean_triple_system_card_budget (T : Family α) :
    T.card ≤ (cleanTripleSystem T).card +
      ∑ z : α, (graphDiagonals (tripleLinkGraph T z)).card := by
  have hcard := Finset.card_le_card_sdiff_add_card
    (s := T) (t := allLinkDeletedTriples T)
  exact hcard.trans (Nat.add_le_add_left
    (all_link_deleted_triples_card_le T) _)

theorem clean_triple_system_link_four_cycle_free (T : Family α) (z : α) :
    FourCycleFree (tripleLinkGraph (cleanTripleSystem T) z) := by
  classical
  have hlocal : linkDeletedTriples z (linkRemovalEdges T z) ⊆
      allLinkDeletedTriples T := by
    unfold allLinkDeletedTriples
    exact Finset.subset_biUnion_of_mem
      (fun w : α => linkDeletedTriples w (linkRemovalEdges T w))
      (Finset.mem_univ z)
  have hsub : cleanTripleSystem T ⊆
      T \ linkDeletedTriples z (linkRemovalEdges T z) := by
    intro E hE
    obtain ⟨hET, hEoutside⟩ := Finset.mem_sdiff.mp hE
    exact Finset.mem_sdiff.mpr ⟨hET, fun hElocal => hEoutside (hlocal hElocal)⟩
  have hgraph : tripleLinkGraph (cleanTripleSystem T) z ≤
      (tripleLinkGraph T z).deleteEdges (linkRemovalEdges T z) :=
    (triple_link_graph_mono hsub z).trans
      (link_graph_after_delete_le T z (linkRemovalEdges T z))
  exact FourCycleFree.mono hgraph (link_removal_edges_four_cycle_free T z)

end JSP523.Coarse
