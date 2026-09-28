import JSP523.Rank4.GraphEdgeAccounting

/-!
# Degree-excess ledger for native pair graphs

The native representation (III.B.8) ultimately reindexes positive
common-neighbor excess over the nonisolated vertices of each native graph.
This file proves the graph-internal identity used at that last step.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α]

/-- Nonisolated vertices of a finite graph, represented as a finset. -/
def nativeActiveVertices (F : SimpleGraph α) [DecidableRel F.Adj] :
    Finset α :=
  Finset.univ.filter fun x => 0 < F.degree x

/-- The sum of degree excesses over nonisolated vertices equals twice the
edge count minus the number of those vertices, without truncated
subtraction in the statement. -/
theorem native_degree_excess_identity
    (F : SimpleGraph α) [DecidableRel F.Adj] :
    (nativeActiveVertices F).sum (fun x => F.degree x - 1) +
      (nativeActiveVertices F).card =
        2 * F.edgeFinset.card := by
  classical
  have hAt : ∀ x ∈ nativeActiveVertices F,
      F.degree x - 1 + 1 = F.degree x := by
    intro x hx
    have hxPos : 0 < F.degree x :=
      (Finset.mem_filter.mp hx).2
    omega
  have hActive :
      (nativeActiveVertices F).sum (fun x => F.degree x - 1) +
        (nativeActiveVertices F).card =
          (nativeActiveVertices F).sum (fun x => F.degree x) := by
    calc
      (nativeActiveVertices F).sum (fun x => F.degree x - 1) +
          (nativeActiveVertices F).card =
          (nativeActiveVertices F).sum (fun x => F.degree x - 1) +
            (nativeActiveVertices F).sum (fun _x => (1 : ℕ)) := by simp
      _ = (nativeActiveVertices F).sum
          (fun x => (F.degree x - 1 + 1)) := by
        rw [Finset.sum_add_distrib]
      _ = (nativeActiveVertices F).sum (fun x => F.degree x) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hAt x hx
  have hDegreeSupport :
      (nativeActiveVertices F).sum (fun x => F.degree x) =
        ∑ x : α, F.degree x := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro x hx hNot
    have hxZero : F.degree x = 0 := by
      have hxNotPos : ¬ 0 < F.degree x := by
        intro hPos
        exact hNot (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hPos⟩)
      omega
    exact hxZero
  have hHand := F.sum_degrees_eq_twice_card_edges
  rw [hActive, hDegreeSupport]
  exact hHand

end JSP523.Rank4
