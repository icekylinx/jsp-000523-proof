import JSP523.Rank4.GraphUnorderedCommonLedger

/-!
# Unordered common-pair potential ledger

For every finite graph, the degree-pair count splits exactly into the
number of unordered pairs with a common neighbor and their positive
multiplicity excess. This is the graph-theoretic half of (III.B.8).
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The number of unordered vertex pairs with at least one common
neighbor. -/
noncomputable def graphCommonPairCount
    (F : SimpleGraph α) [DecidableRel F.Adj] : ℕ :=
  (((Finset.univ : Finset α).powersetCard 2).filter
    (fun P => 0 < graphCommonMultiplicityAtPair F P)).card

/-- The total positive common-neighbor multiplicity excess over
unordered vertex pairs. -/
noncomputable def graphUnorderedCommonExcess
    (F : SimpleGraph α) [DecidableRel F.Adj] : ℕ :=
  ∑ P ∈ (Finset.univ : Finset α).powersetCard 2,
    (graphCommonMultiplicityAtPair F P - 1)

private theorem unordered_common_excess_scalar (m : ℕ) :
    m = (m - 1) + if 0 < m then 1 else 0 := by
  cases m with
  | zero => norm_num
  | succ n => simp

/-- Exact finite graph identity `W=q+excess`, with all three terms
using unordered pair normalization. -/
theorem graph_degree_pairs_eq_common_pairs_add_excess
    (F : SimpleGraph α) [DecidableRel F.Adj] :
    (∑ x : α, (F.degree x).choose 2) =
      graphCommonPairCount F + graphUnorderedCommonExcess F := by
  rw [← graph_unordered_common_multiplicity_eq_degree_pairs]
  unfold graphCommonPairCount graphUnorderedCommonExcess
  rw [Finset.card_filter]
  calc
    (∑ P ∈ (Finset.univ : Finset α).powersetCard 2,
      graphCommonMultiplicityAtPair F P) =
        ∑ P ∈ (Finset.univ : Finset α).powersetCard 2,
          ((if 0 < graphCommonMultiplicityAtPair F P then 1 else 0) +
            (graphCommonMultiplicityAtPair F P - 1)) := by
              apply Finset.sum_congr rfl
              intro P _
              simpa only [add_comm] using
                (unordered_common_excess_scalar
                  (graphCommonMultiplicityAtPair F P))
    _ = _ := by rw [Finset.sum_add_distrib]

end JSP523.Rank4
