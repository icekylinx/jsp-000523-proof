import JSP523.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# The finite rank-three support ledger

The mathematical proof defines `m` as its number of triples, `s` as the number
of used pairs, `t` as the number of used completion pairs, and `cSum` as the
sum of all common-cell sizes.  `L` and `B` are the two surplus budgets; `k₁`,
`b₁`, and `b₂` count the small-degree exceptions.

This module formalizes the exact algebra once the two finite incidence counts
are supplied.  The incidence counts and the structural payment inequality are
still mathematical inputs, not silently assumed theorems about a hypergraph.
-/

namespace JSP523.Rank3

/-- Exact support ledger, with all variables integral and no division by two. -/
theorem support_ledger
    (m s t cSum L B k₁ b₁ b₂ : ℤ)
    (hdegree : 2 * cSum - B = 12 * m - 6 * s + 2 * k₁)
    (hcell : L = cSum - 3 * t + 2 * b₁ + b₂) :
    6 * (2 * m - s - t) = 2 * L - B - 2 * k₁ - 4 * b₁ - 2 * b₂ := by
  linarith

/-- The global payment inequality is precisely the remaining input needed
    to make the finite support defect nonpositive. -/
theorem support_defect_nonpos
    (m s t cSum L B k₁ b₁ b₂ : ℤ)
    (hdegree : 2 * cSum - B = 12 * m - 6 * s + 2 * k₁)
    (hcell : L = cSum - 3 * t + 2 * b₁ + b₂)
    (hpaid : 2 * L ≤ B + 2 * k₁ + 4 * b₁ + 2 * b₂) :
    2 * m ≤ s + t := by
  have hledger := support_ledger m s t cSum L B k₁ b₁ b₂ hdegree hcell
  linarith

/-- Both supports lie among the unordered ground pairs.  Once the support
    defect is nonpositive, the rank-three ambient upper bound follows. -/
theorem edge_count_le_ground_pairs
    (m s t groundPairs : ℕ)
    (hdefect : 2 * m ≤ s + t)
    (hs : s ≤ groundPairs) (ht : t ≤ groundPairs) :
    m ≤ groundPairs := by
  omega

/-- The finite rank-three extremal upper bound from the actual two supports.
    A future module must construct these supports and prove `hSupport` from
    admissibility; no such combinatorial claim is hidden in this theorem. -/
theorem triple_family_card_le_choose_two
    {α : Type*} [DecidableEq α]
    (H : Family α) (V : Finset α)
    (usedPairs usedCells : Family α)
    (hPairs : usedPairs ⊆ V.powersetCard 2)
    (hCells : usedCells ⊆ V.powersetCard 2)
    (hSupport : 2 * H.card ≤ usedPairs.card + usedCells.card) :
    H.card ≤ V.card.choose 2 := by
  have hcard : (V.powersetCard 2).card = V.card.choose 2 :=
    Finset.card_powersetCard 2 V
  have hp : usedPairs.card ≤ V.card.choose 2 :=
    (Finset.card_le_card hPairs).trans (le_of_eq hcard)
  have hc : usedCells.card ≤ V.card.choose 2 :=
    (Finset.card_le_card hCells).trans (le_of_eq hcard)
  exact edge_count_le_ground_pairs H.card usedPairs.card usedCells.card
    (V.card.choose 2) hSupport hp hc

end JSP523.Rank3
