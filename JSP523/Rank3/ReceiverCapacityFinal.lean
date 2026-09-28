import JSP523.Rank3.ReceiverOrdinaryGlobal
import JSP523.Rank3.ReciprocalUsedCell
import JSP523.Rank3.GlobalSourceLedger

/-!
# Final finite receiver-capacity sum

The double receiver cells split into reciprocal pairs with two cores on
both sides and a complement whose reciprocal has at least three cores.
The first class is controlled by pairwise capacity; ordinary members of the
second class have pointwise capacity two, while triangle exceptions spend Xi.
-/

namespace JSP523.Rank3

variable {α : Type*} [DecidableEq α]

/-- Double receiver cells whose reciprocal is not another double cell. -/
noncomputable def reciprocalNonregularDoubleCells
    (H : Family α) (V : Edge α) : Family α := by
  classical
  exact (doubleLinkCells H V).filter
    (fun q => reciprocalCellMap H V q ∉ doubleLinkCells H V)

theorem reciprocal_nonregular_double_cells_subset
    (H : Family α) (V : Edge α) :
    reciprocalNonregularDoubleCells H V ⊆ doubleLinkCells H V := by
  intro q hq
  exact (Finset.mem_filter.mp hq).1

/-- Finite partition of c=2 cells into the reciprocal-paired and
nonregular classes. -/
theorem double_cell_charge_sum_regular_nonregular
    (H : Family α) (V : Edge α) :
    (∑ q ∈ doubleLinkCells H V, actualCellChargeForPair H V q) =
      (∑ q ∈ reciprocalRegularDoubleCells H V,
        actualCellChargeForPair H V q) +
      (∑ q ∈ reciprocalNonregularDoubleCells H V,
        actualCellChargeForPair H V q) := by
  classical
  simpa only [reciprocalRegularDoubleCells,
    reciprocalNonregularDoubleCells] using
    (Finset.sum_filter_add_sum_filter_not
      (doubleLinkCells H V)
      (fun q => reciprocalCellMap H V q ∈ doubleLinkCells H V)
      (actualCellChargeForPair H V)).symm

theorem double_cell_card_regular_nonregular
    (H : Family α) (V : Edge α) :
    (doubleLinkCells H V).card =
      (reciprocalRegularDoubleCells H V).card +
      (reciprocalNonregularDoubleCells H V).card := by
  classical
  simpa only [reciprocalRegularDoubleCells,
    reciprocalNonregularDoubleCells] using
    ((doubleLinkCells H V).card_filter_add_card_filter_not
      (fun q => reciprocalCellMap H V q ∈ doubleLinkCells H V)).symm

/-- A c=2 cell outside the reciprocal-paired class has a reciprocal with
at least three cores. -/
theorem reciprocal_nonregular_card_ge_three
    {H : Family α} {V : Edge α} (hH : Admissible H)
    {q : Edge α} (hq : q ∈ reciprocalNonregularDoubleCells H V) :
    3 ≤ (commonLink H V (reciprocalCellMap H V q)).card := by
  have hdouble := (Finset.mem_filter.mp hq).1
  have hnotDouble := (Finset.mem_filter.mp hq).2
  have htwo := reciprocal_cell_map_card_ge_two_of_double hH hdouble
  have hused := reciprocal_cell_map_mem_used_cells_of_double hH hdouble
  have hnotTwo : (commonLink H V (reciprocalCellMap H V q)).card ≠ 2 := by
    intro hcard
    exact hnotDouble (Finset.mem_filter.mpr ⟨hused, hcard⟩)
  omega

/-- The nonregular c=2 cells cost two each plus the exceptional excess
already recorded in the actual Xi ledger. -/
theorem nonregular_double_cell_sum_le_two_card_add_xi
    (H : Family α) (V : Edge α) (hH : Admissible H)
    (hLarge : ∀ q ∈ reciprocalNonregularDoubleCells H V,
      3 ≤ (commonLink H V (reciprocalCellMap H V q)).card) :
    (∑ q ∈ reciprocalNonregularDoubleCells H V,
      actualCellChargeForPair H V q) ≤
      2 * ((reciprocalNonregularDoubleCells H V).card : ℚ) +
        actualXi H V := by
  classical
  let N := reciprocalNonregularDoubleCells H V
  have hPoint (q : Edge α) (hq : q ∈ N) :
      actualCellChargeForPair H V q ≤
        2 + actualTriangleExcess H V q := by
    apply actual_double_cell_charge_le_two_add_excess
    intro hordinary
    have hdouble := reciprocal_nonregular_double_cells_subset H V hq
    exact ordinary_double_cell_large_reciprocal_le_two
      hH hdouble (hLarge q hq) hordinary
  have hSum : (∑ q ∈ N, actualCellChargeForPair H V q) ≤
      2 * (N.card : ℚ) + ∑ q ∈ N, actualTriangleExcess H V q := by
    calc
      (∑ q ∈ N, actualCellChargeForPair H V q) ≤
          ∑ q ∈ N, (2 + actualTriangleExcess H V q) := by
        apply Finset.sum_le_sum
        exact hPoint
      _ = 2 * (N.card : ℚ) + ∑ q ∈ N, actualTriangleExcess H V q := by
        simp [Finset.sum_add_distrib]
        ring
  have hSub : N ⊆ usedCells H V := by
    exact (reciprocal_nonregular_double_cells_subset H V).trans
      (Finset.filter_subset _ _)
  have hExcess : (∑ q ∈ N, actualTriangleExcess H V q) ≤ actualXi H V := by
    rw [actual_xi_eq_sum_triangle_excess]
    exact Finset.sum_le_sum_of_subset_of_nonneg hSub
      (fun q _ _ => actual_triangle_excess_nonneg H V q)
  linarith

/-- The completed finite sum step from local reciprocal geometry to the
incoming-charge estimate of (II.8). -/
theorem incoming_charge_le_capacity_of_reciprocal_bounds
    (H : Family α) (V : Edge α) (hH : Admissible H)
    (hRegular :
      (∑ q ∈ reciprocalRegularDoubleCells H V,
        actualCellChargeForPair H V q) ≤
        2 * ((reciprocalRegularDoubleCells H V).card : ℚ))
    (hLarge : ∀ q ∈ reciprocalNonregularDoubleCells H V,
      3 ≤ (commonLink H V (reciprocalCellMap H V q)).card) :
    incomingCommonLinkChargeTotal H V ≤
      4 * ((singletonLinkCells H V).card : ℚ) +
      2 * ((doubleLinkCells H V).card : ℚ) + actualXi H V := by
  have hPartition := actual_cell_charge_sum_partition H V
  have hIncoming := incoming_charge_eq_cell_charge_sum H V
  have hSingleton := actual_cell_singleton_sum_le H V
  have hZero := actual_cell_threeplus_sum_eq_zero H V hH
  have hDouble := nonregular_double_cell_sum_le_two_card_add_xi
    H V hH hLarge
  have hSplit := double_cell_charge_sum_regular_nonregular H V
  have hCard := double_cell_card_regular_nonregular H V
  rw [hIncoming, hPartition, hSplit, hZero]
  rw [hCard]
  norm_num only [Nat.cast_add]
  linarith

/-- The actual incoming receiver charge satisfies the manuscript's
unconditional receiver-cell capacity inequality (II.8). -/
theorem incoming_charge_le_actual_capacity
    (H : Family α) (V : Edge α) (hH : Admissible H) :
    incomingCommonLinkChargeTotal H V ≤
      4 * ((singletonLinkCells H V).card : ℚ) +
      2 * ((doubleLinkCells H V).card : ℚ) + actualXi H V := by
  exact incoming_charge_le_capacity_of_reciprocal_bounds H V hH
    (actual_regular_double_cell_sum_le_two_card H V hH)
    (fun q hq => reciprocal_nonregular_card_ge_three hH hq)

end JSP523.Rank3
