import JSP523.Rank3.FirstMoment
import Lean.Elab.Tactic.Omega

/-!
# Exact multiplicity ledger for the actual rank-three cells

The second incidence moment counts one common-link incidence per used cell
and places every further incidence into a nonnegative excess.  Splitting
cells with one parent pair from cells with several parent pairs makes this
excess visible as an exact cardinal term and a residual sum.
-/

namespace JSP523.Rank3

section CellDegreeLedger

variable {α : Type*} [DecidableEq α]

/-- Common-link incidences beyond the first at each actually used cell. -/
def cellDegreeExcess (H : Family α) (V : Edge α) : ℕ :=
  (usedCells H V).sum (fun q => (commonLink H V q).card - 1)

/-- The second moment equals the number of used cells plus the count of
    all further common-link incidences. -/
theorem usedCells_incidence_excess_ledger
    (H : Family α) (V : Edge α) :
    (∑ p ∈ V.powersetCard 2,
        (completionVertices H V p).card.choose 2) =
      (usedCells H V).card + cellDegreeExcess H V := by
  have hlocal : ∀ q ∈ usedCells H V,
      (commonLink H V q).card =
        1 + ((commonLink H V q).card - 1) := by
    intro q hq
    have hnon : (commonLink H V q).Nonempty :=
      ((mem_usedCells_iff_commonLink_nonempty H V q).mp hq).2
    have hpos : 0 < (commonLink H V q).card := Finset.card_pos.mpr hnon
    omega
  calc
    (∑ p ∈ V.powersetCard 2,
        (completionVertices H V p).card.choose 2) =
      ∑ q ∈ usedCells H V, (commonLink H V q).card :=
        (usedCells_common_link_double_count H V).symm
    _ = ∑ q ∈ usedCells H V,
          (1 + ((commonLink H V q).card - 1)) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact hlocal q hq
    _ = (usedCells H V).card + cellDegreeExcess H V := by
      simp [cellDegreeExcess, Finset.sum_add_distrib]

/-- Cells with one actual common-link pair. -/
def singletonLinkCells (H : Family α) (V : Edge α) : Family α :=
  (usedCells H V).filter (fun q => (commonLink H V q).card = 1)

/-- Cells with at least two actual common-link pairs. -/
def multipleLinkCells (H : Family α) (V : Edge α) : Family α :=
  (usedCells H V).filter (fun q => 2 ≤ (commonLink H V q).card)

theorem multipleLinkCells_subset_usedCells (H : Family α) (V : Edge α) :
    multipleLinkCells H V ⊆ usedCells H V := by
  intro q hq
  exact (Finset.mem_filter.mp hq).1

/-- The actual used-cell support splits by common-link multiplicity. -/
theorem usedCells_singleton_multiple_union (H : Family α) (V : Edge α) :
    singletonLinkCells H V ∪ multipleLinkCells H V = usedCells H V := by
  ext q
  constructor
  · intro hq
    rcases Finset.mem_union.mp hq with hsingle | hmultiple
    · exact (Finset.mem_filter.mp hsingle).1
    · exact (Finset.mem_filter.mp hmultiple).1
  · intro hq
    have hnon : (commonLink H V q).Nonempty :=
      ((mem_usedCells_iff_commonLink_nonempty H V q).mp hq).2
    have hpos : 0 < (commonLink H V q).card := Finset.card_pos.mpr hnon
    by_cases hone : (commonLink H V q).card = 1
    · exact Finset.mem_union.mpr (Or.inl
        (Finset.mem_filter.mpr ⟨hq, hone⟩))
    · have htwo : 2 ≤ (commonLink H V q).card := by omega
      exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_filter.mpr ⟨hq, htwo⟩))

theorem singleton_multiple_link_cells_disjoint
    (H : Family α) (V : Edge α) :
    Disjoint (singletonLinkCells H V) (multipleLinkCells H V) := by
  apply Finset.disjoint_left.mpr
  intro q hone hmultiple
  have hOne := (Finset.mem_filter.mp hone).2
  have hTwo := (Finset.mem_filter.mp hmultiple).2
  omega

theorem usedCells_singleton_multiple_card_partition
    (H : Family α) (V : Edge α) :
    (usedCells H V).card =
      (singletonLinkCells H V).card +
        (multipleLinkCells H V).card := by
  have hcard := Finset.card_union_of_disjoint
    (singleton_multiple_link_cells_disjoint H V)
  rw [usedCells_singleton_multiple_union H V] at hcard
  exact hcard

/-- A singleton common link has zero excess, so only multiple-link
    cells contribute to `cellDegreeExcess`. -/
theorem cellDegreeExcess_eq_multiple_sum
    (H : Family α) (V : Edge α) :
    cellDegreeExcess H V =
      (multipleLinkCells H V).sum
        (fun q => (commonLink H V q).card - 1) := by
  unfold cellDegreeExcess
  symm
  apply Finset.sum_subset (multipleLinkCells_subset_usedCells H V)
  intro q hq hnot
  have hnon : (commonLink H V q).Nonempty :=
    ((mem_usedCells_iff_commonLink_nonempty H V q).mp hq).2
  have hpos : 0 < (commonLink H V q).card := Finset.card_pos.mpr hnon
  have hlt : ¬ 2 ≤ (commonLink H V q).card := by
    intro htwo
    exact hnot (Finset.mem_filter.mpr ⟨hq, htwo⟩)
  have hone : (commonLink H V q).card = 1 := by omega
  simp [hone]

/-- Multiplicity beyond the second at each multiple-link cell. -/
def repeatedLinkExcess (H : Family α) (V : Edge α) : ℕ :=
  (multipleLinkCells H V).sum (fun q => (commonLink H V q).card - 2)

/-- Exact decomposition of extra cell incidences into one repeat for
    each multiple-link cell and additional repeats after the second. -/
theorem cellDegreeExcess_eq_multiple_card_add_repeated
    (H : Family α) (V : Edge α) :
    cellDegreeExcess H V =
      (multipleLinkCells H V).card + repeatedLinkExcess H V := by
  calc
    cellDegreeExcess H V =
        (multipleLinkCells H V).sum
          (fun q => (commonLink H V q).card - 1) :=
      cellDegreeExcess_eq_multiple_sum H V
    _ = (multipleLinkCells H V).sum
          (fun q => 1 + ((commonLink H V q).card - 2)) := by
      apply Finset.sum_congr rfl
      intro q hq
      have htwo : 2 ≤ (commonLink H V q).card :=
        (Finset.mem_filter.mp hq).2
      omega
    _ = (multipleLinkCells H V).card + repeatedLinkExcess H V := by
      simp [repeatedLinkExcess, Finset.sum_add_distrib]

/-- Three-term version of the actual second moment, with the one-link
    cells separated from repeated incidences. -/
theorem completion_pair_sum_cell_spectrum
    (H : Family α) (V : Edge α) :
    (∑ p ∈ V.powersetCard 2,
        (completionVertices H V p).card.choose 2) =
      (singletonLinkCells H V).card +
        2 * (multipleLinkCells H V).card +
          repeatedLinkExcess H V := by
  have hmoment := usedCells_incidence_excess_ledger H V
  have hpartition := usedCells_singleton_multiple_card_partition H V
  have hexcess := cellDegreeExcess_eq_multiple_card_add_repeated H V
  omega

end CellDegreeLedger

end JSP523.Rank3
