import JSP523.Rank4.GraphCanonicalActualUniqueFamily

/-!
# Actual colored-facet payment

The selected pair-link potentials pay the canonical colored-facet
records and full-degree marks in the form needed after (III.B.9).
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Equations (III.B.10) and (III.B.11) for the actual selected
pair-link family, with the record and mark correspondences exposed as
finite combinatorial premises. -/
theorem actual_colored_facet_family_payment
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : FiniteCompletionCliqueData α) (C : Finset ι)
    (d : ι → ℕ) (k : ι → CliqueColor → ℕ)
    (hd : ∀ t ∈ C, d t = 3 ∨ d t = 4)
    (hk : ∀ t ∈ C, ∀ x : CliqueColor, k t x ≤ d t)
    (hRecords :
      (∑ t ∈ C, (coloredFacetRecords (d t) -
        ∑ x : CliqueColor, coloredSlotLoss (d t) (k t x))) ≤
      ((actualUniquePairRecordKeys D).card : ℚ))
    (hMarks :
      (∑ t ∈ C, ∑ x : CliqueColor,
        coloredSlotMark (d t) (k t x)) ≤
      (∑ Q ∈ D.ground.powersetCard 2,
        ((actualColoredMarkedThreeSlots D Q).card : ℚ)) / 2 +
      (∑ Q ∈ D.ground.powersetCard 2,
        ((actualColoredMarkedFourSlots D Q).card : ℚ))) :
    (∑ t ∈ C, coloredFacetRecords (d t)) ≤
      actualSelectedPotentialTotal D +
        (∑ t ∈ C, ∑ x : CliqueColor,
          slotSlack (d t) (k t x)) / 2 := by
  have hFacet := colored_family_payment C d k
    ((actualUniquePairRecordKeys D).card : ℚ) hd hk hRecords
  have hGraph := actual_colored_unique_record_payment D
  linarith

end JSP523.Rank4
