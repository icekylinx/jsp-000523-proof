import JSP523.Rank4.GraphMarkedCapacity

/-!
# Summed payment for colored rank-four facets

This packages the nine scalar slot cases of equation (III.B.11) into the
finite sum used after the marked graph inequality (III.B.10).  The record
lower bound is kept as an explicit premise: constructing those records
from actual colored facets remains a separate combinatorial task.
-/

namespace JSP523.Rank4

/-- Records a colored facet can lose at one selected slot. -/
def coloredSlotLoss (d k : ℕ) : ℚ :=
  if d = 3 then rainbowRecordLoss k else properFourRecordLoss k

/-- Extra graph credit when a colored slot is fully selected. -/
def coloredSlotMark (d k : ℕ) : ℚ :=
  if d = 3 then (if k = 3 then 1 / 2 else 0)
  else (if k = 4 then 1 else 0)

/-- Three selected slots of a rainbow facet generate three records;
those of a proper four facet generate six. -/
def coloredFacetRecords (d : ℕ) : ℚ := if d = 3 then 3 else 6

theorem colored_slot_payment
    (d k : ℕ) (hd : d = 3 ∨ d = 4) (hk : k ≤ d) :
    coloredFacetRecords d / 6 + coloredSlotLoss d k / 2 ≤
      slotSlack d k / 2 + coloredSlotMark d k := by
  rcases hd with rfl | rfl
  · have h := rainbow_slot_payment k hk
    dsimp [coloredFacetRecords, coloredSlotLoss, coloredSlotMark]
    norm_num at *
    linarith
  · have h := proper_four_slot_payment k hk
    dsimp [coloredFacetRecords, coloredSlotLoss, coloredSlotMark]
    norm_num at *
    linarith

/-- Sum equation (III.B.11) over the three color slots of one facet. -/
theorem colored_facet_payment
    (d : ℕ) (k : Fin 3 → ℕ)
    (hd : d = 3 ∨ d = 4) (hk : ∀ z, k z ≤ d) :
    coloredFacetRecords d / 2 +
        (∑ z : Fin 3, coloredSlotLoss d (k z)) / 2 ≤
      (∑ z : Fin 3, slotSlack d (k z)) / 2 +
        ∑ z : Fin 3, coloredSlotMark d (k z) := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3)))
    (fun z _ => colored_slot_payment d (k z) hd (hk z))
  simp_rw [Finset.sum_add_distrib, ← Finset.sum_div] at h
  have hConst :
      (∑ _z : Fin 3, coloredFacetRecords d) / 6 =
        coloredFacetRecords d / 2 := by
    simp [Finset.sum_const, Fintype.card_fin]
    ring
  rw [hConst] at h
  exact h

/-- The numerical colored payment following (10): a lower bound on the
number of surviving unique-pair records, together with the slot slack
and full-selection marks, pays the complete colored-facet target. -/
theorem colored_family_payment
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Finset ι) (d : ι → ℕ) (k : ι → Fin 3 → ℕ) (U : ℚ)
    (hd : ∀ t ∈ C, d t = 3 ∨ d t = 4)
    (hk : ∀ t ∈ C, ∀ z, k t z ≤ d t)
    (hRecords :
      (∑ t ∈ C, (coloredFacetRecords (d t) -
        ∑ z : Fin 3, coloredSlotLoss (d t) (k t z))) ≤ U) :
    (∑ t ∈ C, coloredFacetRecords (d t)) ≤
      U / 2 +
      (∑ t ∈ C, ∑ z : Fin 3, slotSlack (d t) (k t z)) / 2 +
      (∑ t ∈ C, ∑ z : Fin 3, coloredSlotMark (d t) (k t z)) := by
  have hSlots := Finset.sum_le_sum (s := C)
    (fun t ht => colored_facet_payment (d t) (k t)
      (hd t ht) (hk t ht))
  simp_rw [Finset.sum_add_distrib, ← Finset.sum_div] at hSlots
  simp_rw [Finset.sum_sub_distrib] at hRecords
  linarith

/-- Equations (10) and (11) combined across selected pair-link graphs.
The hypotheses record the two remaining combinatorial interfaces:
surviving unique-pair records and the correspondence between fully
selected colored slots and marked graph vertices. -/
theorem graph_family_colored_payment
    {α β τ : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [Fintype τ] [DecidableEq τ]
    (F : β → SimpleGraph α) [∀ i, DecidableRel (F i).Adj]
    (M3 M4 : β → Finset α)
    (hDisj : ∀ i, Disjoint (M3 i) (M4 i))
    (h3 : ∀ i, ∀ x ∈ M3 i, (F i).degree x = 3 ∧
      ∀ y : α, y ≠ x → graphCommonMultiplicity (F i) x y ≤ 2)
    (h4 : ∀ i, ∀ x ∈ M4 i, (F i).degree x = 4 ∧
      ∀ y : α, y ≠ x → graphCommonMultiplicity (F i) x y ≤ 2)
    (C : Finset τ) (d : τ → ℕ) (k : τ → Fin 3 → ℕ)
    (hd : ∀ t ∈ C, d t = 3 ∨ d t = 4)
    (hk : ∀ t ∈ C, ∀ z, k t z ≤ d t)
    (hRecords :
      (∑ t ∈ C, (coloredFacetRecords (d t) -
        ∑ z : Fin 3, coloredSlotLoss (d t) (k t z))) ≤
      ∑ i : β, orderedUniquePairCount (F i) / 2)
    (hMarks :
      (∑ t ∈ C, ∑ z : Fin 3, coloredSlotMark (d t) (k t z)) =
      ∑ i : β, (((M3 i).card : ℚ) / 2 + ((M4 i).card : ℚ))) :
    (∑ t ∈ C, coloredFacetRecords (d t)) ≤
      (∑ i : β, graphDeficit (F i)) +
      (∑ t ∈ C, ∑ z : Fin 3, slotSlack (d t) (k t z)) / 2 := by
  have hGraph := Finset.sum_le_sum (s := (Finset.univ : Finset β))
    (fun i _ => graphDeficit_marked (F i) (M3 i) (M4 i)
      (hDisj i) (h3 i) (h4 i))
  have hColor := colored_family_payment C d k
    (∑ i : β, orderedUniquePairCount (F i) / 2)
    hd hk hRecords
  simp_rw [Finset.sum_add_distrib, ← Finset.sum_div] at hGraph
  rw [hMarks] at hColor
  have hMarkSum :
      (∑ i : β, (((M3 i).card : ℚ) / 2 + ((M4 i).card : ℚ))) =
      (∑ i : β, ((M3 i).card : ℚ)) / 2 +
      ∑ i : β, ((M4 i).card : ℚ) := by
    rw [Finset.sum_add_distrib, Finset.sum_div]
  rw [hMarkSum] at hColor
  have hUnique :
      (∑ i : β, orderedUniquePairCount (F i) / 2) / 2 =
      (∑ i : β, orderedUniquePairCount (F i)) / 4 := by
    conv_lhs => rw [Finset.sum_div]
    conv_rhs => rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hUnique] at hColor
  linarith

end JSP523.Rank4
