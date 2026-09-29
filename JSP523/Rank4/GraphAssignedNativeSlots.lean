import JSP523.Rank4.GraphAssignedNativeCenters

/-! # Actual slot eligibility with the given completion centers -/

namespace JSP523.Rank4.AssignedNative

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
theorem actual_pair_label_eq_chosen_center
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (a b : α) (hab : a ≠ b)
    (_hUsed : ({a, b} : Edge α) ∈ nonemptyCommonRoots D.K D.ground) :
    D.label a b = dataRootLabel D fallback {a, b} :=
  (data_root_label_pair D fallback a b hab).symm

omit [Fintype α] in
/-- The center of two completion neighbors at a selected base pair is
the same in the finite completion data and in the canonical root-cell
label function. -/
theorem raw_common_pair_data_label_eq_chosen
    (D : FiniteCompletionCliqueData α)
    (Q : Edge α) (hQ : Q ∈ D.ground.powersetCard 2)
    (fallback : α)
    (p q x : α)
    (hpU : p ∈ D.ground) (hqU : q ∈ D.ground)
    (hpq : p ≠ q)
    (hpx : (rawPairLinkGraph D.K D.ground Q).Adj p x)
    (hqx : (rawPairLinkGraph D.K D.ground Q).Adj q x) :
    D.label p q =
      dataRootLabel D fallback
        ({p, q} : Edge α) := by
  classical
  let P : Edge α := {p, q}
  have hCell := raw_pair_common_neighbor_gives_cell
    D.K D.ground Q D.uniform_four hQ p q x hpU hqU hpq hpx hqx
  have hP : P ∈ D.ground.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, Finset.card_pair hpq⟩
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hpU
    · exact (Finset.mem_singleton.mp ht) ▸ hqU
  have hUsed : P ∈ nonemptyCommonRoots D.K D.ground :=
    Finset.mem_filter.mpr
      ⟨hP, Finset.card_pos.mpr ⟨insert x Q, hCell⟩⟩
  exact actual_pair_label_eq_chosen_center
    D fallback p q hpq hUsed

/-- Under the actual centered completion data, the manuscript's
colored-or-monochromatic selected vertex set is exactly the pair-label
witness set. -/
theorem actual_eligible_pair_slot_vertices_eq_witness_slots
    (D : FiniteCompletionCliqueData α)
    (Q : Edge α) (hQ : Q ∈ D.ground.powersetCard 2)
    (fallback : α) :
    actualEligiblePairSlotVertices D Q =
      pairLabelWitnessSlots D.K D.ground Q fallback (dataCenterAssignment D fallback) := by
  classical
  ext x
  let C := graphFacetCompletions D.K D.ground (insert x Q)
  have hQ' := Finset.mem_powersetCard.mp hQ
  constructor
  · intro hxActual
    have hxParts : x ∈ D.ground ∧ x ∉ Q ∧
        FacetEligibleAtPair C D.label Q := by
      simpa only [actualEligiblePairSlotVertices,
        Finset.mem_filter] using hxActual
    obtain ⟨hxU, hxQ, hEligible⟩ := hxParts
    have hTcard : (insert x Q).card = 3 := by
      rw [Finset.card_insert_of_notMem hxQ, hQ'.2]
    have hTsub : insert x Q ⊆ D.ground :=
      Finset.insert_subset hxU hQ'.1
    have hLabelFacet : ∀ a ∈ C, ∀ b ∈ C,
        a ≠ b → D.label a b ∈ insert x Q := by
      intro a ha b hb hab
      exact completion_pair_label_mem_facet D (insert x Q)
        hTcard hTsub a b ha hb hab
    obtain ⟨p, hp, q, hq, hpq, hLabelQ⟩ :=
      facet_eligible_implies_witness C D.label Q x
        hLabelFacet hEligible
    have hxp : (rawPairLinkGraph D.K D.ground Q).Adj x p :=
      (raw_pair_link_slot_adj_iff_facet_completion
        D Q hQ x p hxU hxQ).2 hp
    have hxq : (rawPairLinkGraph D.K D.ground Q).Adj x q :=
      (raw_pair_link_slot_adj_iff_facet_completion
        D Q hQ x q hxU hxQ).2 hq
    have hpU : p ∈ D.ground := (Finset.mem_filter.mp hp).1
    have hqU : q ∈ D.ground := (Finset.mem_filter.mp hq).1
    have hLabelEq := raw_common_pair_data_label_eq_chosen
      D Q hQ fallback p q x hpU hqU hpq
      hxp.symm hxq.symm
    exact (pair_label_witness_slots_mem
      D.K D.ground Q fallback (dataCenterAssignment D fallback) x).2
      ⟨hxU, p, q, hpq, hxp, hxq, by
        change dataRootLabel D fallback {p, q} ∈ Q
        rw [← hLabelEq]
        exact hLabelQ⟩
  · intro hxWitness
    obtain ⟨hxU, p, q, hpq, hxp, hxq, hChosenQ⟩ :=
      (pair_label_witness_slots_mem
        D.K D.ground Q fallback (dataCenterAssignment D fallback) x).mp hxWitness
    have hxQ : x ∉ Q :=
      ((rawPairLinkGraph_adj D.K D.ground Q x p).mp hxp).1
    have hp : p ∈ C :=
      (raw_pair_link_slot_adj_iff_facet_completion
        D Q hQ x p hxU hxQ).1 hxp
    have hq : q ∈ C :=
      (raw_pair_link_slot_adj_iff_facet_completion
        D Q hQ x q hxU hxQ).1 hxq
    have hpU : p ∈ D.ground := (Finset.mem_filter.mp hp).1
    have hqU : q ∈ D.ground := (Finset.mem_filter.mp hq).1
    have hLabelEq := raw_common_pair_data_label_eq_chosen
      D Q hQ fallback p q x hpU hqU hpq
      hxp.symm hxq.symm
    have hLabelQ : D.label p q ∈ Q := hLabelEq ▸ hChosenQ
    have hEligible := facet_witness_implies_eligible
      C D.label Q D.label_symm p q hp hq hpq hLabelQ
    change x ∈ D.ground.filter fun y => y ∉ Q ∧
      FacetEligibleAtPair
        (graphFacetCompletions D.K D.ground (insert y Q))
        D.label Q
    exact Finset.mem_filter.mpr ⟨hxU, hxQ, hEligible⟩

/-- The selected graph formed with the manuscript's actual eligibility
rule is the witness-selected ordinary pair link. -/
theorem actual_eligible_pair_link_eq_witness_link
    (D : FiniteCompletionCliqueData α)
    (Q : Edge α) (hQ : Q ∈ D.ground.powersetCard 2)
    (fallback : α) :
    selectedCompletionPairGraph D (actualEligiblePairSlotVertices D Q) Q =
      selectedRawPairLinkGraph D.K D.ground Q
        (pairLabelWitnessSlots D.K D.ground Q fallback (dataCenterAssignment D fallback)) := by
  rw [actual_eligible_pair_slot_vertices_eq_witness_slots
    D Q hQ fallback]
  rfl

/-- In an actual selected pair link, a used completion pair has no
positive common-neighbor excess at a base pair omitting its label. -/
theorem actual_eligible_pair_common_le_one_off_label
    (D : FiniteCompletionCliqueData α)
    (Q : Edge α) (hQ : Q ∈ D.ground.powersetCard 2)
    (fallback : α)
    (a b : α) (haU : a ∈ D.ground) (hbU : b ∈ D.ground)
    (hab : a ≠ b)
    (hUsed : ({a, b} : Edge α) ∈
      nonemptyCommonRoots D.K D.ground)
    (hzQ : dataRootLabel D fallback
      ({a, b} : Edge α) ∉ Q) :
    graphCommonMultiplicity
      (selectedCompletionPairGraph D
        (actualEligiblePairSlotVertices D Q) Q) a b ≤ 1 := by
  have hGraphEq := actual_eligible_pair_link_eq_witness_link
    D Q hQ fallback
  have hMultiplicity := graph_common_multiplicity_congr
    (selectedCompletionPairGraph D
      (actualEligiblePairSlotVertices D Q) Q)
    (selectedRawPairLinkGraph D.K D.ground Q
      (pairLabelWitnessSlots D.K D.ground Q fallback (dataCenterAssignment D fallback)))
    (by intro x y; rw [hGraphEq]) a b
  rw [hMultiplicity]
  exact selected_raw_pair_common_multiplicity_le_one_off_label
    D.K D.ground Q
    (pairLabelWitnessSlots D.K D.ground Q fallback (dataCenterAssignment D fallback))
    D.uniform_four hQ a b
    (dataRootLabel D fallback
      ({a, b} : Edge α))
    haU hbU hab hzQ
    (fun T hT => data_root_label_center
      D fallback
      ({a, b} : Edge α) hUsed T hT)

/-- At every on-label base pair, the manuscript's actual selected
pair-link excess equals the native vertex degree excess. -/
theorem actual_eligible_pair_common_excess_eq_native_excess
    (D : FiniteCompletionCliqueData α)
    (fallback : α)
    (a b w : α)
    (haU : a ∈ D.ground) (hbU : b ∈ D.ground)
    (hwU : w ∈ D.ground)
    (hab : a ≠ b)
    (hUsed : ({a, b} : Edge α) ∈
      nonemptyCommonRoots D.K D.ground)
    (hzw : dataRootLabel D fallback
      ({a, b} : Edge α) ≠ w)
    (haQ : a ∉ ({dataRootLabel D fallback
      ({a, b} : Edge α), w} : Edge α))
    (hbQ : b ∉ ({dataRootLabel D fallback
      ({a, b} : Edge α), w} : Edge α)) :
    let z := dataRootLabel D fallback
      ({a, b} : Edge α)
    let Q : Edge α := {z, w}
    graphCommonMultiplicity
        (selectedCompletionPairGraph D
          (actualEligiblePairSlotVertices D Q) Q) a b - 1 =
      (nativeTailGraph D.K D.ground ({a, b} : Edge α) z).degree w - 1 := by
  dsimp
  let z := dataRootLabel D fallback
    ({a, b} : Edge α)
  let Q : Edge α := {z, w}
  have hzU : z ∈ D.ground :=
    (data_root_label_valid D fallback ({a, b} : Edge α) hUsed).1
  have hQ : Q ∈ D.ground.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, Finset.card_pair hzw⟩
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hzU
    · exact (Finset.mem_singleton.mp ht) ▸ hwU
  have hGraphEq := actual_eligible_pair_link_eq_witness_link
    D Q hQ fallback
  have hMultiplicity := graph_common_multiplicity_congr
    (selectedCompletionPairGraph D
      (actualEligiblePairSlotVertices D Q) Q)
    (selectedRawPairLinkGraph D.K D.ground Q
      (pairLabelWitnessSlots D.K D.ground Q fallback (dataCenterAssignment D fallback)))
    (by intro x y; rw [hGraphEq]) a b
  rw [hMultiplicity]
  exact witness_selected_pair_common_excess_eq_native_excess
    D.K D.ground fallback D.uniform_four (dataCenterAssignment D fallback)
    a b z w haU hbU hzU hwU hab hzw haQ hbQ rfl

end JSP523.Rank4.AssignedNative
