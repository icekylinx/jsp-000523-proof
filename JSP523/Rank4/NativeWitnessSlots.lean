import JSP523.Rank4.NativeSelectedLedger

/-!
# Pair-label witness slots

A nonprivate pair-link slot is witnessed by two actual completions whose
common-root label lies in the base pair. These witnesses select every
native neighbor and, when native degree is at least two, both pair-link
endpoints. This is the local eligibility mechanism in (III.B.8).
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
/-- A raw common neighbor at a base pair gives an actual common triple
in the cell of the two pair-link endpoints. -/
theorem raw_pair_common_neighbor_gives_cell
    (K : Family α) (U Q : Edge α)
    (hUniform : Uniform 4 K)
    (hQ : Q ∈ U.powersetCard 2)
    (a b x : α)
    (haU : a ∈ U) (hbU : b ∈ U) (hab : a ≠ b)
    (hax : (rawPairLinkGraph K U Q).Adj a x)
    (hbx : (rawPairLinkGraph K U Q).Adj b x) :
    insert x Q ∈ commonRootCell K U ({a, b} : Edge α) := by
  classical
  let P : Edge α := {a, b}
  let T : Edge α := insert x Q
  have hP : P ∈ U.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, Finset.card_pair hab⟩
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact haU
    · exact (Finset.mem_singleton.mp ht) ▸ hbU
  have hax' := (rawPairLinkGraph_adj K U Q a x).mp hax
  have hbx' := (rawPairLinkGraph_adj K U Q b x).mp hbx
  obtain ⟨_, hxQ, _, hxU, _, hEa⟩ := hax'
  obtain ⟨_, _, _, _, _, hEb⟩ := hbx'
  have hQ' := Finset.mem_powersetCard.mp hQ
  have hT : T ∈ U.powersetCard 3 := by
    apply Finset.mem_powersetCard.mpr
    exact ⟨Finset.insert_subset hxU hQ'.1,
      by rw [Finset.card_insert_of_notMem hxQ, hQ'.2]⟩
  have hSub : P ⊆ facetCompletions K U T := by
    intro t ht
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨haU, hEa⟩
    · exact Finset.mem_filter.mpr ⟨hbU, hEb⟩
  exact (common_root_cell_iff_pair_of_facet_completions
    K U P T hUniform hP hT).2 hSub

/-- Two different common neighbors at Q force the chosen label of the
completion pair into Q. Otherwise the off-label multiplicity bound
would make those neighbors equal. -/
theorem raw_pair_two_common_neighbors_force_label_in_base
    (K : Family α) (U Q : Edge α) (fallback : α)
    (hUniform : Uniform 4 K)
    (hCenters : UniqueCommonRootCenters K U)
    (hQ : Q ∈ U.powersetCard 2)
    (a b x y : α)
    (haU : a ∈ U) (hbU : b ∈ U) (hab : a ≠ b)
    (hax : (rawPairLinkGraph K U Q).Adj a x)
    (hbx : (rawPairLinkGraph K U Q).Adj b x)
    (hay : (rawPairLinkGraph K U Q).Adj a y)
    (hby : (rawPairLinkGraph K U Q).Adj b y)
    (hxy : x ≠ y) :
    chosenCommonRootLabel K U fallback hCenters
      ({a, b} : Edge α) ∈ Q := by
  classical
  let F := rawPairLinkGraph K U Q
  let P : Edge α := {a, b}
  have hP : P ∈ U.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, Finset.card_pair hab⟩
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact haU
    · exact (Finset.mem_singleton.mp ht) ▸ hbU
  have hCell := raw_pair_common_neighbor_gives_cell
    K U Q hUniform hQ a b x haU hbU hab hax hbx
  have hUsed : P ∈ nonemptyCommonRoots K U :=
    Finset.mem_filter.mpr
      ⟨hP, Finset.card_pos.mpr ⟨insert x Q, hCell⟩⟩
  let z := chosenCommonRootLabel K U fallback hCenters P
  by_contra hzQ
  have hCenter : ∀ T ∈ commonRootCell K U P, z ∈ T := by
    intro T hT
    exact chosen_common_root_label_center
      K U fallback hCenters P hUsed T hT
  have hLe : graphCommonMultiplicity F a b ≤ 1 :=
    raw_pair_common_multiplicity_le_one_off_label
      K U Q hUniform hQ a b z haU hbU hab hzQ hCenter
  have hx : x ∈ (F.neighborFinset a).filter (fun t => F.Adj b t) :=
    Finset.mem_filter.mpr
      ⟨by simpa only [SimpleGraph.mem_neighborFinset] using hax, hbx⟩
  have hy : y ∈ (F.neighborFinset a).filter (fun t => F.Adj b t) :=
    Finset.mem_filter.mpr
      ⟨by simpa only [SimpleGraph.mem_neighborFinset] using hay, hby⟩
  exact hxy ((Finset.card_le_one.mp hLe) x hx y hy)

/-- The actual witness selection at a base pair Q. A selected vertex
has two actual completion neighbors whose pair label belongs to Q. -/
noncomputable def pairLabelWitnessSlots
    (K : Family α) (U Q : Edge α) (fallback : α)
    (hCenters : UniqueCommonRootCenters K U) : Finset α :=
  U.filter fun x =>
    ∃ a b : α, a ≠ b ∧
      (rawPairLinkGraph K U Q).Adj x a ∧
      (rawPairLinkGraph K U Q).Adj x b ∧
      chosenCommonRootLabel K U fallback hCenters
        ({a, b} : Edge α) ∈ Q

theorem pair_label_witness_slots_mem
    (K : Family α) (U Q : Edge α) (fallback : α)
    (hCenters : UniqueCommonRootCenters K U)
    (x : α) :
    x ∈ pairLabelWitnessSlots K U Q fallback hCenters ↔
      x ∈ U ∧ ∃ a b : α, a ≠ b ∧
        (rawPairLinkGraph K U Q).Adj x a ∧
        (rawPairLinkGraph K U Q).Adj x b ∧
        chosenCommonRootLabel K U fallback hCenters
          ({a, b} : Edge α) ∈ Q := by
  classical
  simp only [pairLabelWitnessSlots, Finset.mem_filter]

/-- At a native vertex of degree at least two, the actual pair-label
witness rule selects both completion endpoints and every common
neighbor in the corresponding pair link. -/
theorem native_high_degree_witness_slots_saturate
    (K : Family α) (U : Edge α) (fallback : α)
    (hUniform : Uniform 4 K)
    (hCenters : UniqueCommonRootCenters K U)
    (a b z w : α)
    (haU : a ∈ U) (hbU : b ∈ U)
    (hzU : z ∈ U) (hwU : w ∈ U)
    (hab : a ≠ b) (hzw : z ≠ w)
    (haQ : a ∉ ({z, w} : Edge α))
    (hbQ : b ∉ ({z, w} : Edge α))
    (hLabel : chosenCommonRootLabel K U fallback hCenters
      ({a, b} : Edge α) = z)
    (hHigh : 2 ≤
      (nativeTailGraph K U ({a, b} : Edge α) z).degree w) :
    let Q : Edge α := {z, w}
    let S := pairLabelWitnessSlots K U Q fallback hCenters
    a ∈ S ∧ b ∈ S ∧
      ∀ x,
        (rawPairLinkGraph K U Q).Adj a x →
        (rawPairLinkGraph K U Q).Adj b x → x ∈ S := by
  classical
  dsimp
  let Q : Edge α := {z, w}
  let S := pairLabelWitnessSlots K U Q fallback hCenters
  let F := rawPairLinkGraph K U Q
  let G := nativeTailGraph K U ({a, b} : Edge α) z
  have hQ : Q ∈ U.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, Finset.card_pair hzw⟩
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hzU
    · exact (Finset.mem_singleton.mp ht) ▸ hwU
  have hzQ : z ∈ Q := by simp [Q]
  have hCommonSelected (x : α) (hax : F.Adj a x)
      (hbx : F.Adj b x) : x ∈ S := by
    have hxU : x ∈ U :=
      ((rawPairLinkGraph_adj K U Q a x).mp hax).2.2.2.1
    exact (pair_label_witness_slots_mem K U Q fallback hCenters x).2
      ⟨hxU, a, b, hab, hax.symm, hbx.symm, by
        simpa only [hLabel] using hzQ⟩
  have hTwo : 1 < (G.neighborFinset w).card := hHigh
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hTwo
  have hGx : G.Adj w x := by
    simpa only [SimpleGraph.mem_neighborFinset] using hx
  have hGy : G.Adj w y := by
    simpa only [SimpleGraph.mem_neighborFinset] using hy
  have hCommonX : F.Adj a x ∧ F.Adj b x := by
    exact (raw_pair_common_neighbor_iff_native_neighbor
      K U hUniform a b z w x haU hbU hzU hwU
      hab hzw haQ hbQ).2 hGx
  have hCommonY : F.Adj a y ∧ F.Adj b y := by
    exact (raw_pair_common_neighbor_iff_native_neighbor
      K U hUniform a b z w y haU hbU hzU hwU
      hab hzw haQ hbQ).2 hGy
  have hxU : x ∈ U :=
    ((rawPairLinkGraph_adj K U Q a x).mp hCommonX.1).2.2.2.1
  have hyU : y ∈ U :=
    ((rawPairLinkGraph_adj K U Q a y).mp hCommonY.1).2.2.2.1
  have hxyLabel : chosenCommonRootLabel K U fallback hCenters
      ({x, y} : Edge α) ∈ Q :=
    raw_pair_two_common_neighbors_force_label_in_base
      K U Q fallback hUniform hCenters hQ x y a b
      hxU hyU hxy hCommonX.1.symm hCommonY.1.symm
      hCommonX.2.symm hCommonY.2.symm hab
  have haS : a ∈ S :=
    (pair_label_witness_slots_mem K U Q fallback hCenters a).2
      ⟨haU, x, y, hxy, hCommonX.1, hCommonY.1, hxyLabel⟩
  have hbS : b ∈ S :=
    (pair_label_witness_slots_mem K U Q fallback hCenters b).2
      ⟨hbU, x, y, hxy, hCommonX.2, hCommonY.2, hxyLabel⟩
  exact ⟨haS, hbS, hCommonSelected⟩

/-- The witness selection gives the exact local positive-excess identity
for every used completion pair and every on-label native vertex. -/
theorem witness_selected_pair_common_excess_eq_native_excess
    (K : Family α) (U : Edge α) (fallback : α)
    (hUniform : Uniform 4 K)
    (hCenters : UniqueCommonRootCenters K U)
    (a b z w : α)
    (haU : a ∈ U) (hbU : b ∈ U)
    (hzU : z ∈ U) (hwU : w ∈ U)
    (hab : a ≠ b) (hzw : z ≠ w)
    (haQ : a ∉ ({z, w} : Edge α))
    (hbQ : b ∉ ({z, w} : Edge α))
    (hLabel : chosenCommonRootLabel K U fallback hCenters
      ({a, b} : Edge α) = z) :
    let Q : Edge α := {z, w}
    graphCommonMultiplicity
        (selectedRawPairLinkGraph K U Q
          (pairLabelWitnessSlots K U Q fallback hCenters)) a b - 1 =
      (nativeTailGraph K U ({a, b} : Edge α) z).degree w - 1 := by
  dsimp
  apply selected_raw_pair_common_excess_eq_native_excess
    K U (pairLabelWitnessSlots K U ({z, w} : Edge α)
      fallback hCenters) hUniform a b z w
    haU hbU hzU hwU hab hzw haQ hbQ
  intro hHigh
  exact native_high_degree_witness_slots_saturate
    K U fallback hUniform hCenters a b z w
    haU hbU hzU hwU hab hzw haQ hbQ hLabel hHigh

end JSP523.Rank4
