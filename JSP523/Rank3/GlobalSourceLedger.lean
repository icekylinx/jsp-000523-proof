import JSP523.Rank3.ReceiverCapacity
import JSP523.Rank3.LocalPaymentLedger

/-!
# Global source conservation for Part II

This file reconciles the manuscript's unoriented positive weight with the
actual source-pair and receiver-cell sums. The local source conservation is
proved in `ReceiverCapacity`; here we organize the global finite sums.
-/

namespace JSP523.Rank3

variable {α : Type*} [DecidableEq α]

/-- Positive source weight indexed by a genuine unordered core pair. -/
noncomputable def corePositiveWeight
    (H : Family α) (V : Edge α) (z : α) (p : Edge α) : ℚ := by
  classical
  by_cases hp : p.card = 2
  · let e := corePairRep p hp
    exact positiveRootedWeight H V z e.1 e.2
  · exact 0

theorem positive_rooted_weight_comm
    (H : Family α) (V : Edge α) (z x y : α) :
    positiveRootedWeight H V z x y =
      positiveRootedWeight H V z y x := by
  unfold positiveRootedWeight
  rw [rooted_signed_weight_comm]

theorem core_positive_weight_eq_displayed_pair
    (H : Family α) (V p : Edge α) (z x y : α)
    (hp : p.card = 2) (hpair : p = ({x, y} : Edge α)) :
    corePositiveWeight H V z p =
      positiveRootedWeight H V z x y := by
  classical
  let e := corePairRep p hp
  have he := core_pair_rep_spec p hp
  have heq : ({e.1, e.2} : Edge α) = ({x, y} : Edge α) :=
    he.2.symm.trans hpair
  have he1 : e.1 = x ∨ e.1 = y := by
    have hm : e.1 ∈ ({x, y} : Edge α) := by
      rw [← heq]
      simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hcases : (e.1 = x ∧ e.2 = y) ∨ (e.1 = y ∧ e.2 = x) := by
    rcases he1 with h1 | h1
    · have hm : e.2 ∈ ({x, y} : Edge α) := by
        rw [← heq]
        simp
      rcases (show e.2 = x ∨ e.2 = y by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hm) with h2 | h2
      · exact False.elim (he.1 (h1.trans h2.symm))
      · exact Or.inl ⟨h1, h2⟩
    · have hm : e.2 ∈ ({x, y} : Edge α) := by
        rw [← heq]
        simp
      rcases (show e.2 = x ∨ e.2 = y by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hm) with h2 | h2
      · exact Or.inr ⟨h1, h2⟩
      · exact False.elim (he.1 (h1.trans h2.symm))
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [corePositiveWeight, hp, e, h1, h2]
  · rw [positive_rooted_weight_comm]
    simp [corePositiveWeight, hp, e, h1, h2]

private theorem root_link_subset_erased_pairs
    (H : Family α) (V : Edge α) (z : α) :
    rootLink H V z ⊆ (V.erase z).powersetCard 2 := by
  intro p hp
  obtain ⟨hpV, hzNot, _⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpSub, hpCard⟩ := Finset.mem_powersetCard.mp hpV
  apply Finset.mem_powersetCard.mpr
  constructor
  · intro t ht
    exact Finset.mem_erase.mpr
      ⟨fun htz => hzNot (htz ▸ ht), hpSub ht⟩
  · exact hpCard

private theorem root_neighbors_eq_erased_pair_filter
    (H : Family α) (V : Edge α) {z x : α}
    (hx : x ∈ V.erase z) :
    rootNeighbors H V z x =
      ((V.erase z).erase x).filter
        (fun y => ({x, y} : Edge α) ∈ rootLink H V z) := by
  ext y
  have hxV := (Finset.mem_erase.mp hx).2
  have hzx : z ≠ x := Ne.symm (Finset.mem_erase.mp hx).1
  constructor
  · intro hy
    have hLink := (mem_root_neighbors_iff_mem_root_link H V hxV hzx).mp hy
    obtain ⟨hyV, hyNot, _⟩ := Finset.mem_filter.mp hy
    have hyz : y ≠ z := by
      intro h
      exact hyNot (by simp [h])
    have hyx : y ≠ x := by
      intro h
      exact hyNot (by simp [h])
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr
        ⟨hyx, Finset.mem_erase.mpr ⟨hyz, hyV⟩⟩,
        hLink⟩
  · intro hy
    exact (mem_root_neighbors_iff_mem_root_link H V hxV hzx).mpr
      (Finset.mem_filter.mp hy).2

/-- The manuscript's positive-weight total counts each source edge in both
orientations. Dividing by two gives the actual source-pair sum. -/
theorem oriented_positive_eq_core_positive
    (H : Family α) (V : Edge α) :
    orientedPositiveWeightTotal H V / 2 =
      ∑ z ∈ V, ∑ p ∈ rootLink H V z,
        corePositiveWeight H V z p := by
  have hRoot (z : α) (hz : z ∈ V) :
      (∑ x ∈ V.erase z,
        ∑ y ∈ rootNeighbors H V z x,
          positiveRootedWeight H V z x y) =
        2 * (∑ p ∈ rootLink H V z,
          corePositiveWeight H V z p) := by
    let F : Edge α → ℚ := fun p =>
      if p ∈ rootLink H V z then corePositiveWeight H V z p else 0
    have hOrdered := ordered_pair_sum_eq_twice_unordered
      (V.erase z) F
    have hLeft :
        (∑ x ∈ V.erase z,
          ∑ y ∈ rootNeighbors H V z x,
            positiveRootedWeight H V z x y) =
          ∑ x ∈ V.erase z,
            ∑ y ∈ (V.erase z).erase x,
              F ({x, y} : Edge α) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [root_neighbors_eq_erased_pair_filter H V hx]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hxyLink :
          ({x, y} : Edge α) ∈ rootLink H V z
      · have hxy : x ≠ y := Ne.symm (Finset.mem_erase.mp hy).1
        simp only [F, hxyLink, ↓reduceIte]
        rw [core_positive_weight_eq_displayed_pair H V
          ({x, y} : Edge α) z x y (Finset.card_pair hxy) rfl]
      · simp [F, hxyLink]
    have hRight :
        (∑ p ∈ (V.erase z).powersetCard 2, F p) =
          ∑ p ∈ rootLink H V z, corePositiveWeight H V z p := by
      have hSub := root_link_subset_erased_pairs H V z
      calc
        (∑ p ∈ (V.erase z).powersetCard 2, F p) =
            ∑ p ∈ rootLink H V z, F p := by
          symm
          apply Finset.sum_subset hSub
          intro p hp hnot
          simp [F, hnot]
        _ = ∑ p ∈ rootLink H V z,
              corePositiveWeight H V z p := by
          apply Finset.sum_congr rfl
          intro p hp
          simp [F, hp]
    rw [← hLeft, hRight] at hOrdered
    exact hOrdered
  have hSum :
      orientedPositiveWeightTotal H V =
        2 * (∑ z ∈ V, ∑ p ∈ rootLink H V z,
          corePositiveWeight H V z p) := by
    unfold orientedPositiveWeightTotal
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    exact hRoot z hz
  rw [hSum]
  ring


/-- The actual charge kernel over an ambient root's other vertices
is supported exactly on the other completion vertices of its source pair. -/
theorem core_charge_kernel_sum_eq_completion_sum
    (H : Family α) (V p : Edge α) {z : α}
    (hp : p ∈ rootLink H V z) :
    (∑ v ∈ V.erase z, coreChargeKernel H V z v p) =
      ∑ v ∈ (completionVertices H V p).erase z,
        coreReceiverCharge H V z v p := by
  classical
  have hSub : (completionVertices H V p).erase z ⊆ V.erase z := by
    intro v hv
    obtain ⟨hvz, hvN⟩ := Finset.mem_erase.mp hv
    exact Finset.mem_erase.mpr
      ⟨hvz, completion_vertices_subset_ground H V p hvN⟩
  calc
    (∑ v ∈ V.erase z, coreChargeKernel H V z v p) =
        ∑ v ∈ V.erase z,
          if v ∈ (completionVertices H V p).erase z then
            coreReceiverCharge H V z v p else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      simp [coreChargeKernel, hp]
    _ = ∑ v ∈ (completionVertices H V p).erase z,
          coreReceiverCharge H V z v p := by
      rw [← Finset.sum_filter]
      congr 1
      ext v
      simp only [Finset.mem_filter]
      constructor
      · intro hv
        exact hv.2
      · intro hv
        exact ⟨hSub hv, hv⟩

/-- A source pair's positive weight is either retained at degree one or
conserved across its actual outgoing receiver charges. -/
theorem core_positive_weight_split
    (H : Family α) (V p : Edge α) {z : α}
    (hzV : z ∈ V) (hp : p ∈ rootLink H V z) :
    corePositiveWeight H V z p =
      (if (completionVertices H V p).card = 1 then
        corePositiveWeight H V z p else 0) +
      ∑ v ∈ V.erase z, coreChargeKernel H V z v p := by
  classical
  have hp2 : p.card = 2 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp).1).2
  let e := corePairRep p hp2
  have he := core_pair_rep_spec p hp2
  have hsource : ({e.1, e.2} : Edge α) ∈ rootLink H V z := by
    rw [← he.2]
    exact hp
  have hzN : z ∈ completionVertices H V p := by
    rw [he.2]
    exact root_mem_source_completion H V hzV hsource
  have hPos : 0 < (completionVertices H V p).card :=
    Finset.card_pos.mpr ⟨z, hzN⟩
  have hSent := core_charge_kernel_sum_eq_completion_sum H V p hp
  by_cases hOne : (completionVertices H V p).card = 1
  · have hEraseCard : ((completionVertices H V p).erase z).card = 0 := by
      have hCard := Finset.card_erase_add_one hzN
      omega
    have hEraseEmpty : (completionVertices H V p).erase z = ∅ :=
      Finset.card_eq_zero.mp hEraseCard
    rw [hSent, hEraseEmpty]
    simp [hOne]
  · have hAtLeastTwo : 2 ≤ (completionVertices H V p).card := by omega
    have hAtLeastTwo' :
        2 ≤ (completionVertices H V ({e.1, e.2} : Edge α)).card := by
      exact he.2 ▸ hAtLeastTwo
    have hConserve := actual_source_charge_conservation
      H V hzV hsource hAtLeastTwo'
    have hWeight : corePositiveWeight H V z p =
        positiveRootedWeight H V z e.1 e.2 :=
      core_positive_weight_eq_displayed_pair H V p z e.1 e.2 hp2 he.2
    have hCharges :
        (∑ v ∈ (completionVertices H V p).erase z,
          coreReceiverCharge H V z v p) =
        ∑ v ∈ (completionVertices H V ({e.1, e.2} : Edge α)).erase z,
          actualReceiverCharge H V z e.1 e.2 v := by
      have hN : completionVertices H V p =
          completionVertices H V ({e.1, e.2} : Edge α) := by
        rw [he.2]
      rw [hN]
      apply Finset.sum_congr rfl
      intro v hv
      exact core_receiver_charge_eq_displayed_pair
        H V p z v e.1 e.2 hp2 he.2
    rw [hSent, hCharges, hConserve, hWeight]
    simp [hOne]

/-- Positive weight remaining at degree-one sources. -/
noncomputable def retainedCorePositiveTotal
    (H : Family α) (V : Edge α) : ℚ := by
  classical
  exact ∑ z ∈ V, ∑ p ∈ rootLink H V z,
    if (completionVertices H V p).card = 1 then
      corePositiveWeight H V z p else 0

theorem core_positive_eq_retained_add_outgoing
    (H : Family α) (V : Edge α) :
    (∑ z ∈ V, ∑ p ∈ rootLink H V z,
      corePositiveWeight H V z p) =
      retainedCorePositiveTotal H V +
        outgoingCoreChargeTotal H V := by
  classical
  calc
    (∑ z ∈ V, ∑ p ∈ rootLink H V z,
      corePositiveWeight H V z p) =
        ∑ z ∈ V, ∑ p ∈ rootLink H V z,
          ((if (completionVertices H V p).card = 1 then
              corePositiveWeight H V z p else 0) +
            ∑ v ∈ V.erase z, coreChargeKernel H V z v p) := by
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro p hp
      exact core_positive_weight_split H V p hz hp
    _ = retainedCorePositiveTotal H V +
          outgoingCoreChargeTotal H V := by
      simp [retainedCorePositiveTotal, outgoingCoreChargeTotal,
        Finset.sum_add_distrib]

theorem actual_positive_source_conservation
    (H : Family α) (V : Edge α) :
    orientedPositiveWeightTotal H V / 2 =
      retainedCorePositiveTotal H V +
        incomingCommonLinkChargeTotal H V := by
  rw [oriented_positive_eq_core_positive,
    core_positive_eq_retained_add_outgoing,
    actual_charge_fubini_by_common_link]


theorem core_positive_weight_lt_two_of_root_link
    (H : Family α) (V p : Edge α) {z : α}
    (hp : p ∈ rootLink H V z) :
    corePositiveWeight H V z p < 2 := by
  have hp2 : p.card = 2 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp).1).2
  let e := corePairRep p hp2
  have he := core_pair_rep_spec p hp2
  have hsource : ({e.1, e.2} : Edge α) ∈ rootLink H V z := by
    rw [← he.2]
    exact hp
  rw [core_positive_weight_eq_displayed_pair H V p z e.1 e.2 hp2 he.2]
  exact positive_rooted_weight_lt_two H V hsource he.1

/-- Every retained source has a unique root, so the total retained
positive weight is at most two per singleton-completion pair. -/
theorem retained_core_positive_total_le_two_singletons
    (H : Family α) (V : Edge α)
    (hU : Uniform 3 H)
    (hGround : ∀ E ∈ H, E ⊆ V) :
    retainedCorePositiveTotal H V ≤
      2 * ((singletonCompletionPairs H V).card : ℚ) := by
  classical
  have hSwap :
      retainedCorePositiveTotal H V =
        ∑ p ∈ V.powersetCard 2,
          ∑ z ∈ completionVertices H V p,
            if (completionVertices H V p).card = 1 then
              corePositiveWeight H V z p else 0 := by
    unfold retainedCorePositiveTotal
    apply Finset.sum_comm'
    intro z p
    simp only [rootLink, completionVertices, Finset.mem_filter]
    tauto
  have hFilter :
      (V.powersetCard 2).filter
        (fun p => (completionVertices H V p).card = 1) =
          singletonCompletionPairs H V := by
    ext p
    simp only [Finset.mem_filter, singletonCompletionPairs]
    constructor
    · rintro ⟨hpV, hd1⟩
      have hPos : 0 < (completionVertices H V p).card := by omega
      have hNonempty : (completionVertices H V p).Nonempty :=
        Finset.card_pos.mp hPos
      exact ⟨(mem_used_pairs_iff_completion_nonempty
        H V p hU hGround hpV).mpr hNonempty, hd1⟩
    · rintro ⟨hpUsed, hd1⟩
      exact ⟨used_pairs_subset H V hpUsed, hd1⟩
  calc
    retainedCorePositiveTotal H V =
        ∑ p ∈ V.powersetCard 2,
          if (completionVertices H V p).card = 1 then
            ∑ z ∈ completionVertices H V p,
              corePositiveWeight H V z p else 0 := by
        rw [hSwap]
        apply Finset.sum_congr rfl
        intro p hp
        split_ifs <;> simp_all
    _ = ∑ p ∈ singletonCompletionPairs H V,
          ∑ z ∈ completionVertices H V p,
            corePositiveWeight H V z p := by
        rw [← Finset.sum_filter, hFilter]
    _ ≤ ∑ p ∈ singletonCompletionPairs H V, (2 : ℚ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpV : p ∈ V.powersetCard 2 :=
          used_pairs_subset H V (Finset.mem_filter.mp hp).1
        have hd1 : (completionVertices H V p).card = 1 :=
          (Finset.mem_filter.mp hp).2
        obtain ⟨z, hN⟩ :=
          Finset.card_eq_one.mp hd1
        have hzN : z ∈ completionVertices H V p := hN.symm ▸ (by simp)
        have hroot : p ∈ rootLink H V z :=
          Finset.mem_filter.mpr
            ⟨hpV, (Finset.mem_filter.mp hzN).2⟩
        rw [hN]
        simp
        exact (core_positive_weight_lt_two_of_root_link H V p hroot).le
    _ = 2 * ((singletonCompletionPairs H V).card : ℚ) := by
        simp
        ring


/-- Once the receiver cells have their global capacity, the
manuscript's (II.8) bound follows from exact source conservation. -/
theorem positive_total_le_capacity_of_incoming_bound
    (H : Family α) (V : Edge α)
    (hU : Uniform 3 H)
    (hGround : ∀ E ∈ H, E ⊆ V)
    (hIncoming :
      incomingCommonLinkChargeTotal H V ≤
        4 * ((singletonLinkCells H V).card : ℚ) +
        2 * ((doubleLinkCells H V).card : ℚ) +
        actualXi H V) :
    orientedPositiveWeightTotal H V / 2 ≤
      2 * ((singletonCompletionPairs H V).card : ℚ) +
      4 * ((singletonLinkCells H V).card : ℚ) +
      2 * ((doubleLinkCells H V).card : ℚ) +
      actualXi H V := by
  have hConserve := actual_positive_source_conservation H V
  have hRetained :=
    retained_core_positive_total_le_two_singletons H V hU hGround
  linarith


theorem actual_cell_charge_for_pair_eq_displayed
    (H : Family α) (V : Edge α) {z v : α}
    (hzv : z ≠ v) :
    actualCellChargeForPair H V ({z, v} : Edge α) =
      actualCellChargeTotal H V z v := by
  classical
  let q : Edge α := {z, v}
  have hq2 : q.card = 2 := Finset.card_pair hzv
  let e := corePairRep q hq2
  have he := core_pair_rep_spec q hq2
  have heq : ({e.1, e.2} : Edge α) = ({z, v} : Edge α) := by
    simpa [q] using he.2.symm
  have he1 : e.1 = z ∨ e.1 = v := by
    have hm : e.1 ∈ ({z, v} : Edge α) := by
      rw [← heq]
      simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hcases : (e.1 = z ∧ e.2 = v) ∨ (e.1 = v ∧ e.2 = z) := by
    rcases he1 with h1 | h1
    · have hm : e.2 ∈ ({z, v} : Edge α) := by
        rw [← heq]
        simp
      rcases (show e.2 = z ∨ e.2 = v by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hm) with h2 | h2
      · exact False.elim (he.1 (h1.trans h2.symm))
      · exact Or.inl ⟨h1, h2⟩
    · have hm : e.2 ∈ ({z, v} : Edge α) := by
        rw [← heq]
        simp
      rcases (show e.2 = z ∨ e.2 = v by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hm) with h2 | h2
      · exact Or.inr ⟨h1, h2⟩
      · exact False.elim (he.1 (h1.trans h2.symm))
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [actualCellChargeForPair, hq2, q, e, h1, h2]
  · have hComm := actual_cell_charge_total_comm H V v z
    simp [actualCellChargeForPair, hq2, q, e, h1, h2] at hComm ⊢
    exact hComm

/-- The ordered receiver sum agrees with the sum of two-direction
charges over unordered actual receiver cells. -/
theorem incoming_charge_eq_cell_charge_sum
    (H : Family α) (V : Edge α) :
    incomingCommonLinkChargeTotal H V =
      ∑ q ∈ usedCells H V, actualCellChargeForPair H V q := by
  classical
  let F : α → α → ℚ := fun z v =>
    ∑ p ∈ commonLink H V ({z, v} : Edge α),
      coreReceiverCharge H V z v p
  let G : Edge α → ℚ := actualCellChargeForPair H V
  have hPair (z v : α) (hzv : z ≠ v) :
      G ({z, v} : Edge α) = F z v + F v z := by
    change actualCellChargeForPair H V ({z, v} : Edge α) =
      (∑ p ∈ commonLink H V ({z, v} : Edge α),
        coreReceiverCharge H V z v p) +
      (∑ p ∈ commonLink H V ({v, z} : Edge α),
        coreReceiverCharge H V v z p)
    rw [actual_cell_charge_for_pair_eq_displayed H V hzv]
    unfold actualCellChargeTotal
    rw [Finset.sum_add_distrib]
    simp only [Finset.pair_comm]
  have hOrdered := ordered_pair_sum_eq_twice_unordered V G
  have hSwap :
      (∑ z ∈ V, ∑ v ∈ V.erase z, F v z) =
        ∑ z ∈ V, ∑ v ∈ V.erase z, F z v := by
    apply Finset.sum_comm'
    intro z v
    constructor
    · rintro ⟨hzV, hv⟩
      obtain ⟨hvz, hvV⟩ := Finset.mem_erase.mp hv
      exact ⟨Finset.mem_erase.mpr ⟨hvz.symm, hzV⟩, hvV⟩
    · rintro ⟨hz, hvV⟩
      obtain ⟨hzv, hzV⟩ := Finset.mem_erase.mp hz
      exact ⟨hzV, Finset.mem_erase.mpr ⟨hzv.symm, hvV⟩⟩
  have hExpand :
      (∑ z ∈ V, ∑ v ∈ V.erase z,
        G ({z, v} : Edge α)) =
        2 * (∑ z ∈ V, ∑ v ∈ V.erase z, F z v) := by
    calc
      (∑ z ∈ V, ∑ v ∈ V.erase z,
        G ({z, v} : Edge α)) =
          ∑ z ∈ V, ∑ v ∈ V.erase z,
            (F z v + F v z) := by
        apply Finset.sum_congr rfl
        intro z hz
        apply Finset.sum_congr rfl
        intro v hv
        exact hPair z v (Ne.symm (Finset.mem_erase.mp hv).1)
      _ = 2 * (∑ z ∈ V, ∑ v ∈ V.erase z, F z v) := by
        simp only [Finset.sum_add_distrib, ← hSwap]
        ring
  have hAll :
      incomingCommonLinkChargeTotal H V =
        ∑ q ∈ V.powersetCard 2, G q := by
    unfold incomingCommonLinkChargeTotal
    change (∑ z ∈ V, ∑ v ∈ V.erase z, F z v) = _
    rw [hExpand] at hOrdered
    linarith
  calc
    incomingCommonLinkChargeTotal H V =
        ∑ q ∈ V.powersetCard 2, G q := hAll
    _ = ∑ q ∈ usedCells H V, G q := by
      symm
      apply Finset.sum_subset (used_cells_subset H V)
      intro q hqV hqNot
      have hEmpty : commonLink H V q = ∅ := by
        by_contra h
        have hNonempty : (commonLink H V q).Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr h
        exact hqNot ((mem_used_cells_iff_common_link_nonempty H V q).mpr
          ⟨hqV, hNonempty⟩)
      have hq2 := (Finset.mem_powersetCard.mp hqV).2
      let e := corePairRep q hq2
      have he := core_pair_rep_spec q hq2
      have hLinkEmpty :
          commonLink H V ({e.1, e.2} : Edge α) = ∅ :=
        he.2.symm ▸ hEmpty
      simp only [G, actualCellChargeForPair, dite_eq_left hq2]
      change actualCellChargeTotal H V e.1 e.2 = 0
      simp [actualCellChargeTotal, hLinkEmpty]

end JSP523.Rank3
