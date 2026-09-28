import JSP523.Rank3.BridgeDemandGlobal
import JSP523.Rank3.ReciprocalCapacityScalar

set_option maxHeartbeats 800000

/-!
# Exceptional receiver excess and bridge demands

This file proves the finite charging step (II.10) in `paper/proof.pdf`:
the excess of each actual triangle-exception receiver is covered by the two
demands on its bridge triples. It then sums that inequality to bound `actualXi`.
-/

namespace JSP523.Rank3

variable {α : Type*} [DecidableEq α]

private theorem actual_book_charge_nonneg
    {H : Family α} {V : Edge α} {z v x y : α}
    (hzV : z ∈ V)
    (hsource : ({x, y} : Edge α) ∈ rootLink H V z)
    (hrecv : v ∈ (completionVertices H V ({x, y} : Edge α)).erase z) :
    0 ≤ actualReceiverCharge H V z x y v := by
  have hzComp := root_mem_source_completion H V hzV hsource
  have hvComp := (Finset.mem_erase.mp hrecv).2
  have hzv : z ≠ v := Ne.symm (Finset.mem_erase.mp hrecv).1
  have hsub : ({z, v} : Edge α) ⊆ completionVertices H V ({x, y} : Edge α) := by
    intro a ha
    rcases Finset.mem_insert.mp ha with haz | hav
    · exact haz ▸ hzComp
    · exact (Finset.mem_singleton.mp hav) ▸ hvComp
  have hdegree : 2 ≤ (completionVertices H V ({x, y} : Edge α)).card := by
    have hc := Finset.card_le_card hsub
    rw [Finset.card_pair hzv] at hc
    exact hc
  have hden : (0 : ℚ) <
      ((completionVertices H V ({x, y} : Edge α)).card : ℚ) - 1 := by
    have hc : (2 : ℚ) ≤ (completionVertices H V ({x, y} : Edge α)).card := by
      exact_mod_cast hdegree
    linarith
  simp [actualReceiverCharge, hrecv, chargePerOtherCompletion]
  exact div_nonneg (le_max_right _ _) (le_of_lt hden)

/-- Each of the four actual charges into an exceptional receiver lies in
the interval from zero to one. -/
theorem exceptional_book_page_charge_bounds
    {H : Family α} {V q : Edge α}
    (hH : Admissible H) (d : ExceptionalReceiverBookData H V q)
    {w : α} (hxw : d.x ≠ w)
    (hp : ({d.x, w} : Edge α) ∈ commonLink H V q) :
    0 ≤ actualReceiverCharge H V d.z d.x w d.v ∧
    actualReceiverCharge H V d.z d.x w d.v ≤ 1 ∧
    0 ≤ actualReceiverCharge H V d.v d.x w d.z ∧
    actualReceiverCharge H V d.v d.x w d.z ≤ 1 := by
  obtain ⟨hzv, _, _, _⟩ := exceptional_receiver_book_data_distinct d
  have hp' : ({d.x, w} : Edge α) ∈
      commonLink H V ({d.z, d.v} : Edge α) := by
    simpa only [d.hq] using hp
  have hsrc := common_link_pair_gives_two_sources hzv hp'
  have hvComp := root_mem_source_completion H V d.hvV hsrc.2
  have hzComp := root_mem_source_completion H V d.hzV hsrc.1
  have hvRecv : d.v ∈
      (completionVertices H V ({d.x, w} : Edge α)).erase d.z :=
    Finset.mem_erase.mpr ⟨Ne.symm hzv, hvComp⟩
  have hzRecv : d.z ∈
      (completionVertices H V ({d.x, w} : Edge α)).erase d.v :=
    Finset.mem_erase.mpr ⟨hzv, hzComp⟩
  have hcard : (commonLink H V ({d.z, d.v} : Edge α)).card = 2 := by
    simpa only [d.hq] using exceptional_receiver_book_data_cell_card d
  have hcardRev : (commonLink H V ({d.v, d.z} : Edge α)).card = 2 := by
    simpa only [Finset.pair_comm] using hcard
  exact ⟨actual_book_charge_nonneg d.hzV hsrc.1 hvRecv,
    (actual_charge_lt_one_at_double_receiver hH d.hzV hsrc.1 hxw hvRecv hcard).le,
    actual_book_charge_nonneg d.hvV hsrc.2 hzRecv,
    (actual_charge_lt_one_at_double_receiver hH d.hvV hsrc.2 hxw hzRecv hcardRev).le⟩

/-- Every indexed bridge demand is nonnegative. -/
theorem bridge_demand_nonneg
    (H : Family α) (V q E : Edge α) (hH : Admissible H) :
    0 ≤ bridgeDemand H V q E := by
  classical
  by_cases hq : triangleExceptionalReceiverCell H V q
  · let d := canonicalExceptionalReceiverBookData H V q hq
    obtain ⟨_, hxy, hxu, _⟩ := exceptional_receiver_book_data_distinct d
    have hpY : ({d.x, d.y} : Edge α) ∈ commonLink H V q := by
      rw [d.hbook]
      simp
    have hpU : ({d.x, d.u} : Edge α) ∈ commonLink H V q := by
      rw [d.hbook]
      simp
    obtain ⟨ha0, _, hb0, _⟩ :=
      exceptional_book_page_charge_bounds hH d hxy hpY
    obtain ⟨hc0, _, hd0, _⟩ :=
      exceptional_book_page_charge_bounds hH d hxu hpU
    have hY : 0 ≤ min (actualReceiverCharge H V d.z d.x d.y d.v)
        (actualReceiverCharge H V d.v d.x d.y d.z) := le_min ha0 hb0
    have hU : 0 ≤ min (actualReceiverCharge H V d.z d.x d.u d.v)
        (actualReceiverCharge H V d.v d.x d.u d.z) := le_min hc0 hd0
    simp only [bridgeDemand, dite_eq_left hq]
    change 0 ≤ (if E = ({d.z, d.v, d.y} : Edge α) then
      min (actualReceiverCharge H V d.z d.x d.y d.v)
        (actualReceiverCharge H V d.v d.x d.y d.z)
      else if E = ({d.z, d.v, d.u} : Edge α) then
        min (actualReceiverCharge H V d.z d.x d.u d.v)
          (actualReceiverCharge H V d.v d.x d.u d.z)
      else 0)
    by_cases hEy : E = ({d.z, d.v, d.y} : Edge α)
    · rw [ite_eq_left hEy]
      exact hY
    · rw [ite_eq_right hEy]
      by_cases hEu : E = ({d.z, d.v, d.u} : Edge α)
      · rw [ite_eq_left hEu]
        exact hU
      · rw [ite_eq_right hEu]
  · simp [bridgeDemand, hq]

/-- Both bridge triples are genuine triples of the family, and they are
different. This follows from the reciprocal triangle, which makes the two
receiving vertices disjoint from its two page vertices. -/
theorem exceptional_book_bridge_triples
    {H : Family α} {V q : Edge α}
    (d : ExceptionalReceiverBookData H V q) :
    ({d.z, d.v, d.y} : Edge α) ∈ H ∧
    ({d.z, d.v, d.u} : Edge α) ∈ H ∧
    ({d.z, d.v, d.y} : Edge α) ≠ ({d.z, d.v, d.u} : Edge α) := by
  obtain ⟨_, _, _, hyu⟩ := exceptional_receiver_book_data_distinct d
  have hp : ({d.z, d.v} : Edge α) ∈
      commonLink H V ({d.y, d.u} : Edge α) := by
    rw [d.hreciprocal]
    simp
  have hsrc := common_link_pair_gives_two_sources hyu hp
  have hY : ({d.z, d.v} : Edge α) ∪ {d.y} ∈ H :=
    (Finset.mem_filter.mp hsrc.1).2.2
  have hU : ({d.z, d.v} : Edge α) ∪ {d.u} ∈ H :=
    (Finset.mem_filter.mp hsrc.2).2.2
  have hdis : Disjoint ({d.z, d.v} : Edge α) ({d.y, d.u} : Edge α) := by
    obtain ⟨_, _, _, _, _, hd, _, _⟩ := (Finset.mem_filter.mp hp).2
    exact hd
  have hyNot : d.y ∉ ({d.z, d.v} : Edge α) := by
    intro hm
    exact (Finset.disjoint_left.mp hdis) hm (by simp)
  have hyNot' : d.y ≠ d.z ∧ d.y ≠ d.v := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hyNot
  have hYEq : ({d.z, d.v} : Edge α) ∪ {d.y} =
      ({d.z, d.v, d.y} : Edge α) := by
    ext t
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hUEq : ({d.z, d.v} : Edge α) ∪ {d.u} =
      ({d.z, d.v, d.u} : Edge α) := by
    ext t
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  refine ⟨hYEq ▸ hY, hUEq ▸ hU, ?_⟩
  intro he
  have hyMem : d.y ∈ ({d.z, d.v, d.u} : Edge α) := by
    rw [← he]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hyMem
  rcases hyMem with hyz | hyv | hyu'
  · exact hyNot'.1 hyz
  · exact hyNot'.2 hyv
  · exact hyu hyu'

/-- A bridge demand vanishes away from the two triples of its selected
book. -/
theorem bridge_demand_eq_zero_of_not_book_triples
    (H : Family α) (V q E : Edge α)
    (hq : triangleExceptionalReceiverCell H V q)
    (hY : E ≠ ({(canonicalExceptionalReceiverBookData H V q hq).z,
      (canonicalExceptionalReceiverBookData H V q hq).v,
      (canonicalExceptionalReceiverBookData H V q hq).y} : Edge α))
    (hU : E ≠ ({(canonicalExceptionalReceiverBookData H V q hq).z,
      (canonicalExceptionalReceiverBookData H V q hq).v,
      (canonicalExceptionalReceiverBookData H V q hq).u} : Edge α)) :
    bridgeDemand H V q E = 0 := by
  simp [bridgeDemand, hq, hY, hU]

/-- The scalar inequality (II.10) evaluated on one concrete exceptional
receiver book, before substituting the indexed bridge-demand function. -/
theorem exceptional_book_excess_le_page_minima
    {H : Family α} {V q : Edge α}
    (hH : Admissible H) (d : ExceptionalReceiverBookData H V q) :
    max (actualCellChargeForPair H V q - 2) 0 ≤
      min (actualReceiverCharge H V d.z d.x d.y d.v)
        (actualReceiverCharge H V d.v d.x d.y d.z) +
      min (actualReceiverCharge H V d.z d.x d.u d.v)
        (actualReceiverCharge H V d.v d.x d.u d.z) := by
  classical
  obtain ⟨_, hxy, hxu, _⟩ := exceptional_receiver_book_data_distinct d
  have hpY : ({d.x, d.y} : Edge α) ∈ commonLink H V q := by
    rw [d.hbook]
    simp
  have hpU : ({d.x, d.u} : Edge α) ∈ commonLink H V q := by
    rw [d.hbook]
    simp
  obtain ⟨ha0, ha1, hb0, hb1⟩ :=
    exceptional_book_page_charge_bounds hH d hxy hpY
  obtain ⟨hc0, hc1, hd0, hd1⟩ :=
    exceptional_book_page_charge_bounds hH d hxu hpU
  rw [exceptional_receiver_book_data_charge_four_sources d]
  let a := actualReceiverCharge H V d.z d.x d.y d.v
  let b := actualReceiverCharge H V d.v d.x d.y d.z
  let c := actualReceiverCharge H V d.z d.x d.u d.v
  let e := actualReceiverCharge H V d.v d.x d.u d.z
  change max ((a + b) + (c + e) - 2) 0 ≤ min a b + min c e
  have hAssoc : (a + b) + (c + e) - 2 = a + b + c + e - 2 := by ring
  rw [hAssoc]
  exact bridge_excess_le_page_demands a b c e
    ha0 hb0 hc0 hd0 ha1 hb1 hc1 hd1

/-- The exceptional excess of one actual receiver is covered by its two
bridge demands. This is the instantiated inequality (II.10). -/
theorem exceptional_receiver_excess_le_bridge_demands
    {H : Family α} {V q : Edge α}
    (hH : Admissible H)
    (hq : triangleExceptionalReceiverCell H V q) :
    let d := canonicalExceptionalReceiverBookData H V q hq
    max (actualCellChargeForPair H V q - 2) 0 ≤
      bridgeDemand H V q ({d.z, d.v, d.y} : Edge α) +
      bridgeDemand H V q ({d.z, d.v, d.u} : Edge α) := by
  classical
  let d := canonicalExceptionalReceiverBookData H V q hq
  have hEne := (exceptional_book_bridge_triples d).2.2
  have hFirst : bridgeDemand H V q ({d.z, d.v, d.y} : Edge α) =
      min (actualReceiverCharge H V d.z d.x d.y d.v)
        (actualReceiverCharge H V d.v d.x d.y d.z) := by
    simp only [bridgeDemand, dite_eq_left hq]
    change (if ({d.z, d.v, d.y} : Edge α) = {d.z, d.v, d.y} then
      min (actualReceiverCharge H V d.z d.x d.y d.v)
        (actualReceiverCharge H V d.v d.x d.y d.z) else
      if ({d.z, d.v, d.y} : Edge α) = {d.z, d.v, d.u} then
        min (actualReceiverCharge H V d.z d.x d.u d.v)
          (actualReceiverCharge H V d.v d.x d.u d.z) else 0) = _
    simp
  have hSecond : bridgeDemand H V q ({d.z, d.v, d.u} : Edge α) =
      min (actualReceiverCharge H V d.z d.x d.u d.v)
        (actualReceiverCharge H V d.v d.x d.u d.z) := by
    have hNe : ({d.z, d.v, d.u} : Edge α) ≠
        ({d.z, d.v, d.y} : Edge α) := Ne.symm hEne
    simp only [bridgeDemand, dite_eq_left hq]
    change (if ({d.z, d.v, d.u} : Edge α) = {d.z, d.v, d.y} then
      min (actualReceiverCharge H V d.z d.x d.y d.v)
        (actualReceiverCharge H V d.v d.x d.y d.z) else
      if ({d.z, d.v, d.u} : Edge α) = {d.z, d.v, d.u} then
        min (actualReceiverCharge H V d.z d.x d.u d.v)
          (actualReceiverCharge H V d.v d.x d.u d.z) else 0) = _
    simp [hNe]
  change max (actualCellChargeForPair H V q - 2) 0 ≤
    bridgeDemand H V q ({d.z, d.v, d.y} : Edge α) +
    bridgeDemand H V q ({d.z, d.v, d.u} : Edge α)
  rw [hFirst, hSecond]
  exact exceptional_book_excess_le_page_minima hH d

/-- Every bridge demand associated with one exceptional receiver is
supported on its two actual bridge triples. -/
theorem exceptional_receiver_demand_sum_eq_two
    {H : Family α} {V q : Edge α}
    (hq : triangleExceptionalReceiverCell H V q) :
    let d := canonicalExceptionalReceiverBookData H V q hq
    (∑ E ∈ H, bridgeDemand H V q E) =
      bridgeDemand H V q ({d.z, d.v, d.y} : Edge α) +
      bridgeDemand H V q ({d.z, d.v, d.u} : Edge α) := by
  classical
  let d := canonicalExceptionalReceiverBookData H V q hq
  obtain ⟨hY, hU, hNe⟩ := exceptional_book_bridge_triples d
  have hSub : ({({d.z, d.v, d.y} : Edge α),
      ({d.z, d.v, d.u} : Edge α)} : Family α) ⊆ H := by
    intro E hE
    rcases Finset.mem_insert.mp hE with h | h
    · exact h ▸ hY
    · exact (Finset.mem_singleton.mp h) ▸ hU
  have hReduce : (∑ E ∈ H, bridgeDemand H V q E) =
      ∑ E ∈ ({({d.z, d.v, d.y} : Edge α),
        ({d.z, d.v, d.u} : Edge α)} : Family α),
        bridgeDemand H V q E := by
    symm
    apply Finset.sum_subset hSub
    intro E hEH hEout
    have hEY : E ≠ ({d.z, d.v, d.y} : Edge α) := by
      intro he
      exact hEout (by simp [he])
    have hEU : E ≠ ({d.z, d.v, d.u} : Edge α) := by
      intro he
      exact hEout (by simp [he])
    exact bridge_demand_eq_zero_of_not_book_triples H V q E hq hEY hEU
  change (∑ E ∈ H, bridgeDemand H V q E) =
    bridgeDemand H V q ({d.z, d.v, d.y} : Edge α) +
    bridgeDemand H V q ({d.z, d.v, d.u} : Edge α)
  rw [hReduce]
  simp [hNe]

/-- The total actual exceptional excess is bounded by the demand assigned
to actual bridge triples, before any nonduplication or local payment is used.
This is the global form of (II.10). -/
theorem actual_xi_le_bridge_demand_total
    (H : Family α) (V : Edge α) (hH : Admissible H) :
    actualXi H V ≤ bridgeDemandTotal H V := by
  classical
  have hLocal (q : Edge α) (hqUsed : q ∈ usedCells H V) :
      (if triangleExceptionalReceiverCell H V q then
        max (actualCellChargeForPair H V q - 2) 0 else 0) ≤
        ∑ E ∈ H, bridgeDemand H V q E := by
    by_cases hq : triangleExceptionalReceiverCell H V q
    · simp only [hq, ↓reduceIte]
      let d := canonicalExceptionalReceiverBookData H V q hq
      have hExcess := exceptional_receiver_excess_le_bridge_demands hH hq
      have hSum := exceptional_receiver_demand_sum_eq_two hq
      dsimp only at hExcess hSum
      rw [hSum]
      exact hExcess
    · have hZero : ∀ E : Edge α, bridgeDemand H V q E = 0 := by
        intro E
        simp [bridgeDemand, hq]
      simp [hq, hZero]
  calc
    actualXi H V ≤
        ∑ q ∈ usedCells H V, ∑ E ∈ H, bridgeDemand H V q E := by
      unfold actualXi
      apply Finset.sum_le_sum
      intro q hq
      exact hLocal q hq
    _ = bridgeDemandTotal H V := by
      rw [Finset.sum_comm]
      rfl

end JSP523.Rank3
