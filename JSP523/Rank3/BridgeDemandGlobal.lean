import JSP523.Rank3.BridgeNonduplication
import JSP523.Rank3.ReceiverCapacity
import JSP523.Rank3.GlobalSourceLedger
import Mathlib.Algebra.Order.Field.Basic
set_option maxHeartbeats 400000

/-!
# Global bridge demand indexing

This module indexes the positive demands of an exceptional receiver by its
two bridge triples. -/

namespace JSP523.Rank3

variable {α : Type*} [DecidableEq α]

private theorem commonLink_eq_oriented_of_ne
    (H : Family α) (V : Edge α) {z v : α} (hzv : z ≠ v) :
    commonLink H V ({z, v} : Edge α) = orientedCommonLink H V z v := by
  ext p
  exact mem_commonLink_pair_iff_oriented H V hzv p

private theorem pair_subset_triple_other_edge
    {a b c z v : α}
    (hzv : z ≠ v)
    (hsub : ({z, v} : Edge α) ⊆ {a, b, c})
    (hne : ({z, v} : Edge α) ≠ {a, b}) :
    ({z, v} : Edge α) = {a, c} ∨ ({z, v} : Edge α) = {b, c} := by
  have hz : z = a ∨ z = b ∨ z = c := by
    have hm : z ∈ ({a, b, c} : Edge α) := hsub (by simp)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hv : v = a ∨ v = b ∨ v = c := by
    have hm : v ∈ ({a, b, c} : Edge α) := hsub (by simp)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  rcases hz with hza | hzb | hzc <;>
    rcases hv with hva | hvb | hvc
  · exact False.elim (hzv (hza.trans hva.symm))
  · exact False.elim (hne (by ext t; simp [hza, hvb]))
  · left; ext t; simp [hza, hvc]
  · exact False.elim (hne (by ext t; simp [hzb, hva]; tauto))
  · exact False.elim (hzv (hzb.trans hvb.symm))
  · right; ext t; simp [hzb, hvc]
  · left; ext t; simp [hzc, hva, or_comm]
  · right; ext t; simp [hzc, hvb, or_comm]
  · exact False.elim (hzv (hzc.trans hvc.symm))

private theorem pair_eq_oriented
    {a b c d : α} (hcd : c ≠ d)
    (hpair : ({a, b} : Edge α) = {c, d}) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have ha : a = c ∨ a = d := by
    have hm : a ∈ ({c, d} : Edge α) := by rw [← hpair]; simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  rcases ha with hac | had
  · left
    refine ⟨hac, ?_⟩
    have hm : d ∈ ({a, b} : Edge α) := by rw [hpair]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hda | hdb
    · exact False.elim (hcd (hac ▸ hda).symm)
    · exact hdb.symm
  · right
    refine ⟨had, ?_⟩
    have hm : c ∈ ({a, b} : Edge α) := by rw [hpair]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hca | hcb
    · exact False.elim (hcd (hca.trans had))
    · exact hcb.symm

/-- Every two-point subset of a three-point edge is one of its three sides. -/
theorem pair_subset_triple_eq_side
    {a b c z v : α}
    (hzv : z ≠ v)
    (hsub : ({z, v} : Edge α) ⊆ {a, b, c}) :
    ({z, v} : Edge α) = {a, b} ∨
      ({z, v} : Edge α) = {a, c} ∨
      ({z, v} : Edge α) = {b, c} := by
  by_cases hab : ({z, v} : Edge α) = {a, b}
  · exact Or.inl hab
  · rcases pair_subset_triple_other_edge hzv hsub hab with hac | hbc
    · exact Or.inr (Or.inl hac)
    · exact Or.inr (Or.inr hbc)

/-- A concrete witness for one exceptional receiver cell. -/
structure ExceptionalReceiverBookData
    (H : Family α) (V : Edge α) (q : Edge α) where
  z : α
  v : α
  x : α
  y : α
  u : α
  hzV : z ∈ V
  hvV : v ∈ V
  hxV : x ∈ V
  hyV : y ∈ V
  huV : u ∈ V
  hq : q = ({z, v} : Edge α)
  hbook : commonLink H V q =
    ({({x, y} : Edge α), ({x, u} : Edge α)} : Family α)
  hreciprocal : commonLink H V ({y, u} : Edge α) =
    ({({x, z} : Edge α), ({x, v} : Edge α), ({z, v} : Edge α)} : Family α)

/-- The receiver endpoints may be exchanged without changing its book. -/
def reverseExceptionalReceiverBookData
    {H : Family α} {V q : Edge α}
    (d : ExceptionalReceiverBookData H V q) :
    ExceptionalReceiverBookData H V q := by
  refine ⟨d.v, d.z, d.x, d.y, d.u, d.hvV, d.hzV, d.hxV, d.hyV, d.huV, ?_, ?_, ?_⟩
  · simpa [Finset.pair_comm] using d.hq
  · rw [d.hbook]
  · rw [d.hreciprocal]
    ext p
    simp [Finset.pair_comm, or_comm, or_left_comm, or_assoc]

/-- The two book pages can be exchanged while keeping the same receiver. -/
def swapExceptionalReceiverBookPages
    {H : Family α} {V q : Edge α}
    (d : ExceptionalReceiverBookData H V q) :
    ExceptionalReceiverBookData H V q := by
  refine ⟨d.z, d.v, d.x, d.u, d.y, d.hzV, d.hvV, d.hxV, d.huV, d.hyV,
    d.hq, ?_, ?_⟩
  · rw [d.hbook]
    ext p
    simp [Finset.pair_comm, or_comm]
  · have hp : ({d.u, d.y} : Edge α) = {d.y, d.u} := by
      simp [Finset.pair_comm]
    rw [hp, d.hreciprocal]

/-- Select one actual book presentation for an exceptional receiver. -/
noncomputable def canonicalExceptionalReceiverBookData
    (H : Family α) (V : Edge α) (q : Edge α)
    (hq : triangleExceptionalReceiverCell H V q) :
    ExceptionalReceiverBookData H V q := by
  classical
  exact Classical.choice (show Nonempty (ExceptionalReceiverBookData H V q) from by
    rcases hq with ⟨z, v, x, y, u, hzV, hvV, hxV, hyV, huV, hqEq,
      hbook, hreciprocal⟩
    exact ⟨⟨z, v, x, y, u, hzV, hvV, hxV, hyV, huV, hqEq,
      hbook, hreciprocal⟩⟩)

/-- The two directed actual charges supporting a bridge triple from an
exceptional receiver. -/
noncomputable def bridgeDemand
    (H : Family α) (V : Edge α) (q E : Edge α) : ℚ := by
  classical
  by_cases hq : triangleExceptionalReceiverCell H V q
  · let d := canonicalExceptionalReceiverBookData H V q hq
    exact if E = ({d.z, d.v, d.y} : Edge α) then
      min (actualReceiverCharge H V d.z d.x d.y d.v)
        (actualReceiverCharge H V d.v d.x d.y d.z)
    else if E = ({d.z, d.v, d.u} : Edge α) then
      min (actualReceiverCharge H V d.z d.x d.u d.v)
        (actualReceiverCharge H V d.v d.x d.u d.z)
    else 0
  · exact 0

/-- The endpoints and pages in any actual exceptional book are distinct. -/
theorem exceptionalReceiverBookData_distinct
    {H : Family α} {V q : Edge α}
    (d : ExceptionalReceiverBookData H V q) :
    d.z ≠ d.v ∧ d.x ≠ d.y ∧ d.x ≠ d.u ∧ d.y ≠ d.u := by
  have hp : ({d.x, d.y} : Edge α) ∈ commonLink H V q := by
    rw [d.hbook]
    simp
  have hpCard : ({d.x, d.y} : Edge α).card = 2 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp).1).2
  have hxy : d.x ≠ d.y := Finset.card_pair_eq_two_iff.mp hpCard
  have hqDistinct : d.z ≠ d.v := by
    obtain ⟨s, hs, t, ht, hst, _, _, _⟩ := (Finset.mem_filter.mp hp).2
    have hs' : s = d.z ∨ s = d.v := by
      rw [d.hq] at hs
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hs
    have ht' : t = d.z ∨ t = d.v := by
      rw [d.hq] at ht
      simpa only [Finset.mem_insert, Finset.mem_singleton] using ht
    rcases hs' with hsZ | hsV <;> rcases ht' with htZ | htV
    · exact False.elim (hst (hsZ.trans htZ.symm))
    · intro hEq
      exact hst (hsZ.trans (hEq.trans htV.symm))
    · intro hEq
      exact hst (hsV.trans (hEq.symm.trans htZ.symm))
    · exact False.elim (hst (hsV.trans htV.symm))
  have hpU : ({d.x, d.u} : Edge α) ∈ commonLink H V q := by
    rw [d.hbook]
    simp
  have huCard : ({d.x, d.u} : Edge α).card = 2 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hpU).1).2
  have hxu : d.x ≠ d.u := Finset.card_pair_eq_two_iff.mp huCard
  have hpRecip : ({d.z, d.v} : Edge α) ∈
      commonLink H V ({d.y, d.u} : Edge α) := by
    rw [d.hreciprocal]
    simp
  have hyu : d.y ≠ d.u := by
    obtain ⟨s, hs, t, ht, hst, _, _, _⟩ := (Finset.mem_filter.mp hpRecip).2
    have hs' : s = d.y ∨ s = d.u := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hs
    have ht' : t = d.y ∨ t = d.u := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using ht
    rcases hs' with hsY | hsU <;> rcases ht' with htY | htU
    · exact False.elim (hst (hsY.trans htY.symm))
    · intro hEq
      exact hst (hsY.trans (hEq.trans htU.symm))
    · intro hEq
      exact hst (hsU.trans (hEq.symm.trans htY.symm))
    · exact False.elim (hst (hsU.trans htU.symm))
  exact ⟨hqDistinct, hxy, hxu, hyu⟩

private theorem pair_disjoint_cross
    {a b c d : α} (h : Disjoint ({a, b} : Edge α) ({c, d} : Edge α)) :
    a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by
  have hdis := Finset.disjoint_left.mp h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro he
    subst c
    have hna : a ∉ ({a, d} : Edge α) := hdis (a := a) (by simp)
    exact hna (by simp)
  · intro he
    subst d
    have hna : a ∉ ({c, a} : Edge α) := hdis (a := a) (by simp)
    exact hna (by simp)
  · intro he
    subst c
    have hnb : b ∉ ({b, d} : Edge α) := hdis (a := b) (by simp)
    exact hnb (by simp)
  · intro he
    subst d
    have hnb : b ∉ ({c, b} : Edge α) := hdis (a := b) (by simp)
    exact hnb (by simp)

/-- All five named vertices of a concrete exceptional book are distinct. -/
theorem exceptionalReceiverBookData_five_distinct
    {H : Family α} {V q : Edge α}
    (d : ExceptionalReceiverBookData H V q) :
    d.z ≠ d.v ∧ d.z ≠ d.x ∧ d.z ≠ d.y ∧ d.z ≠ d.u ∧
    d.v ≠ d.x ∧ d.v ≠ d.y ∧ d.v ≠ d.u ∧
    d.x ≠ d.y ∧ d.x ≠ d.u ∧ d.y ≠ d.u := by
  obtain ⟨hzv, hxy, hxu, hyu⟩ := exceptionalReceiverBookData_distinct d
  have hxyLink : ({d.x, d.y} : Edge α) ∈ commonLink H V q := by
    rw [d.hbook]
    simp
  have hxuLink : ({d.x, d.u} : Edge α) ∈ commonLink H V q := by
    rw [d.hbook]
    simp
  have hxzRecip : ({d.x, d.z} : Edge α) ∈
      commonLink H V ({d.y, d.u} : Edge α) := by
    rw [d.hreciprocal]
    simp
  have hxvRecip : ({d.x, d.v} : Edge α) ∈
      commonLink H V ({d.y, d.u} : Edge α) := by
    rw [d.hreciprocal]
    simp
  obtain ⟨_, _, _, _, _, hbookXY, _, _⟩ := (Finset.mem_filter.mp hxyLink).2
  obtain ⟨_, _, _, _, _, hbookXU, _, _⟩ := (Finset.mem_filter.mp hxuLink).2
  obtain ⟨_, _, _, _, _, hrecipXZ, _, _⟩ := (Finset.mem_filter.mp hxzRecip).2
  obtain ⟨_, _, _, _, _, hrecipXV, _, _⟩ := (Finset.mem_filter.mp hxvRecip).2
  have hbookXY' : Disjoint ({d.x, d.y} : Edge α) ({d.z, d.v} : Edge α) := by
    simpa only [d.hq] using hbookXY
  have hbookXU' : Disjoint ({d.x, d.u} : Edge α) ({d.z, d.v} : Edge α) := by
    simpa only [d.hq] using hbookXU
  have hbxy := pair_disjoint_cross hbookXY'
  have hbxu := pair_disjoint_cross hbookXU'
  have hrxz := pair_disjoint_cross hrecipXZ
  have hrxv := pair_disjoint_cross hrecipXV
  exact ⟨hzv, hbxy.1.symm, hrxz.2.2.1, hrxz.2.2.2,
    hbxy.2.1.symm, hrxv.2.2.1, hrxv.2.2.2,
    hxy, hxu, hyu⟩

/-- If two distinct receiver pairs both lie in one bridge triple, the second
pair consists of the bridge page and one endpoint of the first pair. -/
theorem distinct_exceptional_pairs_in_bridge_triple
    {H : Family α} {V q₁ q₂ : Edge α}
    (d₁ : ExceptionalReceiverBookData H V q₁)
    (d₂ : ExceptionalReceiverBookData H V q₂)
    (hneq : q₁ ≠ q₂)
    (hsub : q₂ ⊆ ({d₁.z, d₁.v, d₁.y} : Edge α)) :
    ({d₂.z, d₂.v} : Edge α) = {d₁.z, d₁.y} ∨
      ({d₂.z, d₂.v} : Edge α) = {d₁.v, d₁.y} := by
  have hsub' : ({d₂.z, d₂.v} : Edge α) ⊆
      ({d₁.z, d₁.v, d₁.y} : Edge α) := by
    simpa only [d₂.hq] using hsub
  have hne : ({d₂.z, d₂.v} : Edge α) ≠ ({d₁.z, d₁.v} : Edge α) := by
    intro he
    apply hneq
    simpa only [d₁.hq, d₂.hq] using he.symm
  have hzv := (exceptionalReceiverBookData_distinct d₂).1
  exact pair_subset_triple_other_edge hzv hsub' hne

/-- Oriented endpoint alternatives for the two distinct receiver pairs in a
bridge triple. -/
theorem distinct_exceptional_pairs_oriented
    {H : Family α} {V q₁ q₂ : Edge α}
    (d₁ : ExceptionalReceiverBookData H V q₁)
    (d₂ : ExceptionalReceiverBookData H V q₂)
    (hneq : q₁ ≠ q₂)
    (hsub : q₂ ⊆ ({d₁.z, d₁.v, d₁.y} : Edge α)) :
    (d₂.z = d₁.z ∧ d₂.v = d₁.y) ∨
    (d₂.z = d₁.y ∧ d₂.v = d₁.z) ∨
    (d₂.z = d₁.v ∧ d₂.v = d₁.y) ∨
    (d₂.z = d₁.y ∧ d₂.v = d₁.v) := by
  have hzv := (exceptionalReceiverBookData_distinct d₂).1
  rcases distinct_exceptional_pairs_in_bridge_triple d₁ d₂ hneq hsub with hleft | hright
  · have hzy : d₁.z ≠ d₁.y := by
      intro heq
      have hcard := congrArg Finset.card hleft
      rw [heq] at hcard
      simp [Finset.card_pair hzv] at hcard
    rcases pair_eq_oriented hzy hleft with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have hvy : d₁.v ≠ d₁.y := by
      intro heq
      have hcard := congrArg Finset.card hright
      rw [heq] at hcard
      simp [Finset.card_pair hzv] at hcard
    rcases pair_eq_oriented hvy hright with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

theorem exceptionalReceiverBookData_cell_card
    {H : Family α} {V q : Edge α}
    (d : ExceptionalReceiverBookData H V q) :
    (commonLink H V q).card = 2 := by
  obtain ⟨_, hxy, hxu, hyu⟩ := exceptionalReceiverBookData_distinct d
  rw [d.hbook]
  apply Finset.card_pair
  intro he
  have hyMem : d.y ∈ ({d.x, d.u} : Edge α) := by
    rw [← he]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hyMem
  rcases hyMem with hyx | hyu'
  · exact hxy hyx.symm
  · exact hyu hyu'

theorem aligned_exceptional_data_gives_doubleBridgeBook
    {H : Family α} {V : Edge α} {a b c x u y v : α}
    (d₁ : ExceptionalReceiverBookData H V ({a, b} : Edge α))
    (d₂ : ExceptionalReceiverBookData H V ({a, c} : Edge α))
    (hz₁ : d₁.z = a) (hv₁ : d₁.v = b) (hx₁ : d₁.x = x)
    (hy₁ : d₁.y = c) (hu₁ : d₁.u = u)
    (hz₂ : d₂.z = a) (hv₂ : d₂.v = c) (hx₂ : d₂.x = y)
    (hy₂ : d₂.y = b) (hu₂ : d₂.u = v)
    (hab : a ≠ b) (hac : a ≠ c)
    (hcu : c ≠ u) :
    DoubleBridgeBook H V a b c x u y v := by
  have h₁ : commonLink H V ({a, b} : Edge α) =
      ({{x, c}, {x, u}} : Family α) := by
    rw [d₁.hbook]
    simp [hx₁, hy₁, hu₁]
  have h₂ : commonLink H V ({c, u} : Edge α) =
      ({{a, b}, {a, x}, {b, x}} : Family α) := by
    calc
      commonLink H V ({c, u} : Edge α) =
          commonLink H V ({d₁.y, d₁.u} : Edge α) := by simp [hy₁, hu₁]
      _ = ({{a, b}, {a, x}, {b, x}} : Family α) := by
        rw [d₁.hreciprocal]
        ext p
        simp [Finset.pair_comm, hz₁, hv₁, hx₁]; tauto
  have h₃ : commonLink H V ({a, c} : Edge α) =
      ({{y, b}, {y, v}} : Family α) := by
    rw [d₂.hbook]
    simp [hx₂, hy₂, hu₂]
  have h₄ : commonLink H V ({b, v} : Edge α) =
      ({{a, c}, {a, y}, {c, y}} : Family α) := by
    calc
      commonLink H V ({b, v} : Edge α) =
          commonLink H V ({d₂.y, d₂.u} : Edge α) := by simp [hy₂, hu₂]
      _ = ({{a, c}, {a, y}, {c, y}} : Family α) := by
        rw [d₂.hreciprocal]
        ext p
        simp [Finset.pair_comm, hz₂, hv₂, hx₂]; tauto
  have hab' : commonLink H V ({a, b} : Edge α) =
      orientedCommonLink H V b a := by
    calc
      commonLink H V ({a, b} : Edge α) = commonLink H V ({b, a} : Edge α) := by
        simp [Finset.pair_comm]
      _ = orientedCommonLink H V b a := commonLink_eq_oriented_of_ne H V hab.symm
  have hcu' : commonLink H V ({c, u} : Edge α) =
      orientedCommonLink H V c u := commonLink_eq_oriented_of_ne H V hcu
  have hac' : commonLink H V ({a, c} : Edge α) =
      orientedCommonLink H V c a := by
    calc
      commonLink H V ({a, c} : Edge α) = commonLink H V ({c, a} : Edge α) := by
        simp [Finset.pair_comm]
      _ = orientedCommonLink H V c a := commonLink_eq_oriented_of_ne H V hac.symm
  have hbv' : commonLink H V ({b, v} : Edge α) =
      orientedCommonLink H V b v := by
    have hne : b ≠ v := by
      have h := (exceptionalReceiverBookData_distinct d₂).2.2.2
      simpa [hy₂, hu₂] using h
    exact commonLink_eq_oriented_of_ne H V hne
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hab']
    exact h₁
  · rw [← hcu']
    simpa [Finset.pair_comm] using h₂
  · rw [← hac']
    exact h₃
  · rw [← hbv']
    exact h₄

/-- The aligned-book constructor derives endpoint inequalities directly from
the two exceptional data records. -/
theorem aligned_exceptional_data_gives_doubleBridgeBook_of_data
    {H : Family α} {V : Edge α} {a b c x u y v : α}
    (d₁ : ExceptionalReceiverBookData H V ({a, b} : Edge α))
    (d₂ : ExceptionalReceiverBookData H V ({a, c} : Edge α))
    (hz₁ : d₁.z = a) (hv₁ : d₁.v = b) (hx₁ : d₁.x = x)
    (hy₁ : d₁.y = c) (hu₁ : d₁.u = u)
    (hz₂ : d₂.z = a) (hv₂ : d₂.v = c) (hx₂ : d₂.x = y)
    (hy₂ : d₂.y = b) (hu₂ : d₂.u = v) :
    DoubleBridgeBook H V a b c x u y v := by
  have hab : a ≠ b := by
    simpa [hz₁, hv₁] using (exceptionalReceiverBookData_five_distinct d₁).1
  have hac : a ≠ c := by
    simpa [hz₂, hv₂] using (exceptionalReceiverBookData_five_distinct d₂).1
  have hcu : c ≠ u := by
    rcases exceptionalReceiverBookData_five_distinct d₁ with
      ⟨_, _, _, _, _, _, _, _, _, hyu⟩
    simpa [hy₁, hu₁] using hyu
  exact aligned_exceptional_data_gives_doubleBridgeBook d₁ d₂ hz₁ hv₁ hx₁
    hy₁ hu₁ hz₂ hv₂ hx₂ hy₂ hu₂ hab hac hcu

/-- General-index form of the aligned-book constructor. -/
theorem aligned_exceptional_data_gives_doubleBridgeBook_general
    {H : Family α} {V q₁ q₂ : Edge α} {a b c x u y v : α}
    (d₁ : ExceptionalReceiverBookData H V q₁)
    (d₂ : ExceptionalReceiverBookData H V q₂)
    (hq₁ : q₁ = ({a, b} : Edge α))
    (hq₂ : q₂ = ({a, c} : Edge α))
    (hz₁ : d₁.z = a) (hv₁ : d₁.v = b) (hx₁ : d₁.x = x)
    (hy₁ : d₁.y = c) (hu₁ : d₁.u = u)
    (hz₂ : d₂.z = a) (hv₂ : d₂.v = c) (hx₂ : d₂.x = y)
    (hy₂ : d₂.y = b) (hu₂ : d₂.u = v) :
    DoubleBridgeBook H V a b c x u y v := by
  have hab : a ≠ b := by
    simpa [hz₁, hv₁] using (exceptionalReceiverBookData_five_distinct d₁).1
  have hac : a ≠ c := by
    simpa [hz₂, hv₂] using (exceptionalReceiverBookData_five_distinct d₂).1
  have hcu : c ≠ u := by
    rcases exceptionalReceiverBookData_five_distinct d₁ with
      ⟨_, _, _, _, _, _, _, _, _, hyu⟩
    simpa [hy₁, hu₁] using hyu
  have h₁ : commonLink H V ({a, b} : Edge α) =
      ({{x, c}, {x, u}} : Family α) := by
    calc
      commonLink H V ({a, b} : Edge α) = commonLink H V q₁ := by rw [← hq₁]
      _ = ({{d₁.x, d₁.y}, {d₁.x, d₁.u}} : Family α) := d₁.hbook
      _ = ({{x, c}, {x, u}} : Family α) := by simp [hx₁, hy₁, hu₁]
  have h₂ : commonLink H V ({c, u} : Edge α) =
      ({{a, b}, {a, x}, {b, x}} : Family α) := by
    calc
      commonLink H V ({c, u} : Edge α) =
          commonLink H V ({d₁.y, d₁.u} : Edge α) := by simp [hy₁, hu₁]
      _ = ({{a, b}, {a, x}, {b, x}} : Family α) := by
        rw [d₁.hreciprocal]
        ext p
        simp [Finset.pair_comm, hz₁, hv₁, hx₁]; tauto
  have h₃ : commonLink H V ({a, c} : Edge α) =
      ({{y, b}, {y, v}} : Family α) := by
    calc
      commonLink H V ({a, c} : Edge α) = commonLink H V q₂ := by rw [← hq₂]
      _ = ({{d₂.x, d₂.y}, {d₂.x, d₂.u}} : Family α) := d₂.hbook
      _ = ({{y, b}, {y, v}} : Family α) := by simp [hx₂, hy₂, hu₂]
  have h₄ : commonLink H V ({b, v} : Edge α) =
      ({{a, c}, {a, y}, {c, y}} : Family α) := by
    calc
      commonLink H V ({b, v} : Edge α) =
          commonLink H V ({d₂.y, d₂.u} : Edge α) := by simp [hy₂, hu₂]
      _ = ({{a, c}, {a, y}, {c, y}} : Family α) := by
        rw [d₂.hreciprocal]
        ext p
        simp [Finset.pair_comm, hz₂, hv₂, hx₂]; tauto
  have hab' : commonLink H V ({a, b} : Edge α) =
      orientedCommonLink H V b a := by
    calc
      commonLink H V ({a, b} : Edge α) = commonLink H V ({b, a} : Edge α) := by
        simp [Finset.pair_comm]
      _ = orientedCommonLink H V b a := commonLink_eq_oriented_of_ne H V hab.symm
  have hcu' : commonLink H V ({c, u} : Edge α) =
      orientedCommonLink H V c u := commonLink_eq_oriented_of_ne H V hcu
  have hac' : commonLink H V ({a, c} : Edge α) =
      orientedCommonLink H V c a := by
    calc
      commonLink H V ({a, c} : Edge α) = commonLink H V ({c, a} : Edge α) := by
        simp [Finset.pair_comm]
      _ = orientedCommonLink H V c a := commonLink_eq_oriented_of_ne H V hac.symm
  have hbv' : commonLink H V ({b, v} : Edge α) =
    orientedCommonLink H V b v := by
    have hne : b ≠ v := by
      rcases exceptionalReceiverBookData_five_distinct d₂ with
        ⟨_, _, _, _, _, _, _, _, _, hne⟩
      simpa [hy₂, hu₂] using hne
    exact commonLink_eq_oriented_of_ne H V hne
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hab']
    exact h₁
  · rw [← hcu']
    simpa [Finset.pair_comm] using h₂
  · rw [← hac']
    exact h₃
  · rw [← hbv']
    exact h₄

theorem exceptionalReceiverBookData_charge_total
    {H : Family α} {V q : Edge α}
    (d : ExceptionalReceiverBookData H V q) :
    actualCellChargeForPair H V q = actualCellChargeTotal H V d.z d.v := by
  obtain ⟨hzv, _, _, _⟩ := exceptionalReceiverBookData_distinct d
  simpa only [d.hq] using actualCellChargeForPair_eq_displayed H V hzv

theorem exceptionalReceiverBookData_charge_two_cores
    {H : Family α} {V q : Edge α}
    (d : ExceptionalReceiverBookData H V q) :
    actualCellChargeTotal H V d.z d.v =
      (coreReceiverCharge H V d.z d.v ({d.x, d.y} : Edge α) +
        coreReceiverCharge H V d.v d.z ({d.x, d.y} : Edge α)) +
      (coreReceiverCharge H V d.z d.v ({d.x, d.u} : Edge α) +
        coreReceiverCharge H V d.v d.z ({d.x, d.u} : Edge α)) := by
  obtain ⟨_, hxy, hxu, hyu⟩ := exceptionalReceiverBookData_distinct d
  have hp₁ : ({d.x, d.y} : Edge α) ∈ commonLink H V q := by
    rw [d.hbook]
    simp
  have hp₂ : ({d.x, d.u} : Edge α) ∈ commonLink H V q := by
    rw [d.hbook]
    simp
  have hpNe : ({d.x, d.y} : Edge α) ≠ ({d.x, d.u} : Edge α) := by
    intro he
    have hyMem : d.y ∈ ({d.x, d.u} : Edge α) := by
      rw [← he]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hyMem
    rcases hyMem with hyx | hyu'
    · exact hxy hyx.symm
    · exact hyu hyu'
  have hp₁' : ({d.x, d.y} : Edge α) ∈
      commonLink H V ({d.z, d.v} : Edge α) := by
    simpa only [d.hq] using hp₁
  have hp₂' : ({d.x, d.u} : Edge α) ∈
      commonLink H V ({d.z, d.v} : Edge α) := by
    simpa only [d.hq] using hp₂
  have hcard' : (commonLink H V ({d.z, d.v} : Edge α)).card = 2 := by
    simpa only [d.hq] using exceptionalReceiverBookData_cell_card d
  exact actual_cell_charge_total_eq_two_cores H V hp₁' hp₂' hpNe hcard'

theorem exceptionalReceiverBookData_charge_four_sources
    {H : Family α} {V q : Edge α}
    (d : ExceptionalReceiverBookData H V q) :
    actualCellChargeForPair H V q =
      (actualReceiverCharge H V d.z d.x d.y d.v +
        actualReceiverCharge H V d.v d.x d.y d.z) +
      (actualReceiverCharge H V d.z d.x d.u d.v +
        actualReceiverCharge H V d.v d.x d.u d.z) := by
  rw [exceptionalReceiverBookData_charge_total,
    exceptionalReceiverBookData_charge_two_cores]
  obtain ⟨_, hxy, hxu, _⟩ := exceptionalReceiverBookData_distinct d
  have h₁ := coreReceiverCharge_eq_displayed_pair H V
    ({d.x, d.y} : Edge α) d.z d.v d.x d.y (Finset.card_pair hxy) rfl
  have h₂ := coreReceiverCharge_eq_displayed_pair H V
    ({d.x, d.y} : Edge α) d.v d.z d.x d.y (Finset.card_pair hxy) rfl
  have h₃ := coreReceiverCharge_eq_displayed_pair H V
    ({d.x, d.u} : Edge α) d.z d.v d.x d.u (Finset.card_pair hxu) rfl
  have h₄ := coreReceiverCharge_eq_displayed_pair H V
    ({d.x, d.u} : Edge α) d.v d.z d.x d.u (Finset.card_pair hxu) rfl
  rw [h₁, h₂, h₃, h₄]

/-- Positive bridge demand can only be indexed by one of the two triples
in its selected exceptional book. -/
theorem bridgeDemand_pos_cases
    (H : Family α) (V : Edge α) (q E : Edge α)
    (hpos : 0 < bridgeDemand H V q E) :
    ∃ d : ExceptionalReceiverBookData H V q,
      E = ({d.z, d.v, d.y} : Edge α) ∨ E = ({d.z, d.v, d.u} : Edge α) := by
  classical
  by_cases hq : triangleExceptionalReceiverCell H V q
  · let d := canonicalExceptionalReceiverBookData H V q hq
    simp only [bridgeDemand, dite_eq_left hq] at hpos
    change 0 < (if E = ({d.z, d.v, d.y} : Edge α) then
      min (actualReceiverCharge H V d.z d.x d.y d.v)
        (actualReceiverCharge H V d.v d.x d.y d.z)
      else if E = ({d.z, d.v, d.u} : Edge α) then
        min (actualReceiverCharge H V d.z d.x d.u d.v)
          (actualReceiverCharge H V d.v d.x d.u d.z)
      else 0) at hpos
    by_cases hy : E = ({d.z, d.v, d.y} : Edge α)
    · exact ⟨d, Or.inl hy⟩
    · by_cases hu : E = ({d.z, d.v, d.u} : Edge α)
      · exact ⟨d, Or.inr hu⟩
      · simp [hy, hu] at hpos
  · simp [bridgeDemand, hq] at hpos

/-- A positive demand is indexed by a receiver pair contained in its bridge
triple. -/
theorem bridgeDemand_pos_pair_subset
    (H : Family α) (V : Edge α) (q E : Edge α)
    (hpos : 0 < bridgeDemand H V q E) : q ⊆ E := by
  obtain ⟨d, hE | hE⟩ := bridgeDemand_pos_cases H V q E hpos
  · rw [d.hq, hE]
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht ⊢
    rcases ht with rfl | rfl <;> simp
  · rw [d.hq, hE]
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht ⊢
    rcases ht with rfl | rfl <;> simp

/-- A positive bridge demand certifies positivity of both directed source
charges that form its minimum. -/
theorem bridgeDemand_pos_sources
    (H : Family α) (V : Edge α) (q E : Edge α)
    (hpos : 0 < bridgeDemand H V q E) :
    ∃ d : ExceptionalReceiverBookData H V q,
      (E = ({d.z, d.v, d.y} : Edge α) ∧
        0 < actualReceiverCharge H V d.z d.x d.y d.v ∧
        0 < actualReceiverCharge H V d.v d.x d.y d.z) ∨
      (E = ({d.z, d.v, d.u} : Edge α) ∧
        0 < actualReceiverCharge H V d.z d.x d.u d.v ∧
        0 < actualReceiverCharge H V d.v d.x d.u d.z) := by
  classical
  by_cases hq : triangleExceptionalReceiverCell H V q
  · let d := canonicalExceptionalReceiverBookData H V q hq
    simp only [bridgeDemand, dite_eq_left hq] at hpos
    change 0 < (if E = ({d.z, d.v, d.y} : Edge α) then
      min (actualReceiverCharge H V d.z d.x d.y d.v)
        (actualReceiverCharge H V d.v d.x d.y d.z)
      else if E = ({d.z, d.v, d.u} : Edge α) then
        min (actualReceiverCharge H V d.z d.x d.u d.v)
          (actualReceiverCharge H V d.v d.x d.u d.z)
      else 0) at hpos
    by_cases hy : E = ({d.z, d.v, d.y} : Edge α)
    · rw [ite_eq_left hy] at hpos
      exact ⟨d, Or.inl ⟨hy, (lt_min_iff.mp hpos).1,
        (lt_min_iff.mp hpos).2⟩⟩
    · by_cases hu : E = ({d.z, d.v, d.u} : Edge α)
      · rw [ite_eq_right hy, ite_eq_left hu] at hpos
        exact ⟨d, Or.inr ⟨hu, (lt_min_iff.mp hpos).1,
          (lt_min_iff.mp hpos).2⟩⟩
      · rw [ite_eq_right hy, ite_eq_right hu] at hpos
        norm_num at hpos
  · simp [bridgeDemand, hq] at hpos

/-- A positive actual receiver charge comes from a positive rooted source. -/
theorem actualReceiverCharge_pos_rootedWeight
    (H : Family α) (V : Edge α) (z x y v : α)
    (hpos : 0 < actualReceiverCharge H V z x y v) :
    0 < positiveRootedWeight H V z x y := by
  classical
  let N := completionVertices H V ({x, y} : Edge α)
  have hv : v ∈ N.erase z := by
    by_contra hvNot
    simp [actualReceiverCharge, N, hvNot] at hpos
  have hvN : v ∈ N := (Finset.mem_erase.mp hv).2
  have hcardPos : 0 < N.card := Finset.card_pos.mpr ⟨v, hvN⟩
  have hdegree : 2 ≤ N.card := by
    by_contra h
    have hcardOne : N.card = 1 := by omega
    have hzero : actualReceiverCharge H V z x y v = 0 := by
      simp [actualReceiverCharge, chargePerOtherCompletion, hv, N, hcardOne]
    rw [hzero] at hpos
    norm_num at hpos
  have hden : 0 < (N.card : ℚ) - 1 := by
    have hcast : (2 : ℚ) ≤ N.card := by exact_mod_cast hdegree
    linarith
  have hw : 0 < positiveRootedWeight H V z x y := by
    apply (div_pos_iff_of_pos_right hden).mp
    simpa [actualReceiverCharge, chargePerOtherCompletion, hv, N] using hpos
  exact hw

/-- Positivity of the positive part forces positivity of the signed weight. -/
theorem actualReceiverCharge_pos_signedWeight
    (H : Family α) (V : Edge α) (z x y v : α)
    (hpos : 0 < actualReceiverCharge H V z x y v) :
    0 < rootedSignedWeight H V z x y := by
  have hw := actualReceiverCharge_pos_rootedWeight H V z x y v hpos
  simpa [positiveRootedWeight, max_eq_left (le_of_lt hw)] using hw

/-- Positive bridge demand supplies the two positive signed rooted sources
on its bridge edge. -/
theorem bridgeDemand_pos_signed_sources
    (H : Family α) (V : Edge α) (q E : Edge α)
    (hpos : 0 < bridgeDemand H V q E) :
    ∃ d : ExceptionalReceiverBookData H V q,
      (E = ({d.z, d.v, d.y} : Edge α) ∧
        0 < rootedSignedWeight H V d.z d.x d.y ∧
        0 < rootedSignedWeight H V d.v d.x d.y) ∨
      (E = ({d.z, d.v, d.u} : Edge α) ∧
        0 < rootedSignedWeight H V d.z d.x d.u ∧
        0 < rootedSignedWeight H V d.v d.x d.u) := by
  obtain ⟨d, hcases⟩ := bridgeDemand_pos_sources H V q E hpos
  rcases hcases with ⟨hE, hz, hv⟩ | ⟨hE, hz, hv⟩
  · exact ⟨d, Or.inl ⟨hE,
      actualReceiverCharge_pos_signedWeight H V _ _ _ _ hz,
      actualReceiverCharge_pos_signedWeight H V _ _ _ _ hv⟩⟩
  · exact ⟨d, Or.inr ⟨hE,
      actualReceiverCharge_pos_signedWeight H V _ _ _ _ hz,
      actualReceiverCharge_pos_signedWeight H V _ _ _ _ hv⟩⟩

/-- Normalize a positive demand so that its bridge page is the `y` field. -/
theorem bridgeDemand_pos_normalized_sources
    (H : Family α) (V : Edge α) (q E : Edge α)
    (hpos : 0 < bridgeDemand H V q E) :
    ∃ d : ExceptionalReceiverBookData H V q,
      E = ({d.z, d.v, d.y} : Edge α) ∧
        0 < rootedSignedWeight H V d.z d.x d.y ∧
        0 < rootedSignedWeight H V d.v d.x d.y := by
  obtain ⟨d, hcases⟩ := bridgeDemand_pos_signed_sources H V q E hpos
  rcases hcases with ⟨hE, hz, hv⟩ | ⟨hE, hz, hv⟩
  · exact ⟨d, hE, hz, hv⟩
  · refine ⟨swapExceptionalReceiverBookPages d, ?_, ?_, ?_⟩
    · simpa [swapExceptionalReceiverBookPages] using hE
    · simpa [swapExceptionalReceiverBookPages] using hz
    · simpa [swapExceptionalReceiverBookPages] using hv

/-- Two distinct positive demands into the same triple reduce to the two
orientations of distinct two-point subsets of the first exceptional triple. -/
theorem two_positive_bridge_demands_oriented
    (H : Family α) (V : Edge α) (q₁ q₂ E : Edge α)
    (hpos₁ : 0 < bridgeDemand H V q₁ E)
    (hpos₂ : 0 < bridgeDemand H V q₂ E)
    (hneq : q₁ ≠ q₂) :
    ∃ d₁ : ExceptionalReceiverBookData H V q₁,
    ∃ d₂ : ExceptionalReceiverBookData H V q₂,
      E = ({d₁.z, d₁.v, d₁.y} : Edge α) ∧
      E = ({d₂.z, d₂.v, d₂.y} : Edge α) ∧
      0 < rootedSignedWeight H V d₁.z d₁.x d₁.y ∧
      0 < rootedSignedWeight H V d₁.v d₁.x d₁.y ∧
      0 < rootedSignedWeight H V d₂.z d₂.x d₂.y ∧
      0 < rootedSignedWeight H V d₂.v d₂.x d₂.y ∧
      ((d₂.z = d₁.z ∧ d₂.v = d₁.y) ∨
       (d₂.z = d₁.y ∧ d₂.v = d₁.z) ∨
       (d₂.z = d₁.v ∧ d₂.v = d₁.y) ∨
       (d₂.z = d₁.y ∧ d₂.v = d₁.v)) := by
  obtain ⟨d₁, hE₁, h₁z, h₁v⟩ :=
    bridgeDemand_pos_normalized_sources H V q₁ E hpos₁
  obtain ⟨d₂, hE₂, h₂z, h₂v⟩ :=
    bridgeDemand_pos_normalized_sources H V q₂ E hpos₂
  have htriple : ({d₂.z, d₂.v, d₂.y} : Edge α) =
      {d₁.z, d₁.v, d₁.y} := hE₂.symm.trans hE₁
  have hsub' : ({d₂.z, d₂.v} : Edge α) ⊆
      ({d₁.z, d₁.v, d₁.y} : Edge α) := by
    rw [← htriple]
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht ⊢
    rcases ht with h | h <;> simp [h]
  have hsub : q₂ ⊆ ({d₁.z, d₁.v, d₁.y} : Edge α) := by
    simpa only [d₂.hq] using hsub'
  have hOrient := distinct_exceptional_pairs_oriented d₁ d₂ hneq hsub
  exact ⟨d₁, d₂, hE₁, hE₂, h₁z, h₁v, h₂z, h₂v, hOrient⟩

private theorem missing_vertex_of_triple_eq
    {a b c d e f : α}
    (hab : a ≠ b) (hbc : b ≠ c)
    (hda : d = a) (hec : e = c)
    (htriple : ({a, b, c} : Edge α) = {d, e, f}) : f = b := by
  have hb : b ∈ ({d, e, f} : Edge α) := by rw [← htriple]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with hbd | hbe | hbf
  · exact False.elim (hab (hda.symm.trans hbd.symm))
  · exact False.elim (hbc (hbe.trans hec))
  · exact hbf.symm

private theorem triple_swap_first_two (a b c : α) :
    ({b, a, c} : Edge α) = {a, b, c} := by
  ext t
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- Orient two distinct positive receiver pairs as the first two sides of
one bridge triangle, with the bridge pages aligned as well. -/
theorem two_positive_bridge_demands_aligned
    (H : Family α) (V : Edge α) (q₁ q₂ E : Edge α)
    (hpos₁ : 0 < bridgeDemand H V q₁ E)
    (hpos₂ : 0 < bridgeDemand H V q₂ E)
    (hneq : q₁ ≠ q₂) :
    ∃ d₁ : ExceptionalReceiverBookData H V q₁,
    ∃ d₂ : ExceptionalReceiverBookData H V q₂,
      d₁.z = d₂.z ∧ d₁.y = d₂.v ∧ d₁.v = d₂.y ∧
      0 < rootedSignedWeight H V d₁.z d₁.x d₁.y ∧
      0 < rootedSignedWeight H V d₁.v d₁.x d₁.y ∧
      0 < rootedSignedWeight H V d₂.z d₂.x d₂.y ∧
      0 < rootedSignedWeight H V d₂.v d₂.x d₂.y := by
  obtain ⟨d₁, d₂, hE₁, hE₂, h₁z, h₁v, h₂z, h₂v, hOrient⟩ :=
    two_positive_bridge_demands_oriented H V q₁ q₂ E hpos₁ hpos₂ hneq
  rcases hOrient with h₁ | h₂ | h₃ | h₄
  · rcases exceptionalReceiverBookData_five_distinct d₁ with
      ⟨hab, _, _, _, _, hbc, _, _, _, _⟩
    have hmiss := missing_vertex_of_triple_eq hab hbc h₁.1 h₁.2
      (hE₁.symm.trans hE₂)
    exact ⟨d₁, d₂, h₁.1.symm, h₁.2.symm, hmiss.symm,
      h₁z, h₁v, h₂z, h₂v⟩
  · let e₂ := reverseExceptionalReceiverBookData d₂
    have he₂ : E = ({e₂.z, e₂.v, e₂.y} : Edge α) := by
      calc
        E = ({d₂.z, d₂.v, d₂.y} : Edge α) := hE₂
        _ = ({d₂.v, d₂.z, d₂.y} : Edge α) :=
          (triple_swap_first_two d₂.z d₂.v d₂.y).symm
    have hda : e₂.z = d₁.z := by
      simpa [e₂, reverseExceptionalReceiverBookData] using h₂.2
    have hec : e₂.v = d₁.y := by
      simpa [e₂, reverseExceptionalReceiverBookData] using h₂.1
    rcases exceptionalReceiverBookData_five_distinct d₁ with
      ⟨hab, _, _, _, _, hbc, _, _, _, _⟩
    have hmiss := missing_vertex_of_triple_eq hab hbc hda hec
      (hE₁.symm.trans he₂)
    exact ⟨d₁, e₂, hda.symm, hec.symm, hmiss.symm,
      h₁z, h₁v, h₂v, h₂z⟩
  · let e₁ := reverseExceptionalReceiverBookData d₁
    have he₁ : E = ({e₁.z, e₁.v, e₁.y} : Edge α) := by
      calc
        E = ({d₁.z, d₁.v, d₁.y} : Edge α) := hE₁
        _ = ({d₁.v, d₁.z, d₁.y} : Edge α) :=
          (triple_swap_first_two d₁.z d₁.v d₁.y).symm
    have hda : d₂.z = e₁.z := by
      simpa [e₁, reverseExceptionalReceiverBookData] using h₃.1
    have hec : d₂.v = e₁.y := by
      simpa [e₁, reverseExceptionalReceiverBookData] using h₃.2
    rcases exceptionalReceiverBookData_five_distinct d₁ with
      ⟨hab, _, hAc, _, _, _, _, _, _, _⟩
    have hmiss := missing_vertex_of_triple_eq hab.symm hAc hda hec
      (he₁.symm.trans hE₂)
    exact ⟨e₁, d₂, hda.symm, hec.symm, hmiss.symm,
      h₁v, h₁z, h₂z, h₂v⟩
  · let e₁ := reverseExceptionalReceiverBookData d₁
    let e₂ := reverseExceptionalReceiverBookData d₂
    have he₁ : E = ({e₁.z, e₁.v, e₁.y} : Edge α) := by
      calc
        E = ({d₁.z, d₁.v, d₁.y} : Edge α) := hE₁
        _ = ({d₁.v, d₁.z, d₁.y} : Edge α) :=
          (triple_swap_first_two d₁.z d₁.v d₁.y).symm
    have he₂ : E = ({e₂.z, e₂.v, e₂.y} : Edge α) := by
      calc
        E = ({d₂.z, d₂.v, d₂.y} : Edge α) := hE₂
        _ = ({d₂.v, d₂.z, d₂.y} : Edge α) :=
          (triple_swap_first_two d₂.z d₂.v d₂.y).symm
    have hda : e₂.z = e₁.z := by
      simpa [e₁, e₂, reverseExceptionalReceiverBookData] using h₄.2
    have hec : e₂.v = e₁.y := by
      simpa [e₁, e₂, reverseExceptionalReceiverBookData] using h₄.1
    rcases exceptionalReceiverBookData_five_distinct d₁ with
      ⟨hab, _, hAc, _, _, _, _, _, _, _⟩
    have hmiss := missing_vertex_of_triple_eq hab.symm hAc hda hec
      (he₁.symm.trans he₂)
    exact ⟨e₁, e₂, hda.symm, hec.symm, hmiss.symm,
      h₁v, h₁z, h₂v, h₂z⟩

/-- Two positive demands on one triple provide a double bridge book. -/
theorem two_positive_bridge_demands_give_book
    (H : Family α) (V : Edge α) (q₁ q₂ E : Edge α)
    (hpos₁ : 0 < bridgeDemand H V q₁ E)
    (hpos₂ : 0 < bridgeDemand H V q₂ E)
    (hneq : q₁ ≠ q₂) :
    ∃ d₁ : ExceptionalReceiverBookData H V q₁,
    ∃ d₂ : ExceptionalReceiverBookData H V q₂,
      DoubleBridgeBook H V d₁.z d₁.v d₁.y d₁.x d₁.u d₂.x d₂.u ∧
      d₁.z = d₂.z ∧ d₁.y = d₂.v ∧ d₁.v = d₂.y ∧
      0 < rootedSignedWeight H V d₁.v d₁.x d₁.y ∧
      0 < rootedSignedWeight H V d₂.v d₂.x d₂.y := by
  obtain ⟨d₁, d₂, hza, hyc, hbc, h₁z, h₁v, h₂z, h₂v⟩ :=
    two_positive_bridge_demands_aligned H V q₁ q₂ E hpos₁ hpos₂ hneq
  have hq₂ : q₂ = ({d₁.z, d₁.y} : Edge α) := by
    calc
      q₂ = ({d₂.z, d₂.v} : Edge α) := d₂.hq
      _ = ({d₁.z, d₁.y} : Edge α) := by simp [hza, hyc]
  have hBook := aligned_exceptional_data_gives_doubleBridgeBook_general
    d₁ d₂ d₁.hq hq₂ rfl rfl rfl rfl rfl hza.symm hyc.symm rfl hbc.symm rfl
  exact ⟨d₁, d₂, hBook, hza, hyc, hbc, h₁v, h₂v⟩

/-- The two-book obstruction rules out distinct positive demands to one
triple whenever nine- and ten-triple five-sets are absent. -/
theorem positive_bridge_demands_no_overlap
    {H : Family α} {V : Edge α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hNoBlock : NoNineOrTenTripleBlock H)
    {q₁ q₂ E : Edge α}
    (hpos₁ : 0 < bridgeDemand H V q₁ E)
    (hpos₂ : 0 < bridgeDemand H V q₂ E)
    (hneq : q₁ ≠ q₂) : False := by
  obtain ⟨d₁, d₂, hBook, hza, hpage, hbcAlign, hposB, hposC⟩ :=
    two_positive_bridge_demands_give_book H V q₁ q₂ E hpos₁ hpos₂ hneq
  rcases exceptionalReceiverBookData_five_distinct d₁ with
    ⟨hab, hax, hac, hau, hbx, hbc, hbu, hcx', hxu, hcu⟩
  have hcx : d₁.y ≠ d₁.x := hcx'.symm
  rcases exceptionalReceiverBookData_five_distinct d₂ with
    ⟨_, hzx, _, hzu, hvx, _, hvu, hxy, hxu₂, hyu⟩
  have hya : d₂.x ≠ d₂.z := hzx.symm
  have hva : d₂.u ≠ d₂.z := hzu.symm
  have hyb : d₂.x ≠ d₂.y := hxy
  have hyc : d₂.x ≠ d₂.v := hvx.symm
  have hvb : d₂.u ≠ d₂.y := hyu.symm
  have hvc : d₂.u ≠ d₂.v := hvu.symm
  have hyv : d₂.x ≠ d₂.u := hxu₂
  have hposC' : 0 < rootedSignedWeight H V d₁.y d₂.x d₁.v := by
    simpa only [← hpage, ← hbcAlign] using hposC
  have hya' : d₂.x ≠ d₁.z := by
    intro he
    exact hya (he.trans hza)
  have hyc' : d₂.x ≠ d₁.y := by
    intro he
    exact hyc (he.trans hpage)
  have hva' : d₂.u ≠ d₁.z := by
    intro he
    exact hva (he.trans hza)
  have hyb' : d₂.x ≠ d₁.v := by
    intro he
    exact hyb (he.trans hbcAlign)
  have hvb' : d₂.u ≠ d₁.v := by
    intro he
    exact hvb (he.trans hbcAlign)
  have hvc' : d₂.u ≠ d₁.y := by
    intro he
    exact hvc (he.trans hpage)
  exact double_bridge_books_do_not_overlap hH hUniform hNoBlock hBook
    d₁.hzV d₁.hvV d₁.hyV d₁.hxV d₁.huV d₂.hxV d₂.huV
    hab hac hbc hax hbx hcx hau hbu hcu hxu
    hya' hyb' hyc' hva' hvb' hvc' hyv hposB hposC'

/-- At most one receiver pair can send positive bridge demand to any one
triple. This is the exact finite uniqueness interface used in (II.11). -/
theorem positive_bridge_demand_unique
    {H : Family α} {V : Edge α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hNoBlock : NoNineOrTenTripleBlock H)
    (E : Edge α) (_hE : E ∈ H)
    (q₁ q₂ : Edge α) (_hq₁ : q₁ ∈ usedCells H V)
    (_hq₂ : q₂ ∈ usedCells H V)
    (hpos₁ : 0 < bridgeDemand H V q₁ E)
    (hpos₂ : 0 < bridgeDemand H V q₂ E) : q₁ = q₂ := by
  by_contra hneq
  exact False.elim (positive_bridge_demands_no_overlap hH hUniform hNoBlock
    hpos₁ hpos₂ hneq)

/-- Total of the bridge demands allocated to a fixed triple. -/
noncomputable def bridgeDemandOnTriple
    (H : Family α) (V : Edge α) (E : Edge α) : ℚ := by
  classical
  exact ∑ q ∈ usedCells H V, bridgeDemand H V q E

/-- Total bridge demand over all triples. -/
noncomputable def bridgeDemandTotal (H : Family α) (V : Edge α) : ℚ := by
  classical
  exact ∑ E ∈ H, bridgeDemandOnTriple H V E

/-- Flattening the triple-indexed demand total. -/
theorem bridgeDemandTotal_eq_double_sum (H : Family α) (V : Edge α) :
    bridgeDemandTotal H V =
      ∑ E ∈ H, ∑ q ∈ usedCells H V, bridgeDemand H V q E := by
  rfl

end JSP523.Rank3
