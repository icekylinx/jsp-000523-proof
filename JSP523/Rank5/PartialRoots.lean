import JSP523.Basic
import Lean.Elab.Tactic.Omega

/-!
# Finite partial-center compatibility

These lemmas give the formal interface for the partial functional-root theorem
used in rank five.  Root existence for every compatible map on a domain
missing at most one vertex remains a separate theorem to formalize.  Here we
prove uniqueness, the easy compatibility direction, and the first local
restriction obtained from an arrow.
-/

namespace JSP523.Rank5

section PartialRoots

variable {α : Type*} [DecidableEq α]

/-- The cross-face compatibility condition on a possibly partial domain. -/
def PartialCompatible (U : Finset α) (f : α → α) : Prop :=
  ∀ ⦃a b : α⦄, a ∈ U → b ∈ U → a ≠ b →
    f a ≠ b → f b ≠ a → f a = f b

/-- A candidate root receives every arrow except possibly its own. -/
def IsPartialRoot (U : Finset α) (f : α → α) (v : α) : Prop :=
  ∀ a ∈ U, a ≠ v → f a = v

/-- A domain with at least three elements has at most one candidate root. -/
theorem partial_root_unique
    {U : Finset α} {f : α → α} {v w : α}
    (hcard : 3 ≤ U.card)
    (hv : IsPartialRoot U f v) (hw : IsPartialRoot U f w) :
    v = w := by
  by_contra hvw
  have hsub : U ⊆ ({v, w} : Finset α) := by
    intro a ha
    by_contra han
    have hav : a ≠ v := by
      intro heq
      apply han
      simp [heq]
    have haw : a ≠ w := by
      intro heq
      apply han
      simp [heq]
    have hfv : f a = v := hv a ha hav
    have hfw : f a = w := hw a ha haw
    exact hvw (hfv.symm.trans hfw)
  have hpair : ({v, w} : Finset α).card = 2 := Finset.card_pair hvw
  have hbound : U.card ≤ 2 := (Finset.card_le_card hsub).trans (le_of_eq hpair)
  omega

/-- A candidate root automatically satisfies the cross-face compatibility
    implication.  The converse existence statement is the hard part. -/
theorem partial_root_compatible
    {U : Finset α} {f : α → α} {v : α}
    (hroot : IsPartialRoot U f v) :
    PartialCompatible U f := by
  intro a b ha hb hab hfab hfba
  by_cases hav : a = v
  · subst a
    have hbv : b ≠ v := Ne.symm hab
    exact False.elim (hfba (hroot b hb hbv))
  · by_cases hbv : b = v
    · subst b
      exact False.elim (hfab (hroot a ha hav))
    · exact (hroot a ha hav).trans (hroot b hb hbv).symm

/-- If `f a = b`, every third domain point maps to `a` or to `b`.
    This is the elementary arrow restriction used in the two-cycle case. -/
theorem compatible_arrow_range
    {U : Finset α} {f : α → α} {a b x : α}
    (hcomp : PartialCompatible U f)
    (ha : a ∈ U) (hx : x ∈ U)
    (hxa : x ≠ a) (hxb : x ≠ b)
    (hab : f a = b) :
    f x = a ∨ f x = b := by
  by_cases h : f x = a
  · exact Or.inl h
  · right
    have hax : a ≠ x := Ne.symm hxa
    have hbx : f a ≠ x := by simpa [hab] using (Ne.symm hxb)
    have heq : f a = f x := hcomp ha hx hax hbx h
    exact heq.symm.trans hab

/-- One branch of root existence: an internal arrow followed by the unique
    point outside the domain forces its middle vertex to be a root. -/
theorem root_of_arrow_to_external
    {U : Finset α} {f : α → α} {a b w : α}
    (hcomp : PartialCompatible U f)
    (ha : a ∈ U) (hb : b ∈ U)
    (hab : a ≠ b)
    (hfa : f a = b) (hfb : f b = w)
    (hw : w ∉ U) :
    IsPartialRoot U f b := by
  intro x hx hxb
  by_cases hxa : x = a
  · subst x
    exact hfa
  · rcases compatible_arrow_range hcomp ha hx hxa hxb hfa with hfxa | hfxb
    · have hwx : w ≠ x := by
        intro heq
        apply hw
        rw [heq]
        exact hx
      have hbw : f b ≠ x := by simpa [hfb] using hwx
      have hfxb : f x ≠ b := by simpa [hfxa] using hab
      have heq : f b = f x := hcomp hb hx (Ne.symm hxb) hbw hfxb
      have hwa : w = a := by
        calc
          w = f b := hfb.symm
          _ = f x := heq
          _ = a := hfxa
      have hwu : w ∈ U := by rw [hwa]; exact ha
      exact False.elim (hw hwu)
    · exact hfxb

/-- The second finite branch: once a two-cycle has one further domain point,
    one of the two cycle vertices receives every arrow from the others. -/
theorem root_of_two_cycle
    {U : Finset α} {f : α → α} {a b c : α}
    (hcomp : PartialCompatible U f)
    (ha : a ∈ U) (hb : b ∈ U) (hc : c ∈ U)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hfa : f a = b) (hfb : f b = a) :
    IsPartialRoot U f a ∨ IsPartialRoot U f b := by
  rcases compatible_arrow_range hcomp ha hc hca hcb hfa with hfcA | hfcB
  · left
    intro u hu hua
    by_cases hub : u = b
    · subst u
      exact hfb
    · rcases compatible_arrow_range hcomp ha hu hua hub hfa with hfuA | hfuB
      · exact hfuA
      · have huc : u ≠ c := by
          intro heq
          subst u
          exact hab (hfcA.symm.trans hfuB)
        have hfcu : f c ≠ u := by simpa [hfcA] using (Ne.symm hua)
        have hfuc : f u ≠ c := by simpa [hfuB] using (Ne.symm hcb)
        have heq : f c = f u := hcomp hc hu (Ne.symm huc) hfcu hfuc
        have hbad : a = b := (hfcA.symm.trans heq).trans hfuB
        exact False.elim (hab hbad)
  · right
    intro u hu hub
    by_cases hua : u = a
    · subst u
      exact hfa
    · rcases compatible_arrow_range hcomp hb hu hub hua hfb with hfuB | hfuA
      · exact hfuB
      · have huc : u ≠ c := by
          intro heq
          subst u
          exact hab (hfuA.symm.trans hfcB)
        have hfcu : f c ≠ u := by simpa [hfcB] using (Ne.symm hub)
        have hfuc : f u ≠ c := by simpa [hfuA] using (Ne.symm hca)
        have heq : f c = f u := hcomp hc hu (Ne.symm huc) hfcu hfuc
        have hbad : b = a := (hfcB.symm.trans heq).trans hfuA
        exact False.elim (hab hbad.symm)

/-- A directed three-cycle cannot survive an additional domain vertex. -/
theorem no_three_cycle_with_fourth
    {U : Finset α} {f : α → α} {a b c d : α}
    (hcomp : PartialCompatible U f)
    (ha : a ∈ U) (hb : b ∈ U) (hc : c ∈ U) (hd : d ∈ U)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (hda : d ≠ a) (hdb : d ≠ b) (hdc : d ≠ c)
    (hfa : f a = b) (hfb : f b = c) (hfc : f c = a) :
    False := by
  have h₁ := compatible_arrow_range hcomp ha hd hda hdb hfa
  have h₂ := compatible_arrow_range hcomp hb hd hdb hdc hfb
  have h₃ := compatible_arrow_range hcomp hc hd hdc hda hfc
  have hfd : f d = b := by
    rcases h₁ with hfdA | hfdB
    · rcases h₂ with hfdB | hfdC
      · exact False.elim (hab (hfdA.symm.trans hfdB))
      · exact False.elim (hca (hfdC.symm.trans hfdA))
    · exact hfdB
  rcases h₃ with hfdC | hfdA
  · exact hbc (hfd.symm.trans hfdC)
  · exact hab ((hfd.symm.trans hfdA).symm)

end PartialRoots

end JSP523.Rank5
