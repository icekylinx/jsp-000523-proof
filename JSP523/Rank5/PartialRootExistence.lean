import JSP523.Rank5.PartialRoots
import Lean.Elab.Tactic.Omega

/-!
# Existence of a partial functional root

Compatibility and the absence of fixed points force a root on every domain
with at least four elements.  The proof allows the function to take values
outside the domain, without requiring a bound on the number of such values.
The ambient-set corollary records the precise interface used in the
high-rank center-completion argument.
-/

namespace JSP523.Rank5

section RootExistence

variable {α : Type*} [DecidableEq α]

private theorem exists_outside_pair
    {U : Finset α} (hcard : 3 ≤ U.card) (a b : α) :
    ∃ c ∈ U, c ≠ a ∧ c ≠ b := by
  by_contra h
  have hsub : U ⊆ ({a, b} : Finset α) := by
    intro c hc
    by_contra hnot
    have hca : c ≠ a := by
      intro heq
      apply hnot
      simp [heq]
    have hcb : c ≠ b := by
      intro heq
      apply hnot
      simp [heq]
    exact h ⟨c, hc, hca, hcb⟩
  have hbound := Finset.card_le_card hsub
  have hpair : ({a, b} : Finset α).card ≤ 2 := Finset.card_le_two
  omega

private theorem exists_outside_triple
    {U : Finset α} (hcard : 4 ≤ U.card) (a b c : α) :
    ∃ d ∈ U, d ≠ a ∧ d ≠ b ∧ d ≠ c := by
  by_contra h
  have hsub : U ⊆ ({a, b, c} : Finset α) := by
    intro d hd
    by_contra hnot
    have hda : d ≠ a := by
      intro heq
      apply hnot
      simp [heq]
    have hdb : d ≠ b := by
      intro heq
      apply hnot
      simp [heq]
    have hdc : d ≠ c := by
      intro heq
      apply hnot
      simp [heq]
    exact h ⟨d, hd, hda, hdb, hdc⟩
  have hbound := Finset.card_le_card hsub
  have htriple : ({a, b, c} : Finset α).card ≤ 3 := Finset.card_le_three
  omega

/-- The finite functional-root theorem.  No restriction on values outside
    `U` is needed: if there are no internal arrows, compatibility makes all
    values equal; otherwise one arrow leads to an external endpoint or a
    two-cycle.  The remaining three-cycle is ruled out by a fourth point. -/
theorem partial_root_exists
    {U : Finset α} {f : α → α}
    (hcard : 4 ≤ U.card)
    (hcomp : PartialCompatible U f)
    (hnofix : ∀ a ∈ U, f a ≠ a) :
    ∃ v : α, IsPartialRoot U f v := by
  by_cases hinternal : ∃ a ∈ U, f a ∈ U
  · obtain ⟨a, ha, hb⟩ := hinternal
    let b : α := f a
    have hfa : f a = b := rfl
    have hbU : b ∈ U := hb
    have hab : a ≠ b := by
      intro heq
      exact (hnofix a ha) (hfa.trans heq.symm)
    by_cases hfbU : f b ∈ U
    · let c : α := f b
      have hfb : f b = c := rfl
      have hcU : c ∈ U := hfbU
      have hbc : b ≠ c := by
        intro heq
        exact (hnofix b hbU) (hfb.trans heq.symm)
      by_cases hca : c = a
      · obtain ⟨d, hd, hda, hdb⟩ :=
          exists_outside_pair (by omega : 3 ≤ U.card) a b
        have hba : f b = a := hfb.trans hca
        rcases root_of_two_cycle hcomp ha hb hd hab hda hdb hfa hba with hr | hr
        · exact ⟨a, hr⟩
        · exact ⟨b, hr⟩
      · have hca' : c ≠ a := hca
        rcases compatible_arrow_range hcomp ha hcU hca' (Ne.symm hbc) hfa with
          hfcA | hfcB
        · obtain ⟨d, hd, hda, hdb, hdc⟩ :=
            exists_outside_triple hcard a b c
          exact False.elim
            (no_three_cycle_with_fourth hcomp ha hbU hcU hd
              hab hbc hca' hda hdb hdc hfa hfb hfcA)
        · rcases root_of_two_cycle hcomp hbU hcU ha hbc hab (Ne.symm hca')
            hfb hfcB with hr | hr
          · exact ⟨b, hr⟩
          · exact ⟨c, hr⟩
    · exact ⟨b, root_of_arrow_to_external hcomp ha hbU hab hfa rfl hfbU⟩
  · obtain ⟨a, ha⟩ : U.Nonempty := Finset.card_pos.mp (by omega)
    refine ⟨f a, ?_⟩
    intro x hx _
    by_cases hxa : x = a
    · subst x
      rfl
    · have hfax : f a ≠ x := by
        intro heq
        exact hinternal ⟨a, ha, by rw [heq]; exact hx⟩
      have hfxa : f x ≠ a := by
        intro heq
        exact hinternal ⟨x, hx, by rw [heq]; exact ha⟩
      exact (hcomp ha hx (Ne.symm hxa) hfax hfxa).symm

/-- The root is unique, using the earlier elementary uniqueness lemma. -/
theorem partial_root_exists_unique
    {U : Finset α} {f : α → α}
    (hcard : 4 ≤ U.card)
    (hcomp : PartialCompatible U f)
    (hnofix : ∀ a ∈ U, f a ≠ a) :
    ∃! v : α, IsPartialRoot U f v := by
  obtain ⟨v, hv⟩ := partial_root_exists hcard hcomp hnofix
  refine ⟨v, hv, ?_⟩
  intro w hw
  exact partial_root_unique (by omega : 3 ≤ U.card) hw hv

/-- The original ambient formulation.  The proof does not need the usual
    condition `|(V \ U)| ≤ 1`; it only needs every displayed value in `V`. -/
theorem partial_root_exists_unique_in_ambient
    {U V : Finset α} {f : α → α}
    (hcard : 4 ≤ U.card)
    (hmap : ∀ a ∈ U, f a ∈ V)
    (hcomp : PartialCompatible U f)
    (hnofix : ∀ a ∈ U, f a ≠ a) :
    ∃! v : α, v ∈ V ∧ IsPartialRoot U f v := by
  obtain ⟨v, hv⟩ := partial_root_exists hcard hcomp hnofix
  obtain ⟨a, ha, hav, _⟩ :=
    exists_outside_pair (by omega : 3 ≤ U.card) v v
  have hvV : v ∈ V := by
    rw [← hv a ha hav]
    exact hmap a ha
  refine ⟨v, ⟨hvV, hv⟩, ?_⟩
  intro w hw
  exact partial_root_unique (by omega : 3 ≤ U.card) hw.2 hv

end RootExistence

end JSP523.Rank5
