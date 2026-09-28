import Mathlib.Tactic

/-!
# Finite greedy coloring for bounded conflict degree

An elementary finite-set coloring lemma used for the pair-root link graph in
§III.A.5.  The statement is phrased for an actual finite vertex set and an
actual conflict relation, so it can be instantiated without graph-library
colorability interfaces.
-/

namespace JSP523.Rank4

variable {β : Type*} [DecidableEq β]

/-- A finite conflict system of maximum degree at most `d` admits a coloring
with `d + 1` colors. -/
theorem finite_greedy_coloring
    (S : Finset β) (conflict : β → β → Prop) [DecidableRel conflict]
    (d : ℕ)
    (hsymm : ∀ x y, conflict x y → conflict y x)
    (hirrefl : ∀ x, ¬ conflict x x)
    (hdegree : ∀ x ∈ S,
      (S.filter fun y => conflict x y).card ≤ d) :
    ∃ color : β → Fin (d + 1),
      ∀ x ∈ S, ∀ y ∈ S, conflict x y → color x ≠ color y := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨fun _ => 0, by simp⟩
  | @insert a S ha ih =>
      have hdegreeS : ∀ x ∈ S,
          (S.filter fun y => conflict x y).card ≤ d := by
        intro x hx
        calc
          _ ≤ ((insert a S).filter fun y => conflict x y).card := by
            apply Finset.card_le_card
            intro y hy
            exact Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem
              (Finset.mem_filter.mp hy).1, (Finset.mem_filter.mp hy).2⟩
          _ ≤ d := hdegree x (Finset.mem_insert_of_mem hx)
      obtain ⟨color, hcolor⟩ := ih hdegreeS
      let forbidden := (S.filter fun y => conflict a y).image color
      have hforbidden : forbidden.card ≤ d := by
        dsimp [forbidden]
        calc
          _ ≤ (S.filter fun y => conflict a y).card := Finset.card_image_le
          _ ≤ ((insert a S).filter fun y => conflict a y).card := by
            apply Finset.card_le_card
            intro y hy
            exact Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem
              (Finset.mem_filter.mp hy).1, (Finset.mem_filter.mp hy).2⟩
          _ ≤ d := hdegree a (Finset.mem_insert_self ..)
      have hnotAll : ∃ k : Fin (d + 1), k ∉ forbidden := by
        by_contra h
        push Not at h
        have hsub : (Finset.univ : Finset (Fin (d + 1))) ⊆ forbidden := by
          intro k hk
          exact h k
        have hcard := Finset.card_le_card hsub
        simp at hcard
        omega
      obtain ⟨k, hk⟩ := hnotAll
      refine ⟨Function.update color a k, ?_⟩
      intro x hx y hy hxy
      rcases Finset.mem_insert.mp hx with hxa | hxS
      · subst x
        rcases Finset.mem_insert.mp hy with hya | hyS
        · subst y
          exact (hirrefl a hxy).elim
        · intro heq
          apply hk
          dsimp [forbidden]
          have hya' : y ≠ a := by
            intro h
            exact ha (h ▸ hyS)
          have hcolorY : color y = k := by
            simpa [Function.update_of_ne hya'] using heq.symm
          exact Finset.mem_image.mpr
            ⟨y, Finset.mem_filter.mpr ⟨hyS, hxy⟩, hcolorY⟩
      · rcases Finset.mem_insert.mp hy with hya | hyS
        · subst y
          intro heq
          apply hk
          dsimp [forbidden]
          have hxa' : x ≠ a := by
            intro h
            exact ha (h ▸ hxS)
          have hcolorX : color x = k := by
            simpa [Function.update_of_ne hxa'] using heq
          exact Finset.mem_image.mpr
            ⟨x, Finset.mem_filter.mpr ⟨hxS, hsymm x a hxy⟩, hcolorX⟩
        · have hxa' : x ≠ a := by
            intro hEq
            subst x
            exact ha hxS
          have hya' : y ≠ a := by
            intro hEq
            subst y
            exact ha hyS
          simpa [Function.update_of_ne hxa', Function.update_of_ne hya'] using
            hcolor x hxS y hyS hxy

end JSP523.Rank4

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- Conflict between distinct pair roots sharing an endpoint. -/
def pairRootConflict (P R : Finset α) : Prop := P ≠ R ∧ ¬ Disjoint P R

/-- A finite family of pair roots with at most `κ` roots through each point
has a proper shared-endpoint coloring with `2κ - 1` colors. -/
theorem pair_roots_greedy_color
    (S : Finset (Finset α)) (κ : ℕ) (hκ : 1 ≤ κ)
    (hPair : ∀ P ∈ S, P.card = 2)
    (hCodegree : ∀ a, (S.filter fun P => a ∈ P).card ≤ κ) :
    ∃ color : Finset α → Fin (2 * κ - 1),
      ∀ P ∈ S, ∀ R ∈ S, pairRootConflict P R → color P ≠ color R := by
  classical
  let conflict : Finset α → Finset α → Prop := pairRootConflict
  have hsymm : ∀ P R, conflict P R → conflict R P := by
    intro P R h
    refine ⟨Ne.symm h.1, ?_⟩
    intro hdisj
    apply h.2
    exact Finset.disjoint_left.mpr fun a haR haP =>
      Finset.disjoint_left.mp hdisj haP haR
  have hirrefl : ∀ P, ¬ conflict P P := by
    intro P h
    exact h.1 rfl
  have hdegree : ∀ P ∈ S,
      (S.filter fun R => conflict P R).card ≤ 2 * (κ - 1) := by
    intro P hP
    let wedges := P.biUnion fun a => (S.filter fun R => a ∈ R).erase P
    have hsub : (S.filter fun R => conflict P R) ⊆ wedges := by
      intro R hR
      have hconf := (Finset.mem_filter.mp hR).2
      obtain ⟨a, ha⟩ := Finset.not_disjoint_iff_nonempty_inter.mp hconf.2
      have haP : a ∈ P := (Finset.mem_inter.mp ha).1
      have haR : a ∈ R := (Finset.mem_inter.mp ha).2
      exact Finset.mem_biUnion.mpr ⟨a, haP,
        Finset.mem_erase.mpr ⟨Ne.symm hconf.1, Finset.mem_filter.mpr ⟨
          (Finset.mem_filter.mp hR).1, haR⟩⟩⟩
    have hWedge : wedges.card ≤ 2 * (κ - 1) := by
      calc
        _ ≤ ∑ a ∈ P, ((S.filter fun R => a ∈ R).erase P).card := by
          dsimp [wedges]
          exact Finset.card_biUnion_le
        _ ≤ ∑ _a ∈ P, (κ - 1) := by
          apply Finset.sum_le_sum
          intro a ha
          have hPmem : P ∈ S.filter fun R => a ∈ R :=
            Finset.mem_filter.mpr ⟨hP, ha⟩
          have hFilter : (S.filter fun R => a ∈ R).card ≤ κ := hCodegree a
          rw [Finset.card_erase_of_mem hPmem]
          have hPos : 1 ≤ (S.filter fun R => a ∈ R).card := Finset.card_pos.mpr ⟨P, hPmem⟩
          omega
        _ = P.card * (κ - 1) := by simp
        _ = 2 * (κ - 1) := by rw [hPair P hP]
    exact (Finset.card_le_card hsub).trans hWedge
  have hcolor := finite_greedy_coloring S conflict (2 * (κ - 1))
    hsymm hirrefl hdegree
  obtain ⟨color, hcolor⟩ := hcolor
  refine ⟨fun P => ?_, ?_⟩
  · exact Fin.cast (by omega : 2 * (κ - 1) + 1 = 2 * κ - 1) (color P)
  · intro P hP R hR hPR heq
    exact hcolor P hP R hR hPR
      (Fin.cast_injective (by omega : 2 * (κ - 1) + 1 = 2 * κ - 1) heq)

end JSP523.Rank4
