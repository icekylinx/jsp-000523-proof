import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Finite color rigidity

This formalizes the first implication in Lemma IV.6.1 of the current
manuscript: a monochromatic clique with at least as many vertices as there
are available colors forces a complete coloring to be monochromatic.
The triangle rule is the symmetric complete-graph form of excluding a
bicolored triangle.
-/

namespace JSP523.Rank5

variable {α κ : Type*} [DecidableEq α] [Fintype κ] [DecidableEq κ]

/-- Symmetric edge colors with the rule that two equal colors in a triangle
force the third color to agree. Values on the diagonal are irrelevant. -/
def NoBicoloredTriangle (color : α → α → κ) : Prop :=
  (∀ x y, x ≠ y → color x y = color y x) ∧
  ∀ x y z, x ≠ y → x ≠ z → y ≠ z →
    color x y = color x z → color y z = color x y

def MonochromaticClique (color : α → α → κ)
    (C : Finset α) (c : κ) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → color x y = c

def colorNeighbors [Fintype α] (color : α → α → κ) (x : α) (c : κ) : Finset α :=
  (Finset.univ.erase x).filter fun y => color x y = c

/-- A monochromatic clique at least as large as the color palette forces
all edges of the complete graph to have that color. -/
theorem mono_clique_forces_global
    (color : α → α → κ) (C : Finset α) (c : κ)
    (hNoBi : NoBicoloredTriangle color)
    (hC : MonochromaticClique color C c)
    (hsize : Fintype.card κ ≤ C.card) :
    ∀ x y, x ≠ y → color x y = c := by
  classical
  obtain ⟨hSymm, hTri⟩ := hNoBi
  have hPalette : 0 < Fintype.card κ := Fintype.card_pos_iff.mpr ⟨c⟩
  have hCpos : 0 < C.card := lt_of_lt_of_le hPalette hsize
  have hOutside : ∀ x, x ∉ C → ∀ a ∈ C, color x a = c := by
    intro x hx a ha
    let Alt := C.filter fun y => color x y ≠ c
    have hAltInj : Alt.card ≤ (Finset.univ.erase c : Finset κ).card := by
      apply Finset.card_le_card_of_injOn (fun y => color x y)
      · intro y hy
        have hy' := Finset.mem_filter.mp hy
        exact Finset.mem_erase.mpr ⟨hy'.2, Finset.mem_univ _⟩
      · intro y hy z hz hEq
        by_contra hyz
        have hy' := Finset.mem_filter.mp hy
        have hz' := Finset.mem_filter.mp hz
        have hxy : x ≠ y := fun h => hx (h ▸ hy'.1)
        have hxz : x ≠ z := fun h => hx (h ▸ hz'.1)
        have hyzc : color y z = color x y :=
          hTri x y z hxy hxz hyz hEq
        exact hy'.2 (hyzc.symm.trans (hC y hy'.1 z hz'.1 hyz))
    have hAltSmall : Alt.card < C.card := by
      have hErase : (Finset.univ.erase c : Finset κ).card + 1 =
          Fintype.card κ := by simp; omega
      omega
    have hNotSub : ¬ C ⊆ Alt := by
      intro hSub
      have hCard := Finset.card_le_card hSub
      omega
    obtain ⟨b, hbC, hbNotAlt⟩ := Finset.not_subset.mp hNotSub
    have hxb : color x b = c := by
      by_contra hne
      exact hbNotAlt (Finset.mem_filter.mpr ⟨hbC, hne⟩)
    by_cases hab : a = b
    · simpa [hab] using hxb
    · have hbx : color b x = c :=
        (hSymm x b (fun h => hx (h ▸ hbC))).symm.trans hxb
      have hba : color b a = c := hC b hbC a ha (Ne.symm hab)
      have hbaEq : color b x = color b a := hbx.trans hba.symm
      have hxa : color x a = color b x :=
        hTri b x a (fun h => hx (h.symm ▸ hbC))
          (Ne.symm hab) (fun h => hx (h ▸ ha)) hbaEq
      exact hxa.trans hbx
  intro x y hxy
  by_cases hxC : x ∈ C
  · by_cases hyC : y ∈ C
    · exact hC x hxC y hyC hxy
    · exact (hSymm x y hxy).trans (hOutside y hyC x hxC)
  · by_cases hyC : y ∈ C
    · exact hOutside x hxC y hyC
    · obtain ⟨a, ha⟩ := Finset.card_pos.mp hCpos
      have hxa := hOutside x hxC a ha
      have hya := hOutside y hyC a ha
      have hax : color a x = c :=
        (hSymm x a (fun h => hxC (h ▸ ha))).symm.trans hxa
      have hay : color a y = c :=
        (hSymm y a (fun h => hyC (h ▸ ha))).symm.trans hya
      have haxEq : color a x = color a y := hax.trans hay.symm
      exact (hTri a x y (fun h => hxC (h ▸ ha))
        (fun h => hyC (h ▸ ha)) hxy haxEq).trans hax

/-- In a nonmonochromatic coloring, a monochromatic clique has fewer
vertices than the number of colors. -/
theorem mono_clique_card_lt_of_not_global
    (color : α → α → κ) (C : Finset α) (c : κ)
    (hNoBi : NoBicoloredTriangle color)
    (hC : MonochromaticClique color C c)
    (hNotGlobal : ¬ ∀ x y, x ≠ y → color x y = c) :
    C.card < Fintype.card κ := by
  by_contra h
  have hlarge : Fintype.card κ ≤ C.card := by omega
  exact hNotGlobal (mono_clique_forces_global color C c hNoBi hC hlarge)

/-- Lemma IV.6.1: a complete symmetric coloring with no bicolored
triangle is monochromatic whenever its order exceeds `(q-1)²`, where
`q` is the number of available colors. -/
theorem color_rigidity_finite
    [Fintype α]
    (color : α → α → κ)
    (hNoBi : NoBicoloredTriangle color)
    (hq : 2 ≤ Fintype.card κ) :
    (∃ c : κ, ∀ x y, x ≠ y → color x y = c) ∨
      Fintype.card α ≤ (Fintype.card κ - 1) ^ 2 := by
  classical
  by_cases hMono : ∃ c : κ, ∀ x y, x ≠ y → color x y = c
  · exact Or.inl hMono
  right
  by_cases hV : (Finset.univ : Finset α).Nonempty
  · obtain ⟨x, _hx⟩ := hV
    let N : κ → Finset α := colorNeighbors color x
    have hxN : ∀ c : κ, x ∉ N c := by
      intro c
      simp [N, colorNeighbors]
    have hClique : ∀ c : κ,
        MonochromaticClique color (insert x (N c)) c := by
      intro c y hy z hz hyz
      have hSymm := hNoBi.1
      have hTri := hNoBi.2
      simp only [Finset.mem_insert] at hy hz
      rcases hy with rfl | hyN
      · rcases hz with rfl | hzN
        · exact False.elim (hyz rfl)
        · exact (Finset.mem_filter.mp hzN).2
      rcases hz with hzx | hzN
      · have hyColor : color x y = c := (Finset.mem_filter.mp hyN).2
        have hyx : y ≠ x := by simpa [hzx] using hyz
        simpa [hzx] using (hSymm y x hyx).trans hyColor
      · have hyx : x ≠ y := fun h => hxN c (h ▸ hyN)
        have hzx : x ≠ z := fun h => hxN c (h ▸ hzN)
        have hyColor : color x y = c := (Finset.mem_filter.mp hyN).2
        have hzColor : color x z = c := (Finset.mem_filter.mp hzN).2
        exact (hTri x y z hyx hzx hyz (hyColor.trans hzColor.symm)).trans hyColor
    have hClass : ∀ c : κ, (N c).card ≤ Fintype.card κ - 2 := by
      intro c
      have hNotGlobal : ¬ ∀ x y, x ≠ y → color x y = c := by
        intro h
        exact hMono ⟨c, h⟩
      have hSmall := mono_clique_card_lt_of_not_global
        color (insert x (N c)) c hNoBi (hClique c) hNotGlobal
      rw [Finset.card_insert_of_notMem (hxN c)] at hSmall
      omega
    have hUnion : (Finset.univ : Finset κ).biUnion N =
        (Finset.univ : Finset α).erase x := by
      ext y
      constructor
      · intro hy
        obtain ⟨c, _, hyN⟩ := Finset.mem_biUnion.mp hy
        exact (Finset.mem_filter.mp hyN).1
      · intro hy
        apply Finset.mem_biUnion.mpr
        exact ⟨color x y, Finset.mem_univ _,
          Finset.mem_filter.mpr ⟨hy, rfl⟩⟩
    have hSum : ((Finset.univ : Finset κ).biUnion N).card ≤
        Fintype.card κ * (Fintype.card κ - 2) := by
      calc
        _ ≤ ∑ c : κ, (N c).card := Finset.card_biUnion_le
        _ ≤ ∑ _c : κ, (Fintype.card κ - 2) :=
          Finset.sum_le_sum (fun c _ => hClass c)
        _ = Fintype.card κ * (Fintype.card κ - 2) := by simp
    have hErase : ((Finset.univ : Finset α).erase x).card + 1 =
        Fintype.card α := by
      have hCardPos : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨x⟩
      simp
      omega
    rw [hUnion] at hSum
    have hq2 : Fintype.card κ - 2 + 2 = Fintype.card κ := by omega
    have hq1 : Fintype.card κ - 1 + 1 = Fintype.card κ := by omega
    nlinarith
  · have hEmpty : (Finset.univ : Finset α) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hV
    have hCard : Fintype.card α = 0 := by
      simpa using congrArg Finset.card hEmpty
    omega

end JSP523.Rank5
