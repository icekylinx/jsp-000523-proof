import JSP523.Rank5.ColorRigidity

/-!
# Clean-set consequence for quantitative color sampling

This file isolates the deterministic step used after sampling in Lemma
IV.6.2: any sampled set large enough, with no bicolored triangle, is
monochromatic. The probabilistic part of IV.6.2 can then count the samples
that fail these hypotheses.
-/

namespace JSP523.Rank5

variable {α κ : Type*} [DecidableEq α] [Fintype κ] [DecidableEq κ]

/-- A restriction of a triangle-rigid coloring to a large finite vertex set
is monochromatic. This is the clean-sample conclusion needed by IV.6.2. -/
theorem mono_on_large_clean_set
    [Fintype α]
    (color : α → α → κ) (C : Finset α)
    (hNoBi : NoBicoloredTriangle color)
    (hq : 2 ≤ Fintype.card κ)
    (hsize : max 4 ((Fintype.card κ - 1) ^ 2 + 1) ≤ C.card) :
    ∃ c : κ, ∀ x ∈ C, ∀ y ∈ C, x ≠ y → color x y = c := by
  classical
  let V := {x // x ∈ C}
  let restricted : V → V → κ := fun x y => color x.1 y.1
  have hNoBiRestricted : NoBicoloredTriangle restricted := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      exact hNoBi.1 x.1 y.1 (fun h => hxy (Subtype.ext h))
    · intro x y z hxy hxz hyz hEq
      exact hNoBi.2 x.1 y.1 z.1
        (fun h => hxy (Subtype.ext h))
        (fun h => hxz (Subtype.ext h))
        (fun h => hyz (Subtype.ext h)) hEq
  have hSizeV : max 4 ((Fintype.card κ - 1) ^ 2 + 1) ≤ Fintype.card V := by
    simpa [V] using hsize
  have hRigidity := color_rigidity_finite restricted hNoBiRestricted hq
  have hNotSmall : ¬ Fintype.card V ≤ (Fintype.card κ - 1) ^ 2 := by
    omega
  have hMono : ∃ c : κ, ∀ x y : V, x ≠ y → restricted x y = c := by
    rcases hRigidity with hMono | hSmall
    · exact hMono
    · exact False.elim (hNotSmall hSmall)
  obtain ⟨c, hc⟩ := hMono
  refine ⟨c, ?_⟩
  intro x hx y hy hxy
  exact hc ⟨x, hx⟩ ⟨y, hy⟩ (fun h => hxy (congrArg Subtype.val h))

end JSP523.Rank5
