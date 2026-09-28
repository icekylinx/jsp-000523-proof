import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite shadow ownership and deletion

This isolates the deterministic incidence-counting step in Lemma IV.3.2.
Every deleted colored member has a shadow point owned by a different color.
Choosing one such point injects deleted members into the bad incidences, so
the deletion cost is bounded by the sum of non-owner degrees.
-/

namespace JSP523.Rank5

/-- The number of colored objects in `E` incident with `p` and not owned by
their color. -/
def badShadowDegree {ι ε τ : Type*} [DecidableEq ι] [DecidableEq ε] [DecidableEq τ]
    (E : Finset ε) (color : ε → ι) (facets : ε → Finset τ)
    (owner : τ → ι) (p : τ) : ℕ :=
  (E.filter fun e => p ∈ facets e ∧ owner p ≠ color e).card

/-- Count each shadow incidence once by its shadow point. -/
theorem shadow_incidence_count_eq_sum_degrees
    {ι ε τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq ε] [DecidableEq τ]
    (E : Finset ε) (color : ε → ι) (facets : ε → Finset τ)
    (owner : τ → ι) :
    ((E ×ˢ Finset.univ).filter fun ep =>
      ep.2 ∈ facets ep.1 ∧ owner ep.2 ≠ color ep.1).card =
        ∑ p ∈ Finset.univ, badShadowDegree E color facets owner p := by
  classical
  let S := (E ×ˢ Finset.univ).filter fun ep =>
    ep.2 ∈ facets ep.1 ∧ owner ep.2 ≠ color ep.1
  have hmaps : (S : Set (ε × τ)).MapsTo Prod.snd (Finset.univ : Finset τ) := by
    intro ep hep
    exact Finset.mem_univ _
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro p hp
  let Q := E.filter fun e => p ∈ facets e ∧ owner p ≠ color e
  have hfiber : {ep ∈ S | ep.2 = p} = Q.image (fun e => (e, p)) := by
    ext ⟨e, q⟩
    simp [S, Q, Finset.mem_filter, Finset.mem_product, eq_comm]; aesop
  rw [hfiber, Finset.card_image_of_injective]
  · rfl
  · intro a b hab
    exact congrArg Prod.fst hab

/-- Ownership deletion bound. `deleted` contains only objects with at least
one facet assigned to another color. Its size is at most the total number
of non-owner incidences. -/
theorem shadow_ownership_deletion_bound
    {ι ε τ : Type*} [Fintype τ] [Inhabited τ] [DecidableEq ι] [DecidableEq ε] [DecidableEq τ]
    (E : Finset ε) (color : ε → ι) (facets : ε → Finset τ)
    (owner : τ → ι) :
    ((E.filter fun e => ∃ p ∈ facets e, owner p ≠ color e)).card ≤
      ∑ p ∈ Finset.univ, badShadowDegree E color facets owner p := by
  classical
  let D := E.filter fun e => ∃ p ∈ facets e, owner p ≠ color e
  let I := (E ×ˢ Finset.univ).filter fun ep =>
      ep.2 ∈ facets ep.1 ∧ owner ep.2 ≠ color ep.1
  let witness : ε → τ := fun e => if he : e ∈ D then
    Classical.choose (show ∃ p, p ∈ facets e ∧ owner p ≠ color e by
      simpa [D] using (Finset.mem_filter.mp he).2) else default
  have hwitness : ∀ e ∈ D, witness e ∈ facets e ∧ owner (witness e) ≠ color e := by
    intro e he
    dsimp [witness]
    rw [dite_eq_left he]
    exact Classical.choose_spec (show ∃ p, p ∈ facets e ∧ owner p ≠ color e by
      simpa [D] using (Finset.mem_filter.mp he).2)
  let f : ε → ε × τ := fun e => (e, witness e)
  have hfSub : ∀ e ∈ D, f e ∈ I := by
    intro e he
    simp only [I, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, f]
    exact ⟨⟨(Finset.mem_filter.mp he).1, trivial⟩, hwitness e he⟩
  have hfInj : Set.InjOn f (↑D : Set ε) := by
    intro a ha b hb hab
    exact congrArg Prod.fst hab
  have hcard : D.card ≤ I.card := Finset.card_le_card_of_injOn f hfSub hfInj
  calc
    D.card ≤ I.card := hcard
    _ = ∑ p ∈ Finset.univ, badShadowDegree E color facets owner p := by
      exact shadow_incidence_count_eq_sum_degrees E color facets owner

/-- Finite-support version of the ownership bound. Only shadow points in
`P` are considered, so it applies directly when the ambient vertex type is
infinite but the star layers live on a specified finite ground set. -/
theorem shadow_ownership_deletion_bound_on
    {ι ε τ : Type*} [Inhabited τ] [DecidableEq ι] [DecidableEq ε] [DecidableEq τ]
    (E : Finset ε) (P : Finset τ) (color : ε → ι)
    (facets : ε → Finset τ) (owner : τ → ι) :
    ((E.filter fun e => ∃ p ∈ facets e, p ∈ P ∧ owner p ≠ color e)).card ≤
      ∑ p ∈ P, badShadowDegree E color (fun e => facets e ∩ P) owner p := by
  classical
  let D := E.filter fun e => ∃ p ∈ facets e, p ∈ P ∧ owner p ≠ color e
  let I := ((E ×ˢ P).filter fun ep =>
      ep.2 ∈ facets ep.1 ∧ owner ep.2 ≠ color ep.1)
  let witness : ε → τ := fun e => if he : e ∈ D then
    Classical.choose (show ∃ p, p ∈ facets e ∧ p ∈ P ∧ owner p ≠ color e by
      simpa [D] using (Finset.mem_filter.mp he).2) else default
  have hwitness : ∀ e ∈ D,
      witness e ∈ facets e ∧ owner (witness e) ≠ color e := by
    intro e he
    dsimp [witness]
    rw [dite_eq_left he]
    exact ⟨(Classical.choose_spec (show ∃ p, p ∈ facets e ∧ p ∈ P ∧
      owner p ≠ color e by simpa [D] using (Finset.mem_filter.mp he).2)).1,
      (Classical.choose_spec (show ∃ p, p ∈ facets e ∧ p ∈ P ∧
      owner p ≠ color e by simpa [D] using (Finset.mem_filter.mp he).2)).2.2⟩
  have hownP : ∀ e ∈ D, witness e ∈ P := by
    intro e he
    dsimp [witness]
    rw [dite_eq_left he]
    exact (Classical.choose_spec (show ∃ p, p ∈ facets e ∧ p ∈ P ∧
      owner p ≠ color e by simpa [D] using (Finset.mem_filter.mp he).2)).2.1
  let f : ε → ε × τ := fun e => (e, witness e)
  have hfSub : ∀ e ∈ D, f e ∈ I := by
    intro e he
    simp only [I, Finset.mem_filter, Finset.mem_product, f]
    exact ⟨⟨(Finset.mem_filter.mp he).1, hownP e he⟩, hwitness e he⟩
  have hfInj : Set.InjOn f (↑D : Set ε) := by
    intro a ha b hb hab
    exact congrArg Prod.fst hab
  have hcard : D.card ≤ I.card := Finset.card_le_card_of_injOn f hfSub hfInj
  have hmaps : (I : Set (ε × τ)).MapsTo Prod.snd P := by
    intro ep hep
    exact (Finset.mem_product.mp
      (Finset.mem_filter.mp hep).1).2
  calc
    D.card ≤ I.card := hcard
    _ = ∑ p ∈ P, ({ep ∈ I | ep.2 = p}.card) := Finset.card_eq_sum_card_fiberwise hmaps
    _ = ∑ p ∈ P, badShadowDegree E color (fun e => facets e ∩ P) owner p := by
      apply Finset.sum_congr rfl
      intro p hp
      have hEq : {ep ∈ I | ep.2 = p} =
          ((E.filter fun e => p ∈ facets e ∧ owner p ≠ color e).image
            (fun e => (e, p))) := by
        ext ⟨e, q⟩
        simp [I, Finset.mem_filter, Finset.mem_product, eq_comm]; aesop
      rw [hEq, Finset.card_image_of_injective]
      · simp [badShadowDegree, hp]
      · intro a b hab
        exact congrArg Prod.fst hab

end JSP523.Rank5
