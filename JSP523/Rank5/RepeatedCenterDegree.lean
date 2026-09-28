import JSP523.Counting.CommonPrefixTails
import Mathlib.Tactic

/-!
# Repeated-center partner degree from actual common-prefix cells

This file formalizes the incidence count in §IV.7.1. The roots and tails are
actual finite sets, and all degree caps refer to containing-edge fibers of the
fixed parent family.
-/

namespace JSP523.Rank5

open JSP523

variable {α : Type*} [DecidableEq α]

/-- Actual degree of a set in the fixed parent family. -/
def actualDegree (H : Family α) (S : Edge α) : ℕ :=
  (H.filter fun E => S ⊆ E).card

/-- A common-prefix cell has a unique center `z` when every member contains
`z`, and no other vertex belongs to every member. -/
def UniqueCellCenter (C : Family α) (z : α) : Prop :=
  (∀ A ∈ C, z ∈ A) ∧
    ∀ y, (∀ A ∈ C, y ∈ A) → y = z

/-- The strong-partner predicate used in §IV.7.1, with its actual cell,
threshold, and unique center made explicit. -/
def ActualStrongPartner (H : Family α) (W P Q : Edge α)
    (s k t : ℕ) (z : α) : Prop :=
  Q ∈ W.powersetCard s ∧ Disjoint P Q ∧
    t ≤ (commonPrefixTails H W P Q k).card ∧
    UniqueCellCenter (commonPrefixTails H W P Q k) z

/-- Actual partners at `P` with the specified unique center, optionally
required to contain a prescribed set `U`. -/
noncomputable def actualCenterPartners (H : Family α) (W P : Edge α)
    (s k t : ℕ) (z : α) (U : Edge α) : Family α := by
  classical
  exact (W.powersetCard s).filter fun Q =>
    ActualStrongPartner H W P Q s k t z ∧ U ⊆ Q

/-- A finite bipartite incidence bound: if every left vertex has at least
`t` incidences, there are at most `D₁` right vertices and every right vertex
has at most `D₂` incidences, then `t |L| ≤ D₁ D₂`. -/
theorem finite_incidence_degree_bound
    {L R : Type*} [DecidableEq L] [DecidableEq R]
    (I : Finset (L × R)) (left : Finset L) (t d₁ d₂ : ℕ)
    (hMaps : ∀ x ∈ I, x.1 ∈ left)
    (hLeft : ∀ x ∈ left, t ≤ (I.filter fun p => p.1 = x).card)
    (hRightCard : (I.image Prod.snd).card ≤ d₁)
    (hRight : ∀ y, (I.filter fun p => p.2 = y).card ≤ d₂) :
    t * left.card ≤ d₁ * d₂ := by
  classical
  have hEq := Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := I)
    (t := left) hMaps
  have hLower : t * left.card ≤ I.card := by
    rw [hEq]
    calc
      t * left.card = ∑ x ∈ left, t := by simp [Finset.sum_const, mul_comm]
      _ ≤ ∑ x ∈ left, (I.filter fun p => p.1 = x).card :=
        Finset.sum_le_sum fun x hx => hLeft x hx
  have hEqR := Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (s := I)
    (t := I.image Prod.snd) (fun _ => Finset.mem_image_of_mem _)
  have hUpper : I.card ≤ d₁ * d₂ := by
    rw [hEqR]
    calc
      ∑ y ∈ I.image Prod.snd, (I.filter fun p => p.2 = y).card
          ≤ ∑ y ∈ I.image Prod.snd, d₂ :=
        Finset.sum_le_sum fun y hy => hRight y
      _ = (I.image Prod.snd).card * d₂ := by simp
      _ ≤ d₁ * d₂ := Nat.mul_le_mul_right d₂ hRightCard
  exact hLower.trans hUpper

end JSP523.Rank5
