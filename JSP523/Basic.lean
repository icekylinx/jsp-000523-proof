import Mathlib.Data.Finset.Card

/-!
# JSP-000523: basic finite hypergraph language

This file fixes a concrete finite representation for the repeated-union problem.
An edge is a `Finset α`; a family is a `Finset (Finset α)`.

The forbidden configuration consists of four distinct edges `A,B,C,D` with
`A` disjoint from `B`, `C` disjoint from `D`, and equal unions.
-/

namespace JSP523

abbrev Edge (α : Type*) := Finset α
abbrev Family (α : Type*) := Finset (Edge α)

section Basic

variable {α : Type*} [DecidableEq α]

/-- Every edge of `F` has cardinality `r`. -/
def Uniform (r : ℕ) (F : Family α) : Prop :=
  ∀ ⦃E : Edge α⦄, E ∈ F → E.card = r

/-- Explicit pairwise distinctness for four edges. -/
structure FourDistinct (A B C D : Edge α) : Prop where
  ab : A ≠ B
  ac : A ≠ C
  ad : A ≠ D
  bc : B ≠ C
  bd : B ≠ D
  cd : C ≠ D

/-- The four-edge repeated-union configuration forbidden in JSP-000523. -/
structure ForbiddenQuad (A B C D : Edge α) : Prop where
  distinct : FourDistinct A B C D
  disjAB : Disjoint A B
  disjCD : Disjoint C D
  sameUnion : A ∪ B = C ∪ D

/-- A family is admissible if it contains no forbidden quadruple. -/
def Admissible (F : Family α) : Prop :=
  ∀ ⦃A B C D : Edge α⦄,
    A ∈ F → B ∈ F → C ∈ F → D ∈ F →
    ForbiddenQuad A B C D → False

/-- Admissibility is inherited by subfamilies. -/
theorem admissible_mono {F G : Family α}
    (hGF : G ⊆ F) (hF : Admissible F) : Admissible G := by
  intro A B C D hA hB hC hD hq
  exact hF (hGF hA) (hGF hB) (hGF hC) (hGF hD) hq

/-- Reversing the two disjoint pairs preserves the forbidden configuration. -/
theorem ForbiddenQuad.swap_pairs {A B C D : Edge α}
    (h : ForbiddenQuad A B C D) : ForbiddenQuad C D A B := by
  refine ⟨?_, h.disjCD, h.disjAB, h.sameUnion.symm⟩
  exact ⟨h.distinct.cd, h.distinct.ac.symm, h.distinct.bc.symm,
    h.distinct.ad.symm, h.distinct.bd.symm, h.distinct.ab⟩

/-- Swapping the two edges inside each disjoint pair preserves the configuration. -/
theorem ForbiddenQuad.swap_within {A B C D : Edge α}
    (h : ForbiddenQuad A B C D) : ForbiddenQuad B A D C := by
  refine ⟨?_, h.disjAB.symm, h.disjCD.symm, ?_⟩
  · exact ⟨h.distinct.ab.symm, h.distinct.bd, h.distinct.bc,
      h.distinct.ad, h.distinct.ac, h.distinct.cd.symm⟩
  · simpa [Finset.union_comm] using h.sameUnion

end Basic

end JSP523
