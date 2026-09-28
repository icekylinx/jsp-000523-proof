import JSP523.Matching
import Mathlib.Data.Finset.Powerset

set_option linter.unusedSectionVars false

/-!
# The star-plus-matching construction: finite core

The full lower construction is a complete `r`-star through a center `c`,
together with an `r`-uniform matching avoiding `c`.

This file formalizes the star family and the key mixed-pair obstruction.  It
then combines the pure-matching and mixed cases to prove admissibility of the
whole construction.
-/

namespace JSP523

section LowerConstruction

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The complete `r`-uniform star through `c`. -/
def starFamily (c : α) (r : ℕ) : Family α :=
  (Finset.univ.powersetCard r).filter (fun E => c ∈ E)

@[simp] theorem mem_starFamily {c : α} {r : ℕ} {E : Edge α} :
    E ∈ starFamily c r ↔ E.card = r ∧ c ∈ E := by
  simp [starFamily]

/-- The star-plus-matching lower construction in Part I of the all-rank manuscript. -/
def starPlusMatching (c : α) (r : ℕ) (M : Family α) : Family α :=
  starFamily c r ∪ M

/-- The star-plus-matching construction is `r`-uniform when the matching is. -/
theorem starPlusMatching_uniform
    {c : α} {r : ℕ} {M : Family α}
    (hU : Uniform r M) : Uniform r (starPlusMatching c r M) := by
  intro E hE
  simp only [starPlusMatching, Finset.mem_union] at hE
  rcases hE with hEs | hEm
  · exact (mem_starFamily.mp hEs).1
  · exact hU hEm

/-- Two star edges through the same center cannot be disjoint. -/
theorem star_edges_not_disjoint {c : α} {r : ℕ} {A B : Edge α}
    (hA : A ∈ starFamily c r) (hB : B ∈ starFamily c r) :
    ¬ Disjoint A B := by
  intro hAB
  exact (Finset.disjoint_left.mp hAB) (mem_starFamily.mp hA).2 (mem_starFamily.mp hB).2

/--
If two distinct matching blocks occur on the matching sides of two equal-union
mixed pairs, the first matching block is forced inside the opposite star edge.
Equal cardinalities then force equality, contradicting center avoidance.
-/
theorem mixed_equal_union_impossible
    {c : α} {r : ℕ} {M : Family α}
    {S₁ S₂ M₁ M₂ : Edge α}
    (hU : Uniform r M)
    (hMatch : IsMatching M)
    (hAvoid : ∀ ⦃E : Edge α⦄, E ∈ M → c ∉ E)
    (hS₂ : S₂ ∈ starFamily c r)
    (hM₁ : M₁ ∈ M) (hM₂ : M₂ ∈ M)
    (hne : M₁ ≠ M₂)
    (hUnion : S₁ ∪ M₁ = S₂ ∪ M₂) : False := by
  have hMM : Disjoint M₁ M₂ := hMatch hM₁ hM₂ hne
  have hsub : M₁ ⊆ S₂ := by
    intro x hxM₁
    have hxLeft : x ∈ S₁ ∪ M₁ := Finset.mem_union.mpr (Or.inr hxM₁)
    rw [hUnion] at hxLeft
    rcases Finset.mem_union.mp hxLeft with hxS₂ | hxM₂
    · exact hxS₂
    · exact False.elim ((Finset.disjoint_left.mp hMM) hxM₁ hxM₂)
  have hEq : M₁ = S₂ := by
    apply Finset.eq_of_subset_of_card_le hsub
    have hMcard : M₁.card = r := hU hM₁
    have hScard : S₂.card = r := (mem_starFamily.mp hS₂).1
    exact le_of_eq (hScard.trans hMcard.symm)
  have hcS₂ : c ∈ S₂ := (mem_starFamily.mp hS₂).2
  have hcM₁ : c ∉ M₁ := hAvoid hM₁
  apply hcM₁
  rw [hEq]
  exact hcS₂

/-- A union of two matching blocks avoids the star center. -/
theorem matching_union_avoids_center
    {c : α} {M : Family α} {E F : Edge α}
    (hAvoid : ∀ ⦃G : Edge α⦄, G ∈ M → c ∉ G)
    (hE : E ∈ M) (hF : F ∈ M) : c ∉ E ∪ F := by
  intro hc
  rcases Finset.mem_union.mp hc with hcE | hcF
  · exact hAvoid hE hcE
  · exact hAvoid hF hcF

/-- Any union containing a star edge contains the center. -/
theorem center_mem_union_of_star_left
    {c : α} {r : ℕ} {S E : Edge α}
    (hS : S ∈ starFamily c r) : c ∈ S ∪ E := by
  exact Finset.mem_union.mpr (Or.inl (mem_starFamily.mp hS).2)

/-- The full star-plus-matching lower construction is admissible. -/
theorem starPlusMatching_admissible
    {c : α} {r : ℕ} {M : Family α}
    (hr : 0 < r)
    (hU : Uniform r M)
    (hMatch : IsMatching M)
    (hAvoid : ∀ ⦃E : Edge α⦄, E ∈ M → c ∉ E) :
    Admissible (starPlusMatching c r M) := by
  intro A B C D hA hB hC hD hq
  simp only [starPlusMatching, Finset.mem_union] at hA hB hC hD
  rcases hA with hAs | hAm <;>
  rcases hB with hBs | hBm <;>
  rcases hC with hCs | hCm <;>
  rcases hD with hDs | hDm
  · exact star_edges_not_disjoint hAs hBs hq.disjAB
  · exact star_edges_not_disjoint hAs hBs hq.disjAB
  · exact star_edges_not_disjoint hAs hBs hq.disjAB
  · exact star_edges_not_disjoint hAs hBs hq.disjAB
  · exact star_edges_not_disjoint hCs hDs hq.disjCD
  · exact mixed_equal_union_impossible
      (S₁ := A) (S₂ := C) (M₁ := B) (M₂ := D)
      hU hMatch hAvoid hCs hBm hDm hq.distinct.bd hq.sameUnion
  · exact mixed_equal_union_impossible
      (S₁ := A) (S₂ := D) (M₁ := B) (M₂ := C)
      hU hMatch hAvoid hDs hBm hCm hq.distinct.bc
      (hq.sameUnion.trans (Finset.union_comm C D))
  · have hcLeft : c ∈ A ∪ B := center_mem_union_of_star_left hAs
    have hcRight : c ∉ C ∪ D := matching_union_avoids_center hAvoid hCm hDm
    apply hcRight
    rw [← hq.sameUnion]
    exact hcLeft
  · exact star_edges_not_disjoint hCs hDs hq.disjCD
  · exact mixed_equal_union_impossible
      (S₁ := B) (S₂ := C) (M₁ := A) (M₂ := D)
      hU hMatch hAvoid hCs hAm hDm hq.distinct.ad
      ((Finset.union_comm B A).trans hq.sameUnion)
  · exact mixed_equal_union_impossible
      (S₁ := B) (S₂ := D) (M₁ := A) (M₂ := C)
      hU hMatch hAvoid hDs hAm hCm hq.distinct.ac
      ((Finset.union_comm B A).trans
        (hq.sameUnion.trans (Finset.union_comm C D)))
  · have hcLeft : c ∈ A ∪ B :=
      Finset.mem_union.mpr (Or.inr (mem_starFamily.mp hBs).2)
    have hcRight : c ∉ C ∪ D := matching_union_avoids_center hAvoid hCm hDm
    apply hcRight
    rw [← hq.sameUnion]
    exact hcLeft
  · exact star_edges_not_disjoint hCs hDs hq.disjCD
  · have hcLeft : c ∉ A ∪ B := matching_union_avoids_center hAvoid hAm hBm
    have hcRight : c ∈ C ∪ D := center_mem_union_of_star_left hCs
    apply hcLeft
    rw [hq.sameUnion]
    exact hcRight
  · have hcLeft : c ∉ A ∪ B := matching_union_avoids_center hAvoid hAm hBm
    have hcRight : c ∈ C ∪ D :=
      Finset.mem_union.mpr (Or.inr (mem_starFamily.mp hDs).2)
    apply hcLeft
    rw [hq.sameUnion]
    exact hcRight
  · exact matching_admissible hr hU hMatch hAm hBm hCm hDm hq

end LowerConstruction

end JSP523
