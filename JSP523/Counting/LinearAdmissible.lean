import JSP523.Counting.LinearTriple

/-!
# Linear uniform families are admissible above rank two

This simple cardinal obstruction is used by the rank-four equality
constructions.  It is stated at arbitrary rank because the same reasoning
applies to other linear hypergraphs in the project.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

theorem linear_uniform_admissible
    {H : Family α} {r : ℕ}
    (hr : 3 ≤ r) (hU : Uniform r H) (hL : LinearFamily H) :
    Admissible H := by
  intro A B C D hA hB hC hD hq
  have hAC : (A ∩ C).card ≤ 1 :=
    hL hA hC hq.distinct.ac
  have hAD : (A ∩ D).card ≤ 1 :=
    hL hA hD hq.distinct.ad
  have hAsub : A ⊆ C ∪ D := by
    intro x hxA
    have hxAB : x ∈ A ∪ B := Finset.mem_union_left B hxA
    rw [hq.sameUnion] at hxAB
    exact hxAB
  have hAeq : A = (A ∩ C) ∪ (A ∩ D) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · intro hxA
      rcases Finset.mem_union.mp (hAsub hxA) with hxC | hxD
      · exact Or.inl ⟨hxA, hxC⟩
      · exact Or.inr ⟨hxA, hxD⟩
    · rintro (⟨hxA, _⟩ | ⟨hxA, _⟩) <;> exact hxA
  have hCard := Finset.card_union_le (A ∩ C) (A ∩ D)
  rw [← hAeq] at hCard
  have hAcard := hU hA
  omega

end JSP523
