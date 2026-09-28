import JSP523.ExtremalScope
import Mathlib.Data.Finset.Powerset

/-!
# Corollary II.2: the finite triple-star lower bound

For a finite vertex set `V`, the triples through a fixed center form an
admissible supported family with `choose (|V|-1) 2` edges.
-/

namespace JSP523.Rank3

variable {α : Type*} [DecidableEq α]

/-- All triples contained in `V` that contain the center `c`. -/
def tripleStar (V : Edge α) (c : α) : Family α :=
  (V.powersetCard 3).filter (fun E => c ∈ E)

@[simp] theorem mem_tripleStar {V : Edge α} {c : α} {E : Edge α} :
    E ∈ tripleStar V c ↔ E ⊆ V ∧ E.card = 3 ∧ c ∈ E := by
  simp [tripleStar, and_assoc]

theorem triple_star_uniform (V : Edge α) (c : α) :
    Uniform 3 (tripleStar V c) := by
  intro E hE
  exact (mem_tripleStar.mp hE).2.1

theorem triple_star_supported (V : Edge α) (c : α) :
    tripleStar V c ⊆ V.powersetCard 3 := by
  intro E hE
  exact Finset.mem_powersetCard.mpr
    ⟨(mem_tripleStar.mp hE).1, (mem_tripleStar.mp hE).2.1⟩

theorem triple_star_admissible (V : Edge α) (c : α) :
    Admissible (tripleStar V c) := by
  intro A B C D hA hB hC hD hq
  have hcA : c ∈ A := (mem_tripleStar.mp hA).2.2
  have hcB : c ∈ B := (mem_tripleStar.mp hB).2.2
  exact (Finset.disjoint_left.mp hq.disjAB) hcA hcB

theorem triple_star_card (V : Edge α) (c : α) (hc : c ∈ V) :
    (tripleStar V c).card = Nat.choose (V.card - 1) 2 := by
  rw [tripleStar]
  have hsubset : ({c} : Finset α) ⊆ V := by simpa using hc
  have hcount := Finset.card_filter_powersetCard_subset
    ({c} : Finset α) V 3 hsubset (by simp)
  simpa using hcount

theorem triple_star_lower_bound (V : Edge α) (c : α) (hc : c ∈ V) :
    Nat.choose (V.card - 1) 2 ≤ maxAvoidingCard V 3 := by
  rw [← triple_star_card V c hc]
  exact max_avoiding_card_upper
    (triple_star_supported V c) (triple_star_admissible V c)

/-- The finite lower half of Corollary II.2. -/
theorem corollary_ii_2_lower (V : Edge α) (c : α) (hc : c ∈ V) :
    Nat.choose (V.card - 1) 2 ≤ maxAvoidingCard V 3 :=
  triple_star_lower_bound V c hc

end JSP523.Rank3
