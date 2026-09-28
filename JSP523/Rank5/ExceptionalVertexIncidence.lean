import JSP523.Counting.BadSetIncidence
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Exceptional-vertex incidences near a star

This file proves the finite double counts and the exceptional-vertex
missing-facet estimate (IV.2.8) of
`paper/proof.pdf`. The factor-two formulation keeps all
terms in natural numbers.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

/-- Counting incidences between missing facets and designated vertices
in either order. -/
theorem sum_singleton_multiplicity_eq_intersection_card
    (M : Family α) (D : Edge α) :
    (∑ x ∈ D, setMultiplicity M ({x} : Edge α)) =
      ∑ S ∈ M, (S ∩ D).card := by
  classical
  simp only [setMultiplicity, Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _hS
  have hFilter :
      (D.filter fun x => ({x} : Edge α) ⊆ S) = S ∩ D := by
    ext x
    simp [Finset.singleton_subset_iff, and_comm]
  rw [← Finset.card_filter, hFilter]

/-- Counting pairs contained in a missing facet and in the designated
exceptional set, in either order. -/
theorem sum_pair_multiplicity_eq_intersection_choose
    (M : Family α) (D : Edge α) :
    (∑ P ∈ D.powersetCard 2, setMultiplicity M P) =
      ∑ S ∈ M, (S ∩ D).card.choose 2 := by
  classical
  simp only [setMultiplicity, Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _hS
  have hFilter :
      (D.powersetCard 2).filter (fun P => P ⊆ S) =
        (S ∩ D).powersetCard 2 := by
    ext P
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hPD, hPcard⟩, hPS⟩
      exact ⟨Finset.subset_inter hPS hPD, hPcard⟩
    · rintro ⟨hPInt, hPcard⟩
      exact ⟨⟨hPInt.trans Finset.inter_subset_right, hPcard⟩,
        hPInt.trans Finset.inter_subset_left⟩
  rw [← Finset.card_filter, hFilter, Finset.card_powersetCard]

/-- Each exceptional pair belongs to at most the full number of
`t`-subsets of `W` containing it. -/
theorem sum_pair_multiplicity_le_universe_budget
    {M : Family α} {W D : Edge α} {t : ℕ}
    (hM : M ⊆ W.powersetCard t) (hD : D ⊆ W)
    (ht : 2 ≤ t) :
    (∑ S ∈ M, (S ∩ D).card.choose 2) ≤
      D.card.choose 2 * (W.card - 2).choose (t - 2) := by
  classical
  rw [← sum_pair_multiplicity_eq_intersection_choose]
  have hEach : ∀ P ∈ D.powersetCard 2,
      setMultiplicity M P ≤ (W.card - 2).choose (t - 2) := by
    intro P hP
    obtain ⟨hPD, hPcard⟩ := Finset.mem_powersetCard.mp hP
    have hPW : P ⊆ W := hPD.trans hD
    have hSub : (M.filter fun S => P ⊆ S) ⊆
        ((W.powersetCard t).filter fun S => P ⊆ S) := by
      intro S hS
      obtain ⟨hSM, hPS⟩ := Finset.mem_filter.mp hS
      exact Finset.mem_filter.mpr ⟨hM hSM, hPS⟩
    have hCount := Finset.card_filter_powersetCard_subset
      P W t hPW (by omega : P.card ≤ t)
    unfold setMultiplicity
    have hCard := Finset.card_le_card hSub
    rw [hCount] at hCard
    simpa [hPcard] using hCard
  have hSum := Finset.sum_le_card_nsmul (D.powersetCard 2)
    (fun P => setMultiplicity M P)
    ((W.card - 2).choose (t - 2)) hEach
  simpa [Finset.card_powersetCard, nsmul_eq_mul] using hSum

private theorem card_le_nonempty_indicator_add_choose_two (i : ℕ) :
    i ≤ (if 0 < i then 1 else 0) + i.choose 2 := by
  cases i with
  | zero => simp
  | succ n =>
    have hChoose : (n + 1).choose 2 = n + n.choose 2 := by
      simpa [Nat.choose_one_right] using Nat.choose_succ_succ n 1
    simp only [Nat.zero_lt_succ, ↓reduceIte]
    rw [hChoose]
    omega

/-- A missing facet counted `i` times by exceptional vertices costs one
base count and at most one unit for each exceptional pair it contains. -/
theorem sum_intersection_card_le_meeting_add_pairs
    (M : Family α) (D : Edge α) :
    (∑ S ∈ M, (S ∩ D).card) ≤
      (M.filter fun S => (S ∩ D).Nonempty).card +
        ∑ S ∈ M, (S ∩ D).card.choose 2 := by
  classical
  calc
    (∑ S ∈ M, (S ∩ D).card) ≤
        ∑ S ∈ M,
          ((if (S ∩ D).Nonempty then 1 else 0) +
            (S ∩ D).card.choose 2) := by
      apply Finset.sum_le_sum
      intro S _hS
      have hPoint := card_le_nonempty_indicator_add_choose_two (S ∩ D).card
      simpa [Finset.card_pos] using hPoint
    _ = (M.filter fun S => (S ∩ D).Nonempty).card +
          ∑ S ∈ M, (S ∩ D).card.choose 2 := by
      rw [Finset.sum_add_distrib]
      rw [Finset.card_filter]

/-- Exact finite upper half of (IV.2.8), prior to the bad-singleton
threshold: `q_D` counts missing facets meeting `D`; the pair term is `J`. -/
theorem exceptional_vertex_multiplicity_upper
    {M : Family α} {W D : Edge α} {t : ℕ}
    (hM : M ⊆ W.powersetCard t) (hD : D ⊆ W)
    (ht : 2 ≤ t) :
    (∑ x ∈ D, setMultiplicity M ({x} : Edge α)) ≤
      (M.filter fun S => (S ∩ D).Nonempty).card +
        D.card.choose 2 * (W.card - 2).choose (t - 2) := by
  rw [sum_singleton_multiplicity_eq_intersection_card]
  exact (sum_intersection_card_le_meeting_add_pairs M D).trans
    (Nat.add_le_add_left
      (sum_pair_multiplicity_le_universe_budget hM hD ht) _)

/-- Equation (IV.2.8), multiplied by two to avoid natural-number
division. All terms use the actual missing star facets and bad vertices. -/
theorem bad_singleton_exceptional_budget
    (H : Family α) (W : Edge α) (v : α) (r : ℕ)
    (hr : 3 ≤ r) :
    let M := missingStarFacets H W v r
    let D := badSingletonVertices H W v r
    let Λ := (W.card - r - 1).choose (r - 2)
    Λ * D.card ≤
      2 * ((M.filter fun S => (S ∩ D).Nonempty).card +
        D.card.choose 2 * (W.card - 2).choose (r - 3)) := by
  classical
  intro M D Λ
  have hM : M ⊆ W.powersetCard (r - 1) := Finset.filter_subset _ _
  have hD : D ⊆ W := Finset.filter_subset _ _
  have hThreshold : ∀ x ∈ D,
      Λ ≤ 2 * setMultiplicity M ({x} : Edge α) := by
    intro x hx
    exact (Finset.mem_filter.mp
      ((Finset.mem_filter.mp hx).2 :
        ({x} : Edge α) ∈ badMissingSets H W v r 1 Λ)).2
  have hLower : Λ * D.card ≤
      2 * ∑ x ∈ D, setMultiplicity M ({x} : Edge α) := by
    calc
      Λ * D.card = ∑ _x ∈ D, Λ := by simp [Finset.sum_const, mul_comm]
      _ ≤ ∑ x ∈ D, 2 * setMultiplicity M ({x} : Edge α) :=
        Finset.sum_le_sum hThreshold
      _ = 2 * ∑ x ∈ D, setMultiplicity M ({x} : Edge α) := by
        rw [Finset.mul_sum]
  have hUpper := exceptional_vertex_multiplicity_upper hM hD
    (by omega : 2 ≤ r - 1)
  exact hLower.trans (Nat.mul_le_mul_left 2 (by simpa [Nat.sub_sub] using hUpper))

end JSP523
