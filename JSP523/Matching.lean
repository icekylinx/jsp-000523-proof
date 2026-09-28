import JSP523.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Matchings as admissible families

This module proves a first nontrivial, fully finite fact used by the extremal
construction: a positive-uniformity matching cannot itself contain a forbidden
quadruple.
-/

namespace JSP523

section Matching

variable {α : Type*} [DecidableEq α]

/-- A hypergraph matching: distinct member edges are disjoint. -/
def IsMatching (M : Family α) : Prop :=
  ∀ ⦃E F : Edge α⦄, E ∈ M → F ∈ M → E ≠ F → Disjoint E F

/-- Any matching of nonempty uniform edges is admissible. -/
theorem matching_admissible {r : ℕ} {M : Family α}
    (hr : 0 < r) (hU : Uniform r M) (hM : IsMatching M) : Admissible M := by
  intro A B C D hA hB hC hD hq
  have hCA : Disjoint C A := hM hC hA hq.distinct.ac.symm
  have hCB : Disjoint C B := hM hC hB hq.distinct.bc.symm
  have hCcard : C.card = r := hU hC
  have hCpos : 0 < C.card := hCcard.symm ▸ hr
  obtain ⟨x, hxC⟩ := Finset.card_pos.mp hCpos
  have hxCD : x ∈ C ∪ D := Finset.mem_union.mpr (Or.inl hxC)
  have hxAB : x ∈ A ∪ B := by
    rw [hq.sameUnion]
    exact hxCD
  rcases Finset.mem_union.mp hxAB with hxA | hxB
  · exact (Finset.disjoint_left.mp hCA) hxC hxA
  · exact (Finset.disjoint_left.mp hCB) hxC hxB

/-- A finite vertex set can be packed by exactly `⌊|W|/r⌋` disjoint
`r`-sets. This supplies the matching in the common construction of
`paper/proof.pdf`, §I. -/
theorem exists_uniform_matching_floor (W : Edge α) (r : ℕ) (hr : 0 < r) :
    ∃ M : Family α,
      IsMatching M ∧ Uniform r M ∧
      (∀ E ∈ M, E ⊆ W) ∧ M.card = W.card / r := by
  classical
  refine Finset.strongInductionOn W ?_
  intro W ih
  by_cases hsmall : W.card < r
  · refine ⟨∅, ?_, ?_, ?_, ?_⟩
    · intro E F hE
      simp at hE
    · intro E hE
      simp at hE
    · intro E hE
      simp at hE
    · simp [Nat.div_eq_of_lt hsmall]
  · have hlarge : r ≤ W.card := by omega
    obtain ⟨E, hEW, hEcard⟩ := Finset.exists_subset_card_eq hlarge
    have hEN : E.Nonempty := Finset.card_pos.mp (by simpa [hEcard] using hr)
    obtain ⟨M, hMatch, hU, hSupport, hMcard⟩ :=
      ih (W \ E) (Finset.sdiff_ssubset hEW hEN)
    have hEM : E ∉ M := by
      intro hEM
      obtain ⟨x, hxE⟩ := hEN
      exact (Finset.mem_sdiff.mp (hSupport E hEM hxE)).2 hxE
    have hDisj : ∀ F ∈ M, Disjoint E F := by
      intro F hF
      apply Finset.disjoint_left.mpr
      intro x hxE hxF
      exact (Finset.mem_sdiff.mp (hSupport F hF hxF)).2 hxE
    refine ⟨insert E M, ?_, ?_, ?_, ?_⟩
    · intro A B hA hB hne
      rcases Finset.mem_insert.mp hA with hAE | hA
      · subst A
        rcases Finset.mem_insert.mp hB with hBE | hB
        · exact False.elim (hne hBE.symm)
        · exact hDisj B hB
      · rcases Finset.mem_insert.mp hB with hBE | hB
        · subst B
          exact (hDisj A hA).symm
        · exact hMatch hA hB hne
    · intro A hA
      rcases Finset.mem_insert.mp hA with rfl | hA
      · exact hEcard
      · exact hU hA
    · intro A hA
      rcases Finset.mem_insert.mp hA with rfl | hA
      · exact hEW
      · exact (hSupport A hA).trans Finset.sdiff_subset
    · rw [Finset.card_insert_of_notMem hEM, hMcard,
        Finset.card_sdiff_of_subset hEW, hEcard]
      calc
        (W.card - r) / r + 1 = (W.card - r + r) / r := by
          rw [Nat.add_div_right _ hr]
        _ = W.card / r := by rw [Nat.sub_add_cancel hlarge]

/-- The vertex union of an `r`-uniform matching has `r |M|` vertices. -/
theorem matching_vertex_union_card
    (M : Family α) (r : ℕ)
    (hMatch : IsMatching M) (hUniform : Uniform r M) :
    (M.biUnion id).card = r * M.card := by
  classical
  have hDisjoint : (↑M : Set (Edge α)).PairwiseDisjoint id := by
    intro E hE F hF hne
    exact hMatch hE hF hne
  calc
    (M.biUnion id).card = ∑ E ∈ M, E.card := Finset.card_biUnion hDisjoint
    _ = ∑ _E ∈ M, r := Finset.sum_congr rfl fun E hE => hUniform hE
    _ = r * M.card := by simp [mul_comm]

/-- Every `r`-uniform matching supported on `W` has at most
`⌊|W|/r⌋` edges. -/
theorem uniform_matching_card_le_floor
    (W : Edge α) (M : Family α) (r : ℕ) (hr : 0 < r)
    (hMatch : IsMatching M) (hUniform : Uniform r M)
    (hSupport : ∀ E ∈ M, E ⊆ W) :
    M.card ≤ W.card / r := by
  have hUnionSub : M.biUnion id ⊆ W := by
    intro x hx
    obtain ⟨E, hE, hxE⟩ := Finset.mem_biUnion.mp hx
    exact hSupport E hE hxE
  have hBound : r * M.card ≤ W.card := by
    rw [← matching_vertex_union_card M r hMatch hUniform]
    exact Finset.card_le_card hUnionSub
  apply (Nat.le_div_iff_mul_le hr).2
  simpa [mul_comm] using hBound

/-- When `r` divides the ground-set size, a matching of `|W|/r`
blocks covers every vertex of `W`. -/
theorem matching_covers_of_divisible
    (W : Edge α) (M : Family α) (r : ℕ)
    (hMatch : IsMatching M) (hUniform : Uniform r M)
    (hSupport : ∀ E ∈ M, E ⊆ W)
    (hCard : M.card = W.card / r) (hDiv : r ∣ W.card) :
    M.biUnion id = W := by
  have hSubset : M.biUnion id ⊆ W := by
    intro x hx
    obtain ⟨E, hE, hxE⟩ := Finset.mem_biUnion.mp hx
    exact hSupport E hE hxE
  apply Finset.eq_of_subset_of_card_le hSubset
  have hUnionCard := matching_vertex_union_card M r hMatch hUniform
  have hMod : W.card % r = 0 := Nat.mod_eq_zero_of_dvd hDiv
  have hDivEq := Nat.mod_add_div W.card r
  rw [hUnionCard, hCard]
  omega

/-- A perfectly covering `r`-uniform matching exists whenever `r` divides
the number of vertices. -/
theorem exists_perfect_uniform_matching
    (W : Edge α) (r : ℕ) (hr : 0 < r) (hDiv : r ∣ W.card) :
    ∃ M : Family α,
      IsMatching M ∧ Uniform r M ∧
      (∀ E ∈ M, E ⊆ W) ∧
      M.biUnion id = W ∧ M.card = W.card / r := by
  obtain ⟨M, hMatch, hUniform, hSupport, hCard⟩ :=
    exists_uniform_matching_floor W r hr
  exact ⟨M, hMatch, hUniform, hSupport,
    matching_covers_of_divisible W M r hMatch hUniform hSupport hCard hDiv,
    hCard⟩
end Matching

end JSP523
