import JSP523.Rank5.UniqueBadPairGeometry
import JSP523.Counting.BadPairCleaning

/-!
# Actual tail packing for a fixed unique bad pair

The tail distance comes from the outside-edge geometry and the overlap
trade, then the finite distance-packing lemma counts the tails.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

/-- Actual outside edges on `U = W \ D` containing exactly one bad pair,
the prescribed pair `P`. -/
def uniqueBadPairOutsideEdgeFamily
    (H : Family α) (W : Edge α) (v : α) (r : ℕ) (P : Edge α) : Family α :=
  let Bad₂ := badMissingSets H W v r 2 ((W.card - r - 2).choose (r - 3))
  H.filter fun E => E ⊆ W \ badSingletonVertices H W v r ∧
    P ∈ Bad₂ ∧ P ⊆ E ∧ (Bad₂.filter fun Q => Q ⊆ E).card = 1

private theorem unique_of_singleton_bad_pair_fiber
    (Bad : Family α) (P E Q : Edge α)
    (hP : P ∈ Bad) (hPE : P ⊆ E)
    (hCard : (Bad.filter fun R => R ⊆ E).card = 1)
    (hQ : Q ∈ Bad) (hQE : Q ⊆ E) : Q = P := by
  obtain ⟨R, hR⟩ := Finset.card_eq_one.mp hCard
  have hPm : P ∈ Bad.filter (fun R => R ⊆ E) := Finset.mem_filter.mpr ⟨hP, hPE⟩
  have hQm : Q ∈ Bad.filter (fun R => R ⊆ E) := Finset.mem_filter.mpr ⟨hQ, hQE⟩
  rw [hR] at hPm hQm
  exact (Finset.mem_singleton.mp hQm).trans (Finset.mem_singleton.mp hPm).symm

/-- For every fixed actual bad pair `P`, the family of outside edges whose
unique bad pair is `P` satisfies the finite packing bound from §IV.2.1. -/
theorem fixed_unique_bad_pair_outside_tail_packing
    {H : Family α} {W P : Edge α} {v : α} {r : ℕ}
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hr : 5 ≤ r) (hvW : v ∉ W)
    (hPbad : P ∈ badMissingSets H W v r 2
      ((W.card - r - 2).choose (r - 3))) :
    (uniqueBadPairOutsideEdgeFamily H W v r P).card *
        (r - 2).choose (r - 4) ≤ W.card.choose (r - 4) := by
  classical
  let B := uniqueBadPairOutsideEdgeFamily H W v r P
  let T : Family α := B.image fun E => E \ P
  let Bad₂ := badMissingSets H W v r 2 ((W.card - r - 2).choose (r - 3))
  have hPcard : P.card = 2 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hPbad).1).2
  have hData : ∀ E ∈ B,
      E ⊆ W \ badSingletonVertices H W v r ∧ P ∈ Bad₂ ∧ P ⊆ E ∧
        (Bad₂.filter fun Q => Q ⊆ E).card = 1 := by
    intro E hE
    simpa [B, Bad₂, uniqueBadPairOutsideEdgeFamily] using
      (Finset.mem_filter.mp hE).2
  have hBmem : ∀ E ∈ B, E ∈ H := by
    intro E hE
    have hFilter : E ∈ H.filter (fun E =>
        E ⊆ W \ badSingletonVertices H W v r ∧ P ∈ Bad₂ ∧ P ⊆ E ∧
          (Bad₂.filter fun Q => Q ⊆ E).card = 1) := by
      simpa [B, Bad₂, uniqueBadPairOutsideEdgeFamily] using hE
    exact (Finset.mem_filter.mp hFilter).1
  have hBcard : T.card = B.card := by
    apply Finset.card_image_of_injOn
    intro E hE F hF hEF
    obtain ⟨_, _, hPE, _⟩ := hData E hE
    obtain ⟨_, _, hPF, _⟩ := hData F hF
    have hErepr : E \ P ∪ P = E := Finset.sdiff_union_of_subset hPE
    have hFrepr : F \ P ∪ P = F := Finset.sdiff_union_of_subset hPF
    have hEq := congrArg (fun X : Edge α => X ∪ P) hEF
    rw [hErepr, hFrepr] at hEq
    exact hEq
  have hTsub : ∀ A ∈ T, A ⊆ W := by
    intro A hA
    obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hA
    exact (Finset.sdiff_subset).trans ((hData E hE).1.trans Finset.sdiff_subset)
  have hTuniform : Uniform (r - 2) T := by
    intro A hA
    obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨_, _, hPE, _⟩ := hData E hE
    have hEcard := hUniform (hBmem E hE)
    have hTailCard := Finset.card_sdiff_of_subset hPE
    rw [hPcard] at hTailCard
    omega
  have hTdistance : ∀ ⦃A C : Edge α⦄, A ∈ T → C ∈ T → A ≠ C →
      3 ≤ (A \ C).card := by
    intro A C hA hC hAC
    obtain ⟨E, hE, hAT⟩ := Finset.mem_image.mp hA
    obtain ⟨F, hF, hCT⟩ := Finset.mem_image.mp hC
    obtain ⟨hEoutside, hPbadE, hPE, hEone⟩ := hData E hE
    obtain ⟨hFoutside, hPbadF, hPF, hFone⟩ := hData F hF
    have hEF : E ≠ F := by
      intro hEq
      subst F
      exact hAC (hAT.symm.trans hCT)
    have hGeom := unique_bad_pair_outside_edges_difference_at_least_three
      hAdm hUniform (by omega) hvW
      (hBmem E hE) (hBmem F hF) hEF
      hEoutside hFoutside hPbad hPE hPF
      (fun Q hQ hQE => unique_of_singleton_bad_pair_fiber Bad₂ P E
        Q hPbadE hPE hEone hQ hQE)
      (fun Q hQ hQF => unique_of_singleton_bad_pair_fiber Bad₂ P F
        Q hPbadF hPF hFone hQ hQF)
    have hTailDiff : (E \ P) \ (F \ P) = E \ F := by
      ext x
      simp only [Finset.mem_sdiff]
      constructor
      · rintro ⟨⟨hxE, hxnotP⟩, hxnotTailF⟩
        refine ⟨hxE, ?_⟩
        intro hxF
        exact hxnotTailF ⟨hxF, hxnotP⟩
      · rintro ⟨hxE, hxnotF⟩
        refine ⟨⟨hxE, ?_⟩, ?_⟩
        · intro hxP
          exact hxnotF (hPF hxP)
        · rintro ⟨hxF, _⟩
          exact hxnotF hxF
    rw [← hAT, ← hCT, hTailDiff]
    exact hGeom
  have hPacked := fixed_bad_pair_tail_count hr hTsub hTuniform hTdistance
  simpa [B, T, hBcard] using hPacked

end JSP523
