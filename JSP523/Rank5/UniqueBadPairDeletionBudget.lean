import JSP523.Rank5.UniqueBadPairTailPacking
import JSP523.Rank5.LocalExactDeletion

/-!
# Actual finite deletion budget for unique bad-pair edges

Sum the concrete fixed-root tail packing estimate over the actual bad-pair
family, then apply the bad-set incidence bound. All products stay integral.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

/-- The actual unique-bad-pair stratum has the finite deletion budget
obtained by combining (IV.2.3) with the fixed-root tail packing bound.
The outside edge family `B` is required to lie in `U = W \ D`. -/
theorem unique_bad_pair_outside_deletion_budget
    {H B Bad₂ : Family α} {W : Edge α} {v : α} {r : ℕ}
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hr : 5 ≤ r) (hvW : v ∉ W)
    (hBH : B ⊆ H)
    (hOrdinary : ∀ E ∈ B,
      E ⊆ W \ badSingletonVertices H W v r)
    (hBad₂ : Bad₂ = badMissingSets H W v r 2
      ((W.card - r - 2).choose (r - 3))) :
    ((W.card - r - 2).choose (r - 3)) *
        ((r - 2).choose (r - 4) *
          (uniqueBadPairEdges B Bad₂).card) ≤
      (2 * (r - 1).choose 2 *
        (missingStarFacets H W v r).card) * W.card.choose (r - 4) := by
  classical
  let Λ := (W.card - r - 2).choose (r - 3)
  let p := (r - 2).choose (r - 4)
  let BadActual := badMissingSets H W v r 2 Λ
  let fiber := fun P : Edge α =>
    B.filter fun E => P ⊆ E ∧ (Bad₂.filter fun Q => Q ⊆ E).card = 1
  have hRoot : ∀ P ∈ Bad₂, p * (fiber P).card ≤ W.card.choose (r - 4) := by
    intro P hP
    have hPactual : P ∈ BadActual := by simpa [BadActual, Λ, hBad₂] using hP
    have hActualBound := fixed_unique_bad_pair_outside_tail_packing
      (H := H) (W := W) (P := P) (v := v) (r := r)
      hAdm hUniform hr hvW hPactual
    have hFiberSub : fiber P ⊆ uniqueBadPairOutsideEdgeFamily H W v r P := by
      intro E hE
      obtain ⟨hEB, ⟨hPE, hOne⟩⟩ := Finset.mem_filter.mp hE
      have hHE := hBH hEB
      have hPbad : P ∈ BadActual := hPactual
      have hOneActual : (BadActual.filter fun Q => Q ⊆ E).card = 1 := by
        simpa [BadActual, hBad₂] using hOne
      apply Finset.mem_filter.mpr
      exact ⟨hHE, hOrdinary E hEB, hPbad, hPE, hOneActual⟩
    have hFiberCard := Finset.card_le_card hFiberSub
    calc
      p * (fiber P).card ≤
          p * (uniqueBadPairOutsideEdgeFamily H W v r P).card :=
        Nat.mul_le_mul_left p hFiberCard
      _ ≤ W.card.choose (r - 4) := by
        simpa [p, Nat.mul_comm] using hActualBound
  have hUnion :
      p * (uniqueBadPairEdges B Bad₂).card ≤ Bad₂.card * W.card.choose (r - 4) := by
    unfold uniqueBadPairEdges
    calc
      p * (Bad₂.biUnion fiber).card ≤
          p * (∑ P ∈ Bad₂, (fiber P).card) :=
        Nat.mul_le_mul_left p Finset.card_biUnion_le
      _ = ∑ P ∈ Bad₂, p * (fiber P).card := by
        rw [Finset.mul_sum]
      _ ≤ ∑ _P ∈ Bad₂, W.card.choose (r - 4) :=
        Finset.sum_le_sum hRoot
      _ = Bad₂.card * W.card.choose (r - 4) := by
        simp [Finset.sum_const]
  have hIncidence := bad_missing_sets_card_bound H W v r 2 Λ
  rw [← hBad₂] at hIncidence
  calc
    Λ * (p * (uniqueBadPairEdges B Bad₂).card) ≤
        Λ * (Bad₂.card * W.card.choose (r - 4)) :=
      Nat.mul_le_mul_left Λ hUnion
    _ = (Λ * Bad₂.card) * W.card.choose (r - 4) := by ac_rfl
    _ ≤ (2 * (r - 1).choose 2 *
          (missingStarFacets H W v r).card) * W.card.choose (r - 4) :=
      Nat.mul_le_mul_right _ hIncidence

end JSP523
