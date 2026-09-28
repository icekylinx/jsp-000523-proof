import JSP523.Rank5.LocalExactTheorem
import JSP523.Rank5.LocalEqualityForward

/-!
# Equality in the fixed-rank local theorem

This assembles the two forward equality cases of §IV.2.3 from the actual
quantitative hypotheses of Theorem IV.2.1. The complete-star case has a
maximum outside matching. With one missing star facet, the outside family
has the two-core-edge structure and a matching on the remaining vertices.
-/

namespace JSP523

/-- Both forward equality cases in Theorem IV.2.1, using the same explicit
rank-only constants as `quantitative_near_star_exact`. -/
theorem quantitative_local_equality_classification
    {α : Type*} [DecidableEq α]
    (H : Family α) (W : Edge α) (v : α) (r : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hSupport : ∀ E ∈ H, E ⊆ insert v W)
    (hvW : v ∉ W) (hr : 5 ≤ r)
    (hw₀ : localExactGroundThreshold r ≤ W.card)
    (hDensity : ((missingStarFacets H W v r).card : ℝ) ≤
      localExactDensity r * (W.card : ℝ) ^ (r - 1))
    (hEquality : H.card = W.card.choose (r - 1) + W.card / r) :
    ((missingStarFacets H W v r).card = 0 ∧
      IsMatching (outsideFamily H W) ∧
      (outsideFamily H W).card = W.card / r) ∨
    (∃ (P : Edge α) (x : α) (Q : Edge α) (M : Family α),
      missingStarFacets H W v r = {P} ∧ P.card = r - 1 ∧
      W.card % r = r - 1 ∧
      x ∈ W ∧ x ∉ P ∧ Q.card = r - 1 ∧
      Disjoint P Q ∧ x ∉ Q ∧
      outsideFamily H W =
        insert (insert x P) (insert (insert x Q) M) ∧
      IsMatching M ∧
      (∀ E ∈ M, Disjoint E (insert x P ∪ insert x Q)) ∧
      M.biUnion (fun E => E) =
        W \ (insert x P ∪ insert x Q)) := by
  classical
  let B := outsideFamily H W
  let q := (missingStarFacets H W v r).card
  have hWcard : 2 * r - 1 ≤ W.card := by
    have hFour : 4 * r ≤ W.card := by
      dsimp [localExactGroundThreshold] at hw₀
      exact (Nat.le_max_left _ _).trans hw₀
    omega
  have hLin : LinearFamily B :=
    (outside_linear_incidence_of_quantitative_baseline H W v r
      hAdm hUniform hSupport hvW hr hw₀ hDensity
      (by rw [hEquality]; exact Nat.le_add_right _ _)).1
  have hRestr := near_star_equality_missing_restriction
    hAdm hUniform hSupport hvW (by omega : 3 ≤ r) hLin hEquality
  by_cases hZero : q = 0
  · left
    have hMatch := complete_star_equality_max_matching
      hAdm hUniform hSupport hvW hWcard hZero hEquality
    exact ⟨hZero, hMatch.1, hMatch.2⟩
  · right
    have hOne : q = 1 := by omega
    obtain ⟨P, hP⟩ := Finset.card_eq_one.mp hOne
    have hMissing : missingStarFacets H W v r = {P} := hP
    have hPmem : P ∈ missingStarFacets H W v r := by simp [hMissing]
    have hPcard : P.card = r - 1 :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hPmem).1).2
    have hMod : W.card % r = r - 1 := hRestr.2 hOne
    have hBH : B ⊆ H := Finset.filter_subset _ _
    have hBU : Uniform r B := fun E hE => hUniform (hBH hE)
    have hBW : ∀ E ∈ B, E ⊆ W := by
      intro E hE
      exact (Finset.mem_filter.mp hE).2
    have hFacets := present_add_missing_star_facets H W v r
    have hQBound : q ≤ W.card.choose (r - 1) := by
      change (presentStarFacets H W v r).card + q =
        W.card.choose (r - 1) at hFacets
      omega
    have hId := near_star_card_identity hUniform hSupport hvW
    change H.card = W.card.choose (r - 1) - q + B.card at hId
    have hDiv : W.card = r * (W.card / r) + W.card % r := by
      simpa [add_comm, mul_comm] using (Nat.mod_add_div W.card r).symm
    have hb : B.card = W.card / r + 1 := by omega
    have hCount : r * B.card = W.card + 1 := by
      rw [hb, mul_add]
      omega
    obtain ⟨x, Q, M, hxW, hxP, hQcard, hPQ, hxQ,
      hBform, hMatch, hMdisj, hCover⟩ :=
      Rank5.one_missing_equality_outside_normal_form
        hAdm hBH hBU hLin (by omega : 3 ≤ r) hBW hvW
          hMissing hPcard hCount
    exact ⟨P, x, Q, M, hMissing, hPcard, hMod, hxW, hxP,
      hQcard, hPQ, hxQ, hBform, hMatch, hMdisj, hCover⟩

end JSP523
