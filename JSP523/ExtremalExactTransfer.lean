import JSP523.ExtremalScope
import Mathlib.Data.Fintype.Card

/-!
# Transfer from an extremal family theorem to the forcing threshold

These finite lemmas apply to the exact rank-four and higher-rank results in
Theorem 1 of `paper/proof.pdf`.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

/-- An attaining admissible family and a universal upper bound determine the
extremal function. -/
theorem max_avoiding_card_eq_of_exact_bound
    (V : Edge α) (r m : ℕ)
    (hWitness : ∃ H : Family α,
      H ⊆ V.powersetCard r ∧ Admissible H ∧ H.card = m)
    (hUpper : ∀ H : Family α,
      H ⊆ V.powersetCard r → Admissible H → H.card ≤ m) :
    maxAvoidingCard V r = m := by
  obtain ⟨H, hSupport, hAdm, hCard⟩ := hWitness
  have hLower := max_avoiding_card_upper hSupport hAdm
  obtain ⟨F, hFSupport, hFAdm, hFCard⟩ :=
    max_avoiding_card_attained V r
  have hBound := hUpper F hFSupport hFAdm
  omega

/-- A family theorem stated with uniformity on `Fin n` determines the exact
maximum in the notation of the manuscript. -/
theorem max_avoiding_card_fin_eq_of_family_exact
    (n r m : ℕ)
    (hWitness : ∃ H : Family (Fin n),
      Admissible H ∧ Uniform r H ∧ H.card = m)
    (hUpper : ∀ H : Family (Fin n),
      Admissible H → Uniform r H → H.card ≤ m) :
    maxAvoidingCard (Finset.univ : Edge (Fin n)) r = m := by
  apply max_avoiding_card_eq_of_exact_bound
  · obtain ⟨H, hAdm, hUniform, hCard⟩ := hWitness
    refine ⟨H, ?_, hAdm, hCard⟩
    intro E hE
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ E, hUniform hE⟩
  · intro H hSupport hAdm
    apply hUpper H hAdm
    intro E hE
    exact (Finset.mem_powersetCard.mp (hSupport hE)).2

/-- The same exact family theorem gives the least forcing threshold. -/
theorem forcing_threshold_fin_exact_of_family_exact
    (n r m : ℕ)
    (hWitness : ∃ H : Family (Fin n),
      Admissible H ∧ Uniform r H ∧ H.card = m)
    (hUpper : ∀ H : Family (Fin n),
      Admissible H → Uniform r H → H.card ≤ m) :
    IsForcingThreshold (Finset.univ : Edge (Fin n)) r (m + 1) ∧
      ∀ k, IsForcingThreshold (Finset.univ : Edge (Fin n)) r k →
        m + 1 ≤ k := by
  have hExact := max_avoiding_card_fin_eq_of_family_exact
    n r m hWitness hUpper
  simpa only [hExact] using
    forcing_threshold_exact (Finset.univ : Edge (Fin n)) r

end JSP523
