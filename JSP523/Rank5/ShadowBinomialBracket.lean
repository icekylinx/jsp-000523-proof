import JSP523.Rank5.ShadowPower
import Mathlib.Tactic

/-!
# Binomial bracket for a finite uniform family

The maximal integer binomial threshold below a nonempty family is used by
both finite shadow-power interpolation and shadow allocation.
-/

namespace JSP523.Rank5

/-- A largest integer binomial threshold below a nonempty uniform family.
The upper endpoint may exceed the ambient size by one. -/
theorem exists_binomial_card_bracket
    {n k : ℕ} (A : Family (Fin n)) (hUniform : Uniform k A)
    (hA : A.Nonempty) :
    ∃ t : ℕ, k ≤ t ∧ t ≤ n ∧
      t.choose k ≤ A.card ∧ A.card ≤ (t + 1).choose k := by
  classical
  obtain ⟨E, hE⟩ := hA
  have hkn : k ≤ n := by
    have hEcard := hUniform hE
    have hEbound := Finset.card_le_card (Finset.subset_univ E)
    simpa only [Finset.card_univ, Fintype.card_fin, hEcard] using hEbound
  have hApos : 1 ≤ A.card := by
    have := Finset.card_pos.mpr ⟨E, hE⟩
    omega
  let S := (Finset.range (n + 1)).filter
    (fun t => k ≤ t ∧ t.choose k ≤ A.card)
  have hkS : k ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega), le_rfl, ?_⟩
    simpa only [Nat.choose_self] using hApos
  obtain ⟨t, htS, htmax⟩ :=
    Finset.exists_max_image S (fun t : ℕ => t) ⟨k, hkS⟩
  have ht := Finset.mem_filter.mp htS
  have htn : t ≤ n := by
    have := Finset.mem_range.mp ht.1
    omega
  refine ⟨t, ht.2.1, htn, ht.2.2, ?_⟩
  by_cases htn' : t < n
  · have hnot : ¬ (t + 1).choose k ≤ A.card := by
      intro hnext
      have hnextS : t + 1 ∈ S := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_range.mpr (by omega), by omega, hnext⟩
      have := htmax (t + 1) hnextS
      omega
    omega
  · have hteq : t = n := by omega
    have hSub : A ⊆ (Finset.univ : Finset (Fin n)).powersetCard k := by
      intro T hT
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hUniform hT⟩
    have hBound : A.card ≤ n.choose k := by
      simpa only [Finset.card_powersetCard, Finset.card_univ,
        Fintype.card_fin] using Finset.card_le_card hSub
    exact hBound.trans (Nat.choose_le_choose k (by omega))

end JSP523.Rank5
