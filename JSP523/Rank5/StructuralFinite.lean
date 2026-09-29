import JSP523.Rank5.CleanupFiniteCost
import JSP523.Rank5.RootedPrefixEndpoint

/-! # Rank-five finite structural theorem from an actual parent family

Both cleanup families, the majority labels, inheritance repair, roots,
and prefixes are constructed. Only numerical parameters and ordinary
parent codegree caps remain in the finite bound.
-/

namespace JSP523.Rank5

noncomputable def rankFiveInheritanceCost (n m P Q L₃ t D₃ D₄ : ℕ) : ℝ :=
  40 * (P : ℝ) * m / Q + 4 * (n.choose 2 : ℝ) ^ 2 * D₃ * D₄ * D₄ / ((t : ℝ) * L₃)

noncomputable def rankFivePrefixCost (n D₃ D₄ : ℕ) (ε : ℝ) : ℝ :=
  (n.choose 3 : ℝ) * ((1 + 2 * (D₄ - 1) : ℕ) : ℝ) +
    Real.sqrt ((n.choose 3 : ℝ) *
      ((n.choose 2 * (n - 2).choose 2 : ℕ) : ℝ) * max 7 (1 + ε * D₃))

noncomputable def rankFiveStructuralError
    (n m P Q L₃ tLower tUpper u q D₂ D₃ D₄ : ℕ) (ε : ℝ) : ℝ :=
  rankFiveLowerCleanupCost n m tLower u q D₃ D₄ +
    rankFiveUpperCleanupCost n tUpper D₂ D₃ D₄ +
    rankFiveInheritanceCost n m P Q L₃ tLower D₃ D₄ +
    rankFivePrefixCost n D₃ D₄ ε

variable {α : Type*} [DecidableEq α] [Nonempty α]

/-- The finite rank-five structural deficit, with no labels, subfamily,
    root assignment, deletion-cost bound or coloring hypotheses supplied
    by the caller. -/
theorem rank_five_finite_structural_surplus_bound
    (H : Family α) (V : Edge α)
    (P Q L₃ tLower tUpper u q D₂ D₃ D₄ : ℕ) (ε : ℝ)
    (hAdm : Admissible H) (hUniform : Uniform 5 H)
    (hAmbient : ∀ E ∈ H, E ⊆ V)
    (hu : 8 ≤ u) (htLower : 1 ≤ tLower) (htUpper : 1 ≤ tUpper)
    (hqPos : 0 < q) (hQ : 0 < Q) (hL₃ : 0 < L₃)
    (hRetention : Q * L₃ ≤ P * u) (hq : 4 * q ≤ L₃) (hqu : q < u)
    (hScale : (q : ℝ) ≤ ε * u) (hε : 0 ≤ ε) (hD₄pos : 1 ≤ D₄)
    (hD₂ : ∀ S : Edge α, S.card = 2 → (H.filter fun E => S ⊆ E).card ≤ D₂)
    (hD₃ : ∀ S : Edge α, S.card = 3 → (H.filter fun E => S ⊆ E).card ≤ D₃)
    (hD₄ : ∀ S : Edge α, S.card = 4 → (H.filter fun E => S ⊆ E).card ≤ D₄) :
    (H.card : ℝ) - ((fourShadow H).card : ℝ) ≤ -(H.card : ℝ) +
      2 * rankFiveStructuralError V.card H.card
        P Q L₃ tLower tUpper u q D₂ D₃ D₄ ε := by
  classical
  let z := lowerMajorityLabel H V tLower
  let upper := upperFacetColorCleanupEdges H V tUpper
  let lower := multilevelDeletedEdges H V (V.powersetCard 3) 2 u q
    (fun B R T => ¬ ActualStrongPartner H V R T 2 3 tLower (z B))
  let K := H \ (upper ∪ lower)
  have hKH : K ⊆ H := Finset.sdiff_subset
  have hUniformK : Uniform 5 K := fun E hE => hUniform (hKH hE)
  have hUpper : Disjoint K upper := by
    apply Finset.disjoint_left.mpr
    intro E hE hU
    exact (Finset.mem_sdiff.mp hE).2 (Finset.mem_union_left _ hU)
  have hLower : Disjoint K lower := by
    apply Finset.disjoint_left.mpr
    intro E hE hL
    exact (Finset.mem_sdiff.mp hE).2 (Finset.mem_union_right _ hL)
  have hLoss : H \ K ⊆ upper ∪ lower := by
    intro E hE
    by_contra hD
    exact (Finset.mem_sdiff.mp hE).2 (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hE).1,hD⟩)
  have hLossNat := (Finset.card_le_card hLoss).trans (Finset.card_union_le upper lower)
  have hLossReal : ((H \ K).card : ℝ) ≤ (upper.card : ℝ) + lower.card := by exact_mod_cast hLossNat
  have hUC := upper_cleanup_card_le_explicit_cost H V tUpper D₂ D₃ D₄
    hAdm htUpper hD₂ hD₃ hD₄
  have hLC := lower_cleanup_card_le_explicit_cost H V tLower u q D₃ D₄
    hAdm hUniform hAmbient hu htLower hqPos hD₃ hD₄
  have hMain := four_shadow_surplus_bound_with_inheritance_budget
    K H V P Q L₃ tLower tUpper u q D₃ D₄ ε z
    hAdm hKH hUniformK hUniform hAmbient hUpper hLower hScale
    hQ hL₃ htLower hRetention hq hqu hD₄pos hε hD₃ hD₄
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hTReal : (0 : ℝ) < tLower := by exact_mod_cast (by omega : 0 < tLower)
  have hLReal : (0 : ℝ) < L₃ := by exact_mod_cast hL₃
  have hRatio :
      ((tLower * (2 * L₃) * (40 * P * H.card) +
        Q * (8 * (V.powersetCard 2).card ^ 2 * D₃ * D₄ * D₄) : ℕ) : ℝ) /
        ((Q * tLower * (2 * L₃) : ℕ) : ℝ) =
      rankFiveInheritanceCost V.card H.card P Q L₃ tLower D₃ D₄ := by
    dsimp [rankFiveInheritanceCost]
    simp only [Finset.card_powersetCard, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    field_simp
    ring
  dsimp only at hMain
  rw [hRatio] at hMain
  change (H.card : ℝ) - ((fourShadow H).card : ℝ) ≤ _ at hMain
  change (upper.card : ℝ) ≤ _ at hUC
  change (lower.card : ℝ) ≤ _ at hLC
  dsimp [rankFiveStructuralError, rankFivePrefixCost]
  linarith

end JSP523.Rank5
