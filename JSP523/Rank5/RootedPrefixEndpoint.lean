import JSP523.Rank5.RootedPrefixBound
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Rank-five surplus from the actual cleanup and prefix count

This gives the finite IV.B endpoint, with the rooted term eliminated by
solving its quadratic inequality. The remaining costs are the actual
initial edge deletion and the actual inheritance bad incidences.
-/

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α] [Nonempty α]

omit [DecidableEq α] [Nonempty α] in
/-- A nonnegative solution of the prefix quadratic has this elementary
    upper bound. -/
theorem prefix_quadratic_le_linear_add_sqrt
    {x a b : ℝ} (_hx : 0 ≤ x) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : x ^ 2 ≤ a * x + b) : x ≤ a + Real.sqrt b := by
  have hs := Real.sqrt_nonneg b
  have he := Real.sq_sqrt hb
  by_contra hn
  have hlt : a + Real.sqrt b < x := lt_of_not_ge hn
  have hxS : Real.sqrt b < x := by linarith
  have hprod := mul_pos (by linarith : 0 < x) (sub_pos.mpr hlt)
  nlinarith [mul_nonneg hs (sub_nonneg.mpr hxS.le)]

theorem four_shadow_surplus_bound_of_actual_cleanups
    (K H : Family α) (V : Edge α)
    (tLower tUpper u q D D₄ : ℕ) (ε : ℝ)
    (tripleLabel : Edge α → α)
    (hAdmH : Admissible H)
    (hKH : K ⊆ H) (hUniformK : Uniform 5 K)
    (hUniformH : Uniform 5 H)
    (hAmbientH : ∀ E ∈ H, E ⊆ V)
    (hUpperSurvive : Disjoint K
      (upperFacetColorCleanupEdges H V tUpper))
    (hLowerSurvive : Disjoint K
      (multilevelDeletedEdges H V (V.powersetCard 3) 2 u q
        (fun B R T => ¬ ActualStrongPartner H V R T 2 3 tLower
          (tripleLabel B))))
    (hScale : (q : ℝ) ≤ ε * (u : ℝ))
    (hD₄pos : 1 ≤ D₄) (hε : 0 ≤ ε)
    (hD : ∀ A : Edge α, A.card = 3 →
      (H.filter (fun E => A ⊆ E)).card ≤ D)
    (hD₄ : ∀ Q : Edge α, Q.card = 4 →
      (H.filter (fun E => Q ⊆ E)).card ≤ D₄) :
    let center := upperFacetColorCenter K H V tUpper hKH hUniformK
      (fun E hE => hAmbientH E (hKH hE)) hUpperSurvive
    (H.card : ℝ) - ((fourShadow H).card : ℝ) ≤ -(H.card : ℝ) +
      2 * (((H \ K).card : ℝ) +
        ((facetBadIncidences K V center tripleLabel).card : ℝ) +
        (V.card.choose 3 : ℝ) * ((1 + 2 * (D₄ - 1) : ℕ) : ℝ) +
        Real.sqrt ((V.card.choose 3 : ℝ) *
          ((V.card.choose 2 * (V.card - 2).choose 2 : ℕ) : ℝ) *
            max 7 (1 + ε * (D : ℝ)))) := by
  classical
  let center := upperFacetColorCenter K H V tUpper hKH hUniformK
    (fun E hE => hAmbientH E (hKH hE)) hUpperSurvive
  let L := repairSharedFacetInheritance K center tripleLabel
  let R := rootedEdges L tripleLabel
  have hD₄L : ∀ Q : Edge α, Q.card = 4 →
      (L.filter fun E => Q ⊆ E).card ≤ D₄ := by
    intro Q hQ
    apply (Finset.card_le_card ?_).trans (hD₄ Q hQ)
    intro E hE
    have h := Finset.mem_filter.mp hE
    exact Finset.mem_filter.mpr ⟨hKH (Finset.mem_of_mem_filter E h.1), h.2⟩
  have hQuadratic := rooted_prefix_bound_of_actual_cleanups
    K H V tLower tUpper u q D D₄ ε tripleLabel
    hAdmH hKH hUniformK hUniformH hAmbientH hUpperSurvive
    hLowerSurvive hScale hD₄pos hε hD hD₄L
  change (R.card : ℝ) ^ 2 ≤ _ at hQuadratic
  have hRoot : (R.card : ℝ) ≤
      (V.card.choose 3 : ℝ) * ((1 + 2 * (D₄ - 1) : ℕ) : ℝ) +
      Real.sqrt ((V.card.choose 3 : ℝ) *
        ((V.card.choose 2 * (V.card - 2).choose 2 : ℕ) : ℝ) *
          max 7 (1 + ε * (D : ℝ))) := by
    apply prefix_quadratic_le_linear_add_sqrt (Nat.cast_nonneg _)
      (by positivity) (by positivity)
    nlinarith [hQuadratic]
  have hFacetCenters : ∀ A ∈ sharedFourShadow K, center A ∈ A := by
    intro A hA
    exact (upper_facet_color_center_spec K H V tUpper hKH hUniformK
      (fun E hE => hAmbientH E (hKH hE)) hUpperSurvive hA).1
  have hLedger := four_shadow_bound_after_facet_incidence_repair
    K V center tripleLabel hUniformK
    (fun E hE => hAmbientH E (hKH hE)) hFacetCenters
  have hLedgerReal : 2 * (K.card : ℝ) ≤ ((fourShadow K).card : ℝ) +
      2 * (R.card : ℝ) +
      2 * ((facetBadIncidences K V center tripleLabel).card : ℝ) := by
    exact_mod_cast hLedger
  have hShadow : ((fourShadow K).card : ℝ) ≤ ((fourShadow H).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (four_shadow_mono hKH)
  have hLossNat := Finset.card_sdiff_add_card_eq_card hKH
  have hLoss : ((H \ K).card : ℝ) + (K.card : ℝ) = (H.card : ℝ) := by
    exact_mod_cast hLossNat
  change (H.card : ℝ) - ((fourShadow H).card : ℝ) ≤ _
  linarith

/-- The finite rank-five structural surplus estimate with the IV.9 bad
    incidence count discharged by its actual witness budget. -/
theorem four_shadow_surplus_bound_with_inheritance_budget
    (K H : Family α) (V : Edge α)
    (P Q L₃ tLower tUpper u q D D₄ : ℕ) (ε : ℝ)
    (tripleLabel : Edge α → α)
    (hAdmH : Admissible H)
    (hKH : K ⊆ H) (hUniformK : Uniform 5 K)
    (hUniformH : Uniform 5 H)
    (hAmbientH : ∀ E ∈ H, E ⊆ V)
    (hUpperSurvive : Disjoint K
      (upperFacetColorCleanupEdges H V tUpper))
    (hLowerSurvive : Disjoint K
      (multilevelDeletedEdges H V (V.powersetCard 3) 2 u q
        (fun B R T => ¬ ActualStrongPartner H V R T 2 3 tLower
          (tripleLabel B))))
    (hScale : (q : ℝ) ≤ ε * (u : ℝ))
    (hQ : 0 < Q) (hL₃ : 0 < L₃) (ht : 1 ≤ tLower)
    (hRetention : Q * L₃ ≤ P * u) (hq : 4 * q ≤ L₃) (hqu : q < u)
    (hD₄pos : 1 ≤ D₄) (hε : 0 ≤ ε)
    (hD : ∀ A : Edge α, A.card = 3 →
      (H.filter (fun E => A ⊆ E)).card ≤ D)
    (hD₄ : ∀ Q : Edge α, Q.card = 4 →
      (H.filter (fun E => Q ⊆ E)).card ≤ D₄) :
    let W : ℕ := tLower * (2 * L₃) * (40 * P * H.card) +
      Q * (8 * (V.powersetCard 2).card ^ 2 * D * D₄ * D₄)
    let M : ℕ := Q * tLower * (2 * L₃)
    (H.card : ℝ) - ((fourShadow H).card : ℝ) ≤ -(H.card : ℝ) +
      2 * (((H \ K).card : ℝ) + (W : ℝ) / (M : ℝ) +
        (V.card.choose 3 : ℝ) * ((1 + 2 * (D₄ - 1) : ℕ) : ℝ) +
        Real.sqrt ((V.card.choose 3 : ℝ) *
          ((V.card.choose 2 * (V.card - 2).choose 2 : ℕ) : ℝ) *
            max 7 (1 + ε * (D : ℝ)))) := by
  let center := upperFacetColorCenter K H V tUpper hKH hUniformK
    (fun E hE => hAmbientH E (hKH hE)) hUpperSurvive
  let I := facetBadIncidences K V center tripleLabel
  let W : ℕ := tLower * (2 * L₃) * (40 * P * H.card) +
    Q * (8 * (V.powersetCard 2).card ^ 2 * D * D₄ * D₄)
  let M : ℕ := Q * tLower * (2 * L₃)
  have hBudget := facet_bad_incidence_budget_of_actual_cleanups
    K H V P Q L₃ tLower tUpper u q D D₄ tripleLabel
    hKH hUniformK hUniformH hAmbientH hUpperSurvive hQ
    hRetention hq hLowerSurvive hqu ht hD hD₄
  have hNat : M * I.card ≤ W := by
    dsimp [M, I, center, W]
    simpa only [Nat.mul_assoc] using hBudget
  have hReal : (M : ℝ) * (I.card : ℝ) ≤ (W : ℝ) := by exact_mod_cast hNat
  have hMpos : 0 < (M : ℝ) := by
    have : 0 < M := by dsimp [M]; positivity
    exact_mod_cast this
  have hBound : (I.card : ℝ) ≤ (W : ℝ) / (M : ℝ) :=
    (le_div_iff₀ hMpos).2 (by simpa only [mul_comm] using hReal)
  have hSurplus := four_shadow_surplus_bound_of_actual_cleanups
    K H V tLower tUpper u q D D₄ ε tripleLabel
    hAdmH hKH hUniformK hUniformH hAmbientH hUpperSurvive
    hLowerSurvive hScale hD₄pos hε hD hD₄
  change (H.card : ℝ) - ((fourShadow H).card : ℝ) ≤ _ at hSurplus ⊢
  change (I.card : ℝ) ≤ _ at hBound
  dsimp [I, center] at hBound
  dsimp only [W, M] at hBound
  linarith

end JSP523.Rank5
