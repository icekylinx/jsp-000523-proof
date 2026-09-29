import JSP523.Rank5.FinalExtractionError
import JSP523.Rank5.StructuralIntegerEndpoint
import JSP523.Rank5.PrivateFacetAssembly

/-!
# The coefficient-one extraction contradiction

This is the scalar closing step after the finite structural endpoint.
The endpoint error may contain a small multiple of the retained mass.
-/

namespace JSP523.Rank5

/-- A family supported on the retained vertex set has its full four-shadow
there. -/
theorem shadow_on_eq_four_shadow_of_supported
    {n : ℕ} (K : Family (Fin n)) (W : Edge (Fin n))
    (hSupport : ∀ E ∈ K, E ⊆ W) :
    shadowOn K W 5 = fourShadow K := by
  classical
  ext T
  simp only [shadowOn, fourShadow, Finset.mem_filter,
    Finset.mem_powersetCard, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨hTW, hTcard⟩, E, hE, hTE⟩
    exact ⟨E, hE, hTE, hTcard⟩
  · rintro ⟨E, hE, hT⟩
    obtain ⟨hTE, hTcard⟩ := hT
    exact ⟨⟨hTE.trans (hSupport E hE), hTcard⟩, E, hE, hTE⟩

/-- A positive extracted mass, a coefficient-one shadow ledger, and a
rank-five shadow endpoint with small mass-dependent error cannot coexist. -/
theorem positive_mass_excludes_rank_five_real_endpoint
    (a b B F K shadow extractionError endpointConstant endpointMass : ℝ)
    (hb : 0 ≤ b) (hKnonneg : 0 ≤ K)
    (hBaseline : B ≤ F)
    (hMass : a * B ≤ b * K)
    (hLedger : F - B ≤ K - shadow + extractionError)
    (hEndpoint : 2 * K - shadow ≤ endpointConstant + endpointMass * K)
    (hMassError : endpointMass ≤ 1 / 2)
    (hSmall : 2 * b * (extractionError + endpointConstant) < a * B) :
    False := by
  have hShadow : shadow ≤ K + extractionError := by linarith
  have hMassTerm : endpointMass * K ≤ K / 2 := by
    have h := mul_le_mul_of_nonneg_right hMassError hKnonneg
    nlinarith
  have hK : K ≤ 2 * (extractionError + endpointConstant) := by
    linarith
  have hScaled := mul_le_mul_of_nonneg_left hK hb
  nlinarith


/-- A concrete simultaneous saving for the extraction and structural
error when the positive-mass coefficient is `α/(4β)`. -/
theorem rank_five_scaled_errors_small
    (α β n B E : ℕ) (hα : 0 < α) (hβ : 0 < β)
    (hB : 0 < B)
    (hError : (100000 * β) * E ≤ 3458 * B)
    (hPower : n ^ 4 ≤ 384 * B) :
    2 * (4 * (β : ℝ)) *
        ((E : ℝ) + (1 / (100000 * (β : ℝ))) * (n : ℝ) ^ 4) <
      (α : ℝ) * (B : ℝ) := by
  have hβr : (0 : ℝ) < β := by exact_mod_cast hβ
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hαr : (1 : ℝ) ≤ α := by exact_mod_cast hα
  have hEr : (100000 * (β : ℝ)) * (E : ℝ) ≤ 3458 * (B : ℝ) := by
    exact_mod_cast hError
  have hPr : (n : ℝ) ^ 4 ≤ 384 * (B : ℝ) := by
    exact_mod_cast hPower
  have hIdentity :
      2 * (4 * (β : ℝ)) *
          ((E : ℝ) + (1 / (100000 * (β : ℝ))) * (n : ℝ) ^ 4) =
        8 * (β : ℝ) * (E : ℝ) +
          (8 / 100000 : ℝ) * (n : ℝ) ^ 4 := by
    field_simp
    ring
  rw [hIdentity]
  have hEbound : 8 * (β : ℝ) * (E : ℝ) ≤
      (27664 / 100000 : ℝ) * B := by nlinarith [hEr]
  have hPbound : (8 / 100000 : ℝ) * (n : ℝ) ^ 4 ≤
      (3072 / 100000 : ℝ) * B := by nlinarith [hPr]
  nlinarith [hEbound, hPbound]


/-- A fixed gap below the star degree is incompatible with eventual
rank-five star-sized mass. -/
theorem rank_five_degree_gap_excludes_eventual_star_mass
    (δ : ℝ) (hδ : 0 < δ)
    (H : ∀ n : ℕ, Family (Fin n)) (M : ℕ → ℕ)
    (hAdm : ∀ n, Admissible (H n))
    (hUniform : ∀ n, Uniform 5 (H n))
    (hMax : ∀ n z, ((H n).filter (fun E => z ∈ E)).card ≤ M n)
    (hDegree : ∀ᶠ n : ℕ in Filter.atTop,
      (M n : ℝ) ≤ (1 - δ) * ((n - 1).choose 4 : ℝ)) :
    ¬ (∀ᶠ n : ℕ in Filter.atTop,
      (n - 1).choose 4 ≤ (H n).card) := by
  intro hMass
  obtain ⟨α, β, m, hα, hβ, hm, hExtract⟩ :=
    eventually_initial_polynomial_extraction_of_degree_gap
      5 9 δ (by omega) hδ H M hAdm hUniform hMax
      (by simpa only [show 5 - 1 = 4 by omega] using hDegree) hMass
  let ε : ℝ := 1 / (100000 * (β : ℝ))
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hEndpoint := eventually_rank_five_small_structural_error ε hε
  have hError := eventually_rank_five_extraction_error_factor_bound
    H hAdm hUniform (100000 * β) (by omega)
  suffices hEventual : ∀ᶠ n : ℕ in Filter.atTop, False from
    (hEventual.exists).elim (fun _ h => h)
  filter_upwards [hExtract, hEndpoint, hError, hMass,
    Filter.eventually_ge_atTop 9]
    with n hExtractN hEndpointN hErrorN hMassN hn
  obtain ⟨K₀, K, hKK₀, hK₀Out, _hK₀H, hAdmK, hUniformK,
    hCapsK, hMassK, hDiscard, hRoundDiscard, hLedger⟩ := hExtractN
  let X := initialPolynomialChosenCover 5 H hUniform n
  let W : Edge (Fin n) := Finset.univ \ X
  let B := (n - 1).choose 4
  have hKOut : K ⊆ outsideFamily (H n) W := hKK₀.trans hK₀Out
  have hSupport : ∀ E ∈ K, E ⊆ W := by
    intro E hE
    exact (Finset.mem_filter.mp (hKOut hE)).2
  have hShadow : shadowOn K W 5 = fourShadow K :=
    shadow_on_eq_four_shadow_of_supported K W hSupport
  have hCapsK' : ∀ j, 2 ≤ j → j ≤ 4 →
      ∀ S : Edge (Fin n), S.card = j →
      (K.filter fun E => S ⊆ E).card ≤
        discreteRoundIterate (initialPolynomialScale n) 9 * n ^ (4 - j) := by
    intro j hj hj4 S hS
    simpa only [show 5 - j - 1 = 4 - j by omega] using
      hCapsK j (by omega) (by omega) S hS
  have hEndpointK := hEndpointN K hAdmK hUniformK hCapsK'
  have hMassSimple : α * B ≤ (4 * β) * K.card := by
    have hScaled : m * (α * B) ≤ m * ((4 * β) * K.card) := by
      calc
        m * (α * B) = m * α * B := by ring
        _ ≤ 4 * m * β * K.card := by simpa only [B] using hMassK
        _ = m * ((4 * β) * K.card) := by ring
    exact Nat.le_of_mul_le_mul_left hScaled hm
  have hStarPower : n ^ 4 ≤ 384 * B := by
    have h := far_star_power_le_choose_multiple n 4 (by omega)
    norm_num at h
    simpa only [B] using h
  have hBpos : 0 < B := by
    simpa only [B] using Nat.choose_pos (show 4 ≤ n - 1 by omega)
  have hSmall := rank_five_scaled_errors_small α β n B
    (rankFiveExtractionError H hUniform n) hα hβ hBpos
    (by simpa only [B] using hErrorN) hStarPower
  have hLedgerI : ((H n).card : ℤ) - (B : ℤ) ≤
      (K.card : ℤ) - ((shadowOn K W 5).card : ℤ) +
        (((K₀ \ K).card + ((outsideFamily (H n) W \ K₀).card) +
          rankFiveCoverError n X) : ℤ) := by
    simpa only [B, W, X, rankFiveCoverError, Nat.cast_add,
      show 5 - 1 = 4 by omega, show 5 - 2 = 3 by omega,
      show 5 - 3 = 2 by omega, add_assoc] using hLedger
  have hActualError : (K₀ \ K).card +
      (outsideFamily (H n) W \ K₀).card + rankFiveCoverError n X ≤
        rankFiveExtractionError H hUniform n := by
    have hRoundN : (K₀ \ K).card ≤ rankFiveRoundLoss n := by
      simpa only [rankFiveRoundLoss] using hRoundDiscard
    have hCleanupN : (outsideFamily (H n) W \ K₀).card ≤
        rankFiveCleanupCharge H n := by
      simpa only [rankFiveCleanupCharge, W, X] using hDiscard
    dsimp only [rankFiveExtractionError]
    change (K₀ \ K).card +
      (outsideFamily (H n) W \ K₀).card + rankFiveCoverError n X ≤
        rankFiveRoundLoss n + rankFiveCleanupCharge H n + rankFiveCoverError n X
    omega
  have hLedgerR : ((H n).card : ℝ) - (B : ℝ) ≤
      (K.card : ℝ) - ((shadowOn K W 5).card : ℝ) +
        (rankFiveExtractionError H hUniform n : ℝ) := by
    have hCast : ((H n).card : ℝ) - (B : ℝ) ≤
        (K.card : ℝ) - ((shadowOn K W 5).card : ℝ) +
          (((K₀ \ K).card + (outsideFamily (H n) W \ K₀).card +
            rankFiveCoverError n X) : ℝ) := by
      exact_mod_cast hLedgerI
    have hErrorR : (((K₀ \ K).card + (outsideFamily (H n) W \ K₀).card +
        rankFiveCoverError n X) : ℝ) ≤
          (rankFiveExtractionError H hUniform n : ℝ) := by
      exact_mod_cast hActualError
    linarith
  have hMassR : (α : ℝ) * (B : ℝ) ≤
      (4 * (β : ℝ)) * (K.card : ℝ) := by exact_mod_cast hMassSimple
  have hBaselineR : (B : ℝ) ≤ ((H n).card : ℝ) := by
    exact_mod_cast hMassN
  have hEndpointR : 2 * (K.card : ℝ) -
      ((shadowOn K W 5).card : ℝ) ≤
        ε * (n : ℝ) ^ 4 + ε * (K.card : ℝ) := by
    rw [hShadow]
    nlinarith [hEndpointK]
  exact positive_mass_excludes_rank_five_real_endpoint
    (α : ℝ) (4 * (β : ℝ)) (B : ℝ) ((H n).card : ℝ)
    (K.card : ℝ) ((shadowOn K W 5).card : ℝ)
    (rankFiveExtractionError H hUniform n : ℝ)
    (ε * (n : ℝ) ^ 4) ε
    (by positivity) (by positivity) hBaselineR hMassR hLedgerR
    hEndpointR (by
      have hβr : (1 : ℝ) ≤ β := by exact_mod_cast hβ
      have hden : (0 : ℝ) < 100000 * β := by positivity
      dsimp [ε]
      apply (div_le_iff₀ hden).2
      nlinarith)
    (by simpa only [ε, B] using hSmall)

end JSP523.Rank5
