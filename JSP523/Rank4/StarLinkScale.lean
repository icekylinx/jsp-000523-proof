import JSP523.Rank4.StarLinkNativeBudget
import Mathlib.Data.Nat.Sqrt

/-!
# Choosing the star-link sampling scale

The fixed-size sample has size square-root of the ground-set size plus
two.  Elementary binomial identities turn the sampling coefficient and
active-vertex payment into explicit finite quantities.
-/

namespace JSP523.Rank4

/-- The selected sample size is admissible for every ground set of at
least three vertices. -/
theorem sqrt_sample_size_bounds (u : ℕ) (hu : 3 ≤ u) :
    3 ≤ Nat.sqrt u + 2 ∧ Nat.sqrt u + 2 ≤ u := by
  have hsPos : 0 < Nat.sqrt u :=
    (Nat.sqrt_pos).2 (by omega)
  constructor
  · omega
  by_cases hsTwo : 2 ≤ Nat.sqrt u
  · have hsSq := Nat.sqrt_le u
    nlinarith
  · omega

/-- A fixed-size sample contains a given triple relative to a pair with
the expected integer ratio. -/
theorem fixed_sample_triple_pair_ratio
    (u m : ℕ) (hu : 3 ≤ u) (hm : 3 ≤ m) :
    (u - 2) * ((u - 3).choose (m - 3)) =
      (u - 2).choose (m - 2) * (m - 2) := by
  have h := Nat.add_one_mul_choose_eq (u - 3) (m - 3)
  have hu' : u - 3 + 1 = u - 2 := by omega
  have hm' : m - 3 + 1 = m - 2 := by omega
  simpa only [hu', hm'] using h

/-- Two applications of the binomial incidence identity give the
active-vertex sampling coefficient without a quotient. -/
theorem fixed_sample_active_ratio
    (u m : ℕ) (hu : 3 ≤ u) (hm : 3 ≤ m) :
    u * m * (u.choose m) * (m - 1) =
      u * u * (u - 1) * ((u - 2).choose (m - 2)) := by
  have hTop := Nat.add_one_mul_choose_eq (u - 1) (m - 1)
  have hLow := Nat.add_one_mul_choose_eq (u - 2) (m - 2)
  have hu1 : u - 1 + 1 = u := by omega
  have hu2 : u - 2 + 1 = u - 1 := by omega
  have hm1 : m - 1 + 1 = m := by omega
  have hm2 : m - 2 + 1 = m - 1 := by omega
  rw [hu1, hm1] at hTop
  rw [hu2, hm2] at hLow
  calc
    u * m * (u.choose m) * (m - 1) =
      u * ((u.choose m) * m) * (m - 1) := by ring
    _ = u * (u * (u - 1).choose (m - 1)) * (m - 1) := by
        rw [hTop]
    _ = u * u * ((u - 1).choose (m - 1) * (m - 1)) := by ring
    _ = u * u * ((u - 1) * ((u - 2).choose (m - 2))) := by
        rw [hLow]
    _ = u * u * (u - 1) * ((u - 2).choose (m - 2)) := by ring

/-- At the square-root sample size, the total used-pair and active-vertex
cost is at most one explicit square-root-scale error term. -/
theorem sqrt_sample_error_bound
    (u c : ℕ) (hu : 3 ≤ u) (hc : c ≤ u.choose 2) :
    let s := Nat.sqrt u
    let m := s + 2
    let c₂ : ℚ := (u - 2).choose (m - 2)
    let c₃ : ℚ := (u - 3).choose (m - 3)
    2 * (c : ℚ) * ((u : ℚ) - 3) * c₃ +
      (u : ℚ) * (m : ℚ) * (u.choose m : ℚ) ≤
        2 * c₂ * (u : ℚ) ^ 2 * ((s : ℚ) + 1) := by
  dsimp
  let s := Nat.sqrt u
  let m := s + 2
  let c₂ : ℚ := (u - 2).choose (m - 2)
  let c₃ : ℚ := (u - 3).choose (m - 3)
  have hs : 0 < s := (Nat.sqrt_pos).2 (by omega)
  have hm : 3 ≤ m := by dsimp [m]; omega
  have hPairCast : (2 : ℚ) * c ≤
      (u : ℚ) * ((u : ℚ) - 1) := by
    have hcQ : (c : ℚ) ≤ (u.choose 2 : ℚ) := by
      exact_mod_cast hc
    have hTwo : (u.choose 2 : ℚ) =
        (u : ℚ) * ((u : ℚ) - 1) / 2 :=
      Nat.cast_choose_two ℚ u
    rw [hTwo] at hcQ
    linarith
  have hRatioNat := fixed_sample_triple_pair_ratio u m hu hm
  have hRatio :
      ((u : ℚ) - 2) * c₃ = c₂ * (s : ℚ) := by
    have hQ : (((u - 2 : ℕ) : ℚ)) *
        (((u - 3).choose (m - 3) : ℕ) : ℚ) =
        (((u - 2).choose (m - 2) : ℕ) : ℚ) *
          (((m - 2 : ℕ) : ℚ)) := by
      exact_mod_cast hRatioNat
    have hm2 : m - 2 = s := by dsimp [m]; omega
    rw [Nat.cast_sub (by omega : 2 ≤ u), hm2] at hQ
    exact hQ
  have hActiveNat := fixed_sample_active_ratio u m hu hm
  have hActive :
      (u : ℚ) * (m : ℚ) * (u.choose m : ℚ) *
          ((s : ℚ) + 1) =
        (u : ℚ) ^ 2 * ((u : ℚ) - 1) * c₂ := by
    have hQ : (u : ℚ) * (m : ℚ) * (u.choose m : ℚ) *
        (((m - 1 : ℕ) : ℚ)) =
        (u : ℚ) * (u : ℚ) * (((u - 1 : ℕ) : ℚ)) *
          (((u - 2).choose (m - 2) : ℕ) : ℚ) := by
      exact_mod_cast hActiveNat
    have hm1 : m - 1 = s + 1 := by omega
    rw [hm1, Nat.cast_add,
      Nat.cast_sub (by omega : 1 ≤ u)] at hQ
    norm_num at hQ
    dsimp [c₂, m] at hQ ⊢
    push_cast
    have hidx : s + 2 - 2 = s := by omega
    rw [hidx] at hQ
    nlinarith [hQ]
  have hc₂Nonneg : 0 ≤ c₂ := Nat.cast_nonneg _
  have hc₃Nonneg : 0 ≤ c₃ := Nat.cast_nonneg _
  have huNonneg : 0 ≤ (u : ℚ) := Nat.cast_nonneg _
  have hsNonneg : 0 ≤ (s : ℚ) := Nat.cast_nonneg _
  have huQ : (3 : ℚ) ≤ u := by exact_mod_cast hu
  have hUsed1 := mul_le_mul_of_nonneg_right hPairCast
    (mul_nonneg (by linarith : (0 : ℚ) ≤ (u : ℚ) - 3)
      hc₃Nonneg)
  have hUsed2 :
      ((u : ℚ) - 3) * c₃ ≤ c₂ * (s : ℚ) := by
    have hDiff : ((u : ℚ) - 3) * c₃ ≤
        ((u : ℚ) - 2) * c₃ := by
      nlinarith [hc₃Nonneg]
    nlinarith [hRatio]
  have hUsed3 := mul_le_mul_of_nonneg_left hUsed2
    (mul_nonneg huNonneg (by linarith : 0 ≤ (u : ℚ) - 1))
  have hUsed4 : (u : ℚ) * ((u : ℚ) - 1) * (c₂ * s) ≤
      (u : ℚ) ^ 2 * c₂ * s := by
    have hPos : 0 ≤ (u : ℚ) * c₂ * s :=
      mul_nonneg (mul_nonneg huNonneg hc₂Nonneg) hsNonneg
    nlinarith [hPos]
  have hUsed :
      2 * (c : ℚ) * ((u : ℚ) - 3) * c₃ ≤
        (u : ℚ) ^ 2 * c₂ * s := by
    nlinarith [hUsed1, hUsed3, hUsed4]
  have hRootNat := Nat.lt_succ_sqrt u
  have hRoot : ((u : ℚ) - 1) ≤ ((s : ℚ) + 1) ^ 2 := by
    have hQ : (u : ℚ) <
        (((s + 1) * (s + 1) : ℕ) : ℚ) := by
      exact_mod_cast hRootNat
    push_cast at hQ
    nlinarith
  have hActiveScaled := mul_le_mul_of_nonneg_left hRoot
    (mul_nonneg (sq_nonneg (u : ℚ)) hc₂Nonneg)
  have hActiveBound :
      (u : ℚ) * (m : ℚ) * (u.choose m : ℚ) ≤
        (u : ℚ) ^ 2 * c₂ * ((s : ℚ) + 1) := by
    have hsPlus : 0 < (s : ℚ) + 1 := by positivity
    apply (mul_le_mul_iff_of_pos_right hsPlus).mp
    nlinarith [hActive, hActiveScaled]
  dsimp [c₂, c₃] at *
  nlinarith [hUsed, hActiveBound]

/-- The actual star layer and native vertices satisfy the square-root
finite form of the shared budget once used pairs have their parent
matching labels and the native vertex count is paid by used pairs. -/
theorem star_native_sqrt_budget
    {α : Type*} [Fintype α] [DecidableEq α]
    (A : Family α) (U : Finset α)
    (C : Family α) (label : Edge α → α) (V : ℕ)
    (hC : C ⊆ U.powersetCard 2)
    (hU : 3 ≤ U.card)
    (hGround : ∀ T ∈ A, T ⊆ U)
    (hUniform : ∀ T ∈ A, T.card = 3)
    (hOff : ∀ a ∈ U, ∀ b ∈ U.erase a,
      ({a, b} : Edge α) ∈ C →
      ∀ x ∈ U, x ≠ label ({a, b} : Edge α) →
        graphCommonMultiplicity
          (JSP523.Coarse.tripleLinkGraph A x) a b ≤ 1)
    (hV : V ≤ (U.card - 3) * C.card) :
    3 * A.card + V ≤
      3 * U.card.choose 3 +
        U.card ^ 2 * (Nat.sqrt U.card + 1) := by
  let u := U.card
  let s := Nat.sqrt u
  let m := s + 2
  let c₂ : ℚ := (u - 2).choose (m - 2)
  have hm := (sqrt_sample_size_bounds u hU).1
  have hmLe := (sqrt_sample_size_bounds u hU).2
  have hCcard : C.card ≤ u.choose 2 := by
    have h := Finset.card_le_card hC
    simpa only [Finset.card_powersetCard] using h
  have hMain := star_native_fixed_size_budget
    A U m C label V hC hU hm hGround hUniform hOff hV
  have hErr := sqrt_sample_error_bound u C.card hU hCcard
  dsimp only at hErr
  have hc₂Pos : 0 < c₂ := by
    dsimp [c₂]
    exact_mod_cast Nat.choose_pos (by omega : m - 2 ≤ u - 2)
  have hQ :
      (((3 * A.card + V : ℕ) : ℚ)) ≤
        (3 : ℚ) * (u.choose 3 : ℚ) +
          (u : ℚ) ^ 2 * ((s : ℚ) + 1) := by
    have hCombined :
        2 * c₂ * (((3 * A.card + V : ℕ) : ℚ)) ≤
          2 * c₂ *
            ((3 : ℚ) * (u.choose 3 : ℚ) +
              (u : ℚ) ^ 2 * ((s : ℚ) + 1)) := by
      dsimp [c₂, m, s, u] at hMain hErr ⊢
      nlinarith [hMain, hErr]
    exact (mul_le_mul_iff_of_pos_left (by positivity : (0 : ℚ) < 2 * c₂)).mp
      hCombined
  have hNatCast :
      (((3 * U.card.choose 3 +
        U.card ^ 2 * (Nat.sqrt U.card + 1) : ℕ) : ℚ)) =
        (3 : ℚ) * (u.choose 3 : ℚ) +
          (u : ℚ) ^ 2 * ((s : ℚ) + 1) := by
    dsimp [u, s]
    push_cast
    ring
  rw [← hNatCast] at hQ
  exact_mod_cast hQ

end JSP523.Rank4
