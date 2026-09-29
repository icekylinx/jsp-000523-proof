import JSP523.Rank5.InitialPolynomialScale

/-!
# Polynomial initial cleanup, natural rounds, and shadow extraction

This finite bridge keeps the actual removed vertex set through every stage.
The final family retains positive mass and the coefficient-one shadow ledger.
-/

namespace JSP523.Rank5

open Finset
open Filter Asymptotics

/-- The fixed-round loss condition in the finite extraction bridge is
automatic for every fixed positive tail coefficient. -/
theorem eventually_initial_polynomial_round_saving
    (r steps m α β : ℕ) (hr : 4 ≤ r) (hα : 1 ≤ α) :
    ∀ᶠ n : ℕ in atTop,
      4 * m * β *
        (∑ i ∈ Finset.range steps,
          discreteRoundAdditiveLoss n r
            (discreteRoundIterate (initialPolynomialScale n) i)) ≤
        m * α * (n - 1).choose (r - 1) := by
  have hScale : ∀ᶠ n : ℕ in atTop,
      (initialPolynomialScale n) ^ 3 ≤ n ^ 2 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (initial_polynomial_scale_bounds n hn).2.2
  have hLittle := iterated_natural_loss_is_little_o r steps
    initialPolynomialScale hr initial_polynomial_scale_tendsto_at_top hScale
  let q := 4 * β + 1
  have hq : (0 : ℝ) < q := by positivity
  have hc : (0 : ℝ) < 1 / (q : ℝ) := one_div_pos.mpr hq
  have hBound := hLittle.def hc
  filter_upwards [hBound] with n hn
  let L := ∑ i ∈ Finset.range steps,
    discreteRoundAdditiveLoss n r
      (discreteRoundIterate (initialPolynomialScale n) i)
  let B := (n - 1).choose (r - 1)
  have hReal : (L : ℝ) ≤ (1 / (q : ℝ)) * (B : ℝ) := by
    have hCast : (L : ℝ) =
        ∑ i ∈ Finset.range steps,
          (discreteRoundAdditiveLoss n r
            (discreteRoundIterate (initialPolynomialScale n) i) : ℝ) := by
      simp [L]
    rw [hCast]
    have hLnonneg : (0 : ℝ) ≤
        ∑ i ∈ Finset.range steps,
          (discreteRoundAdditiveLoss n r
            (discreteRoundIterate (initialPolynomialScale n) i) : ℝ) := by
      positivity
    have hBnonneg : (0 : ℝ) ≤ (B : ℝ) := by positivity
    simpa only [B, Real.norm_eq_abs, abs_of_nonneg hLnonneg,
      abs_of_nonneg hBnonneg] using hn
  have hScaled : (q : ℝ) * (L : ℝ) ≤ (B : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hReal hq.le
    convert h using 1; field_simp
  have hNat : q * L ≤ B := by exact_mod_cast hScaled
  have hB : B ≤ α * B := by
    simpa only [one_mul] using Nat.mul_le_mul_right B hα
  have hCore : 4 * β * L ≤ α * B := by
    dsimp [q] at hNat
    nlinarith [hNat, hB]
  have hFinal := Nat.mul_le_mul_left m hCore
  simpa only [L, B, Nat.mul_assoc, Nat.mul_left_comm,
    Nat.mul_comm] using hFinal

/-- The actual initial heavy-root cleanup charge vanishes against the
star, uniformly for all admissible families with the coarse fixed-rank
edge-count bound. -/
theorem initial_polynomial_cleanup_charge_is_little_o
    (r C D : ℕ) (H : ∀ n : ℕ, Family (Fin n))
    (hFamily : ∀ᶠ n : ℕ in atTop,
      (H n).card ≤ C * (n - 1).choose (r - 1))
    (hSet : ∀ᶠ n : ℕ in atTop,
      initialPolynomialFarSize n + 1 ≤
        D * (n - 1).choose (r - 1)) :
    (fun n : ℕ =>
      (r * r * initialScaleMultiplier n (initialPolynomialScale n) *
        initialVertexCap r (initialPolynomialFarSize n) (H n).card : ℝ))
      =o[atTop]
    (fun n : ℕ => ((n - 1).choose (r - 1) : ℝ)) := by
  apply IsLittleO.of_bound
  intro c hc
  let A := r * C + D
  obtain ⟨m, hmgt⟩ := exists_nat_gt ((A : ℝ) / c)
  have hmpos : 0 < m := by
    have hNonneg : (0 : ℝ) ≤ (A : ℝ) / c := by positivity
    exact_mod_cast (lt_of_le_of_lt hNonneg hmgt)
  have hCoeff : (A : ℝ) ≤ c * (m : ℝ) := by
    have h := (div_lt_iff₀ hc).mp hmgt
    nlinarith
  have hRoot := initial_polynomial_root_tendsto_at_top.eventually
    (eventually_ge_atTop (m * (r * r) * (3 * 2 ^ 16 + 1)))
  filter_upwards [eventually_ge_atTop 1, hFamily, hSet, hRoot]
    with n hn hFamilyN hSetN hRootN
  let Q := r * r * initialScaleMultiplier n (initialPolynomialScale n) *
    initialVertexCap r (initialPolynomialFarSize n) (H n).card
  let B := (n - 1).choose (r - 1)
  have hRate : m * Q ≤ A * B :=
    initial_polynomial_cleanup_loss_rate n r m C D (H n).card hn
      hRootN hFamilyN hSetN
  have hReal : (m : ℝ) * (Q : ℝ) ≤ (A : ℝ) * (B : ℝ) := by
    exact_mod_cast hRate
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hBound : (Q : ℝ) ≤ c * (B : ℝ) := by
    apply le_of_mul_le_mul_left (a0 := hmreal)
    calc
      (m : ℝ) * (Q : ℝ) ≤ (A : ℝ) * (B : ℝ) := hReal
      _ ≤ (c * (m : ℝ)) * (B : ℝ) :=
        mul_le_mul_of_nonneg_right hCoeff (by positivity)
      _ = (m : ℝ) * (c * (B : ℝ)) := by ring
  simpa [Q, B, Real.norm_eq_abs] using hBound

/-- An explicit arbitrary-factor saving for the mixed shadow-link error
after nine polynomial-scale rounds. -/
theorem initial_polynomial_shadow_cross_star_rate
    (n r q : ℕ) (hr : 4 ≤ r)
    (hn : 2 * (r - 1) + 1 ≤ n)
    (hSmall : q * (initialPolynomialFarSize n + 1) *
      discreteRoundIterate (initialPolynomialScale n) 9 ≤ n) :
    q * ((initialPolynomialFarSize n + 1) *
      (n * ((r - 1) *
        (discreteRoundIterate (initialPolynomialScale n) 9 *
          n ^ (r - 3))))) ≤
      (r - 1) * (2 ^ (r - 1) * (r - 1).factorial) *
        (n - 1).choose (r - 1) := by
  let h := initialPolynomialFarSize n + 1
  let R := discreteRoundIterate (initialPolynomialScale n) 9
  let C := 2 ^ (r - 1) * (r - 1).factorial
  have hPower : n ^ 2 * n ^ (r - 3) = n ^ (r - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hStar := far_star_power_le_choose_multiple n (r - 1) hn
  calc
    q * (h * (n * ((r - 1) * (R * n ^ (r - 3))))) =
        (q * h * R) * ((r - 1) * (n * n ^ (r - 3))) := by ring
    _ ≤ n * ((r - 1) * (n * n ^ (r - 3))) :=
      Nat.mul_le_mul_right _ hSmall
    _ = (r - 1) * (n ^ 2 * n ^ (r - 3)) := by ring
    _ = (r - 1) * n ^ (r - 1) := by rw [hPower]
    _ ≤ (r - 1) * C * (n - 1).choose (r - 1) := by
      have h := Nat.mul_le_mul_left (r - 1) hStar
      simpa only [C, Nat.mul_assoc] using h

/-- The two-hit error has an arbitrary-factor saving whenever the
removed-set square is small against `n`. -/
theorem initial_polynomial_multihit_star_rate
    (n r q : ℕ) (hr : 4 ≤ r)
    (hn : 2 * (r - 1) + 1 ≤ n)
    (hSmall : q * (initialPolynomialFarSize n + 1) ^ 2 ≤ n) :
    q * ((initialPolynomialFarSize n + 1) ^ 2 *
      (n - 2).choose (r - 2)) ≤
      (2 ^ (r - 1) * (r - 1).factorial) *
        (n - 1).choose (r - 1) := by
  let h := initialPolynomialFarSize n + 1
  have hChoose : (n - 2).choose (r - 2) ≤ n ^ (r - 2) :=
    (Nat.choose_le_pow _ _).trans
      (Nat.pow_le_pow_left (Nat.sub_le n 2) _)
  have hPow : n * n ^ (r - 2) = n ^ (r - 1) := by
    rw [Nat.mul_comm, ← pow_succ]
    congr 1
    omega
  have hStar := far_star_power_le_choose_multiple n (r - 1) hn
  calc
    q * (h ^ 2 * (n - 2).choose (r - 2)) =
        (q * h ^ 2) * (n - 2).choose (r - 2) := by ring
    _ ≤ n * (n - 2).choose (r - 2) :=
      Nat.mul_le_mul_right _ hSmall
    _ ≤ n * n ^ (r - 2) := Nat.mul_le_mul_left n hChoose
    _ = n ^ (r - 1) := hPow
    _ ≤ (2 ^ (r - 1) * (r - 1).factorial) *
        (n - 1).choose (r - 1) := hStar

/-- The unordered link-collision term in the shadow ledger obeys the
same square-small-set saving. -/
theorem initial_polynomial_link_collision_star_rate
    (n r q : ℕ) (hr : 4 ≤ r)
    (hn : 2 * (r - 1) + 1 ≤ n)
    (hSmall : q * (initialPolynomialFarSize n + 1) ^ 2 ≤ n) :
    q * ((initialPolynomialFarSize n + 1) ^ 2 *
      ((r - 1) * (n - 1).choose (r - 2))) ≤
      (r - 1) * (2 ^ (r - 1) * (r - 1).factorial) *
        (n - 1).choose (r - 1) := by
  let h := initialPolynomialFarSize n + 1
  have hChoose : (n - 1).choose (r - 2) ≤ n ^ (r - 2) :=
    (Nat.choose_le_pow _ _).trans
      (Nat.pow_le_pow_left (Nat.sub_le n 1) _)
  have hPow : n * n ^ (r - 2) = n ^ (r - 1) := by
    rw [Nat.mul_comm, ← pow_succ]
    congr 1
    omega
  have hStar := far_star_power_le_choose_multiple n (r - 1) hn
  calc
    q * (h ^ 2 * ((r - 1) * (n - 1).choose (r - 2))) =
        (q * h ^ 2) * ((r - 1) * (n - 1).choose (r - 2)) := by ring
    _ ≤ n * ((r - 1) * (n - 1).choose (r - 2)) :=
      Nat.mul_le_mul_right _ hSmall
    _ ≤ (r - 1) * (n * n ^ (r - 2)) := by
      have h := Nat.mul_le_mul_left (n * (r - 1)) hChoose
      nlinarith [h]
    _ = (r - 1) * n ^ (r - 1) := by rw [hPow]
    _ ≤ (r - 1) * (2 ^ (r - 1) * (r - 1).factorial) *
        (n - 1).choose (r - 1) := by
      have h := Nat.mul_le_mul_left (r - 1) hStar
      simpa only [Nat.mul_assoc] using h

theorem initial_polynomial_rounds_and_shadow_extraction
    {n r α β C D m : ℕ} (H : Family (Fin n))
    (X : Edge (Fin n)) (steps : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hn : 1 ≤ n) (hr : 5 ≤ r) (hX : X.Nonempty)
    (hOutside : ∀ z : Fin n, z ∉ X →
      (H.filter (fun E => z ∈ E)).card <
        initialVertexCap r (initialPolynomialFarSize n) H.card)
    (hTail : α * (n - 1).choose (r - 1) ≤
      β * (H.filter (fun E => Disjoint E X)).card)
    (hFamily : H.card ≤ C * (n - 1).choose (r - 1))
    (hSet : initialPolynomialFarSize n + 1 ≤
      D * (n - 1).choose (r - 1))
    (hRoot : m * (r * r) * (3 * 2 ^ 16 + 1) ≤
      initialPolynomialRoot n)
    (hSeparation : 16 * r * 2 ^ 16 <
      (initialPolynomialRoot n) ^ 4)
    (hCoeff : 2 * β * (r * C + D) ≤ m * α)
    (hLarge : ∀ i < steps,
      (16 * (36 * r) ^ 3) ^ 8 ≤
        (discreteRoundIterate (initialPolynomialScale n) i) ^ 5)
    (hRoundSaving :
      4 * m * β *
        (∑ i ∈ Finset.range steps,
          discreteRoundAdditiveLoss n r
            (discreteRoundIterate (initialPolynomialScale n) i)) ≤
        m * α * (n - 1).choose (r - 1)) :
    ∃ K₀ K : Family (Fin n), K ⊆ K₀ ∧
      K₀ ⊆ outsideFamily H (Finset.univ \ X) ∧ K₀ ⊆ H ∧
      Admissible K ∧ Uniform r K ∧
      (∀ j, 1 ≤ j → j ≤ r - 1 →
        ∀ S : Edge (Fin n), S.card = j →
          (K.filter (fun E => S ⊆ E)).card ≤
            discreteRoundIterate (initialPolynomialScale n) steps *
              n ^ (r - j - 1)) ∧
      m * α * (n - 1).choose (r - 1) ≤ 4 * m * β * K.card ∧
      ((outsideFamily H (Finset.univ \ X)) \ K₀).card ≤
        r * r * initialScaleMultiplier n (initialPolynomialScale n) *
          initialVertexCap r (initialPolynomialFarSize n) H.card ∧
      (K₀ \ K).card ≤
        ∑ i ∈ Finset.range steps,
          discreteRoundAdditiveLoss n r
            (discreteRoundIterate (initialPolynomialScale n) i) ∧
      ((H.card : ℤ) - ((n - 1).choose (r - 1) : ℤ) ≤
        (K.card : ℤ) -
          ((shadowOn K (Finset.univ \ X) r).card : ℤ) +
          ((K₀ \ K).card : ℤ) +
          (((outsideFamily H (Finset.univ \ X)) \ K₀).card : ℤ) +
          (X.card.choose 2 * ((n - 2).choose (r - 2)) : ℕ) +
          (X.card * ((Finset.univ \ X).card *
            ((r - 1) *
              (discreteRoundIterate (initialPolynomialScale n) steps *
                n ^ (r - 3)))) : ℕ) +
          (X.card.choose 2 * ((r - 1) *
            ((Finset.univ \ X).card - 1).choose (r - 2)) : ℕ)) := by
  classical
  have hr4 : 4 ≤ r := by omega
  obtain ⟨K₀, hK₀H, hAvoid, hAdm₀, hUniform₀,
    hCaps₀, hInitialLoss, hMass₀⟩ :=
    initial_polynomial_positive_mass_after_cleanup H X hAdm hUniform
      hn hr4 hOutside hTail hFamily hSet hRoot hSeparation hCoeff
  have hCube : (initialPolynomialScale n) ^ 3 ≤ n ^ 2 :=
    (initial_polynomial_scale_bounds n hn).2.2
  obtain ⟨K, hKK₀, hAdmK, hUniformK, hCapsK, hRoundLoss⟩ :=
    natural_scale_finite_regularization_iterate steps K₀ hr4 hn
      hCube hLarge hAdm₀ hUniform₀ hCaps₀
  let W : Edge (Fin n) := Finset.univ \ X
  have hSupport : ∀ E ∈ H, E ⊆ W ∪ X := by
    intro E hE z hzE
    by_cases hzX : z ∈ X
    · exact Finset.mem_union_right W hzX
    · exact Finset.mem_union_left X
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hzX⟩)
  have hXW : ∀ x ∈ X, x ∉ W := by
    intro x hx hxW
    exact (Finset.mem_sdiff.mp hxW).2 hx
  have hK₀Out : K₀ ⊆ outsideFamily H W := by
    intro E hE
    apply Finset.mem_filter.mpr
    refine ⟨hK₀H hE, ?_⟩
    intro z hzE
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ z,
      fun hzX => (Finset.disjoint_left.mp (hAvoid E hE)) hzE hzX⟩
  have hKOut : K ⊆ outsideFamily H W := hKK₀.trans hK₀Out
  have hPair : ∀ Q : Edge (Fin n), Q.card = 2 →
      (K.filter fun E => Q ⊆ E).card ≤
        discreteRoundIterate (initialPolynomialScale n) steps *
          n ^ (r - 3) := by
    intro Q hQ
    have hTwo : 2 ≤ r - 1 := by omega
    have he : r - 2 - 1 = r - 3 := by omega
    simpa only [he] using hCapsK 2 (by omega) hTwo Q hQ
  have hV : (Finset.univ : Edge (Fin n)) = W ∪ X := by
    ext z
    constructor
    · intro _
      by_cases hz : z ∈ X
      · exact Finset.mem_union_right W hz
      · exact Finset.mem_union_left X
          (Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hz⟩)
    · intro _
      exact Finset.mem_univ z
  have hWX : Disjoint W X := by
    apply Finset.disjoint_left.mpr
    intro z hzW hzX
    exact (Finset.mem_sdiff.mp hzW).2 hzX
  have hOutsideEq : outsideFamily H W =
      H.filter (fun E => Disjoint E X) := by
    ext E
    constructor
    · intro hE
      obtain ⟨hEH, hSub⟩ := Finset.mem_filter.mp hE
      apply Finset.mem_filter.mpr
      refine ⟨hEH, Finset.disjoint_left.mpr ?_⟩
      intro z hzE hzX
      exact (Finset.mem_sdiff.mp (hSub hzE)).2 hzX
    · intro hE
      obtain ⟨hEH, hDisj⟩ := Finset.mem_filter.mp hE
      apply Finset.mem_filter.mpr
      refine ⟨hEH, ?_⟩
      intro z hzE
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ z,
        fun hzX => (Finset.disjoint_left.mp hDisj) hzE hzX⟩
  have hDiscard : ((outsideFamily H W) \ K₀).card ≤
      r * r * initialScaleMultiplier n (initialPolynomialScale n) *
        initialVertexCap r (initialPolynomialFarSize n) H.card := by
    have hSub : K₀ ⊆ outsideFamily H W := hK₀Out
    have hCard := Finset.card_sdiff_add_card_eq_card hSub
    rw [hOutsideEq] at hCard ⊢
    omega
  have hLedger := finite_shadow_surplus_star_baseline
    (F := H) (K := K) (H := K) (W := W) (X := X)
    (V := Finset.univ) (r := r)
    (D := discreteRoundIterate (initialPolynomialScale n) steps *
      n ^ (r - 3))
    hAdm hUniform hSupport hXW hKOut (Finset.Subset.rfl)
    (by omega : 2 ≤ r) hPair hV hWX hX
  have hStarCard : ((Finset.univ : Edge (Fin n)).card - 1).choose
      (r - 1) = (n - 1).choose (r - 1) := by simp
  rw [hStarCard] at hLedger
  have hOutCard := Finset.card_sdiff_add_card_eq_card hKOut
  have hK₀Card := Finset.card_sdiff_add_card_eq_card hKK₀
  have hOutK₀Card := Finset.card_sdiff_add_card_eq_card hK₀Out
  have hDiscardSplit : ((outsideFamily H W) \ K).card =
      (K₀ \ K).card + ((outsideFamily H W) \ K₀).card := by
    omega
  have hRoundMass :
      m * α * (n - 1).choose (r - 1) ≤ 4 * m * β * K.card := by
    have hA := Nat.mul_le_mul_left (2 * m * β) hRoundLoss
    nlinarith [hA, hMass₀, hRoundSaving]
  have hRoundDiscard : (K₀ \ K).card ≤
      ∑ i ∈ Finset.range steps,
        discreteRoundAdditiveLoss n r
          (discreteRoundIterate (initialPolynomialScale n) i) := by
    have hCard := Finset.card_sdiff_add_card_eq_card hKK₀
    omega
  refine ⟨K₀, K, hKK₀, hK₀Out, hK₀H, hAdmK, hUniformK,
    hCapsK, hRoundMass, hDiscard, hRoundDiscard, ?_⟩
  simpa only [W, Finset.card_univ, Fintype.card_fin,
    hDiscardSplit, Finset.sdiff_self, Finset.card_empty,
    Nat.cast_zero, zero_add, add_zero, Nat.cast_add, add_assoc] using hLedger

/-- An actual admissible far-star sequence with a fixed maximum-degree
gap reaches the positive-mass, regularized, coefficient-one extraction
ledger after any fixed number of rounds. All numerical parameters are
chosen from the rank and the far-tail coefficients. -/
theorem eventually_initial_polynomial_extraction_of_degree_gap
    (r steps : ℕ) (δ : ℝ) (hr : 5 ≤ r) (hδ : 0 < δ)
    (H : ∀ n : ℕ, Family (Fin n)) (M : ℕ → ℕ)
    (hAdm : ∀ n, Admissible (H n))
    (hUniform : ∀ n, Uniform r (H n))
    (hMax : ∀ n z, ((H n).filter (fun E => z ∈ E)).card ≤ M n)
    (hDegree : ∀ᶠ n : ℕ in atTop,
      (M n : ℝ) ≤ (1 - δ) * ((n - 1).choose (r - 1) : ℝ))
    (hMass : ∀ᶠ n : ℕ in atTop,
      (n - 1).choose (r - 1) ≤ (H n).card) :
    ∃ α β m : ℕ, 0 < α ∧ 0 < β ∧ 0 < m ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ K₀ K : Family (Fin n), K ⊆ K₀ ∧
          K₀ ⊆ outsideFamily (H n)
            (Finset.univ \ initialPolynomialChosenCover r H hUniform n) ∧
          K₀ ⊆ H n ∧
          Admissible K ∧ Uniform r K ∧
          (∀ j, 1 ≤ j → j ≤ r - 1 →
            ∀ S : Edge (Fin n), S.card = j →
              (K.filter (fun E => S ⊆ E)).card ≤
                discreteRoundIterate (initialPolynomialScale n) steps *
                  n ^ (r - j - 1)) ∧
          m * α * (n - 1).choose (r - 1) ≤ 4 * m * β * K.card ∧
          ((outsideFamily (H n)
            (Finset.univ \ initialPolynomialChosenCover r H hUniform n))
              \ K₀).card ≤
            r * r * initialScaleMultiplier n (initialPolynomialScale n) *
              initialVertexCap r (initialPolynomialFarSize n) (H n).card ∧
          (K₀ \ K).card ≤
            ∑ i ∈ Finset.range steps,
              discreteRoundAdditiveLoss n r
                (discreteRoundIterate (initialPolynomialScale n) i) ∧
          ((H n).card : ℤ) - ((n - 1).choose (r - 1) : ℤ) ≤
            (K.card : ℤ) -
              ((shadowOn K
                (Finset.univ \ initialPolynomialChosenCover r H hUniform n)
                r).card : ℤ) +
              ((K₀ \ K).card : ℤ) +
              (((outsideFamily (H n)
                (Finset.univ \ initialPolynomialChosenCover r H hUniform n))
                  \ K₀).card : ℤ) +
              ((initialPolynomialChosenCover r H hUniform n).card.choose 2 *
                ((n - 2).choose (r - 2)) : ℕ) +
              ((initialPolynomialChosenCover r H hUniform n).card *
                ((Finset.univ \ initialPolynomialChosenCover r H hUniform n).card *
                  ((r - 1) *
                    (discreteRoundIterate (initialPolynomialScale n) steps *
                      n ^ (r - 3)))) : ℕ) +
              ((initialPolynomialChosenCover r H hUniform n).card.choose 2 *
                ((r - 1) *
                  (((Finset.univ \ initialPolynomialChosenCover r H hUniform n).card - 1).choose
                    (r - 2))) : ℕ) := by
  have hr4 : 4 ≤ r := by omega
  obtain ⟨α, β, hα, hβ, hTail⟩ :=
    eventually_initial_polynomial_chosen_far_tail_mass r δ hr4 hδ
      H M hAdm hUniform hMax hDegree hMass
  let D := 2 ^ (r - 1) * (r - 1).factorial
  let C := 3 * r ^ r * D
  let m := 2 * β * (r * C + D) + 1
  have hm : 0 < m := by dsimp [m]; omega
  have hCoeff : 2 * β * (r * C + D) ≤ m * α := by
    have hmα := Nat.mul_le_mul_left m hα
    have hBase : 2 * β * (r * C + D) ≤ m := by
      dsimp [m]
      omega
    exact hBase.trans (by simpa using hmα)
  have hSet := eventually_initial_polynomial_far_set_le_star_multiple r hr4
  have hRounds := eventually_initial_polynomial_parameters r steps m
  have hRoundSave := eventually_initial_polynomial_round_saving
    r steps m α β hr4 (by omega)
  let T := max (m * (r * r) * (3 * 2 ^ 16 + 1))
    (16 * r * 2 ^ 16 + 1)
  have hRoot := initial_polynomial_root_tendsto_at_top.eventually
    (eventually_ge_atTop T)
  refine ⟨α, β, m, hα, hβ, hm, ?_⟩
  filter_upwards [eventually_ge_atTop (2 * (r - 1) + 1),
    hTail, hSet, hRounds, hRoundSave, hRoot]
    with n hnStar hTailN hSetN hRoundsN hSavingN hRootN
  let X := initialPolynomialChosenCover r H hUniform n
  have hn : 1 ≤ n := by omega
  have hFamily : (H n).card ≤ C * (n - 1).choose (r - 1) :=
    initial_polynomial_coarse_star_bound (H n) hr4 hnStar
      (hAdm n) (hUniform n)
  have hRootGap : m * (r * r) * (3 * 2 ^ 16 + 1) ≤
      initialPolynomialRoot n := (le_max_left _ _).trans hRootN
  have hSep : 16 * r * 2 ^ 16 <
      (initialPolynomialRoot n) ^ 4 := by
    have hL : 16 * r * 2 ^ 16 + 1 ≤ initialPolynomialRoot n :=
      (le_max_right _ _).trans hRootN
    have hUone : 1 ≤ initialPolynomialRoot n := by omega
    have hPow := le_self_pow hUone (by norm_num : 4 ≠ 0)
    omega
  obtain ⟨hX, hOutside, hMassX⟩ := hTailN
  have hLarge := hRoundsN.2.2.2
  exact initial_polynomial_rounds_and_shadow_extraction (H n) X
    steps (hAdm n) (hUniform n) hn hr hX hOutside hMassX
    hFamily hSetN hRootGap hSep hCoeff hLarge hSavingN

/-- Finite rank-five contradiction once the IV.9 endpoint and the
coefficient-one extraction ledger have both been established. The two
error terms may include all intermediate deletions. -/
theorem positive_mass_excludes_rank_five_shadow_endpoint
    (a b B F K shadow extractionError endpointError : ℕ)
    (hBaseline : B ≤ F)
    (hMass : a * B ≤ b * K)
    (hLedger : (F : ℤ) - (B : ℤ) ≤
      (K : ℤ) - (shadow : ℤ) + (extractionError : ℤ))
    (hEndpoint : 2 * K ≤ shadow + endpointError)
    (hSmall : b * (extractionError + endpointError) < a * B) : False := by
  have hShadow : shadow ≤ K + extractionError := by omega
  have hK : K ≤ extractionError + endpointError := by omega
  have hScaled := Nat.mul_le_mul_left b hK
  omega

/-- The corresponding higher-rank contradiction needs only a direct
small-mass endpoint for the regularized actual family. -/
theorem positive_mass_excludes_higher_rank_small_endpoint
    (a b B K error : ℕ)
    (hMass : a * B ≤ b * K)
    (hEndpoint : K ≤ error)
    (hSmall : b * error < a * B) : False := by
  have hScaled := Nat.mul_le_mul_left b hEndpoint
  omega

/-- Any later structural cleanup can be charged directly to the same
coefficient-one ledger. This is the interface to the IV.7–IV.9 parent
and inherited-center constructions. -/
theorem extracted_shadow_ledger_after_subfamily
    {n r B error : ℕ} {F K L : Family (Fin n)}
    {W : Edge (Fin n)}
    (hLK : L ⊆ K)
    (hLedger : (F.card : ℤ) - (B : ℤ) ≤
      (K.card : ℤ) - ((shadowOn K W r).card : ℤ) +
        (error : ℤ)) :
    (F.card : ℤ) - (B : ℤ) ≤
      (L.card : ℤ) - ((shadowOn L W r).card : ℤ) +
        (error : ℤ) + ((K \ L).card : ℤ) := by
  have hStability := shadow_surplus_loss_le_deleted_edges
    (V := W) (r := r) hLK
  omega

end JSP523.Rank5
