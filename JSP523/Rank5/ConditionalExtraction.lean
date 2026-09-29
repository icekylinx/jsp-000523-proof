import JSP523.Rank5.ConditionalFarStar
import JSP523.Rank5.InitialPolynomialExtraction

namespace JSP523.Rank5

open Filter

theorem eventually_conditional_initial_polynomial_far_tail_mass
    (r : ℕ) (δ : ℝ) (hr : 4 ≤ r) (hδ : 0 < δ)
    (H : ∀ n : ℕ, Family (Fin n)) (M : ℕ → ℕ)
    (hAdm : ∀ n, Admissible (H n))
    (hUniform : ∀ n, Uniform r (H n))
    (hMax : ∀ n z, ((H n).filter (fun E => z ∈ E)).card ≤ M n)
 :
    ∃ α β : ℕ, 0 < α ∧ 0 < β ∧
      ∀ᶠ n : ℕ in atTop,
        (M n : ℝ) ≤ (1 - δ) * ((n - 1).choose (r - 1) : ℝ) →
        (n - 1).choose (r - 1) ≤ (H n).card →
        (initialPolynomialChosenCover r H hUniform n).Nonempty ∧
        (∀ z : Fin n,
          z ∉ initialPolynomialChosenCover r H hUniform n →
            ((H n).filter (fun E => z ∈ E)).card <
              initialVertexCap r (initialPolynomialFarSize n) (H n).card) ∧
        α * (n - 1).choose (r - 1) ≤
          β * ((H n).filter (fun E =>
            Disjoint E (initialPolynomialChosenCover r H hUniform n))).card := by
  let X := initialPolynomialChosenCover r H hUniform
  obtain ⟨α, β, hα, hβ, hTail⟩ :=
    eventually_conditional_far_star_mass_of_degree_gap r δ hr hδ
      H X (fun n => initialPolynomialFarSize n + 1) M
      hAdm hUniform
      (by intro n; exact initial_polynomial_chosen_cover_size r H hUniform n)
      hMax (by
        simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
          initial_polynomial_nonempty_cover_square_is_little_o)
  refine ⟨α, β, hα, hβ, ?_⟩
  filter_upwards [eventually_ge_atTop 1, hTail] with n hn hTailN
  intro hDegreeN hMassN
  obtain ⟨hNonempty, _, hOutside⟩ :=
    initial_polynomial_chosen_cover_spec r H hUniform n hn
  exact ⟨hNonempty, hOutside, hTailN hDegreeN hMassN⟩

theorem eventually_conditional_initial_polynomial_extraction
    (r steps : ℕ) (δ : ℝ) (hr : 5 ≤ r) (hδ : 0 < δ)
    (H : ∀ n : ℕ, Family (Fin n)) (M : ℕ → ℕ)
    (hAdm : ∀ n, Admissible (H n))
    (hUniform : ∀ n, Uniform r (H n))
    (hMax : ∀ n z, ((H n).filter (fun E => z ∈ E)).card ≤ M n)
 :
    ∃ α β m : ℕ, 0 < α ∧ 0 < β ∧ 0 < m ∧
      ∀ᶠ n : ℕ in atTop,
        (M n : ℝ) ≤ (1 - δ) * ((n - 1).choose (r - 1) : ℝ) →
        (n - 1).choose (r - 1) ≤ (H n).card →
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
    eventually_conditional_initial_polynomial_far_tail_mass r δ hr4 hδ
      H M hAdm hUniform hMax
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
  intro hDegreeN hMassN
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
  obtain ⟨hX, hOutside, hMassX⟩ := hTailN hDegreeN hMassN
  have hLarge := hRoundsN.2.2.2
  exact initial_polynomial_rounds_and_shadow_extraction (H n) X
    steps (hAdm n) (hUniform n) hn hr hX hOutside hMassX
    hFamily hSetN hRootGap hSep hCoeff hLarge hSavingN


end JSP523.Rank5
