import JSP523.Rank5.HigherRankActualRepairScale
import JSP523.Rank5.RootedPrefixEndpoint

namespace JSP523.Rank5

theorem higher_prefix_quadratic_scale_bound
    (N U k D D₄ : ℕ) (x : ℝ) (hU : 2 ≤ U) (hN : U ^ 32 ≤ N) (hx : 0 ≤ x)
    (hD : D ≤ 4 * U ^ 2 * N) (hD₄ : D₄ ≤ 4 * U ^ 2 * N ^ (k + 1))
    (hQuad : x ^ 2 ≤ (N.choose 3 : ℝ) *
      (((1 + (k + 3) * (D₄ - 1) : ℕ) : ℝ) * x +
        ((N.choose (k + 3) * (N - (k + 3)).choose (k + 3) : ℕ) : ℝ) *
          max 7 (1 + (2 / (U : ℝ) ^ 3) * D))) :
    x ≤ (4 * (k : ℝ) + 13) * ((N : ℝ) ^ (k + 5) / U) +
      3 * ((N : ℝ) ^ (k + 5) / Real.sqrt U) := by
  have hUOne : (1 : ℝ) ≤ U := by exact_mod_cast (by omega : 1 ≤ U)
  have hUp : (0 : ℝ) < U := by linarith
  have hNR : (U : ℝ) ^ 32 ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hNR
  have hNOne : (1 : ℝ) ≤ N := (one_le_pow₀ hUOne).trans hNR
  have hC₃ : (N.choose 3 : ℝ) ≤ (N : ℝ) ^ 3 := by exact_mod_cast Nat.choose_le_pow N 3
  have hC : (N.choose (k + 3) : ℝ) ≤ (N : ℝ) ^ (k + 3) := by
    exact_mod_cast Nat.choose_le_pow N (k + 3)
  have hC' : ((N - (k + 3)).choose (k + 3) : ℝ) ≤ (N : ℝ) ^ (k + 3) := by
    exact_mod_cast (Nat.choose_le_pow (N - (k + 3)) (k + 3)).trans
      (Nat.pow_le_pow_left (Nat.sub_le N (k + 3)) (k + 3))
  have hDReal : (D : ℝ) ≤ 4 * (U : ℝ) ^ 2 * N := by exact_mod_cast hD
  have hD₄Real : ((D₄ - 1 : ℕ) : ℝ) ≤ 4 * (U : ℝ) ^ 2 * (N : ℝ) ^ (k + 1) := by
    exact_mod_cast (Nat.sub_le D₄ 1).trans hD₄
  have hBaseOne : 1 ≤ (U : ℝ) ^ 2 * (N : ℝ) ^ (k + 1) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hUOne) (one_le_pow₀ hNOne)
  have hCoeff : ((1 + (k + 3) * (D₄ - 1) : ℕ) : ℝ) ≤
      (4 * (k : ℝ) + 13) * (U : ℝ) ^ 2 * (N : ℝ) ^ (k + 1) := by
    push_cast
    have hMult := mul_le_mul_of_nonneg_left hD₄Real (by positivity : 0 ≤ (k : ℝ) + 3)
    nlinarith only [hMult, hBaseOne]
  have hMax : max 7 (1 + (2 / (U : ℝ) ^ 3) * D) ≤
      max 7 (1 + 8 * (N : ℝ) / U) := by
    apply max_le_max le_rfl
    apply add_le_add_right
    calc
      _ ≤ (2 / (U : ℝ) ^ 3) * (4 * (U : ℝ) ^ 2 * N) := by gcongr
      _ = _ := by field_simp; ring
  have hWeak : x ^ 2 ≤
      ((4 * (k : ℝ) + 13) * (U : ℝ) ^ 2 * (N : ℝ) ^ (k + 4)) * x +
      (N : ℝ) ^ (2 * k + 9) * max 7 (1 + 8 * (N : ℝ) / U) := by
    calc
      _ ≤ _ := hQuad
      _ ≤ (N : ℝ) ^ 3 *
          (((4 * (k : ℝ) + 13) * (U : ℝ) ^ 2 * (N : ℝ) ^ (k + 1)) * x +
            ((N : ℝ) ^ (k + 3) * (N : ℝ) ^ (k + 3)) *
              max 7 (1 + 8 * (N : ℝ) / U)) := by
        push_cast
        push_cast at hCoeff
        gcongr
      _ = _ := by
        simp only [show 2 * k + 9 = k + k + 9 by omega, pow_add]
        ring
  have hLinear := prefix_quadratic_le_linear_add_sqrt hx (by positivity) (by positivity) hWeak
  exact hLinear.trans (higher_prefix_scale_envelope N U k hUOne hNR)

variable {α : Type*} [DecidableEq α] [Nonempty α]

theorem higher_actual_final_family_scale_bound
    (H : Family α) (V : Edge α) (U k tSingleton : ℕ)
    (hU : 2 ≤ U) (hN : U ^ 32 ≤ V.card)
    (hAdm : Admissible H) (hUniform : Uniform (k + 6) H) (hAmbient : ∀ E ∈ H, E ⊆ V)
    (hDBase : ∀ S : Edge α, S.card = k + 4 →
      (H.filter fun E => S ⊆ E).card ≤ 4 * U ^ 2 * V.card)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ 4 * U ^ 2 * V.card ^ (k + 1)) :
    let N := V.card
    let L := higherFinalFamily H V (k + 3) tSingleton (N ^ (k + 2) / U ^ 9)
      (N ^ (k + 1) / U ^ 9) (N / U ^ 3) (N / U ^ 6) (N ^ 2 / U ^ 3) (N ^ 2 / U ^ 6)
    (L.card : ℝ) ≤ (4 * (k : ℝ) + 13) * ((N : ℝ) ^ (k + 5) / U) +
      3 * ((N : ℝ) ^ (k + 5) / Real.sqrt U) := by
  have hUOne : 1 ≤ U := by omega
  have hNOne : 1 ≤ V.card := (Nat.one_le_pow _ _ hUOne).trans hN
  rcases higher_parameter_feasibility V.card U hU hN with
    ⟨_, _, _, _, _, hGap, hScale⟩
  have hQuad := higher_final_family_prefix_bound H V (k + 3) tSingleton
    (V.card ^ (k + 2) / U ^ 9) (V.card ^ (k + 1) / U ^ 9)
    (V.card / U ^ 3) (V.card / U ^ 6) (V.card ^ 2 / U ^ 3) (V.card ^ 2 / U ^ 6)
    (4 * U ^ 2 * V.card) (4 * U ^ 2 * V.card ^ (k + 1)) (2 / (U : ℝ) ^ 3)
    (by omega) (by
      have hPos : 0 < 4 * U ^ 2 * V.card ^ (k + 1) := by positivity
      omega) (by positivity) hAdm
    (by simpa only [Nat.add_assoc] using hUniform) hAmbient hGap hScale
    (by simpa only [Nat.add_assoc] using hDBase) hD₄
  exact higher_prefix_quadratic_scale_bound V.card U k _ _ _ hU hN
    (by positivity) (by rfl) (by rfl) hQuad

end JSP523.Rank5
