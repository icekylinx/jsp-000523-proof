import JSP523.Rank5.FarStarAsymptotic

namespace JSP523.Rank5

open Filter Asymptotics

theorem eventually_conditional_far_star_positive_mass
    (r p p' q s : ℕ)
    (hr : 4 ≤ r) (hpp' : p < p') (hp'q : p' < q)
    (hCollisionCoeff : farStarCollisionConstant r * q ≤ s ^ 2)
    (hErrorCoeff : 2 * (s + 2) *
      (2 ^ (r - 1) * (r - 1).factorial) ≤ q - p')
    (H : ∀ n : ℕ, Family (Fin n))
    (X : ∀ n : ℕ, Edge (Fin n))
    (h M : ℕ → ℕ)
    (hAdm : ∀ n, Admissible (H n))
    (hUniform : ∀ n, Uniform r (H n))
    (hX : ∀ n, (X n).card ≤ h n)
    (hMax : ∀ n z, ((H n).filter (fun E => z ∈ E)).card ≤ M n)
    (hLittle : (fun n : ℕ => ((h n) ^ 2 : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ))) :
    ∀ᶠ n : ℕ in atTop,
      q ^ (r - 1) * M n ≤ p ^ (r - 1) * (n - 1).choose (r - 1) →
      (n - 1).choose (r - 1) ≤ (H n).card →
      (q - p') * (n - 1).choose (r - 1) ≤
        2 * q * ((H n).filter (fun E => Disjoint E (X n))).card := by
  let N := max (2 * (r - 1) + 1)
    (max q (q * r + 2 * p' * (r - 1)))
  have hSmall := eventually_small_set_of_square_is_little_o h q hLittle
  filter_upwards [eventually_ge_atTop N, hSmall] with n hn hTiny
  intro hnRatio hnMass
  have hnLarge : 2 * (r - 1) + 1 ≤ n :=
    (le_max_left _ _).trans hn
  have hqN : q ≤ n :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hThresholdLower : q * r + 2 * p' * (r - 1) ≤ n :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hGap : 1 ≤ p' - p := by omega
  have hThreshold : q * r + 2 * p' * (r - 1) ≤
      (p' - p) * n := by
    exact hThresholdLower.trans
      (by simpa using Nat.mul_le_mul_right n hGap)
  have hQ : q ≤ n ^ (r - 1) :=
    hqN.trans (le_self_pow (by omega : 1 ≤ n)
      (by omega : r - 1 ≠ 0))
  have hDegree := far_star_degree_rate_of_star_ratio
    n (r - 1) (M n) p q hnRatio
  let : Inhabited (Fin n) := ⟨⟨0, by omega⟩⟩
  exact finite_far_star_tail_positive_from_small_set (H n) (X n)
    (hAdm n) (hUniform n) hr hnLarge (hX n)
    (hMax n)
    hpp'.le hp'q hDegree hThreshold hnMass hTiny hQ
    hCollisionCoeff hErrorCoeff

/-- A fixed positive real gap in maximum degree gives a fixed positive
fraction of the extremal star in the far tail of the actual family. -/
theorem eventually_conditional_far_star_mass_of_degree_gap
    (r : ℕ) (δ : ℝ) (hr : 4 ≤ r) (hδ : 0 < δ)
    (H : ∀ n : ℕ, Family (Fin n))
    (X : ∀ n : ℕ, Edge (Fin n))
    (h M : ℕ → ℕ)
    (hAdm : ∀ n, Admissible (H n))
    (hUniform : ∀ n, Uniform r (H n))
    (hX : ∀ n, (X n).card ≤ h n)
    (hMax : ∀ n z, ((H n).filter (fun E => z ∈ E)).card ≤ M n)
    (hLittle : (fun n : ℕ => ((h n) ^ 2 : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ))) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      ∀ᶠ n : ℕ in atTop,
        (M n : ℝ) ≤ (1 - δ) * ((n - 1).choose (r - 1) : ℝ) →
        (n - 1).choose (r - 1) ≤ (H n).card →
        a * (n - 1).choose (r - 1) ≤
          b * ((H n).filter (fun E => Disjoint E (X n))).card := by
  obtain ⟨A, B, hAB, hGap⟩ :=
    exists_integer_degree_gap_of_real_gap δ hδ
  obtain ⟨p, p', q, s, hpp', hp'q, hPower, hCollision, hError⟩ :=
    exists_far_star_rational_coefficients r (r - 1) A B hAB (by omega)
  have hBpos : 0 < B := by omega
  have hRatio : ∀ n : ℕ,
      (M n : ℝ) ≤ (1 - δ) * ((n - 1).choose (r - 1) : ℝ) →
      q ^ (r - 1) * M n ≤
        p ^ (r - 1) * (n - 1).choose (r - 1) := by
    intro n hn
    let t := (n - 1).choose (r - 1)
    have hBDegree : B * M n ≤ A * t := hGap (M n) t hn
    have hMul : B * (q ^ (r - 1) * M n) ≤
        B * (p ^ (r - 1) * t) := by
      calc
        B * (q ^ (r - 1) * M n) =
            q ^ (r - 1) * (B * M n) := by ring
        _ ≤ q ^ (r - 1) * (A * t) :=
          Nat.mul_le_mul_left _ hBDegree
        _ = (A * q ^ (r - 1)) * t := by ring
        _ ≤ (B * p ^ (r - 1)) * t :=
          Nat.mul_le_mul_right _ hPower
        _ = B * (p ^ (r - 1) * t) := by ring
    exact Nat.le_of_mul_le_mul_left hMul hBpos
  refine ⟨q - p', 2 * q, Nat.sub_pos_of_lt hp'q, ?_, ?_⟩
  · omega
  · have h := eventually_conditional_far_star_positive_mass r p p' q s hr hpp' hp'q
      hCollision hError H X h M hAdm hUniform hX hMax hLittle
    filter_upwards [h] with n hn
    intro hGapN hMassN
    exact hn (hRatio n hGapN) hMassN

end JSP523.Rank5
