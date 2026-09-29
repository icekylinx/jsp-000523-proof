import JSP523.Rank4.PreprocessActualContractionStep

/-! # Integer-power certificates for geometric regularization -/

namespace JSP523.Rank4

def contractionRadius (q n : ℕ) : ℕ := 6 * (n / q + 1)

/-- The radius is large enough for allocation and costs only O(n/q). -/
theorem contraction_radius_bounds (q n : ℕ) (hq : 2 ≤ q) (hn : q ^ 11 ≤ n) :
    6 * (q ^ 8 * n ^ 2) ≤ contractionRadius q n ^ 3 ∧
      q * (contractionRadius q n + 3) ≤ 15 * n := by
  have hqPos : 0 < q := by omega
  have hq1 : 1 ≤ q := by omega
  have hqN : q ≤ n := by
    have hPow : q ≤ q ^ 11 := Nat.le_self_pow (by omega) q
    exact hPow.trans hn
  have hDiv : q * (n / q + 1) ≥ n := by
    have hh := Nat.lt_mul_div_succ n hqPos
    omega
  have hLower : 6 * n ≤ q * contractionRadius q n := by
    dsimp [contractionRadius]
    nlinarith [hDiv]
  have hCube := Nat.pow_le_pow_left hLower 3
  have hRad : 6 * (q ^ 8 * n ^ 2) ≤ contractionRadius q n ^ 3 := by
    apply Nat.le_of_mul_le_mul_left (c := q ^ 3) _ (by positivity)
    calc
      q ^ 3 * (6 * (q ^ 8 * n ^ 2)) = 6 * q ^ 11 * n ^ 2 := by ring
      _ ≤ 6 * n * n ^ 2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 6 hn)
      _ ≤ (6 * n) ^ 3 := by nlinarith
      _ ≤ (q * contractionRadius q n) ^ 3 := hCube
      _ = q ^ 3 * contractionRadius q n ^ 3 := by ring
  refine ⟨hRad, ?_⟩
  have hFloor := Nat.mul_div_le n q
  dsimp [contractionRadius]
  nlinarith

/-- Pure integer arithmetic absorbs every actual deletion term. -/
theorem contraction_actual_loss_certificate
    (q n x c loss : ℕ) (hq : 2 ≤ q) (hn : q ^ 11 ≤ n)
    (hx : x * q ^ 5 ≤ 8 * n)
    (hc : c ^ 2 ≤ n.choose 2 *
      (x * (x - 1) * (3 * max (q ^ 8 * n) (9 * q ^ 8) + q ^ 8 * n ^ 2)))
    (hLoss : 3 * q ^ 6 * loss ≤ q ^ 6 *
      (3 * (x.choose 2 * (q ^ 8 * n)) + 3 * c +
        (contractionRadius q n + 3) * n.choose 2) +
      6 * n.choose 2 * max (q ^ 5 * n) (9 * q ^ 8)) :
    q * loss ≤ 128 * n ^ 3 := by
  have hq1 : 1 ≤ q := by omega
  have hqPos : 0 < q := by omega
  have hn1 : 1 ≤ n := (one_le_pow₀ hq1).trans hn
  have hChoose : n.choose 2 ≤ n ^ 2 := Nat.choose_le_pow n 2
  have hxChoose : x.choose 2 ≤ x ^ 2 := Nat.choose_le_pow x 2
  have hnSq : n ≤ n ^ 2 := Nat.le_self_pow (by omega) n
  have hMax : max (q ^ 8 * n) (9 * q ^ 8) ≤ 9 * q ^ 8 * n := by
    apply max_le
    · nlinarith [Nat.zero_le (q ^ 8 * n)]
    · exact Nat.le_mul_of_pos_right _ hn1
  have hcm : c ^ 2 ≤ (6 * q ^ 4 * x * n ^ 2) ^ 2 := by
    calc
      c ^ 2 ≤ n ^ 2 * (x ^ 2 * (3 * (9 * q ^ 8 * n) + q ^ 8 * n ^ 2)) := by
        apply hc.trans
        apply Nat.mul_le_mul hChoose
        apply Nat.mul_le_mul
        · nlinarith [Nat.sub_le x 1]
        · exact Nat.add_le_add_right (Nat.mul_le_mul_left 3 hMax) _
      _ ≤ n ^ 2 * (x ^ 2 * (3 * (9 * q ^ 8 * n ^ 2) + q ^ 8 * n ^ 2)) := by
        gcongr
      _ ≤ (6 * q ^ 4 * x * n ^ 2) ^ 2 := by nlinarith [Nat.zero_le (q ^ 8 * x ^ 2 * n ^ 4)]
  have hcBound : c ≤ 6 * q ^ 4 * x * n ^ 2 := (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hcm
  have hcq : q * c ≤ 48 * n ^ 3 := by
    calc
      _ ≤ q * (6 * q ^ 4 * x * n ^ 2) := Nat.mul_le_mul_left q hcBound
      _ = 6 * (x * q ^ 5) * n ^ 2 := by ring
      _ ≤ 6 * (8 * n) * n ^ 2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 6 hx)
      _ = 48 * n ^ 3 := by ring
  have hPow : q ^ 9 ≤ q ^ 10 := by
    calc
      _ = q ^ 9 * 1 := by simp
      _ ≤ q ^ 9 * q := Nat.mul_le_mul_left _ hq1
      _ = q ^ 10 := by ring
  have hPair : q * (x.choose 2 * (q ^ 8 * n)) ≤ 64 * n ^ 3 := by
    calc
      _ = q ^ 9 * x.choose 2 * n := by ring
      _ ≤ q ^ 10 * x ^ 2 * n := Nat.mul_le_mul_right n (Nat.mul_le_mul hPow hxChoose)
      _ = (x * q ^ 5) ^ 2 * n := by ring
      _ ≤ (8 * n) ^ 2 * n := Nat.mul_le_mul_right n (Nat.pow_le_pow_left hx 2)
      _ = 64 * n ^ 3 := by ring
  have hRadius := (contraction_radius_bounds q n hq hn).2
  have hAlloc : q * ((contractionRadius q n + 3) * n.choose 2) ≤ 15 * n ^ 3 := by
    calc
      _ = (q * (contractionRadius q n + 3)) * n.choose 2 := by ring
      _ ≤ (15 * n) * n ^ 2 := Nat.mul_le_mul hRadius hChoose
      _ = 15 * n ^ 3 := by ring
  have hQ8 : 9 ≤ q ^ 8 := by
    have hh := Nat.pow_le_pow_left hq 8
    norm_num at hh
    omega
  have hSmall : 9 * q ^ 3 ≤ n := by
    calc
      _ ≤ q ^ 8 * q ^ 3 := Nat.mul_le_mul_right _ hQ8
      _ = q ^ 11 := by ring
      _ ≤ n := hn
  have hTailMax : max (q ^ 5 * n) (9 * q ^ 8) = q ^ 5 * n := by
    apply max_eq_left
    have hh := Nat.mul_le_mul_left (q ^ 5) hSmall
    nlinarith only [hh]
  have hTail : q * (6 * n.choose 2 * max (q ^ 5 * n) (9 * q ^ 8)) ≤
      6 * q ^ 6 * n ^ 3 := by
    rw [hTailMax]
    calc
      _ ≤ q * (6 * n ^ 2 * (q ^ 5 * n)) := by gcongr
      _ = 6 * q ^ 6 * n ^ 3 := by ring
  have hMain : q * (3 * (x.choose 2 * (q ^ 8 * n)) + 3 * c +
      (contractionRadius q n + 3) * n.choose 2) ≤ 351 * n ^ 3 := by
    nlinarith only [hPair, hcq, hAlloc]
  have hScale := Nat.mul_le_mul_left q hLoss
  have hScaleMain := Nat.mul_le_mul_left (q ^ 6) hMain
  have hCombined : (3 * q ^ 6) * (q * loss) ≤ (3 * q ^ 6) * (128 * n ^ 3) := by
    nlinarith only [hScale, hScaleMain, hTail, Nat.zero_le (q ^ 6 * n ^ 3)]
  exact Nat.le_of_mul_le_mul_left hCombined (by positivity)

/-- Concrete integer-power contraction, with no geometric or error-bound
premise beyond the actual degree caps of the input family. -/
theorem exists_actual_eighth_power_contraction
    {n : ℕ} (F : Family (Fin n)) (q : ℕ)
    (hq : 2 ≤ q) (hn : q ^ 11 ≤ n)
    (hAdm : Admissible F) (hUniform : Uniform 4 F)
    (hVertex : ∀ v, (F.filter fun E => v ∈ E).card ≤ q ^ 8 * n ^ 2)
    (hPair : ∀ P : Edge (Fin n), P.card = 2 → rankFourPairDegree F P ≤ q ^ 8 * n)
    (hFacet : ∀ Q : Edge (Fin n), Q.card = 3 →
      (facetCompletions F Finset.univ Q).card ≤ q ^ 8) :
    ∃ K : Family (Fin n), K ⊆ F ∧ q * (F \ K).card ≤ 128 * n ^ 3 ∧
      (∀ v, (K.filter fun E => v ∈ E).card ≤ q ^ 6 * n ^ 2) ∧
      (∀ P : Edge (Fin n), P.card = 2 → rankFourPairDegree K P ≤ q ^ 6 * n) ∧
      (∀ Q : Edge (Fin n), Q.card = 3 → (facetCompletions K Finset.univ Q).card ≤ q ^ 6) := by
  have hq1 : 1 ≤ q := by omega
  have hqPos : 0 < q := by omega
  have hnPos : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hR : 3 ≤ q ^ 8 := by
    have hh := Nat.pow_le_pow_left hq 8
    norm_num at hh
    omega
  have hTS : q ^ 5 ≤ q ^ 6 := by
    calc
      _ = q ^ 5 * 1 := by simp
      _ ≤ q ^ 5 * q := Nat.mul_le_mul_left _ hq1
      _ = q ^ 6 := by ring
  have hGap : 2 * q ^ 8 ≤ (q ^ 5) ^ 2 := by
    have h2 : 2 ≤ q ^ 2 := by nlinarith
    calc
      _ ≤ q ^ 2 * q ^ 8 := Nat.mul_le_mul_right _ h2
      _ = (q ^ 5) ^ 2 := by ring
  obtain ⟨K, x, c, hKF, hx, hc, hV, hP, hF, hLoss⟩ :=
    exists_actual_degree_contraction_step F (q ^ 8) (q ^ 5) (q ^ 6) (contractionRadius q n)
      hnPos hR (by positivity) hTS hGap hAdm hUniform hVertex hPair hFacet
      (contraction_radius_bounds q n hq hn).1
  exact ⟨K, hKF, contraction_actual_loss_certificate q n x c (F \ K).card hq hn hx hc hLoss, hV, hP, hF⟩

end JSP523.Rank4
