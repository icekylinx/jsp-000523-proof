import JSP523.Rank4.GlobalActualSingleCenterEndpoint

/-! # Near-extremal original families have one original main center -/
namespace JSP523.Rank4

theorem shifted_quadratic_cubic_ratio_tendsto_zero (C : ℕ) :
    Filter.Tendsto (fun n : ℕ => ((C * (n + 1) ^ 2 : ℕ) : ℝ) / (n : ℝ) ^ 3)
      Filter.atTop (nhds 0) := by
  have hInv : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  have hUpper : Filter.Tendsto (fun n : ℕ => (4 * C : ℝ) * (n : ℝ)⁻¹)
      Filter.atTop (nhds 0) := by simpa using hInv.const_mul (4 * C : ℝ)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => by positivity)) ?_ hUpper
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  have hnPos : (0 : ℝ) < n := by exact_mod_cast hn
  have hSq : C * (n + 1) ^ 2 ≤ 4 * C * n ^ 2 := by
    have h := Nat.mul_le_mul_left C (Nat.pow_le_pow_left (show n + 1 ≤ 2 * n by omega) 2)
    nlinarith only [h]
  have hReal : ((C * (n + 1) ^ 2 : ℕ) : ℝ) ≤ 4 * (C : ℝ) * (n : ℝ) ^ 2 := by
    exact_mod_cast hSq
  have hDiv := div_le_div_of_nonneg_right hReal (by positivity : 0 ≤ (n : ℝ) ^ 3)
  convert hDiv using 1
  field_simp

/-- The deficit below the full star and the actual preprocessing loss may
both be arbitrary `o(n³)` sequences. The resulting center belongs to the
original center set, and does not use the cleaned labels. -/
theorem actual_original_center_stability_of_near_extremal_layers
    (H : (n : ℕ) → Family (Fin (n + 1)))
    (V centers : (n : ℕ) → Edge (Fin (n + 1)))
    (L : (n : ℕ) → Fin (n + 1) → Family (Fin (n + 1)))
    (owner : (n : ℕ) → Edge (Fin (n + 1)) → Fin (n + 1))
    (missing loss : ℕ → ℕ)
    (hData : ∀ᶠ n in Filter.atTop,
      (∀ c ∈ centers n, c ∉ V n) ∧
      (∀ c ∈ centers n, ∀ T ∈ L n c, T ∈ (V n).powersetCard 3) ∧
      (∀ c ∈ centers n, ∀ T ∈ L n c, insert c T ∈ H n) ∧
      n.choose 3 ≤ (H n).card + missing n ∧
      (H n).card ≤ (∑ c ∈ centers n, (pairOwnerCleanedLink (L n) (owner n) c).card) + loss n)
    (hMissing : Filter.Tendsto (fun n => (missing n : ℝ) / (n : ℝ) ^ 3)
      Filter.atTop (nhds 0))
    (hLoss : Filter.Tendsto (fun n => (loss n : ℝ) / (n : ℝ) ^ 3)
      Filter.atTop (nhds 0)) :
    (∀ᶠ n in Filter.atTop, actualOriginalMainCenter (H n) (centers n) ∈ centers n) ∧
    Filter.Tendsto
      (fun n => ((outsideEdges (H n)
        (Finset.univ.erase (actualOriginalMainCenter (H n) (centers n)))).card : ℝ) / (n : ℝ) ^ 3)
      Filter.atTop (nhds 0) := by
  have hSumRatio : Filter.Tendsto
      (fun n => (missing n : ℝ) / (n : ℝ) ^ 3 + (loss n : ℝ) / (n : ℝ) ^ 3)
      Filter.atTop (nhds 0) := by simpa using hMissing.add hLoss
  have hSmall := (tendsto_order.1 hSumRatio).2 (1 / 12) (by norm_num)
  have hGap : ∀ᶠ n in Filter.atTop, missing n + loss n < n.choose 3 := by
    filter_upwards [hSmall, cubic_le_twelve_choose_eventually,
      Filter.eventually_ge_atTop (1 : ℕ)] with n hSmall hCube hn
    have hnPos : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
    have hRatio : ((missing n : ℝ) + loss n) / (n : ℝ) ^ 3 < 1 / 12 := by
      simpa only [add_div] using hSmall
    have hMul := (div_lt_iff₀ hnPos).1 hRatio
    have hReal : (missing n : ℝ) + loss n < n.choose 3 := by nlinarith
    exact_mod_cast hReal
  have hCenters : ∀ᶠ n in Filter.atTop, (centers n).Nonempty := by
    filter_upwards [hData, hGap] with n hData hGap
    by_contra hEmpty
    have hC : centers n = ∅ := Finset.not_nonempty_iff_eq_empty.mp hEmpty
    have hMass : (H n).card ≤ loss n := by
      simpa only [hC, Finset.sum_empty, zero_add] using hData.2.2.2.2
    have hLower := hData.2.2.2.1
    omega
  constructor
  · filter_upwards [hCenters] with n hn
    exact (actual_original_main_center_spec (H n) (centers n) hn).1
  · let deficit := fun n => 6 * missing n + 9 * (n + 1) ^ 2
    have hDeficit : Filter.Tendsto (fun n => (deficit n : ℝ) / (n : ℝ) ^ 3)
        Filter.atTop (nhds 0) := by
      have h := (hMissing.const_mul 6).add (shifted_quadratic_cubic_ratio_tendsto_zero 9)
      simpa only [deficit, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, add_div, mul_div_assoc,
        mul_zero, zero_add] using h
    apply actual_original_main_center_outside_ratio_tendsto_zero H V centers L owner deficit loss
      ?_ hDeficit hLoss
    filter_upwards [hData, hCenters, Filter.eventually_ge_atTop (2 : ℕ)] with n hData hCenters hn
    rcases hData with ⟨hOutside, hGround, hEdges, hLower, hMass⟩
    refine ⟨hCenters, hOutside, hGround, hEdges, ?_, hMass⟩
    have hV : (V n).card ≤ n + 1 := by
      simpa only [Fintype.card_fin] using Finset.card_le_univ (V n)
    have hNear := star_lower_supplies_cubic_deficit n ((H n).card + missing n) (V n).card
      hn hV hLower
    dsimp [deficit]
    omega

end JSP523.Rank4
