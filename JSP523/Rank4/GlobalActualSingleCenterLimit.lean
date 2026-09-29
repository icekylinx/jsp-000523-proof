import JSP523.Rank4.GlobalActualSingleCenterFinite

/-! # One original center for the entire stability parameter argument -/
namespace JSP523.Rank4

/-- The minimizing center depends only on the original family and original
center set, so later cleanup parameters cannot change the selected center. -/
noncomputable def actualOriginalMainCenter {n : ℕ}
    (H : Family (Fin (n + 1))) (centers : Edge (Fin (n + 1))) : Fin (n + 1) :=
  if h : centers.Nonempty then
    Classical.choose (Finset.exists_min_image centers
      (fun c => (outsideEdges H (Finset.univ.erase c)).card) h)
  else 0

theorem actual_original_main_center_spec {n : ℕ}
    (H : Family (Fin (n + 1))) (centers : Edge (Fin (n + 1)))
    (hCenters : centers.Nonempty) :
    actualOriginalMainCenter H centers ∈ centers ∧
      ∀ c ∈ centers, (outsideEdges H (Finset.univ.erase (actualOriginalMainCenter H centers))).card ≤
        (outsideEdges H (Finset.univ.erase c)).card := by
  unfold actualOriginalMainCenter
  rw [dite_eq_left hCenters]
  exact Classical.choose_spec (Finset.exists_min_image centers
    (fun c => (outsideEdges H (Finset.univ.erase c)).card) hCenters)

theorem actual_original_main_center_outside_bound
    {n : ℕ} (H : Family (Fin (n + 1))) (V centers : Edge (Fin (n + 1)))
    (L : Fin (n + 1) → Family (Fin (n + 1))) (owner : Edge (Fin (n + 1)) → Fin (n + 1))
    (deficit loss : ℕ) (hCenters : centers.Nonempty)
    (hOutside : ∀ c ∈ centers, c ∉ V)
    (hGround : ∀ c ∈ centers, ∀ T ∈ L c, T ∈ V.powersetCard 3)
    (hEdges : ∀ c ∈ centers, ∀ T ∈ L c, insert c T ∈ H)
    (hNear : V.card ^ 3 ≤ 6 * H.card + deficit)
    (hMass : H.card ≤ (∑ c ∈ centers, (pairOwnerCleanedLink L owner c).card) + loss) :
    6 * (outsideEdges H (Finset.univ.erase (actualOriginalMainCenter H centers))).card ≤
      2 * deficit + 18 * loss + 12 * V.card ^ 2 := by
  obtain ⟨c, hc, hBound⟩ := actual_original_single_center_outside_bound H V centers L owner
    deficit loss hCenters hOutside hGround hEdges hNear hMass
  exact (Nat.mul_le_mul_left 6 ((actual_original_main_center_spec H centers hCenters).2 c hc)).trans hBound

/-- Actual star-layer mass tending to the extremal scale yields outside
stability at a single, parameter-independent original center. -/
theorem actual_original_main_center_outside_ratio_tendsto_zero
    (H : (n : ℕ) → Family (Fin (n + 1)))
    (V centers : (n : ℕ) → Edge (Fin (n + 1)))
    (L : (n : ℕ) → Fin (n + 1) → Family (Fin (n + 1)))
    (owner : (n : ℕ) → Edge (Fin (n + 1)) → Fin (n + 1))
    (deficit loss : ℕ → ℕ)
    (hData : ∀ᶠ n in Filter.atTop,
      (centers n).Nonempty ∧
      (∀ c ∈ centers n, c ∉ V n) ∧
      (∀ c ∈ centers n, ∀ T ∈ L n c, T ∈ (V n).powersetCard 3) ∧
      (∀ c ∈ centers n, ∀ T ∈ L n c, insert c T ∈ H n) ∧
      (V n).card ^ 3 ≤ 6 * (H n).card + deficit n ∧
      (H n).card ≤ (∑ c ∈ centers n, (pairOwnerCleanedLink (L n) (owner n) c).card) + loss n)
    (hDeficit : Filter.Tendsto (fun n => (deficit n : ℝ) / (n : ℝ) ^ 3)
      Filter.atTop (nhds 0))
    (hLoss : Filter.Tendsto (fun n => (loss n : ℝ) / (n : ℝ) ^ 3)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => ((outsideEdges (H n)
        (Finset.univ.erase (actualOriginalMainCenter (H n) (centers n)))).card : ℝ) / (n : ℝ) ^ 3)
      Filter.atTop (nhds 0) := by
  have hInv : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  have hUpper : Filter.Tendsto
      (fun n => 2 * ((deficit n : ℝ) / (n : ℝ) ^ 3) +
        18 * ((loss n : ℝ) / (n : ℝ) ^ 3) + 48 * (n : ℝ)⁻¹)
      Filter.atTop (nhds 0) := by
    simpa using ((hDeficit.const_mul 2).add (hLoss.const_mul 18)).add (hInv.const_mul 48)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => by positivity)) ?_ hUpper
  filter_upwards [hData, Filter.eventually_ge_atTop (1 : ℕ)] with n hData hn
  rcases hData with ⟨hCenters, hOutside, hGround, hEdges, hNear, hMass⟩
  have hBound := actual_original_main_center_outside_bound (H n) (V n) (centers n)
    (L n) (owner n) (deficit n) (loss n) hCenters hOutside hGround hEdges hNear hMass
  have hV : (V n).card ≤ 2 * n := by
    have h := Finset.card_le_univ (V n)
    simp only [Fintype.card_fin] at h
    omega
  have hSquare := Nat.pow_le_pow_left hV 2
  have hNat : (outsideEdges (H n)
      (Finset.univ.erase (actualOriginalMainCenter (H n) (centers n)))).card ≤
      2 * deficit n + 18 * loss n + 48 * n ^ 2 := by nlinarith only [hBound, hSquare]
  have hnPos : (0 : ℝ) < n := by exact_mod_cast hn
  have hReal : ((outsideEdges (H n)
      (Finset.univ.erase (actualOriginalMainCenter (H n) (centers n)))).card : ℝ) ≤
      2 * (deficit n : ℝ) + 18 * (loss n : ℝ) + 48 * (n : ℝ) ^ 2 := by exact_mod_cast hNat
  have hDiv := div_le_div_of_nonneg_right hReal (by positivity : 0 ≤ (n : ℝ) ^ 3)
  convert hDiv using 1
  field_simp

end JSP523.Rank4
