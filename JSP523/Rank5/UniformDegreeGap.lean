import JSP523.Rank5.ConditionalRankFive

/-! # Uniform degree concentration from conditional sequence exclusion

Choosing one counterexample at every bad ambient size avoids any
assumption that the bad sizes contain an eventual interval.
-/

namespace JSP523.Rank5

open Filter

/-- Conditional sequence exclusion implies a threshold valid for every
family of every sufficiently large ambient size. -/
theorem eventually_uniform_degree_concentration_of_conditional_exclusion
    (r : ℕ) (δ : ℝ)
    (hExclude : ∀ (H : ∀ n : ℕ, Family (Fin n)) (M : ℕ → ℕ),
      (∀ n, Admissible (H n)) → (∀ n, Uniform r (H n)) →
      (∀ n z, ((H n).filter (fun E => z ∈ E)).card ≤ M n) →
      ∀ᶠ n : ℕ in atTop,
        ¬ ((M n : ℝ) ≤ (1 - δ) * ((n - 1).choose (r - 1) : ℝ) ∧
          (n - 1).choose (r - 1) ≤ (H n).card)) :
    ∀ᶠ n : ℕ in atTop, ∀ F : Family (Fin n),
      Admissible F → Uniform r F → (n - 1).choose (r - 1) ≤ F.card →
      ∃ z : Fin n, (1 - δ) * ((n - 1).choose (r - 1) : ℝ) <
        ((F.filter fun E => z ∈ E).card : ℝ) := by
  classical
  let P := fun (n : ℕ) (F : Family (Fin n)) =>
    Admissible F ∧ Uniform r F ∧ (n - 1).choose (r - 1) ≤ F.card ∧
      ∀ z : Fin n, ((F.filter fun E => z ∈ E).card : ℝ) ≤
        (1 - δ) * ((n - 1).choose (r - 1) : ℝ)
  let H : ∀ n : ℕ, Family (Fin n) := fun n =>
    if h : ∃ F, P n F then Classical.choose h else ∅
  have hSelected (n : ℕ) (h : ∃ F, P n F) : P n (H n) := by
    simpa only [H, dite_eq_left h] using Classical.choose_spec h
  have hAdm : ∀ n, Admissible (H n) := by
    intro n
    by_cases h : ∃ F, P n F
    · exact (hSelected n h).1
    · simp only [H, dite_eq_right h]
      simp [Admissible]
  have hUniform : ∀ n, Uniform r (H n) := by
    intro n
    by_cases h : ∃ F, P n F
    · exact (hSelected n h).2.1
    · simp only [H, dite_eq_right h]
      simp [Uniform]
  let M : ℕ → ℕ := fun n =>
    (Finset.univ : Finset (Fin n)).sup fun z => ((H n).filter fun E => z ∈ E).card
  have hMax : ∀ n z, ((H n).filter (fun E => z ∈ E)).card ≤ M n := by
    intro n z
    exact Finset.le_sup (f := fun z : Fin n => ((H n).filter fun E => z ∈ E).card)
      (Finset.mem_univ z)
  have hNoGap := hExclude H M hAdm hUniform hMax
  filter_upwards [hNoGap, eventually_ge_atTop 1] with n hNoGapN hn
  intro F hAdmF hUniformF hMassF
  by_contra hNoCenter
  have hAll : ∀ z : Fin n, ((F.filter fun E => z ∈ E).card : ℝ) ≤
      (1 - δ) * ((n - 1).choose (r - 1) : ℝ) := by
    intro z
    exact le_of_not_gt (fun hz => hNoCenter ⟨z,hz⟩)
  have hBad : ∃ F, P n F := ⟨F,hAdmF,hUniformF,hMassF,hAll⟩
  have hSel := hSelected n hBad
  obtain ⟨z, _, hSup⟩ := Finset.exists_mem_eq_sup
    (Finset.univ : Finset (Fin n))
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    (fun z => ((H n).filter fun E => z ∈ E).card)
  have hM : M n = ((H n).filter fun E => z ∈ E).card := hSup
  apply hNoGapN
  refine ⟨?_, hSel.2.2.1⟩
  rw [hM]
  exact hSel.2.2.2 z

/-- Rank-five degree concentration, uniformly over all admissible
star-sized families, with no remaining sequence premise. -/
theorem eventually_uniform_rank_five_degree_concentration
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ F : Family (Fin n),
      Admissible F → Uniform 5 F → (n - 1).choose 4 ≤ F.card →
      ∃ z : Fin n, (1 - δ) * ((n - 1).choose 4 : ℝ) <
        ((F.filter fun E => z ∈ E).card : ℝ) := by
  exact eventually_uniform_degree_concentration_of_conditional_exclusion 5 δ
    (fun H M hAdm hUniform hMax =>
      eventually_rank_five_degree_gap_excludes_star_mass δ hδ H M hAdm hUniform hMax)

end JSP523.Rank5
