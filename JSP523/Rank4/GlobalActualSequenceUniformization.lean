import JSP523.Rank4.GlobalNearStarThreshold
import JSP523.LowerConstruction

/-! # Uniformizing rank-four assertions proved for every sequence -/

namespace JSP523.Rank4

open Filter

/-- If every sequence of actual admissible families above the star lower
bound eventually has a property, then one threshold works for all such
families.  A bad witness is selected at each size where one exists. -/
theorem eventually_uniform_of_rank_four_sequence_property
    (P : (n : ℕ) → Family (Fin (n + 1)) → Prop)
    (hEndpoint : ∀ H : (n : ℕ) → Family (Fin (n + 1)),
      (∀ n, Admissible (H n)) → (∀ n, Uniform 4 (H n)) →
      (∀ n, n.choose 3 ≤ (H n).card) →
      ∀ᶠ n in atTop, P n (H n)) :
    ∀ᶠ n : ℕ in atTop, ∀ F : Family (Fin (n + 1)),
      Admissible F → Uniform 4 F → n.choose 3 ≤ F.card → P n F := by
  classical
  let good : (n : ℕ) → Family (Fin (n + 1)) := fun n =>
    Classical.choose (JSP523.exists_star_plus_matching_exact
      (0 : Fin (n + 1)) 4 (by omega))
  let bad : ℕ → Prop := fun n =>
    ∃ F : Family (Fin (n + 1)),
      Admissible F ∧ Uniform 4 F ∧ n.choose 3 ≤ F.card ∧ ¬ P n F
  let H : (n : ℕ) → Family (Fin (n + 1)) := fun n =>
    if h : bad n then Classical.choose h else good n
  have hGood (n : ℕ) :
      Admissible (good n) ∧ Uniform 4 (good n) ∧
      n.choose 3 ≤ (good n).card := by
    have h := Classical.choose_spec (JSP523.exists_star_plus_matching_exact
      (0 : Fin (n + 1)) 4 (by omega))
    have hSize : (Finset.univ.erase (0 : Fin (n + 1)) : Edge (Fin (n + 1))).card = n := by
      simp
    have hCard : (good n).card = n.choose 3 + n / 4 := by
      simpa only [good, hSize] using h.2.2
    exact ⟨h.2.1, h.1, by rw [hCard]; omega⟩
  have hBad (n : ℕ) (hb : bad n) :
      Admissible (H n) ∧ Uniform 4 (H n) ∧
      n.choose 3 ≤ (H n).card ∧ ¬ P n (H n) := by
    simp only [H, dite_eq_left hb]
    exact Classical.choose_spec hb
  have hProperties : ∀ n, Admissible (H n) ∧ Uniform 4 (H n) ∧ n.choose 3 ≤ (H n).card := by
    intro n
    by_cases hb : bad n
    · have h := hBad n hb
      exact ⟨h.1, h.2.1, h.2.2.1⟩
    · simpa only [H, dite_eq_right hb] using hGood n
  filter_upwards [hEndpoint H (fun n => (hProperties n).1)
    (fun n => (hProperties n).2.1) (fun n => (hProperties n).2.2)] with n hP
  intro F hF hF4 hFLower
  by_contra hNot
  have hb : bad n := ⟨F, hF, hF4, hFLower, hNot⟩
  exact (hBad n hb).2.2.2 hP

end JSP523.Rank4
