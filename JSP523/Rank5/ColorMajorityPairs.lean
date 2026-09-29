import JSP523.Rank5.ColorRigiditySampling

/-! # Most frequent color from discordant ordered pairs

This is the finite counting form of the last step of IV.6.2. Uncolored
edges are exceptions, including when an edge is paired with itself.
-/

namespace JSP523.Rank5

variable {α κ : Type*} [DecidableEq α] [DecidableEq κ]

/-- Two objects are discordant if they do not both carry one common color. -/
noncomputable def discordantColorPairs (S : Finset α) (color : α → Option κ) :
    Finset (α × α) := by
  classical
  exact (S ×ˢ S).filter fun p => ¬ ∃ c, color p.1 = some c ∧ color p.2 = some c

omit [DecidableEq α] in
/-- A most frequent color has at most the discordant ordered-pair count
    divided by the number of objects as exceptions. This form uses no
    division and includes all uncolored objects in its exception count. -/
theorem exists_color_exception_mul_card_le_discordant
    (S : Finset α) (colors : Finset κ) (color : α → Option κ)
    (hColors : colors.Nonempty)
    (hSupport : ∀ x ∈ S, ∀ c, color x = some c → c ∈ colors) :
    ∃ c ∈ colors,
      (S.filter fun x => color x ≠ some c).card * S.card ≤
        (discordantColorPairs S color).card := by
  classical
  obtain ⟨c, hc, hMax⟩ := Finset.exists_max_image colors
    (fun c => (S.filter fun x => color x = some c).card) hColors
  refine ⟨c, hc, ?_⟩
  let M := (S.filter fun x => color x ≠ some c).card
  have hFiber : ∀ x ∈ S,
      M ≤ (S.filter fun y => ¬ ∃ d, color x = some d ∧ color y = some d).card := by
    intro x hx
    cases hColor : color x with
    | none =>
      simpa using (Finset.card_filter_le S (fun x => color x ≠ some c))
    | some d =>
      have hd := hSupport x hx d hColor
      have hCount := hMax d hd
      have hPartitionC := Finset.card_filter_add_card_filter_not
        (s := S) (fun x => color x = some c)
      have hPartitionD := Finset.card_filter_add_card_filter_not
        (s := S) (fun x => color x = some d)
      simp only [Option.some.injEq, exists_eq_left']
      dsimp [M]
      omega
  have hSum := Finset.sum_le_sum hFiber
  have hCount : (discordantColorPairs S color).card =
      ∑ x ∈ S, (S.filter fun y => ¬ ∃ d, color x = some d ∧ color y = some d).card := by
    simp only [discordantColorPairs, Finset.card_eq_sum_ones, Finset.sum_filter,
      Finset.sum_product]
  rw [hCount]
  simpa only [Finset.sum_const, smul_eq_mul, mul_comm] using hSum

end JSP523.Rank5
