import JSP523.Rank5.StarLayerLoss
import JSP523.Rank5.RegularizationRound

/-!
# Finite regularization with the removed-layer estimate discharged

The energy estimate uses the improved pair cap after removing the heavy
root cover, not the original parent's pair cap.  No old declaration is
changed.  Numerical scale hypotheses are explicit; asymptotic evaluation
of this finite bound is a separate matter.
-/

namespace JSP523.Rank5

open Finset
open scoped BigOperators
open JSP523.Rank5

variable {α : Type*} [DecidableEq α]

/-- Monotonicity of an actual codegree under edge deletion. -/
theorem completion_codegree_mono {F G : Family α} (hFG : F ⊆ G) (S : Edge α) :
    (F.filter (fun E => S ⊆ E)).card ≤ (G.filter (fun E => S ⊆ E)).card := by
  apply Finset.card_le_card
  intro E hE
  exact Finset.mem_filter.mpr
    ⟨hFG (Finset.mem_filter.mp hE).1, (Finset.mem_filter.mp hE).2⟩

/-- Deleting the cover enforces the stated cap on every root of the given
size, including roots outside the ambient set (whose fibers are empty). -/
theorem avoiding_cover_codegree_le
    (H : Family α) (V X : Edge α) (s C : ℕ)
    (hGround : ∀ E ∈ H, E ⊆ V)
    (hCover : ∀ S ∈ V.powersetCard s, Disjoint S X →
      (H.filter (fun E => S ⊆ E)).card ≤ C)
    (S : Edge α) (hS : S.card = s) :
    ((H.filter (fun E => Disjoint E X)).filter (fun E => S ⊆ E)).card ≤ C := by
  classical
  let F := (H.filter (fun E => Disjoint E X)).filter (fun E => S ⊆ E)
  by_cases hF : F.Nonempty
  · obtain ⟨E, hE⟩ := hF
    obtain ⟨hE₀, hSE⟩ := Finset.mem_filter.mp hE
    obtain ⟨hEH, hEX⟩ := Finset.mem_filter.mp hE₀
    have hSV : S ⊆ V := hSE.trans (hGround E hEH)
    have hSX : Disjoint S X := Finset.disjoint_left.mpr
      (fun x hxS hxX => (Finset.disjoint_left.mp hEX) (hSE hxS) hxX)
    exact (completion_codegree_mono (Finset.filter_subset _ _) S).trans
      (hCover S (Finset.mem_powersetCard.mpr ⟨hSV, hS⟩) hSX)
  · have hEmpty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    change F.card ≤ C
    simp only [hEmpty, Finset.card_empty, Nat.zero_le]

/-- Strengthened finite cover assembly: the facet energy is evaluated with
`d 2`, the post-cover pair cap. The old assembly remains unchanged. -/
theorem regularization_after_cover_improved_energy
    (H : Family α) (V X : Edge α) (r t L : ℕ) (d : ℕ → ℕ)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hGround : ∀ E ∈ H, E ⊆ V) (hr : 4 ≤ r)
    (hCover : ∀ s, 1 ≤ s → s ≤ r - 2 →
      ∀ S ∈ V.powersetCard s, Disjoint S X →
        (H.filter (fun E => S ⊆ E)).card ≤ d s)
    (hLayer : H.card - (H.filter (fun E => Disjoint E X)).card ≤ L) :
    ∃ H' : Family α, H' ⊆ H ∧ Admissible H' ∧ Uniform r H' ∧
      (∀ s, 1 ≤ s → s ≤ r - 2 → ∀ S ∈ V.powersetCard s,
        (H'.filter (fun E => S ⊆ E)).card ≤ d s) ∧
      (∀ A ∈ V.powersetCard (r - 1),
        (H'.filter (fun E => A ⊆ E)).card ≤ t) ∧
      (t - 1) * (H.card - H'.card) ≤ (t - 1) * L +
        2 * (V.card.choose 2 * ((r - 1) * d 2)) := by
  classical
  let H₀ := H.filter (fun E => Disjoint E X)
  have hSub₀ : H₀ ⊆ H := Finset.filter_subset _ _
  have hAdm₀ : Admissible H₀ := admissible_mono hSub₀ hAdm
  have hUniform₀ : Uniform r H₀ := fun _ hE => hUniform (hSub₀ hE)
  have hGround₀ : ∀ E ∈ H₀, E ⊆ V := fun E hE => hGround E (hSub₀ hE)
  have hCaps₀ : ∀ s, 1 ≤ s → s ≤ r - 2 →
      ∀ S : Edge α, S.card = s → (H₀.filter (fun E => S ⊆ E)).card ≤ d s := by
    intro s hs hsr S hS
    exact avoiding_cover_codegree_le H V X s (d s) hGround (hCover s hs hsr) S hS
  obtain ⟨H', hH'₀, hAdm', hUniform', hSmall, hFacet, hLoss₀⟩ :=
    regularization_round_from_cover_and_layer_bound H₀ V ∅ r t (d 2) 0 d
      hAdm₀ hUniform₀ hGround₀ hr
      (by
        intro s hs hsr S hS hDisj
        exact hCaps₀ s hs hsr S (Finset.mem_powersetCard.mp hS).2)
      (by simp)
      (by intro S hS; exact hCaps₀ 2 (by omega) (by omega) S hS)
  have hSplit : H.card - H'.card =
      (H.card - H₀.card) + (H₀.card - H'.card) := by
    have := Finset.card_le_card hSub₀
    have := Finset.card_le_card hH'₀
    omega
  simp only [Nat.mul_zero, Nat.zero_add] at hLoss₀
  refine ⟨H', hH'₀.trans hSub₀, hAdm', hUniform', hSmall, hFacet, ?_⟩
  rw [hSplit, Nat.mul_add]
  exact Nat.add_le_add (Nat.mul_le_mul_left _ hLayer) hLoss₀

/-- A complete finite round from actual codegrees and explicit scalar
budgets. In particular, no cover, removed-layer estimate, or facet-energy
estimate is passed in as a geometric hypothesis. -/
theorem regularization_explicit_finite_round
    {n : ℕ} [Inhabited (Fin n)]
    (H : Family (Fin n)) (V : Edge (Fin n))
    (r t h D₁ D₂ D₃ L b : ℕ) (d D a : ℕ → ℕ)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hGround : ∀ E ∈ H, E ⊆ V) (hr : 4 ≤ r)
    (hOffPrefixCap : ∀ s, 1 ≤ s → s ≤ r - 2 →
      ∀ P ∈ V.powersetCard s, ∀ x : Fin n, x ∉ P →
        (H.filter (fun E => P ∪ {x} ⊆ E)).card ≤ D s)
    (hGap : ∀ s, 1 ≤ s → s ≤ r - 2 →
      (V.powersetCard (r - s)).card +
        a s * a s * ((r - s) * D s) < a s * d s)
    (hCoverSize : (∑ s ∈ Finset.Icc 1 (r - 2), s * (a s - 1)) ≤ h)
    (hD₁ : ∀ z : Fin n, (H.filter (fun E => z ∈ E)).card ≤ D₁)
    (hD₂ : ∀ S : Edge (Fin n), S.card = 2 →
      (H.filter (fun E => S ⊆ E)).card ≤ D₂)
    (hD₃ : ∀ S : Edge (Fin n), S.card = 3 →
      (H.filter (fun E => S ⊆ E)).card ≤ D₃)
    (hRadius : (r - 1).factorial * D₁ ≤ L ^ (r - 1))
    (hCollision : n.choose (r - 2) * (h * (h - 1) *
      ((r - 1) * (r - 1) * D₂ + n * (n - 1) * (r - 2) * D₃)) ≤ b ^ 2) :
    ∃ H' : Family (Fin n), H' ⊆ H ∧ Admissible H' ∧ Uniform r H' ∧
      (∀ s, 1 ≤ s → s ≤ r - 2 → ∀ S ∈ V.powersetCard s,
        (H'.filter (fun E => S ⊆ E)).card ≤ d s) ∧
      (∀ A ∈ V.powersetCard (r - 1),
        (H'.filter (fun E => A ⊆ E)).card ≤ t) ∧
      (t - 1) * (H.card - H'.card) ≤
        (t - 1) * (b + ((L + (r - 1)) * n.choose (r - 2)) / (r - 1) +
          h.choose 2 * D₂) + 2 * (V.card.choose 2 * ((r - 1) * d 2)) := by
  obtain ⟨X, hXV, hXcard, hCover⟩ :=
    exists_all_ranks_actual_heavy_root_cover H V r d D a
      hUniform hGround hAdm hr hOffPrefixCap hGap
  have hLayer := removed_layer_bound_from_codegrees H V X r h D₁ D₂ D₃ L b
    hAdm hUniform hGround hr (hXcard.trans hCoverSize)
    hD₁ hD₂ hD₃ hRadius hCollision
  exact regularization_after_cover_improved_energy H V X r t _ d
    hAdm hUniform hGround hr hCover hLayer

end JSP523.Rank5
