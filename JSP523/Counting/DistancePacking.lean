import JSP523.Basic
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Distance packing for uniform finite families

This is Lemma IV.1.2 of `paper/proof.pdf`, §IV.1.
The proof counts small subsets inside each member.  Distinct members
cannot contain the same small subset under the stated distance condition.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

/-- If the required difference is larger than the size of a member, the
family contains at most one member. -/
theorem distance_packing_at_most_one
    {_W : Edge α} {T : Family α} {t d : ℕ}
    (hU : Uniform t T)
    (hDistance : ∀ ⦃A B : Edge α⦄, A ∈ T → B ∈ T →
      A ≠ B → d ≤ (A \ B).card)
    (htd : t < d) : T.card ≤ 1 := by
  by_contra hNot
  obtain ⟨A, hA, B, hB, hAB⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < T.card)
  have hBound : (A \ B).card ≤ A.card :=
    Finset.card_le_card Finset.sdiff_subset
  have hD := hDistance hA hB hAB
  have hCard := hU hA
  omega

/-- Lemma IV.1.2: with `d ≤ t`, no two members share a
`(t-d+1)`-subset.  The displayed inequality is the resulting exact
double count. -/
theorem distance_packing_choose_bound
    {W : Edge α} {T : Family α} {t d : ℕ}
    (hW : ∀ A ∈ T, A ⊆ W)
    (hU : Uniform t T)
    (hDistance : ∀ ⦃A B : Edge α⦄, A ∈ T → B ∈ T →
      A ≠ B → d ≤ (A \ B).card)
    (hdt : d ≤ t) :
    T.card * t.choose (t - d + 1) ≤
      W.card.choose (t - d + 1) := by
  classical
  let k := t - d + 1
  let I : Finset (Σ _A : Edge α, Edge α) :=
    T.sigma (fun A => A.powersetCard k)
  let f : (Σ _A : Edge α, Edge α) → Edge α := fun p => p.2
  have hMap : ∀ p ∈ I, f p ∈ W.powersetCard k := by
    intro ⟨A, S⟩ hp
    obtain ⟨hA, hS⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hSA, hScard⟩ := Finset.mem_powersetCard.mp hS
    exact Finset.mem_powersetCard.mpr
      ⟨hSA.trans (hW A hA), hScard⟩
  have hUnique (A B S : Edge α)
      (hA : A ∈ T) (hB : B ∈ T)
      (hSA : S ∈ A.powersetCard k)
      (hSB : S ∈ B.powersetCard k) : A = B := by
    by_contra hAB
    have hSsubA := (Finset.mem_powersetCard.mp hSA).1
    have hSsubB := (Finset.mem_powersetCard.mp hSB).1
    have hSsub : S ⊆ A ∩ B :=
      Finset.subset_inter hSsubA hSsubB
    have hScard := (Finset.mem_powersetCard.mp hSA).2
    have hInterBound := Finset.card_le_card hSsub
    have hDiff := Finset.card_sdiff_add_card_inter A B
    have hAcard := hU hA
    have hDist := hDistance hA hB hAB
    have hk : k + d = t + 1 := by
      dsimp [k]
      omega
    omega
  have hInj : Set.InjOn f (↑I : Set (Σ _A : Edge α, Edge α)) := by
    intro ⟨A, S⟩ hp ⟨B, R⟩ hq hEq
    obtain ⟨hA, hS⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hB, hR⟩ := Finset.mem_sigma.mp hq
    have hSR : S = R := hEq
    subst R
    have hAB := hUnique A B S hA hB hS hR
    subst B
    rfl
  have hCount : I.card ≤ (W.powersetCard k).card :=
    Finset.card_le_card_of_injOn f hMap hInj
  have hIcard : I.card = T.card * t.choose k := by
    rw [Finset.card_sigma]
    simp_rw [Finset.card_powersetCard]
    have hTerms : (∑ A ∈ T, A.card.choose k) = ∑ _A ∈ T, t.choose k := by
      apply Finset.sum_congr rfl
      intro A hA
      rw [hU hA]
    rw [hTerms]
    simp [Finset.sum_const]
  rw [hIcard, Finset.card_powersetCard] at hCount
  simpa only [k] using hCount

end JSP523
