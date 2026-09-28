import JSP523.Rank5.HeavyRootActual
import Mathlib.Order.Interval.Finset.Nat

/-!
# All-ranks heavy-root cover for IV.4

For each root size, filter the actual ambient powerset by the actual
codegree threshold.  The rankwise common-prefix theorem gives a small cover;
their finite union is one cover working for every root size.
-/

namespace JSP523.Rank5

open JSP523

variable {α : Type*} [DecidableEq α]

/-- Assemble the rankwise IV.4 covers into the one cover set used by
`regularization_round_from_cover_and_layer_bound`.  All numerical gaps,
off-prefix codegree caps, and heavy-root tail fibers are explicit.
-/
theorem exists_all_ranks_actual_heavy_root_cover
    (H : Family α) (V : Edge α) (r : ℕ)
    (d D a : ℕ → ℕ)
    (hUniform : Uniform r H)
    (hGround : ∀ E ∈ H, E ⊆ V)
    (hAdm : Admissible H)
    (hr : 4 ≤ r)
    (hOffPrefixCap : ∀ s, 1 ≤ s → s ≤ r - 2 →
      ∀ P ∈ V.powersetCard s, ∀ x : α, x ∉ P →
        (H.filter fun E => P ∪ {x} ⊆ E).card ≤ D s)
    (hGap : ∀ s, 1 ≤ s → s ≤ r - 2 →
      (V.powersetCard (r - s)).card +
        a s * a s * ((r - s) * D s) < a s * d s) :
    ∃ X : Edge α, X ⊆ V ∧
      X.card ≤ ∑ s ∈ Finset.Icc 1 (r - 2), s * (a s - 1) ∧
      (∀ s, 1 ≤ s → s ≤ r - 2 →
        ∀ S ∈ V.powersetCard s, Disjoint S X →
          (H.filter fun E => S ⊆ E).card ≤ d s) := by
  classical
  let I := Finset.Icc 1 (r - 2)
  let heavy : ℕ → Family α := fun s =>
    (V.powersetCard s).filter fun P =>
      d s < (H.filter fun E => P ⊆ E).card
  have rankCover : ∀ s, s ∈ I →
      ∃ Xs : Edge α, Xs ⊆ V ∧
        Xs.card ≤ s * (a s - 1) ∧
        (∀ S ∈ V.powersetCard s, Disjoint S Xs →
          (H.filter fun E => S ⊆ E).card ≤ d s) := by
    intro s hsI
    have hs : 1 ≤ s := (Finset.mem_Icc.mp hsI).1
    have hsr : s ≤ r - 2 := (Finset.mem_Icc.mp hsI).2
    have hst : s + (r - s) = r := by omega
    have ht : 1 ≤ r - s := by omega
    let R := heavy s
    have hRsize : ∀ P ∈ R, P.card = s := by
      intro P hP
      have hmem := (Finset.mem_filter.mp hP).1
      exact (Finset.mem_powersetCard.mp hmem).2
    have hRinside : ∀ P ∈ R, P ⊆ V := by
      intro P hP
      exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hP).1).1
    have hRheavy : ∀ P ∈ R,
        d s < (H.filter fun E => P ⊆ E).card := by
      intro P hP
      exact (Finset.mem_filter.mp hP).2
    have hComplete : ∀ S ∈ V.powersetCard s,
        d s < (H.filter fun E => S ⊆ E).card → S ∈ R := by
      intro S hS hD
      exact Finset.mem_filter.mpr ⟨hS, hD⟩
    have hDegreeCap : ∀ P ∈ R, ∀ x : α, x ∉ P →
        (H.filter fun E => P ∪ {x} ⊆ E).card ≤ D s := by
      intro P hP x hx
      exact hOffPrefixCap s hs hsr P
        ((Finset.mem_filter.mp hP).1) x hx
    obtain ⟨Xs, hXsV, _hXsCover, hXsCard, hXsCap⟩ :=
      actual_common_prefix_cover_degree_cap H V R r s (r - s)
        (d s) (D s) (a s) hAdm
        hUniform hGround hst hs ht hRinside hRsize hRheavy hComplete
        hDegreeCap (hGap s hs hsr)
    exact ⟨Xs, hXsV, hXsCard, hXsCap⟩
  let Xs : ℕ → Edge α := fun s =>
    if hs : s ∈ I then Classical.choose (rankCover s hs) else ∅
  have hXs : ∀ s, s ∈ I → Xs s ⊆ V ∧
      (Xs s).card ≤ s * (a s - 1) ∧
      (∀ S ∈ V.powersetCard s, Disjoint S (Xs s) →
        (H.filter fun E => S ⊆ E).card ≤ d s) := by
    intro s hsI
    dsimp [Xs]
    rw [dite_eq_left hsI]
    exact Classical.choose_spec (rankCover s hsI)
  let X : Edge α := I.biUnion Xs
  have hXsub : X ⊆ V := by
    intro x hx
    obtain ⟨s, hsI, hxS⟩ := Finset.mem_biUnion.mp hx
    exact hXs s hsI |>.1 hxS
  have hXcard : X.card ≤ ∑ s ∈ I, s * (a s - 1) := by
    calc
      X.card ≤ ∑ s ∈ I, (Xs s).card := by
        dsimp [X]
        exact Finset.card_biUnion_le
      _ ≤ ∑ s ∈ I, s * (a s - 1) := by
        apply Finset.sum_le_sum
        intro s hsI
        exact (hXs s hsI).2.1
  have hXcap : ∀ s, 1 ≤ s → s ≤ r - 2 →
      ∀ S ∈ V.powersetCard s, Disjoint S X →
        (H.filter fun E => S ⊆ E).card ≤ d s := by
    intro s hs hsr S hS hSX
    have hsI : s ∈ I := Finset.mem_Icc.mpr ⟨hs, hsr⟩
    have hSXs : Disjoint S (Xs s) := by
      apply Finset.disjoint_left.mpr
      intro x hxS hxXs
      apply (Finset.disjoint_left.mp hSX) hxS
      exact Finset.mem_biUnion.mpr ⟨s, hsI, hxXs⟩
    exact (hXs s hsI).2.2 S hS hSXs
  exact ⟨X, hXsub, hXcard, hXcap⟩

end JSP523.Rank5
