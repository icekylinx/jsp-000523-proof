import JSP523.Basic
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite crossing-coloring count for Part I

The all-rank reduction first chooses an `r`-coloring under which many
members use each color exactly once.  Here a crossing member is expressed
as injectivity of its color map.  The count is finite and exact; no
probability theory is used.
-/

namespace JSP523.Coarse

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A coloring is crossing on `E` when different vertices of `E` have
different colors. -/
def CrossingOn (r : ℕ) (κ : α → Fin r) (E : Edge α) : Prop :=
  Set.InjOn κ (↑E : Set α)

/-- Split a coloring into its values on a finite set and on its
complement. -/
def coloringSplitEquiv (E : Edge α) (r : ℕ) :
    (α → Fin r) ≃
      (({x : α // x ∈ E} → Fin r) ×
        ({x : α // x ∉ E} → Fin r)) where
  toFun κ := (fun x => κ x, fun x => κ x)
  invFun fg x := if hx : x ∈ E then fg.1 ⟨x, hx⟩ else fg.2 ⟨x, hx⟩
  left_inv κ := by
    funext x
    by_cases hx : x ∈ E <;> simp [hx]
  right_inv fg := by
    cases fg with
    | mk f g =>
      apply Prod.ext
      · funext x
        simp [x.property]
      · funext x
        simp [x.property]

/-- A crossing coloring amounts to an injection on `E` and an arbitrary
coloring of the complement. -/
def crossingColoringEquiv (E : Edge α) (r : ℕ) :
    {κ : α → Fin r // CrossingOn r κ E} ≃
      (({x : α // x ∈ E} ↪ Fin r) ×
        ({x : α // x ∉ E} → Fin r)) where
  toFun κ :=
    (⟨(coloringSplitEquiv E r κ.1).1, by
      intro x y hxy
      apply Subtype.ext
      exact κ.2 x.property y.property hxy⟩,
      (coloringSplitEquiv E r κ.1).2)
  invFun fg :=
    ⟨(coloringSplitEquiv E r).symm ((fg.1 : _ → Fin r), fg.2), by
      intro x hx y hy hxy
      dsimp [coloringSplitEquiv] at hxy
      change x ∈ E at hx
      change y ∈ E at hy
      simp [hx, hy] at hxy
      exact hxy⟩
  left_inv κ := by
    apply Subtype.ext
    exact (coloringSplitEquiv E r).left_inv κ.1
  right_inv fg := by
    have hright := (coloringSplitEquiv E r).right_inv
      ((fg.1 : {x : α // x ∈ E} → Fin r), fg.2)
    apply Prod.ext
    · apply Function.Embedding.ext
      intro x
      exact congrArg (fun p => p.1 x) hright
    · change ((coloringSplitEquiv E r)
        ((coloringSplitEquiv E r).symm ((fg.1 : _ → Fin r), fg.2))).2 = fg.2
      exact congrArg Prod.snd hright

/-- The finite set of colorings crossing on one edge. -/
noncomputable def crossingColorings (E : Edge α) (r : ℕ) :
    Finset (α → Fin r) := by
  classical
  exact Finset.univ.filter (fun κ => CrossingOn r κ E)

/-- Exact count of colorings injective on a prescribed `r`-edge. -/
theorem crossing_colorings_card
    (E : Edge α) (r : ℕ) (hE : E.card = r) :
    (crossingColorings E r).card =
      r.factorial * r ^ (Fintype.card α - r) := by
  classical
  have hEcard : Fintype.card {x : α // x ∈ E} = r := by
    simpa only [Fintype.card_coe] using hE
  have hCompCard : Fintype.card {x : α // x ∉ E} =
      Fintype.card α - r := by
    rw [Fintype.card_subtype_compl (fun x : α => x ∈ E), hEcard]
  calc
    (crossingColorings E r).card =
        Fintype.card {κ : α → Fin r // CrossingOn r κ E} := by
      simp [crossingColorings, Fintype.card_subtype]
    _ = Fintype.card ({x : α // x ∈ E} ↪ Fin r) *
          Fintype.card ({x : α // x ∉ E} → Fin r) := by
      rw [Fintype.card_congr (crossingColoringEquiv E r),
        Fintype.card_prod]
    _ = r.factorial * r ^ (Fintype.card α - r) := by
      rw [Fintype.card_embedding_eq, Fintype.card_fun,
        hEcard, hCompCard, Fintype.card_fin,
        Nat.descFactorial_self]

/-- Members of `H` that are crossing under one coloring. -/
noncomputable def crossingSubfamily
    (H : Family α) (r : ℕ) (κ : α → Fin r) : Family α := by
  classical
  exact H.filter (fun E => CrossingOn r κ E)

omit [Fintype α] [DecidableEq α] in
theorem crossing_subfamily_subset
    (H : Family α) (r : ℕ) (κ : α → Fin r) :
    crossingSubfamily H r κ ⊆ H := by
  classical
  intro E hE
  exact (Finset.mem_filter.mp hE).1

omit [Fintype α] [DecidableEq α] in
theorem mem_crossing_subfamily_iff
    (H : Family α) (r : ℕ) (κ : α → Fin r) (E : Edge α) :
    E ∈ crossingSubfamily H r κ ↔ E ∈ H ∧ CrossingOn r κ E := by
  classical
  exact Finset.mem_filter

/-- Exact double count of a coloring and one of its crossing edges. -/
theorem sum_crossing_subfamily_card
    (H : Family α) (r : ℕ) :
    (∑ κ : α → Fin r, (crossingSubfamily H r κ).card) =
      ∑ E ∈ H, (crossingColorings E r).card := by
  classical
  calc
    (∑ κ : α → Fin r, (crossingSubfamily H r κ).card) =
        ∑ κ : α → Fin r, ∑ E ∈ H,
          if CrossingOn r κ E then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro κ _
      exact Finset.card_filter (fun E => CrossingOn r κ E) H
    _ = ∑ E ∈ H, ∑ κ : α → Fin r,
          if CrossingOn r κ E then (1 : ℕ) else 0 :=
      Finset.sum_comm
    _ = ∑ E ∈ H, (crossingColorings E r).card := by
      apply Finset.sum_congr rfl
      intro E _
      exact (Finset.card_filter
        (fun κ : α → Fin r => CrossingOn r κ E) Finset.univ).symm

theorem sum_crossing_subfamily_card_uniform
    (H : Family α) (r : ℕ) (hU : Uniform r H) :
    (∑ κ : α → Fin r, (crossingSubfamily H r κ).card) =
      H.card * (r.factorial * r ^ (Fintype.card α - r)) := by
  rw [sum_crossing_subfamily_card]
  calc
    (∑ E ∈ H, (crossingColorings E r).card) =
        ∑ _E ∈ H,
          r.factorial * r ^ (Fintype.card α - r) := by
      apply Finset.sum_congr rfl
      intro E hE
      exact crossing_colorings_card E r (hU hE)
    _ = H.card * (r.factorial * r ^ (Fintype.card α - r)) := by
      simp [mul_comm]

/-- Finite averaging step (I.6).  The ambient size hypothesis follows
automatically when a nonempty `r`-uniform family is present. -/
theorem exists_crossing_subfamily
    (H : Family α) (r : ℕ) (hr : 0 < r)
    (hU : Uniform r H) (hrN : r ≤ Fintype.card α) :
    ∃ κ : α → Fin r,
      r.factorial * H.card ≤
        r ^ r * (crossingSubfamily H r κ).card := by
  classical
  let C : Finset (α → Fin r) := Finset.univ
  have hCcard : C.card = r ^ Fintype.card α := by
    simp [C]
  have hPow : r ^ (Fintype.card α - r) * r ^ r =
      r ^ Fintype.card α := by
    rw [← pow_add, Nat.sub_add_cancel hrN]
  have hDouble := sum_crossing_subfamily_card_uniform H r hU
  have hScaled :
      (∑ κ ∈ C, r ^ r * (crossingSubfamily H r κ).card) =
        ∑ _κ ∈ C, r.factorial * H.card := by
    calc
      (∑ κ ∈ C, r ^ r * (crossingSubfamily H r κ).card) =
          r ^ r * (∑ κ ∈ C, (crossingSubfamily H r κ).card) := by
        rw [Finset.mul_sum]
      _ = r ^ r * (H.card *
            (r.factorial * r ^ (Fintype.card α - r))) := by
        simpa only [C] using congrArg (r ^ r * ·) hDouble
      _ = H.card * r.factorial *
            (r ^ (Fintype.card α - r) * r ^ r) := by ac_rfl
      _ = C.card * (r.factorial * H.card) := by
        rw [hPow, hCcard]
        ac_rfl
      _ = ∑ _κ ∈ C, r.factorial * H.card := by simp
  by_contra hnone
  have hStrict : ∀ κ ∈ C,
      r ^ r * (crossingSubfamily H r κ).card <
        r.factorial * H.card := by
    intro κ _
    exact Nat.lt_of_not_ge (fun h => hnone ⟨κ, h⟩)
  have hCnon : C.Nonempty :=
    ⟨fun _ => (⟨0, hr⟩ : Fin r), Finset.mem_univ _⟩
  have hSumStrict := Finset.sum_lt_sum_of_nonempty hCnon hStrict
  exact (Nat.lt_irrefl _) (hScaled ▸ hSumStrict)

/-- Equation (I.6) without an ambient-size side condition. -/
theorem exists_crossing_subfamily_uniform
    (H : Family α) (r : ℕ) (hr : 0 < r)
    (hU : Uniform r H) :
    ∃ κ : α → Fin r,
      r.factorial * H.card ≤
        r ^ r * (crossingSubfamily H r κ).card := by
  by_cases hH : H.Nonempty
  · obtain ⟨E, hEH⟩ := hH
    have hrN : r ≤ Fintype.card α := by
      rw [← hU hEH]
      exact (Finset.card_le_card (Finset.subset_univ E)).trans_eq
        (Finset.card_univ)
    exact exists_crossing_subfamily H r hr hU hrN
  · let κ : α → Fin r := fun _ => ⟨0, hr⟩
    refine ⟨κ, ?_⟩
    have hEmpty : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hH
    simp [hEmpty]

/-- A crossing `r`-edge is canonically in bijection with the `r` colors. -/
noncomputable def edgeColorEquiv
    (E : Edge α) (r : ℕ) (κ : α → Fin r)
    (hcard : E.card = r) (hcross : CrossingOn r κ E) :
    ↥E ≃ Fin r :=
  Equiv.ofBijective (fun x : ↥E => κ x) <| by
    apply (Fintype.bijective_iff_injective_and_card _).2
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact hcross x.property y.property hxy
    · simp [Fintype.card_coe, hcard]

/-- The unique member of a crossing edge with color `i`. -/
noncomputable def vertexAtColor
    (E : Edge α) (r : ℕ) (κ : α → Fin r)
    (hcard : E.card = r) (hcross : CrossingOn r κ E)
    (i : Fin r) : α :=
  (edgeColorEquiv E r κ hcard hcross).symm i

omit [Fintype α] [DecidableEq α] in
theorem vertex_at_color_mem
    (E : Edge α) (r : ℕ) (κ : α → Fin r)
    (hcard : E.card = r) (hcross : CrossingOn r κ E)
    (i : Fin r) :
    vertexAtColor E r κ hcard hcross i ∈ E :=
  (edgeColorEquiv E r κ hcard hcross).symm i |>.property

omit [Fintype α] [DecidableEq α] in
theorem color_vertex_at_color
    (E : Edge α) (r : ℕ) (κ : α → Fin r)
    (hcard : E.card = r) (hcross : CrossingOn r κ E)
    (i : Fin r) :
    κ (vertexAtColor E r κ hcard hcross i) = i := by
  exact (edgeColorEquiv E r κ hcard hcross).apply_symm_apply i

omit [Fintype α] [DecidableEq α] in
theorem vertex_at_color_injective
    (E : Edge α) (r : ℕ) (κ : α → Fin r)
    (hcard : E.card = r) (hcross : CrossingOn r κ E) :
    Function.Injective (vertexAtColor E r κ hcard hcross) := by
  intro i j hij
  have hcolor := congrArg κ hij
  simpa only [color_vertex_at_color] using hcolor

omit [Fintype α] [DecidableEq α] in
theorem mem_edge_iff_exists_vertex_at_color
    (E : Edge α) (r : ℕ) (κ : α → Fin r)
    (hcard : E.card = r) (hcross : CrossingOn r κ E)
    (x : α) :
    x ∈ E ↔ ∃ i : Fin r, vertexAtColor E r κ hcard hcross i = x := by
  constructor
  · intro hx
    refine ⟨κ x, ?_⟩
    exact congrArg Subtype.val
      ((edgeColorEquiv E r κ hcard hcross).symm_apply_apply ⟨x, hx⟩)
  · rintro ⟨i, rfl⟩
    exact vertex_at_color_mem E r κ hcard hcross i

end JSP523.Coarse
