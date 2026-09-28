import JSP523.Coarse.AlignmentCoordinates
import JSP523.Coarse.BlockContraction
import JSP523.Coarse.TripartiteColors

/-!
# Contracting one aligned difference fiber

For a fixed coordinate-difference vector, every crossing edge has a
prefix block indexed by its color-zero coordinate.  We contract that
block to a tagged vertex and retain the two last-color vertices.
This is the deterministic counterpart of the aligned-edge
representation in the manuscript's proof of (I.7).
-/

namespace JSP523.Coarse

open Finset

variable {α β : Type*} [Fintype α] [DecidableEq α]
  [AddCommGroup β] [Fintype β] [DecidableEq β]

noncomputable def differenceFiber
    (F : Family α) (s : ℕ) (κ : α → Fin (s + 3))
    (hU : Uniform (s + 3) F)
    (hC : ∀ E ∈ F, CrossingOn (s + 3) κ E)
    (e : α ≃ β) (δ : Fin s → β) : Finset ↥F := by
  classical
  exact F.attach.filter fun E =>
    familyDifference F s κ hU hC e E = δ

omit [Fintype α] [DecidableEq α] [Fintype β] in
theorem mem_differenceFiber_iff
    (F : Family α) (s : ℕ) (κ : α → Fin (s + 3))
    (hU : Uniform (s + 3) F)
    (hC : ∀ E ∈ F, CrossingOn (s + 3) κ E)
    (e : α ≃ β) (δ : Fin s → β) (E : ↥F) :
    E ∈ differenceFiber F s κ hU hC e δ ↔
      familyDifference F s κ hU hC e E = δ := by
  simp [differenceFiber]

noncomputable def contractTriple
    (F : Family α) (s : ℕ) (κ : α → Fin (s + 3))
    (hU : Uniform (s + 3) F)
    (hC : ∀ E ∈ F, CrossingOn (s + 3) κ E)
    (e : α ≃ β) (E : ↥F) : Edge (β ⊕ α) :=
  {Sum.inl (familyAnchor F s κ hU hC e E),
    Sum.inr (familyVertex F s κ hU hC E (lastColor₁ s)),
    Sum.inr (familyVertex F s κ hU hC E (lastColor₂ s))}

noncomputable def contractedFamily
    (F : Family α) (s : ℕ) (κ : α → Fin (s + 3))
    (hU : Uniform (s + 3) F)
    (hC : ∀ E ∈ F, CrossingOn (s + 3) κ E)
    (e : α ≃ β) (δ : Fin s → β) : Family (β ⊕ α) := by
  classical
  exact (differenceFiber F s κ hU hC e δ).image
    (contractTriple F s κ hU hC e)

omit [Fintype β] in
theorem expand_contractTriple
    (F : Family α) (s : ℕ) (κ : α → Fin (s + 3))
    (hU : Uniform (s + 3) F)
    (hC : ∀ E ∈ F, CrossingOn (s + 3) κ E)
    (e : α ≃ β) (δ : Fin s → β) (E : ↥F)
    (hδ : familyDifference F s κ hU hC e E = δ) :
    expandBlock (prefixBlock s κ e δ)
      (contractTriple F s κ hU hC e E) = E.1 := by
  rw [← hδ]
  simpa [expandBlock, contractTriple] using
    family_edge_reconstruct F s κ hU hC e E


omit [Fintype α] [AddCommGroup β] [Fintype β] in
theorem contractTriple_anchor_mem
    (F : Family α) (s : ℕ) (κ : α → Fin (s + 3))
    (hU : Uniform (s + 3) F)
    (hC : ∀ E ∈ F, CrossingOn (s + 3) κ E)
    (e : α ≃ β) (E : ↥F) :
    Sum.inl (familyAnchor F s κ hU hC e E) ∈
      contractTriple F s κ hU hC e E := by
  simp [contractTriple]

omit [Fintype α] [AddCommGroup β] [Fintype β] in
theorem contractTriple_last₁_mem
    (F : Family α) (s : ℕ) (κ : α → Fin (s + 3))
    (hU : Uniform (s + 3) F)
    (hC : ∀ E ∈ F, CrossingOn (s + 3) κ E)
    (e : α ≃ β) (E : ↥F) :
    Sum.inr (familyVertex F s κ hU hC E (lastColor₁ s)) ∈
      contractTriple F s κ hU hC e E := by
  simp [contractTriple]

omit [Fintype α] [AddCommGroup β] [Fintype β] in
theorem contractTriple_last₂_mem
    (F : Family α) (s : ℕ) (κ : α → Fin (s + 3))
    (hU : Uniform (s + 3) F)
    (hC : ∀ E ∈ F, CrossingOn (s + 3) κ E)
    (e : α ≃ β) (E : ↥F) :
    Sum.inr (familyVertex F s κ hU hC E (lastColor₂ s)) ∈
      contractTriple F s κ hU hC e E := by
  simp [contractTriple]

omit [Fintype α] [Fintype β] in
theorem family_disjoint_of_contract_disjoint
    (F : Family α) (s : ℕ) (κ : α → Fin (s + 3))
    (hU : Uniform (s + 3) F)
    (hC : ∀ E ∈ F, CrossingOn (s + 3) κ E)
    (e : α ≃ β) (δ : Fin s → β)
    (E K : ↥F)
    (hEδ : familyDifference F s κ hU hC e E = δ)
    (hKδ : familyDifference F s κ hU hC e K = δ)
    (hdisj : Disjoint
      (contractTriple F s κ hU hC e E)
      (contractTriple F s κ hU hC e K)) :
    Disjoint E.1 K.1 := by
  apply Finset.disjoint_left.mpr
  intro v hvE hvK
  rcases color_eq_prefix_or_last s (κ v) with ⟨i, hi⟩ | hi | hi
  · have hEv : familyVertex F s κ hU hC E (prefixColor s i) = v := by
      rw [← hi]
      exact familyVertex_surjective_on_edge F s κ hU hC E v hvE
    have hKv : familyVertex F s κ hU hC K (prefixColor s i) = v := by
      rw [← hi]
      exact familyVertex_surjective_on_edge F s κ hU hC K v hvK
    have hcE : e v = familyAnchor F s κ hU hC e E +
        prefixOffset δ i := by
      rw [← hEv, ← hEδ]
      exact familyVertex_prefix_coordinate F s κ hU hC e E i
    have hcK : e v = familyAnchor F s κ hU hC e K +
        prefixOffset δ i := by
      rw [← hKv, ← hKδ]
      exact familyVertex_prefix_coordinate F s κ hU hC e K i
    have hAnchor : familyAnchor F s κ hU hC e E =
        familyAnchor F s κ hU hC e K :=
      add_right_cancel (hcE.symm.trans hcK)
    exact (Finset.disjoint_left.mp hdisj)
      (contractTriple_anchor_mem F s κ hU hC e E)
      (hAnchor ▸ contractTriple_anchor_mem F s κ hU hC e K)
  · have hEv : familyVertex F s κ hU hC E (lastColor₁ s) = v := by
      rw [← hi]
      exact familyVertex_surjective_on_edge F s κ hU hC E v hvE
    have hKv : familyVertex F s κ hU hC K (lastColor₁ s) = v := by
      rw [← hi]
      exact familyVertex_surjective_on_edge F s κ hU hC K v hvK
    exact (Finset.disjoint_left.mp hdisj)
      (hEv ▸ contractTriple_last₁_mem F s κ hU hC e E)
      (hKv ▸ contractTriple_last₁_mem F s κ hU hC e K)
  · have hEv : familyVertex F s κ hU hC E (lastColor₂ s) = v := by
      rw [← hi]
      exact familyVertex_surjective_on_edge F s κ hU hC E v hvE
    have hKv : familyVertex F s κ hU hC K (lastColor₂ s) = v := by
      rw [← hi]
      exact familyVertex_surjective_on_edge F s κ hU hC K v hvK
    exact (Finset.disjoint_left.mp hdisj)
      (hEv ▸ contractTriple_last₂_mem F s κ hU hC e E)
      (hKv ▸ contractTriple_last₂_mem F s κ hU hC e K)



omit [Fintype β] in
theorem contractTriple_inj_on_fiber
    (F : Family α) (s : ℕ) (κ : α → Fin (s + 3))
    (hU : Uniform (s + 3) F)
    (hC : ∀ E ∈ F, CrossingOn (s + 3) κ E)
    (e : α ≃ β) (δ : Fin s → β)
    (E K : ↥F)
    (hE : E ∈ differenceFiber F s κ hU hC e δ)
    (hK : K ∈ differenceFiber F s κ hU hC e δ)
    (heq : contractTriple F s κ hU hC e E =
      contractTriple F s κ hU hC e K) : E = K := by
  apply Subtype.ext
  have h := congrArg (expandBlock (prefixBlock s κ e δ)) heq
  rw [expand_contractTriple F s κ hU hC e δ E
      ((mem_differenceFiber_iff ..).mp hE),
    expand_contractTriple F s κ hU hC e δ K
      ((mem_differenceFiber_iff ..).mp hK)] at h
  exact h

omit [Fintype β] in
theorem contractedFamily_card_eq_fiber
    (F : Family α) (s : ℕ) (κ : α → Fin (s + 3))
    (hU : Uniform (s + 3) F)
    (hC : ∀ E ∈ F, CrossingOn (s + 3) κ E)
    (e : α ≃ β) (δ : Fin s → β) :
    (contractedFamily F s κ hU hC e δ).card =
      (differenceFiber F s κ hU hC e δ).card := by
  classical
  exact Finset.card_image_of_injOn (fun E hE K hK heq =>
    contractTriple_inj_on_fiber F s κ hU hC e δ E K hE hK heq)

omit [Fintype β] in
theorem contractedFamily_admissible
    (F : Family α) (s : ℕ) (κ : α → Fin (s + 3))
    (hU : Uniform (s + 3) F)
    (hC : ∀ E ∈ F, CrossingOn (s + 3) κ E)
    (hAdm : Admissible F)
    (e : α ≃ β) (δ : Fin s → β) :
    Admissible (contractedFamily F s κ hU hC e δ) := by
  let B : β → Edge α := prefixBlock s κ e δ
  apply admissible_of_expandBlock B
    (contractedFamily F s κ hU hC e δ) F hAdm
  · intro S hS
    obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hS
    exact (expand_contractTriple F s κ hU hC e δ E
      ((mem_differenceFiber_iff ..).mp hE)) ▸ E.property
  · intro S hS U hU' heq
    obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp hU'
    have heq' : E.1 = K.1 := by
      simpa only [B,
        expand_contractTriple F s κ hU hC e δ E
          ((mem_differenceFiber_iff ..).mp hE),
        expand_contractTriple F s κ hU hC e δ K
          ((mem_differenceFiber_iff ..).mp hK)] using heq
    exact congrArg (contractTriple F s κ hU hC e)
      (Subtype.ext heq')
  · intro S hS U hU' hdisj
    obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp hU'
    rw [show B = prefixBlock s κ e δ from rfl,
      expand_contractTriple F s κ hU hC e δ E
        ((mem_differenceFiber_iff ..).mp hE),
      expand_contractTriple F s κ hU hC e δ K
        ((mem_differenceFiber_iff ..).mp hK)]
    exact family_disjoint_of_contract_disjoint F s κ hU hC e δ
      E K ((mem_differenceFiber_iff ..).mp hE)
      ((mem_differenceFiber_iff ..).mp hK) hdisj



def contractedColor (s : ℕ) (κ : α → Fin (s + 3)) :
    β ⊕ α → Fin 3
  | Sum.inl _ => 0
  | Sum.inr v => if κ v = lastColor₁ s then 1 else 2

omit [Fintype α] [AddCommGroup β] [Fintype β] in
theorem contractTriple_rainbow
    (F : Family α) (s : ℕ) (κ : α → Fin (s + 3))
    (hU : Uniform (s + 3) F)
    (hC : ∀ E ∈ F, CrossingOn (s + 3) κ E)
    (e : α ≃ β) (E : ↥F) :
    (contractTriple F s κ hU hC e E).card = 3 ∧
      ∀ x ∈ contractTriple F s κ hU hC e E,
        ∀ y ∈ contractTriple F s κ hU hC e E,
          x ≠ y → contractedColor s κ x ≠ contractedColor s κ y := by
  let a : β ⊕ α := Sum.inl (familyAnchor F s κ hU hC e E)
  let b : β ⊕ α := Sum.inr (familyVertex F s κ hU hC E (lastColor₁ s))
  let c : β ⊕ α := Sum.inr (familyVertex F s κ hU hC E (lastColor₂ s))
  have hbc : b ≠ c := by
    intro h
    have hv : familyVertex F s κ hU hC E (lastColor₁ s) =
        familyVertex F s κ hU hC E (lastColor₂ s) :=
      Sum.inr_injective h
    have hc := congrArg κ hv
    exact lastColor₁_ne_lastColor₂ s (by
      simpa only [familyVertex_color F s κ hU hC E (lastColor₁ s),
        familyVertex_color F s κ hU hC E (lastColor₂ s)] using hc)
  have hcolorA : contractedColor s κ a = 0 := rfl
  have hcolorB : contractedColor s κ b = 1 := by
    simp [b, contractedColor, familyVertex_color]
  have hcolorC : contractedColor s κ c = 2 := by
    simp [c, contractedColor, familyVertex_color,
      (lastColor₁_ne_lastColor₂ s).symm]
  have hcard : ({a, b, c} : Edge (β ⊕ α)).card = 3 := by
    apply Finset.card_triple_eq_three_iff.mpr
    exact ⟨by simp [a, b], by simp [a, c], hbc⟩
  constructor
  · simpa only [contractTriple, a, b, c] using hcard
  · intro x hx y hy hxy
    change x ∈ ({a, b, c} : Edge (β ⊕ α)) at hx
    change y ∈ ({a, b, c} : Edge (β ⊕ α)) at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl <;>
      simp_all

omit [Fintype α] [Fintype β] in
theorem contractedFamily_rainbow
    (F : Family α) (s : ℕ) (κ : α → Fin (s + 3))
    (hU : Uniform (s + 3) F)
    (hC : ∀ E ∈ F, CrossingOn (s + 3) κ E)
    (e : α ≃ β) (δ : Fin s → β) :
    RainbowTripleSystem
      (contractedFamily F s κ hU hC e δ)
      (contractedColor s κ) := by
  intro S hS
  obtain ⟨E, _, rfl⟩ := Finset.mem_image.mp hS
  exact contractTriple_rainbow F s κ hU hC e E



omit [AddCommGroup β] in
theorem contractedColor_class_card_le
    (s : ℕ) (κ : α → Fin (s + 3)) (e : α ≃ β)
    (i : Fin 3) :
    (colorClass (contractedColor (β := β) s κ) i).card ≤ Fintype.card α := by
  classical
  by_cases hi : i = 0
  · subst i
    have hsub : colorClass (contractedColor (β := β) s κ) 0 ⊆
        (Finset.univ : Finset β).image (Sum.inl : β → β ⊕ α) := by
      intro v hv
      cases v with
      | inl j => simp
      | inr x =>
          have hc := (Finset.mem_filter.mp hv).2
          by_cases h : κ x = lastColor₁ s
          · simp [contractedColor, h] at hc
          · simp [contractedColor, h] at hc
    calc
      (colorClass (contractedColor (β := β) s κ) 0).card ≤
          ((Finset.univ : Finset β).image
            (Sum.inl : β → β ⊕ α)).card :=
        Finset.card_le_card hsub
      _ ≤ Fintype.card β := by
        simpa using (Finset.card_image_le :
          ((Finset.univ : Finset β).image
            (Sum.inl : β → β ⊕ α)).card ≤
              (Finset.univ : Finset β).card)
      _ = Fintype.card α := (Fintype.card_congr e).symm
  · have hsub : colorClass (contractedColor (β := β) s κ) i ⊆
        (Finset.univ : Finset α).image (Sum.inr : α → β ⊕ α) := by
      intro v hv
      cases v with
      | inl j =>
          have hc := (Finset.mem_filter.mp hv).2
          exact False.elim (hi (by
            simpa [contractedColor] using hc.symm))
      | inr x => simp
    calc
      (colorClass (contractedColor (β := β) s κ) i).card ≤
          ((Finset.univ : Finset α).image
            (Sum.inr : α → β ⊕ α)).card :=
        Finset.card_le_card hsub
      _ ≤ Fintype.card α := by
        simpa using (Finset.card_image_le :
          ((Finset.univ : Finset α).image
            (Sum.inr : α → β ⊕ α)).card ≤
              (Finset.univ : Finset α).card)

/-- The manuscript's aligned-edge estimate for one deterministic
coordinate-difference fiber. -/
theorem differenceFiber_card_le_three_square
    (F : Family α) (s : ℕ) (κ : α → Fin (s + 3))
    (hU : Uniform (s + 3) F)
    (hC : ∀ E ∈ F, CrossingOn (s + 3) κ E)
    (hAdm : Admissible F)
    (e : α ≃ β) (δ : Fin s → β) :
    (differenceFiber F s κ hU hC e δ).card ≤
      3 * (Fintype.card α) ^ 2 := by
  rw [← contractedFamily_card_eq_fiber F s κ hU hC e δ]
  exact rainbow_triple_card_le_three_square
    (contractedFamily_admissible F s κ hU hC hAdm e δ)
    (contractedFamily_rainbow F s κ hU hC e δ)
    (Fintype.card α)
    (contractedColor_class_card_le s κ e)



/-- Sum over all coordinate-difference fibers.  This is (I.7) in
the deterministic partition model. -/
theorem crossing_family_card_le_three_power
    (F : Family α) (s : ℕ) (κ : α → Fin (s + 3))
    (hU : Uniform (s + 3) F)
    (hC : ∀ E ∈ F, CrossingOn (s + 3) κ E)
    (hAdm : Admissible F)
    (e : α ≃ β) :
    F.card ≤ 3 * (Fintype.card α) ^ (s + 2) := by
  classical
  have hsum : F.card =
      ∑ δ : Fin s → β, (differenceFiber F s κ hU hC e δ).card := by
    rw [← Finset.card_attach]
    simpa only [differenceFiber] using
      (Finset.card_eq_sum_card_fiberwise
        (s := F.attach)
        (t := (Finset.univ : Finset (Fin s → β)))
        (f := familyDifference F s κ hU hC e)
        (fun E _ => Finset.mem_univ _))
  have hcount : Fintype.card (Fin s → β) =
      (Fintype.card α) ^ s := by
    rw [Fintype.card_fun]
    simpa only [Fintype.card_fin] using
      congrArg (fun n : ℕ => n ^ s) (Fintype.card_congr e).symm
  calc
    F.card = ∑ δ : Fin s → β,
        (differenceFiber F s κ hU hC e δ).card := hsum
    _ ≤ ∑ _δ : Fin s → β,
        3 * (Fintype.card α) ^ 2 := by
      apply Finset.sum_le_sum
      intro δ _
      exact differenceFiber_card_le_three_square F s κ hU hC hAdm e δ
    _ = (Fintype.card α) ^ s *
        (3 * (Fintype.card α) ^ 2) := by
      simp [hcount, mul_comm]
    _ = 3 * (Fintype.card α) ^ (s + 2) := by
      rw [pow_add]
      ac_rfl


end JSP523.Coarse
