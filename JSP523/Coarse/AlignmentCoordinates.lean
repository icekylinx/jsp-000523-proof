import JSP523.Coarse.Coloring
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Abel

/-!
# Cyclic-coordinate alignment for Part I (§I.1 of
`paper/proof.pdf`)

The manuscript averages independent bijections of the first `r-2` color
classes with an `n`-element index set.  With `r = s+3`, there are `s+1`
prefix classes.  Their `s` differences from the first coordinate form a
deterministic partition of the crossing family: each edge has one unique
difference vector, and each fixed vector has disjoint prefix blocks indexed
by the finite group of size `n`.  Thus there are `n^s` fibers, each bounded
by `3 n²` by the tripartite lemma.  This gives `3 n^(s+2) = 3 n^(r-1)`,
the same exponent and constant as the manuscript's `n^-(r-3)` alignment
probability followed by its `3 n²` bound.  The Lean proof formalizes this
partition argument, not the average over all padded-class bijections.
-/

namespace JSP523.Coarse

open Finset

variable {α β : Type*} [Fintype α] [DecidableEq α]
  [AddCommGroup β] [Fintype β] [DecidableEq β]

def prefixColor (s : ℕ) (i : Fin (s + 1)) : Fin (s + 3) :=
  ⟨i.val, by omega⟩

def lastColor₁ (s : ℕ) : Fin (s + 3) := ⟨s + 1, by omega⟩
def lastColor₂ (s : ℕ) : Fin (s + 3) := ⟨s + 2, by omega⟩

theorem prefixColor_injective (s : ℕ) :
    Function.Injective (prefixColor s) := by
  intro i j h
  exact Fin.ext (by simpa [prefixColor] using congrArg Fin.val h)

theorem prefixColor_ne_last₁ (s : ℕ) (i : Fin (s + 1)) :
    prefixColor s i ≠ lastColor₁ s := by
  intro h
  have := congrArg Fin.val h
  simp only [prefixColor, lastColor₁] at this
  omega

theorem prefixColor_ne_last₂ (s : ℕ) (i : Fin (s + 1)) :
    prefixColor s i ≠ lastColor₂ s := by
  intro h
  have := congrArg Fin.val h
  simp only [prefixColor, lastColor₂] at this
  omega

theorem lastColor₁_ne_lastColor₂ (s : ℕ) :
    lastColor₁ s ≠ lastColor₂ s := by
  intro h
  have := congrArg Fin.val h
  simp only [lastColor₁, lastColor₂] at this
  omega

theorem color_eq_prefix_or_last (s : ℕ) (i : Fin (s + 3)) :
    (∃ j : Fin (s + 1), i = prefixColor s j) ∨
      i = lastColor₁ s ∨ i = lastColor₂ s := by
  by_cases hi : i.val < s + 1
  · left
    exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
  · right
    have hi' := i.isLt
    by_cases h : i.val = s + 1
    · exact Or.inl (Fin.ext (by simpa [lastColor₁] using h))
    · exact Or.inr (Fin.ext (by simp only [lastColor₂]; omega))

noncomputable def familyVertex
    (F : Family α) (s : ℕ) (κ : α → Fin (s + 3))
    (hU : Uniform (s + 3) F)
    (hC : ∀ E ∈ F, CrossingOn (s + 3) κ E)
    (E : ↥F) (i : Fin (s + 3)) : α :=
  vertexAtColor E.1 (s + 3) κ (hU E.2) (hC E.1 E.2) i

omit [Fintype α] [DecidableEq α] in
theorem familyVertex_mem
    (F : Family α) (s : ℕ) (κ : α → Fin (s + 3))
    (hU : Uniform (s + 3) F)
    (hC : ∀ E ∈ F, CrossingOn (s + 3) κ E)
    (E : ↥F) (i : Fin (s + 3)) :
    familyVertex F s κ hU hC E i ∈ E.1 :=
  vertexAtColor_mem E.1 (s + 3) κ (hU E.2) (hC E.1 E.2) i

omit [Fintype α] [DecidableEq α] in
theorem familyVertex_color
    (F : Family α) (s : ℕ) (κ : α → Fin (s + 3))
    (hU : Uniform (s + 3) F)
    (hC : ∀ E ∈ F, CrossingOn (s + 3) κ E)
    (E : ↥F) (i : Fin (s + 3)) :
    κ (familyVertex F s κ hU hC E i) = i :=
  color_vertexAtColor E.1 (s + 3) κ (hU E.2) (hC E.1 E.2) i

omit [Fintype α] [DecidableEq α] in
theorem familyVertex_surjective_on_edge
    (F : Family α) (s : ℕ) (κ : α → Fin (s + 3))
    (hU : Uniform (s + 3) F)
    (hC : ∀ E ∈ F, CrossingOn (s + 3) κ E)
    (E : ↥F) (v : α) (hv : v ∈ E.1) :
    familyVertex F s κ hU hC E (κ v) = v := by
  obtain ⟨i, hi⟩ :=
    (mem_edge_iff_exists_vertexAtColor E.1 (s + 3) κ
      (hU E.2) (hC E.1 E.2) v).mp hv
  have hi' : familyVertex F s κ hU hC E i = v := hi
  have hcol : κ v = i := by
    rw [← hi']
    exact familyVertex_color F s κ hU hC E i
  rw [hcol]
  exact hi'

/-- Offset zero for the first class, followed by the prescribed differences. -/
def prefixOffset (δ : Fin s → β) : Fin (s + 1) → β :=
  Fin.cases 0 δ

omit [Fintype β] [DecidableEq β] in
@[simp] theorem prefixOffset_zero (δ : Fin s → β) :
    prefixOffset δ 0 = 0 := rfl

omit [Fintype β] [DecidableEq β] in
@[simp] theorem prefixOffset_succ (δ : Fin s → β) (i : Fin s) :
    prefixOffset δ (Fin.succ i) = δ i := rfl

noncomputable def familyAnchor
    (F : Family α) (s : ℕ) (κ : α → Fin (s + 3))
    (hU : Uniform (s + 3) F)
    (hC : ∀ E ∈ F, CrossingOn (s + 3) κ E)
    (e : α ≃ β) (E : ↥F) : β :=
  e (familyVertex F s κ hU hC E (prefixColor s 0))

noncomputable def familyDifference
    (F : Family α) (s : ℕ) (κ : α → Fin (s + 3))
    (hU : Uniform (s + 3) F)
    (hC : ∀ E ∈ F, CrossingOn (s + 3) κ E)
    (e : α ≃ β) (E : ↥F) : Fin s → β :=
  fun i => e (familyVertex F s κ hU hC E
    (prefixColor s (Fin.succ i))) - familyAnchor F s κ hU hC e E

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem familyVertex_prefix_coordinate
    (F : Family α) (s : ℕ) (κ : α → Fin (s + 3))
    (hU : Uniform (s + 3) F)
    (hC : ∀ E ∈ F, CrossingOn (s + 3) κ E)
    (e : α ≃ β) (E : ↥F) (i : Fin (s + 1)) :
    e (familyVertex F s κ hU hC E (prefixColor s i)) =
      familyAnchor F s κ hU hC e E +
        prefixOffset (familyDifference F s κ hU hC e E) i := by
  induction i using Fin.cases with
  | zero => simp [familyAnchor]
  | succ i =>
      simp only [prefixOffset_succ, familyDifference]
      abel

noncomputable def prefixBlock
    (s : ℕ) (κ : α → Fin (s + 3)) (e : α ≃ β)
    (δ : Fin s → β) (j : β) : Edge α := by
  classical
  exact Finset.univ.filter fun v => ∃ i : Fin (s + 1),
    κ v = prefixColor s i ∧ e v = j + prefixOffset δ i

omit [DecidableEq α] [Fintype β] in
theorem mem_prefixBlock_iff
    (s : ℕ) (κ : α → Fin (s + 3)) (e : α ≃ β)
    (δ : Fin s → β) (j : β) (v : α) :
    v ∈ prefixBlock s κ e δ j ↔ ∃ i : Fin (s + 1),
      κ v = prefixColor s i ∧ e v = j + prefixOffset δ i := by
  simp [prefixBlock]

omit [DecidableEq α] [Fintype β] in
theorem prefixBlock_disjoint
    (s : ℕ) (κ : α → Fin (s + 3)) (e : α ≃ β)
    (δ : Fin s → β) {j k : β} (hjk : j ≠ k) :
    Disjoint (prefixBlock s κ e δ j)
      (prefixBlock s κ e δ k) := by
  apply Finset.disjoint_left.mpr
  intro v hvj hvk
  obtain ⟨i, hci, hei⟩ :=
    (mem_prefixBlock_iff s κ e δ j v).mp hvj
  obtain ⟨i', hci', hei'⟩ :=
    (mem_prefixBlock_iff s κ e δ k v).mp hvk
  have hii' : i = i' := prefixColor_injective s (hci.symm.trans hci')
  subst i'
  exact hjk (add_right_cancel (hei.symm.trans hei'))

omit [DecidableEq α] [Fintype β] in
theorem family_prefix_vertex_mem_block
    (F : Family α) (s : ℕ) (κ : α → Fin (s + 3))
    (hU : Uniform (s + 3) F)
    (hC : ∀ E ∈ F, CrossingOn (s + 3) κ E)
    (e : α ≃ β) (E : ↥F) (i : Fin (s + 1)) :
    familyVertex F s κ hU hC E (prefixColor s i) ∈
      prefixBlock s κ e (familyDifference F s κ hU hC e E)
        (familyAnchor F s κ hU hC e E) := by
  apply (mem_prefixBlock_iff ..).2
  exact ⟨i, familyVertex_color F s κ hU hC E _,
    familyVertex_prefix_coordinate F s κ hU hC e E i⟩

omit [Fintype β] in
/-- In its unique difference fiber, a crossing edge is its prefix block
plus its two last-color vertices. -/
theorem family_edge_reconstruct
    (F : Family α) (s : ℕ) (κ : α → Fin (s + 3))
    (hU : Uniform (s + 3) F)
    (hC : ∀ E ∈ F, CrossingOn (s + 3) κ E)
    (e : α ≃ β) (E : ↥F) :
    prefixBlock s κ e (familyDifference F s κ hU hC e E)
        (familyAnchor F s κ hU hC e E) ∪
      {familyVertex F s κ hU hC E (lastColor₁ s),
        familyVertex F s κ hU hC E (lastColor₂ s)} = E.1 := by
  ext v
  constructor
  · intro hv
    rcases Finset.mem_union.mp hv with hb | ht
    · obtain ⟨i, _, heq⟩ :=
        (mem_prefixBlock_iff ..).mp hb
      have hv' : v = familyVertex F s κ hU hC E (prefixColor s i) := by
        apply e.injective
        exact heq.trans (familyVertex_prefix_coordinate F s κ hU hC e E i).symm
      rw [hv']
      exact familyVertex_mem F s κ hU hC E _
    · simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact familyVertex_mem F s κ hU hC E _
      · exact familyVertex_mem F s κ hU hC E _
  · intro hv
    rcases color_eq_prefix_or_last s (κ v) with ⟨i, hi⟩ | hi | hi
    · apply Finset.mem_union.mpr
      left
      have hv' : familyVertex F s κ hU hC E (prefixColor s i) = v := by
        rw [← hi]
        exact familyVertex_surjective_on_edge F s κ hU hC E v hv
      rw [← hv']
      exact family_prefix_vertex_mem_block F s κ hU hC e E i
    · apply Finset.mem_union.mpr
      right
      have hv' : familyVertex F s κ hU hC E (lastColor₁ s) = v := by
        rw [← hi]
        exact familyVertex_surjective_on_edge F s κ hU hC E v hv
      simp [hv']
    · apply Finset.mem_union.mpr
      right
      have hv' : familyVertex F s κ hU hC E (lastColor₂ s) = v := by
        rw [← hi]
        exact familyVertex_surjective_on_edge F s κ hU hC E v hv
      simp [hv']

omit [DecidableEq α] [Fintype β] in
theorem prefixBlock_no_last₁
    (s : ℕ) (κ : α → Fin (s + 3)) (e : α ≃ β)
    (δ : Fin s → β) (j : β) {v : α}
    (hv : κ v = lastColor₁ s) :
    v ∉ prefixBlock s κ e δ j := by
  intro hb
  obtain ⟨i, hi, _⟩ := (mem_prefixBlock_iff ..).mp hb
  exact prefixColor_ne_last₁ s i (hi.symm.trans hv)

omit [DecidableEq α] [Fintype β] in
theorem prefixBlock_no_last₂
    (s : ℕ) (κ : α → Fin (s + 3)) (e : α ≃ β)
    (δ : Fin s → β) (j : β) {v : α}
    (hv : κ v = lastColor₂ s) :
    v ∉ prefixBlock s κ e δ j := by
  intro hb
  obtain ⟨i, hi, _⟩ := (mem_prefixBlock_iff ..).mp hb
  exact prefixColor_ne_last₂ s i (hi.symm.trans hv)

end JSP523.Coarse
