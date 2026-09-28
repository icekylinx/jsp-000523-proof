import JSP523.Rank4.PreprocessFixedDecomposition

/-!
# Finite high-codegree cleanup

This is the final deletion step used in the regularization argument: a
triple whose completion degree exceeds the target is charged to its
pair-collision moment.  The statement is finite and keeps the actual
four-edges and ground set.
-/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- Actual completion vertices of a triple inside a four-family. -/
def tripleCompletionVertices (F : Family α) (V T : Edge α) : Finset α :=
  V.filter fun x => insert x T ∈ F

/-- Triple roots whose completion degree exceeds `R`. -/
def highCodegreeTriples (F : Family α) (V : Edge α) (R : ℕ) : Family α :=
  (V.powersetCard 3).filter fun T => R < (tripleCompletionVertices F V T).card

/-- Delete every four-edge supported by a high-codegree triple. -/
def highCodegreeDeletion (F : Family α) (V : Edge α) (R : ℕ) : Family α :=
  (highCodegreeTriples F V R).biUnion fun T =>
    (tripleCompletionVertices F V T).image fun x => insert x T

/-- The deletion is contained in the original four-family. -/
theorem high_codegree_deletion_subset
    (F : Family α) (V : Edge α) (R : ℕ) :
    highCodegreeDeletion F V R ⊆ F := by
  classical
  intro E hE
  obtain ⟨T, hT, hImage⟩ := Finset.mem_biUnion.mp hE
  obtain ⟨x, hx, hEq⟩ := Finset.mem_image.mp hImage
  have hxF : insert x T ∈ F := (Finset.mem_filter.mp hx).2
  simpa [hEq] using hxF

/-- Every remaining triple has degree at most the target. -/
theorem triple_completion_vertices_card_le_of_survives
    (F : Family α) (V : Edge α) (R : ℕ) (T : Edge α)
    (hT : T ∈ V.powersetCard 3)
    (hSurvive : ∀ x ∈ tripleCompletionVertices F V T,
      insert x T ∉ highCodegreeDeletion F V R) :
    (tripleCompletionVertices F V T).card ≤ R := by
  by_contra h
  have hLarge : R < (tripleCompletionVertices F V T).card := by omega
  have hHigh : T ∈ highCodegreeTriples F V R := by
    exact Finset.mem_filter.mpr ⟨hT, hLarge⟩
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega :
    0 < (tripleCompletionVertices F V T).card)
  have hxMem : x ∈ tripleCompletionVertices F V T := hx
  have hxE : insert x T ∈
      (tripleCompletionVertices F V T).image fun y => insert y T :=
    Finset.mem_image.mpr ⟨x, hxMem, rfl⟩
  have hxDelete : insert x T ∈ highCodegreeDeletion F V R :=
    Finset.mem_biUnion.mpr ⟨T, hHigh, hxE⟩
  exact hSurvive x hxMem hxDelete

/-- Cardinality of the high-codegree deletion is at most the sum of the
degrees of its high triple roots. -/
theorem high_codegree_deletion_card_le
    (F : Family α) (V : Edge α) (R : ℕ) :
    (highCodegreeDeletion F V R).card ≤
      ∑ T ∈ highCodegreeTriples F V R,
        (tripleCompletionVertices F V T).card := by
  classical
  unfold highCodegreeDeletion
  calc
    _ ≤ ∑ T ∈ highCodegreeTriples F V R,
        ((tripleCompletionVertices F V T).image fun x => insert x T).card :=
          Finset.card_biUnion_le
    _ ≤ ∑ T ∈ highCodegreeTriples F V R,
        (tripleCompletionVertices F V T).card := by
          apply Finset.sum_le_sum
          intro T hT
          exact Finset.card_image_le

/-- Actual tail deletion bound from the pair-collision moment.  For a
triple degree `d > R`, its contribution `R*d` is bounded by `d*(d-1)`. -/
theorem high_codegree_deletion_mul_le_collision_moment
    (F : Family α) (V : Edge α) (R : ℕ) :
    R * (highCodegreeDeletion F V R).card ≤
      ∑ T ∈ V.powersetCard 3,
        (tripleCompletionVertices F V T).card *
          ((tripleCompletionVertices F V T).card - 1) := by
  classical
  let d := fun T : Edge α => (tripleCompletionVertices F V T).card
  have hTail : R * (∑ T ∈ highCodegreeTriples F V R, d T) ≤
      ∑ T ∈ highCodegreeTriples F V R, d T * (d T - 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro T hT
    have hDegree : R < d T := (Finset.mem_filter.mp hT).2
    have hPos : 0 < d T := by omega
    have hR : R ≤ d T - 1 := by omega
    have hMul := Nat.mul_le_mul_right (d T) hR
    simpa [Nat.mul_comm] using hMul
  have hSum :
      (∑ T ∈ highCodegreeTriples F V R, d T * (d T - 1)) ≤
        ∑ T ∈ V.powersetCard 3, d T * (d T - 1) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro T hT
      exact (Finset.mem_filter.mp hT).1
    · intro T hT hNot
      exact Nat.zero_le _
  calc
    R * (highCodegreeDeletion F V R).card ≤
        R * (∑ T ∈ highCodegreeTriples F V R, d T) :=
          Nat.mul_le_mul_left R (high_codegree_deletion_card_le F V R)
    _ ≤ ∑ T ∈ highCodegreeTriples F V R, d T * (d T - 1) := hTail
    _ ≤ ∑ T ∈ V.powersetCard 3, d T * (d T - 1) := hSum

/-- The high-codegree deletion leaves a subfamily in which every triple has
degree at most `R`.  A supplied collision-moment bound gives its explicit
finite deletion budget. -/
theorem high_codegree_deletion_regularizes
    (F : Family α) (V : Edge α) (R M : ℕ)
    (hMoment : ∑ T ∈ V.powersetCard 3,
        (tripleCompletionVertices F V T).card *
          ((tripleCompletionVertices F V T).card - 1) ≤ M) :
    ∃ K : Family α,
      K ⊆ F ∧
      R * (F \ K).card ≤ M ∧
      (∀ T ∈ V.powersetCard 3,
        (tripleCompletionVertices K V T).card ≤ R) := by
  classical
  let D := highCodegreeDeletion F V R
  let K := F \ D
  have hDF : D ⊆ F := high_codegree_deletion_subset F V R
  have hRemoved : F \ K = D := by
    ext E
    simp [K, D, hDF]
  refine ⟨K, ?_, ?_, ?_⟩
  · intro E hE
    exact (Finset.mem_sdiff.mp hE).1
  · rw [hRemoved]
    exact (high_codegree_deletion_mul_le_collision_moment F V R).trans hMoment
  · intro T hT
    have hSub : tripleCompletionVertices K V T ⊆
        tripleCompletionVertices F V T := by
      intro x hx
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,
        (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).2).1⟩
    by_contra hBound
    have hKLarge : R < (tripleCompletionVertices K V T).card := by omega
    have hFLarge : R < (tripleCompletionVertices F V T).card :=
      lt_of_lt_of_le hKLarge (Finset.card_le_card hSub)
    have hHigh : T ∈ highCodegreeTriples F V R :=
      Finset.mem_filter.mpr ⟨hT, hFLarge⟩
    obtain ⟨x, hxK⟩ := Finset.card_pos.mp (by omega :
      0 < (tripleCompletionVertices K V T).card)
    have hxF : x ∈ tripleCompletionVertices F V T := hSub hxK
    have hxDel : insert x T ∈ highCodegreeDeletion F V R := by
      apply Finset.mem_biUnion.mpr
      refine ⟨T, hHigh, ?_⟩
      exact Finset.mem_image.mpr ⟨x, hxF, rfl⟩
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hxK).2).2 hxDel

end JSP523.Rank4
