import JSP523.Rank4.PreprocessHeavyPairCover
import JSP523.Rank3.PairGraphClassification
import Mathlib.Tactic

/-!
# Finite heavy-pair tail multiplicity bounds

This file records the exact finite second-moment consequence used after
selecting the same number of tails from every member of a disjoint matching.
The incidence identities are exposed as hypotheses so that the geometric
selection step can discharge them independently.
-/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- Pair tails which complete a fixed pair root to an actual four-edge. -/
def actualPairRootTails (F : Family α) (U P : Edge α) : Family α :=
  (U.powersetCard 2).filter fun Q => Disjoint P Q ∧ P ∪ Q ∈ F

/-- A selected family of exactly `d` actual tails for every matching root.
The selections are subsets of the completion families in `F`. -/
def uniformActualPairTailSelection
    (F M : Family α) (U : Edge α) (d : ℕ) (A : Edge α → Family α) : Prop :=
  ∀ P ∈ M, A P ⊆ actualPairRootTails F U P ∧ (A P).card = d

/-- Choose exactly `d` tails at each root of a finite matching whenever
that root has at least `d` actual completions. -/
noncomputable def chooseActualPairTailSelection
    (F M : Family α) (U : Edge α) (d : ℕ)
    (h : ∀ P ∈ M, d ≤ (actualPairRootTails F U P).card) :
    Edge α → Family α := by
  classical
  exact fun P => if hP : P ∈ M then
    Classical.choose (Finset.exists_subset_card_eq (h P hP)) else ∅

theorem chooseActualPairTailSelection_spec
    (F M : Family α) (U : Edge α) (d : ℕ)
    (h : ∀ P ∈ M, d ≤ (actualPairRootTails F U P).card) :
    uniformActualPairTailSelection F M U d
      (chooseActualPairTailSelection F M U d h) := by
  classical
  intro P hP
  dsimp [chooseActualPairTailSelection]
  split
  · exact Classical.choose_spec
      (Finset.exists_subset_card_eq (h P hP))
  · simp_all

theorem mem_actualPairRootTails_iff
    (F : Family α) (U P Q : Edge α) :
    Q ∈ actualPairRootTails F U P ↔
      Q ∈ U.powersetCard 2 ∧ Disjoint P Q ∧ P ∪ Q ∈ F := by
  simp [actualPairRootTails]

/-- Exact first incidence count for a finite selected-tail system. -/
theorem selectedTail_first_moment
    {ι β : Type*} [DecidableEq ι] [DecidableEq β]
    (I : Finset ι) (Ω : Finset β) (A : ι → Finset β) :
    (∑ x ∈ Ω, (I.filter fun i => x ∈ A i).card) =
      ∑ i ∈ I, (A i ∩ Ω).card := by
  classical
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have hFilter : Ω.filter (fun x => x ∈ A i) = A i ∩ Ω := by
    ext x
    simp [and_comm]
  rw [← Finset.card_filter, hFilter]

/-- If each selected tail family has exactly `d` points inside the
finite universe, its total incidence count is `|I| d`. -/
theorem selectedTail_first_moment_eq
    {ι β : Type*} [DecidableEq ι] [DecidableEq β]
    (I : Finset ι) (Ω : Finset β) (A : ι → Finset β) (d : ℕ)
    (hSubset : ∀ i ∈ I, A i ⊆ Ω)
    (hSize : ∀ i ∈ I, (A i).card = d) :
    (∑ x ∈ Ω, (I.filter fun i => x ∈ A i).card) = I.card * d := by
  rw [selectedTail_first_moment]
  calc
    (∑ i ∈ I, (A i ∩ Ω).card) = ∑ i ∈ I, d := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.inter_eq_left.mpr (hSubset i hi), hSize i hi]
    _ = I.card * d := by simp

/-- Exact second incidence count: each point contributes the ordered
pairs of selected roots whose tails contain it. -/
theorem selectedTail_second_moment_rearrange
    {ι β : Type*} [DecidableEq ι] [DecidableEq β]
    (I : Finset ι) (Ω : Finset β) (A : ι → Finset β) :
    (∑ x ∈ Ω, (I.filter fun i => x ∈ A i).card ^ 2) =
      ∑ ij ∈ I ×ˢ I, ((A ij.1 ∩ A ij.2) ∩ Ω).card := by
  classical
  have hPoint (x : β) :
      (I.filter fun i => x ∈ A i).card ^ 2 =
        ((I ×ˢ I).filter fun ij => x ∈ A ij.1 ∧ x ∈ A ij.2).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_product]
    calc
      (∑ i ∈ I, if x ∈ A i then 1 else 0) ^ 2 =
          (∑ i ∈ I, if x ∈ A i then 1 else 0) *
            (∑ i ∈ I, if x ∈ A i then 1 else 0) := by ring
      _ = ∑ i ∈ I, ∑ j ∈ I,
          (if x ∈ A i then 1 else 0) * (if x ∈ A j then 1 else 0) :=
            Finset.sum_mul_sum I I _ _
      _ = ∑ i ∈ I, ∑ j ∈ I,
          if x ∈ A i ∧ x ∈ A j then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hxi : x ∈ A i <;> by_cases hxj : x ∈ A j <;>
              simp [hxi, hxj]
  calc
    _ = ∑ x ∈ Ω,
        ((I ×ˢ I).filter fun ij => x ∈ A ij.1 ∧ x ∈ A ij.2).card := by
          apply Finset.sum_congr rfl
          intro x hx
          exact hPoint x
    _ = ∑ ij ∈ I ×ˢ I,
        (Ω.filter fun x => x ∈ A ij.1 ∧ x ∈ A ij.2).card := by
          simp only [Finset.card_filter]
          rw [Finset.sum_comm]
    _ = ∑ ij ∈ I ×ˢ I, ((A ij.1 ∩ A ij.2) ∩ Ω).card := by
          apply Finset.sum_congr rfl
          intro ij hij
          congr 1
          ext x
          simp [and_left_comm, and_comm]

/-- Pairwise tail intersections give the diagonal/off-diagonal second-moment
bound for an actual finite selected family. -/
theorem selectedTail_second_moment_le
    {ι β : Type*} [DecidableEq ι] [DecidableEq β]
    (I : Finset ι) (Ω : Finset β) (A : ι → Finset β) (d R : ℕ)
    (hSize : ∀ i ∈ I, (A i).card = d)
    (hCross : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ((A i ∩ A j) ∩ Ω).card ≤ R) :
    (∑ x ∈ Ω, (I.filter fun i => x ∈ A i).card ^ 2) ≤
      I.card * d + I.card * (I.card - 1) * R := by
  classical
  rw [selectedTail_second_moment_rearrange]
  calc
    (∑ ij ∈ I ×ˢ I, ((A ij.1 ∩ A ij.2) ∩ Ω).card) ≤
        ∑ ij ∈ I ×ˢ I, if ij.1 = ij.2 then d else R := by
          apply Finset.sum_le_sum
          intro ij hij
          by_cases heq : ij.1 = ij.2
          · have hi : ij.1 ∈ I := (Finset.mem_product.mp hij).1
            have hi2 : ij.2 ∈ I := heq ▸ hi
            rw [heq, Finset.inter_self]
            simpa using (Finset.card_le_card Finset.inter_subset_left).trans_eq
              (hSize ij.2 hi2)
          · have hij' : ij.1 ∈ I ∧ ij.2 ∈ I :=
              Finset.mem_product.mp hij
            simpa [heq] using hCross ij.1 hij'.1 ij.2 hij'.2 heq
    _ = I.card * d + I.card * (I.card - 1) * R := by
          rw [Finset.sum_product]
          have hInner (i : ι) (hi : i ∈ I) :
              (∑ j ∈ I, if i = j then d else R) =
                d + (I.card - 1) * R := by
            rw [Finset.sum_ite]
            have hEq : I.filter (fun j => i = j) = {i} := by
              ext j
              simp only [Finset.mem_filter, Finset.mem_singleton]
              constructor
              · rintro ⟨hj, hij⟩
                have hji : j = i := hij.symm
                subst j
                rfl
              · intro hj
                subst j
                exact ⟨hi, rfl⟩
            have hNe : I.filter (fun j => ¬ i = j) = I.erase i := by
              ext j
              simp [Finset.mem_filter, Finset.mem_erase, and_comm, eq_comm]
            rw [hEq, hNe]
            simp [Finset.card_erase_of_mem hi]
          calc
            (∑ i ∈ I, ∑ j ∈ I, if i = j then d else R) =
                ∑ i ∈ I, (d + (I.card - 1) * R) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  exact hInner i hi
            _ = I.card * d + I.card * (I.card - 1) * R := by
                  simp [mul_add, Nat.mul_comm, Nat.mul_left_comm]

/-- Finite Cauchy--Schwarz for the point multiplicities of the selected
tails. -/
theorem selectedTail_cauchy
    {ι β : Type*} [DecidableEq ι] [DecidableEq β]
    (I : Finset ι) (Ω : Finset β) (A : ι → Finset β) :
    (∑ x ∈ Ω, (I.filter fun i => x ∈ A i).card) ^ 2 ≤
      Ω.card * (∑ x ∈ Ω, (I.filter fun i => x ∈ A i).card ^ 2) := by
  classical
  have hReal :
      (∑ x ∈ Ω, ((I.filter fun i => x ∈ A i).card : ℝ)) ^ 2 ≤
        (∑ _x ∈ Ω, (1 : ℝ)) *
          ∑ x ∈ Ω, (((I.filter fun i => x ∈ A i).card : ℝ) ^ 2) := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Ω
    · intro x hx
      norm_num
    · intro x hx
      positivity
    · intro x hx
      ring_nf
      nlinarith
  have hNat :
      (∑ x ∈ Ω, (I.filter fun i => x ∈ A i).card) ^ 2 ≤
        (∑ _x ∈ Ω, (1 : ℕ)) *
          (∑ x ∈ Ω, (I.filter fun i => x ∈ A i).card ^ 2) := by
    exact_mod_cast hReal
  simpa using hNat

/-- The actual square-moment inequality for a finite family of selected
tails, with the diagonal and cross intersections charged separately. -/
theorem selectedTail_square_moment_bound
    {ι β : Type*} [DecidableEq ι] [DecidableEq β]
    (I : Finset ι) (Ω : Finset β) (A : ι → Finset β) (d R : ℕ)
    (hSubset : ∀ i ∈ I, A i ⊆ Ω)
    (hSize : ∀ i ∈ I, (A i).card = d)
    (hCross : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ((A i ∩ A j) ∩ Ω).card ≤ R) :
    (I.card * d) ^ 2 ≤
      Ω.card * (I.card * d + I.card * (I.card - 1) * R) := by
  have hFirst := selectedTail_first_moment_eq I Ω A d hSubset hSize
  calc
    (I.card * d) ^ 2 =
        (∑ x ∈ Ω, (I.filter fun i => x ∈ A i).card) ^ 2 := by rw [hFirst]
    _ ≤ Ω.card * (∑ x ∈ Ω,
        (I.filter fun i => x ∈ A i).card ^ 2) := selectedTail_cauchy I Ω A
    _ ≤ Ω.card * (I.card * d + I.card * (I.card - 1) * R) :=
          Nat.mul_le_mul_left _
            (selectedTail_second_moment_le I Ω A d R hSize hCross)

/-- The actual selected tails common to two pair roots. -/
def actualCommonPairRootTails
    (A : Edge α → Family α) (P Q : Edge α) : Family α := A P ∩ A Q

/-- In an admissible rank-four family, two common tails of disjoint pair
roots cannot be disjoint: the four cross completions would form a trade. -/
theorem actual_common_pair_tails_intersect
    (F : Family α) (U P Q S T : Edge α)
    (hAdm : Admissible F) (hPQ : Disjoint P Q)
    (hPcard : P.card = 2) (hQcard : Q.card = 2)
    (hS : S ∈ actualCommonPairRootTails
      (fun R => actualPairRootTails F U R) P Q)
    (hT : T ∈ actualCommonPairRootTails
      (fun R => actualPairRootTails F U R) P Q) :
    ¬ Disjoint S T := by
  classical
  let aP := actualPairRootTails F U P
  let aQ := actualPairRootTails F U Q
  have hSP : S ∈ aP := (Finset.mem_inter.mp hS).1
  have hSQ : S ∈ aQ := (Finset.mem_inter.mp hS).2
  have hTP : T ∈ aP := (Finset.mem_inter.mp hT).1
  have hTQ : T ∈ aQ := (Finset.mem_inter.mp hT).2
  have hSpropP := (mem_actualPairRootTails_iff F U P S).mp hSP
  have hSpropQ := (mem_actualPairRootTails_iff F U Q S).mp hSQ
  have hTpropP := (mem_actualPairRootTails_iff F U P T).mp hTP
  have hTpropQ := (mem_actualPairRootTails_iff F U Q T).mp hTQ
  have hScard : S.card = 2 :=
    (Finset.mem_powersetCard.mp hSpropP.1).2
  have hTcard : T.card = 2 :=
    (Finset.mem_powersetCard.mp hTpropP.1).2
  have hPne : P.Nonempty := Finset.card_pos.mp (by omega)
  have hQne : Q.Nonempty := Finset.card_pos.mp (by omega)
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  have hPS : Disjoint P S := hSpropP.2.1
  have hPT : Disjoint P T := hTpropP.2.1
  have hQS : Disjoint Q S := hSpropQ.2.1
  have hQT : Disjoint Q T := hTpropQ.2.1
  intro hST
  let E₁ := P ∪ S
  let E₂ := Q ∪ T
  let E₃ := P ∪ T
  let E₄ := Q ∪ S
  have hE₁F : E₁ ∈ F := hSpropP.2.2
  have hE₂F : E₂ ∈ F := hTpropQ.2.2
  have hE₃F : E₃ ∈ F := hTpropP.2.2
  have hE₄F : E₄ ∈ F := hSpropQ.2.2
  have hUnionDisj (A B C D : Edge α) (hA : A.Nonempty)
      (hAC : Disjoint A C) (hAD : Disjoint A D) : A ∪ B ≠ C ∪ D := by
    intro heq
    obtain ⟨x, hx⟩ := hA
    have hxCD : x ∈ C ∪ D := by
      rw [← heq]
      exact Finset.mem_union_left B hx
    rcases Finset.mem_union.mp hxCD with hxC | hxD
    · exact (Finset.disjoint_left.mp hAC) hx hxC
    · exact (Finset.disjoint_left.mp hAD) hx hxD
  have hDistinct : FourDistinct E₁ E₂ E₃ E₄ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hUnionDisj P S Q T hPne hPQ hPT
    · intro hEq
      have hEq' : S ∪ P = P ∪ T := by simpa [E₁, E₃, Finset.union_comm] using hEq
      exact hUnionDisj S P P T hSne hPS.symm hST hEq'
    · exact hUnionDisj P S Q S hPne hPQ hPS
    · exact hUnionDisj Q T P T hQne hPQ.symm hQT
    · intro hEq
      have hEq' : T ∪ Q = Q ∪ S := by simpa [E₂, E₄, Finset.union_comm] using hEq
      exact hUnionDisj T Q Q S hTne hQT.symm hST.symm hEq'
    · exact hUnionDisj P T Q S hPne hPQ hPS
  have hDisj₁₂ : Disjoint E₁ E₂ := by
    apply Finset.disjoint_left.mpr
    intro x hx₁ hx₂
    rcases Finset.mem_union.mp hx₁ with hxP | hxS
    · rcases Finset.mem_union.mp hx₂ with hxQ | hxT
      · exact (Finset.disjoint_left.mp hPQ) hxP hxQ
      · exact (Finset.disjoint_left.mp hPT) hxP hxT
    · rcases Finset.mem_union.mp hx₂ with hxQ | hxT
      · exact (Finset.disjoint_left.mp hQS.symm) hxS hxQ
      · exact (Finset.disjoint_left.mp hST) hxS hxT
  have hDisj₃₄ : Disjoint E₃ E₄ := by
    apply Finset.disjoint_left.mpr
    intro x hx₃ hx₄
    rcases Finset.mem_union.mp hx₃ with hxP | hxT
    · rcases Finset.mem_union.mp hx₄ with hxQ | hxS
      · exact (Finset.disjoint_left.mp hPQ) hxP hxQ
      · exact (Finset.disjoint_left.mp hPS) hxP hxS
    · rcases Finset.mem_union.mp hx₄ with hxQ | hxS
      · exact (Finset.disjoint_left.mp hQT.symm) hxT hxQ
      · exact (Finset.disjoint_left.mp hST.symm) hxT hxS
  have hSame : E₁ ∪ E₂ = E₃ ∪ E₄ := by
    ext x
    simp [E₁, E₂, E₃, E₄, or_assoc, or_left_comm, or_comm]
  have hForbidden : ForbiddenQuad E₁ E₂ E₃ E₄ :=
    ⟨hDistinct, hDisj₁₂, hDisj₃₄, hSame⟩
  exact hAdm hE₁F hE₂F hE₃F hE₄F hForbidden

/-- Actual pair-root tails are in bijection with four-edges containing the
root: take the residual pair after removing the root. -/
theorem actualPairRootTails_card_eq_rankFourPairDegree
    (F : Family α) (U P : Edge α)
    (hSupport : F ⊆ U.powersetCard 4)
    (hP : P ∈ U.powersetCard 2) :
    (actualPairRootTails F U P).card = rankFourPairDegree F P := by
  classical
  let B := F.filter fun E => P ⊆ E
  let f : Edge α → Edge α := fun E => E \ P
  have hImage : B.image f = actualPairRootTails F U P := by
    ext Q
    constructor
    · intro hQ
      obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hQ
      have hEF : E ∈ F := (Finset.mem_filter.mp hE).1
      have hPE : P ⊆ E := (Finset.mem_filter.mp hE).2
      have hE4 : E.card = 4 := (Finset.mem_powersetCard.mp (hSupport hEF)).2
      have hP2 : P.card = 2 := (Finset.mem_powersetCard.mp hP).2
      have hQcard : (E \ P).card = 2 := by
        have hcard := Finset.card_sdiff_add_card_eq_card hPE
        omega
      have hQsub : E \ P ⊆ U :=
        (Finset.sdiff_subset).trans ((Finset.mem_powersetCard.mp (hSupport hEF)).1)
      have hUnion : P ∪ (E \ P) = E := by
        ext x
        by_cases hx : x ∈ P
        · simp [hx, hPE hx]
        · simp [hx]
      have hTail : E \ P ∈ actualPairRootTails F U P := by
        apply (mem_actualPairRootTails_iff F U P (E \ P)).mpr
        refine ⟨Finset.mem_powersetCard.mpr ⟨hQsub, hQcard⟩, ?_, ?_⟩
        · apply Finset.disjoint_left.mpr
          intro x hxP hxQ
          exact (Finset.mem_sdiff.mp hxQ).2 hxP
        · simpa [hUnion] using hEF
      exact hTail
    · intro hQ
      have hTail := (mem_actualPairRootTails_iff F U P Q).mp hQ
      refine Finset.mem_image.mpr ⟨P ∪ Q, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨hTail.2.2, ?_⟩
        intro x hxP
        exact Finset.mem_union_left Q hxP
      · ext x
        constructor
        · intro hx
          have hxUnion : x ∈ P ∪ Q := (Finset.mem_sdiff.mp hx).1
          have hxNotP : x ∉ P := (Finset.mem_sdiff.mp hx).2
          rcases Finset.mem_union.mp hxUnion with hxP | hxQ
          · exact False.elim (hxNotP hxP)
          · exact hxQ
        · intro hxQ
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right P hxQ,
            fun hxP => (Finset.disjoint_left.mp hTail.2.1) hxP hxQ⟩
  have hInj : Set.InjOn f (↑B : Set (Edge α)) := by
    intro E hE E' hE' hEq
    have hPE : P ⊆ E := (Finset.mem_filter.mp hE).2
    have hPE' : P ⊆ E' := (Finset.mem_filter.mp hE').2
    have hRec (S : Edge α) (hPS : P ⊆ S) : S = P ∪ (S \ P) := by
      ext x
      by_cases hx : x ∈ P
      · simp [hx, hPS hx]
      · simp [hx]
    calc
      E = P ∪ (E \ P) := hRec E hPE
      _ = P ∪ (E' \ P) := by
        change E \ P = E' \ P at hEq
        rw [hEq]
      _ = E' := (hRec E' hPE').symm
  have hCardImage : (B.image f).card = B.card := Finset.card_image_of_injOn hInj
  rw [← hImage, hCardImage]
  simp [rankFourPairDegree, B]

/-- A two-element set containing `x` has a unique other endpoint. -/
private theorem pair_eq_insert_other
    {S : Edge α} {x : α} (hS : S.card = 2) (hx : x ∈ S) :
    ∃ y : α, y ≠ x ∧ S = {x, y} := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hS
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hxa | hxb
  · subst a
    exact ⟨b, hab.symm, rfl⟩
  · subst b
    exact ⟨a, hab, Finset.pair_comm a x⟩

/-- The vertex degree in the actual common-tail graph is bounded by the
completion degree of the triple consisting of one root and that vertex. -/
theorem actual_common_pair_tail_vertex_degree_le
    (F : Family α) (U P Q : Edge α) (x : α) (R : ℕ)
    (hP : P ∈ U.powersetCard 2)
    (hxU : x ∈ U) (hxP : x ∉ P)
    (hTripleCap : ∀ T ∈ U.powersetCard 3,
      (tripleCompletionVertices F U T).card ≤ R) :
    ((actualCommonPairRootTails
      (fun S => actualPairRootTails F U S) P Q).filter fun S => x ∈ S).card ≤ R := by
  classical
  let G := actualCommonPairRootTails
    (fun S => actualPairRootTails F U S) P Q
  let J := G.filter fun S => x ∈ S
  let T := insert x P
  have hPcard : P.card = 2 := (Finset.mem_powersetCard.mp hP).2
  have hTcard : T.card = 3 := by simp [T, hxP, hPcard]
  have hTsub : T ⊆ U := by
    intro y hy
    simp only [T, Finset.mem_insert] at hy
    rcases hy with rfl | hyP
    · exact hxU
    · exact (Finset.mem_powersetCard.mp hP).1 hyP
  have hTmem : T ∈ U.powersetCard 3 :=
    Finset.mem_powersetCard.mpr ⟨hTsub, hTcard⟩
  have hProperties (S : Edge α) (hS : S ∈ J) :
      (S ∈ U.powersetCard 2 ∧ Disjoint P S ∧ P ∪ S ∈ F) ∧ x ∈ S := by
    have hG : S ∈ G := (Finset.mem_filter.mp hS).1
    have hxS : x ∈ S := (Finset.mem_filter.mp hS).2
    have hTail := (mem_actualPairRootTails_iff F U P S).mp
      ((Finset.mem_inter.mp hG).1)
    exact ⟨hTail, hxS⟩
  let f : Edge α → α := fun S => if hS : S ∈ J then
    Classical.choose (pair_eq_insert_other
      (Finset.mem_powersetCard.mp (hProperties S hS).1.1).2
      (hProperties S hS).2) else x
  have hfSpec (S : Edge α) (hS : S ∈ J) :
      f S ≠ x ∧ S = {x, f S} := by
    dsimp only [f]
    rw [dite_eq_left hS]
    exact Classical.choose_spec (pair_eq_insert_other
      (Finset.mem_powersetCard.mp (hProperties S hS).1.1).2
      (hProperties S hS).2)
  have hfInjective : Set.InjOn f (↑J : Set (Edge α)) := by
    intro S hSJ T' hT' hEq
    have hSeq := (hfSpec S hSJ).2
    have hTeq := (hfSpec T' hT').2
    rw [hSeq, hTeq, hEq]
  have hImageSub : J.image f ⊆ tripleCompletionVertices F U T := by
    intro y hy
    obtain ⟨S, hSJ, rfl⟩ := Finset.mem_image.mp hy
    have hProps := hProperties S hSJ
    have hOther := hfSpec S hSJ
    let y := f S
    have hyS : y ∈ S := hOther.2.symm ▸ (by simp : y ∈ {x, y})
    have hyU : y ∈ U := (Finset.mem_powersetCard.mp hProps.1.1).1 hyS
    have hEdge : insert y T ∈ F := by
      have hEq : insert y (insert x P) = P ∪ S := by
        rw [hOther.2]
        ext z
        dsimp [y]
        simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
        tauto
      rw [hEq]
      exact hProps.1.2.2
    exact Finset.mem_filter.mpr ⟨hyU, by simpa [T] using hEdge⟩
  have hImageCard : (J.image f).card = J.card :=
    Finset.card_image_of_injOn hfInjective
  calc
    _ = J.card := rfl
    _ = (J.image f).card := hImageCard.symm
    _ ≤ (tripleCompletionVertices F U T).card := Finset.card_le_card hImageSub
    _ ≤ R := hTripleCap T hTmem

/-- Every pair of actual common tails for disjoint pair roots intersects. -/
theorem actual_common_pair_tail_family_intersecting
    (F : Family α) (U P Q : Edge α)
    (hAdm : Admissible F) (hPQ : Disjoint P Q)
    (hPcard : P.card = 2) (hQcard : Q.card = 2) :
    ∀ S ∈ actualCommonPairRootTails
        (fun R => actualPairRootTails F U R) P Q,
      ∀ T ∈ actualCommonPairRootTails
        (fun R => actualPairRootTails F U R) P Q,
        ¬ Disjoint S T := by
  intro S hS T hT
  exact actual_common_pair_tails_intersect F U P Q S T hAdm hPQ
    hPcard hQcard hS hT

/-- The common tails of two roots form an intersecting pair graph; if every
vertex belongs to at most `R` common tails, classification bounds the whole
family by `max R 3`. -/
theorem actual_common_pair_tail_card_le_max
    (A : Edge α → Family α) (P Q : Edge α) (R : ℕ)
    (hPair : ∀ S ∈ actualCommonPairRootTails A P Q, S.card = 2)
    (hMeet : ∀ S ∈ actualCommonPairRootTails A P Q,
      ∀ T ∈ actualCommonPairRootTails A P Q, ¬ Disjoint S T)
    (hDegree : ∀ x : α,
      ((actualCommonPairRootTails A P Q).filter fun S => x ∈ S).card ≤ R) :
    (actualCommonPairRootTails A P Q).card ≤ max R 3 := by
  rcases JSP523.Rank3.intersecting_pair_graph_star_or_small
      (actualCommonPairRootTails A P Q) hPair hMeet with hStar | hSmall
  · obtain ⟨x, hx⟩ := hStar
    have hSub : actualCommonPairRootTails A P Q ⊆
        (actualCommonPairRootTails A P Q).filter fun S => x ∈ S := by
      intro S hS
      exact Finset.mem_filter.mpr ⟨hS, hx S hS⟩
    exact (Finset.card_le_card hSub).trans
      ((hDegree x).trans (Nat.le_max_left R 3))
  · exact hSmall.trans (Nat.le_max_right R 3)

/-- Actual matching-tail cross bound from admissibility and the local degree
argument can be supplied as point-degree/intersection properties of each
common-tail graph. -/
theorem actual_pair_root_matching_cross_intersection_bound
    (F M : Family α) (U : Edge α) (A : Edge α → Family α) (P Q : Edge α)
    (d R : ℕ)
    (hSelection : uniformActualPairTailSelection F M U d A)
    (hPM : P ∈ M) (hQM : Q ∈ M)
    (hAdm : Admissible F) (hPQ : Disjoint P Q)
    (hPcard : P.card = 2) (hQcard : Q.card = 2)
    (hDegree : ∀ x : α,
      ((actualCommonPairRootTails A P Q).filter fun S => x ∈ S).card ≤ R)
    (hR : 3 ≤ R) :
    ((A P ∩ A Q) ∩ U.powersetCard 2).card ≤ R := by
  have hPair : ∀ S ∈ actualCommonPairRootTails A P Q, S.card = 2 := by
    intro S hS
    have hSP : S ∈ A P := (Finset.mem_inter.mp hS).1
    have hTail := (hSelection P hPM).1 hSP
    exact (Finset.mem_powersetCard.mp
      (Finset.mem_filter.mp hTail).1).2
  have hMeet : ∀ S ∈ actualCommonPairRootTails A P Q,
      ∀ T ∈ actualCommonPairRootTails A P Q, ¬ Disjoint S T := by
    intro S hS T hT
    have hSP : S ∈ actualPairRootTails F U P :=
      (hSelection P hPM).1 ((Finset.mem_inter.mp hS).1)
    have hSQ : S ∈ actualPairRootTails F U Q :=
      (hSelection Q hQM).1 ((Finset.mem_inter.mp hS).2)
    have hTP : T ∈ actualPairRootTails F U P :=
      (hSelection P hPM).1 ((Finset.mem_inter.mp hT).1)
    have hTQ : T ∈ actualPairRootTails F U Q :=
      (hSelection Q hQM).1 ((Finset.mem_inter.mp hT).2)
    exact actual_common_pair_tails_intersect F U P Q S T hAdm hPQ
      hPcard hQcard (Finset.mem_inter.mpr ⟨hSP, hSQ⟩)
      (Finset.mem_inter.mpr ⟨hTP, hTQ⟩)
  have hG : (actualCommonPairRootTails A P Q).card ≤ R := by
    have hBound := actual_common_pair_tail_card_le_max A P Q R
      hPair hMeet hDegree
    exact hBound.trans (by simp [Nat.max_eq_left hR])
  have hSub : (A P ∩ A Q) ∩ U.powersetCard 2 ⊆
      actualCommonPairRootTails A P Q := by
    intro S hS
    exact (Finset.mem_inter.mp hS).1
  exact (Finset.card_le_card hSub).trans hG

/-- Selected common-tail vertex degrees inherit the completion cap from
actual tails. -/
theorem actual_selected_pair_tail_vertex_degree_le
    (F M : Family α) (U P Q : Edge α) (d R : ℕ)
    (A : Edge α → Family α)
    (hSelection : uniformActualPairTailSelection F M U d A)
    (hPM : P ∈ M) (hQM : Q ∈ M)
    (hP : P ∈ U.powersetCard 2)
    (hTripleCap : ∀ T ∈ U.powersetCard 3,
      (tripleCompletionVertices F U T).card ≤ R) :
    ∀ x : α,
      ((actualCommonPairRootTails A P Q).filter fun S => x ∈ S).card ≤ R := by
  classical
  intro x
  let J := actualCommonPairRootTails A P Q
  let Jfull := actualCommonPairRootTails
    (fun S => actualPairRootTails F U S) P Q
  have hSub : J ⊆ Jfull := by
    intro S hS
    exact Finset.mem_inter.mpr
      ⟨(hSelection P hPM).1 (Finset.mem_inter.mp hS).1,
        (hSelection Q hQM).1 (Finset.mem_inter.mp hS).2⟩
  have hFilterSub : J.filter (fun S => x ∈ S) ⊆
      Jfull.filter (fun S => x ∈ S) := by
    intro S hS
    exact Finset.mem_filter.mpr
      ⟨hSub (Finset.mem_filter.mp hS).1, (Finset.mem_filter.mp hS).2⟩
  change (J.filter fun S => x ∈ S).card ≤ R
  by_cases hxU : x ∈ U
  · by_cases hxP : x ∈ P
    · have hEmpty : J.filter (fun S => x ∈ S) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro S hS
        have hFull : S ∈ Jfull := hSub (Finset.mem_filter.mp hS).1
        have hTail := (mem_actualPairRootTails_iff F U P S).mp
          ((Finset.mem_inter.mp hFull).1)
        exact ((Finset.disjoint_left.mp hTail.2.1) hxP
          (Finset.mem_filter.mp hS).2).elim
      rw [hEmpty]
      simp
    · exact (Finset.card_le_card hFilterSub).trans
        (actual_common_pair_tail_vertex_degree_le F U P Q x R hP
          hxU hxP hTripleCap)
  · have hEmpty : J.filter (fun S => x ∈ S) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro S hS
      have hFull : S ∈ Jfull := hSub (Finset.mem_filter.mp hS).1
      have hTail := (mem_actualPairRootTails_iff F U P S).mp
        ((Finset.mem_inter.mp hFull).1)
      have hxU' : x ∈ U :=
        (Finset.mem_powersetCard.mp hTail.1).1 (Finset.mem_filter.mp hS).2
      exact (hxU hxU').elim
    rw [hEmpty]
    simp

/-- Instantiation of the double-counting inequality to actual pair roots and
their selected actual four-edge completion tails. -/
theorem actualPairTailSelection_square_moment
    (F M : Family α) (U : Edge α) (A : Edge α → Family α) (d R : ℕ)
    (hSelection : uniformActualPairTailSelection F M U d A)
    (hCross : ∀ P ∈ M, ∀ Q ∈ M, P ≠ Q →
      ((A P ∩ A Q) ∩ U.powersetCard 2).card ≤ R) :
    (M.card * d) ^ 2 ≤
      (U.powersetCard 2).card *
        (M.card * d + M.card * (M.card - 1) * R) := by
  apply selectedTail_square_moment_bound M (U.powersetCard 2) A d R
  · intro P hP Q hQ
    have hA := (hSelection P hP).1
    have hQ' : Q ∈ actualPairRootTails F U P := hA hQ
    exact (mem_actualPairRootTails_iff F U P Q).mp hQ' |>.1
  · intro P hP
    exact (hSelection P hP).2
  · exact hCross

/-- Actual selected matching-tail second moment under admissibility and a
triple completion cap. This is the finite A.4 input before the numerical
heavy-pair estimate. -/
theorem actualPairTailSelection_square_moment_of_caps
    (F M : Family α) (U : Edge α) (A : Edge α → Family α) (d R : ℕ)
    (hSelection : uniformActualPairTailSelection F M U d A)
    (hMpair : ∀ P ∈ M, P ∈ U.powersetCard 2)
    (hMatching : pairRootMatching M)
    (hAdm : Admissible F)
    (hTripleCap : ∀ T ∈ U.powersetCard 3,
      (tripleCompletionVertices F U T).card ≤ R)
    (hR : 3 ≤ R) :
    (M.card * d) ^ 2 ≤
      (U.powersetCard 2).card *
        (M.card * d + M.card * (M.card - 1) * R) := by
  apply actualPairTailSelection_square_moment F M U A d R hSelection
  intro P hP Q hQ hne
  have hPQ := hMatching P hP Q hQ hne
  exact actual_pair_root_matching_cross_intersection_bound
    F M U A P Q d R hSelection hP hQ hAdm hPQ
    ((Finset.mem_powersetCard.mp (hMpair P hP)).2)
    ((Finset.mem_powersetCard.mp (hMpair Q hQ)).2)
    (actual_selected_pair_tail_vertex_degree_le F M U P Q d R A
      hSelection hP hQ (hMpair P hP) hTripleCap) hR

/-- A useful algebraic consequence of the selected-tail second-moment
bound. The moment hypothesis is the finite incidence estimate
`(kd)^2 ≤ u (kd + k(k−1)R)`; in applications `u` is the number of pair
nodes and `R` bounds the intersection of two distinct selected tail sets. -/
theorem heavy_matching_card_le_four_mul_n_div_T
    {k d u R n T : ℕ}
    (hMoment : (k * d) ^ 2 ≤ u * (k * d + k * (k - 1) * R))
    (hkd : 0 < k)
    (hd : T * n ≤ d)
    (hTn : 0 < T * n)
    (hu : u ≤ n * n)
    (hDenom : 2 * u * R ≤ d * d) :
    k * T ≤ 4 * n := by
  have hn : 0 < n := by nlinarith
  have hdPos : 0 < d := by nlinarith
  have hPairTerm : u * (k * (k - 1) * R) ≤ u * (k * k * R) := by
    apply Nat.mul_le_mul_left
    apply Nat.mul_le_mul_right
    exact Nat.mul_le_mul_left k (Nat.sub_le k 1)
  have hNorm : k * d * d ≤ u * d + u * k * R := by
    nlinarith [hMoment, hPairTerm]
  have hKey : k * d * d ≤ 2 * u * d := by
    nlinarith [hNorm, hDenom]
  have hkdBound : k * d ≤ 2 * u := by
    nlinarith
  have hScale : k * T * n ≤ k * d := by
    nlinarith
  have hFinal : k * T * n ≤ 2 * n * n := by
    calc
      k * T * n ≤ k * d := hScale
      _ ≤ 2 * u := hkdBound
      _ ≤ 2 * n * n := by nlinarith [hu]
  nlinarith

/-- One-shot finite heavy-pair matching bound. The roots are actual high
codegree pairs, each has at least `T |U|` actual completion tails, and the
triple completion cap controls common-tail intersections. -/
theorem actual_heavy_pair_matching_card_bound
    (F M : Family α) (U : Edge α) (T R : ℕ)
    (hHeavy : M ⊆ actualHeavyPairRoots F U T)
    (hTailLower : ∀ P ∈ M,
      T * U.card ≤ (actualPairRootTails F U P).card)
    (hMatching : pairRootMatching M)
    (hAdm : Admissible F)
    (hTripleCap : ∀ S ∈ U.powersetCard 3,
      (tripleCompletionVertices F U S).card ≤ R)
    (hR : 3 ≤ R) (hM : 0 < M.card) (hTn : 0 < T * U.card)
    (hPairs : (U.powersetCard 2).card ≤ U.card * U.card)
    (hDenom : 2 * (U.powersetCard 2).card * R ≤ (T * U.card) ^ 2) :
    M.card * T ≤ 4 * U.card := by
  classical
  have hMpair : ∀ P ∈ M, P ∈ U.powersetCard 2 := by
    intro P hP
    exact (Finset.mem_filter.mp (hHeavy hP)).1
  let A := chooseActualPairTailSelection F M U (T * U.card) hTailLower
  have hSelection : uniformActualPairTailSelection F M U (T * U.card) A :=
    chooseActualPairTailSelection_spec F M U (T * U.card) hTailLower
  have hMoment := actualPairTailSelection_square_moment_of_caps
    F M U A (T * U.card) R hSelection hMpair hMatching hAdm hTripleCap hR
  exact heavy_matching_card_le_four_mul_n_div_T hMoment hM (Nat.le_refl _) hTn hPairs (by simpa [pow_two] using hDenom)

end JSP523.Rank4
