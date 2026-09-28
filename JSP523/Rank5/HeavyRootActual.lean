import JSP523.Rank5.HeavyRootPacking
import JSP523.Counting.CommonPrefixTails
import Mathlib.Data.Finset.Max

/-!
# Finite heavy-root matching and vertex cover

This is the finite numerical core of the first step in IV.4.  The roots and
their completion tails are actual finsets.  A specified matching whose roots
are maximal among heavy roots gives a vertex cover by selecting one vertex
from each matched root; its size is bounded by the explicit quadratic gap.
-/

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α]

/-- Pairwise disjointness for a finite family of actual roots. -/
def RootMatching (M : Family α) : Prop :=
  ∀ P ∈ M, ∀ Q ∈ M.erase P, Disjoint P Q

/-- Actual completion tails of a root inside a fixed ambient tail universe. -/
def rootCompletionTails (H : Family α) (W P : Edge α) (t : ℕ) : Family α :=
  (W.powersetCard t).filter fun T => Disjoint T P ∧ P ∪ T ∈ H

theorem mem_root_completion_tails {H : Family α} {W P T : Edge α} {t : ℕ} :
    T ∈ rootCompletionTails H W P t ↔
      T ⊆ W ∧ T.card = t ∧ Disjoint T P ∧ P ∪ T ∈ H := by
  simp only [rootCompletionTails, Finset.mem_filter, Finset.mem_powersetCard]
  tauto

/-- Off-prefix version of the common-prefix vertex cap. Vertices inside the
fixed prefix have empty tail fibers; all other fibers inject into parent
codegree fibers. This duplicates the local argument used in
`StarLayerCollision` so this module does not depend on that unrelated file. -/
theorem common_prefix_tails_card_le_vertex_degree_off_prefix_actual
    {H : Family α} {W Y Z A : Edge α} {t D : ℕ}
    (hH : Admissible H) (hY : Y.Nonempty) (hZ : Z.Nonempty)
    (hYZ : Disjoint Y Z) (ht : 1 ≤ t)
    (hA : A ∈ commonPrefixTails H W Y Z t)
    (hCap : ∀ x : α, x ∉ Y →
      (H.filter fun E => Y ∪ {x} ⊆ E).card ≤ D) :
    (commonPrefixTails H W Y Z t).card ≤ t * D := by
  have hUniform : Uniform t (commonPrefixTails H W Y Z t) := by
    intro P hP
    exact (mem_common_prefix_tails.mp hP).2.1
  apply intersecting_card_le_vertex_cap hUniform
    (common_prefix_tails_intersecting hH hY hZ hYZ ht) hA ht
  intro x
  by_cases hxY : x ∈ Y
  · have hEmpty :
      (commonPrefixTails H W Y Z t).filter (fun P => x ∈ P) = ∅ := by
      ext P
      constructor
      · intro h
        obtain ⟨hP, hxP⟩ := Finset.mem_filter.mp h
        exact False.elim ((Finset.disjoint_left.mp
          (mem_common_prefix_tails.mp hP).2.2.1) hxP
          (Finset.mem_union_left Z hxY))
      · intro h
        simp at h
    simp [hEmpty]
  · simpa only [Finset.singleton_subset_iff] using
      (common_prefix_tails_fiber_le_parent_degree
        (H := H) (W := W) (Y := Y) (Z := Z) (S := ({x} : Edge α))
        (t := t)).trans (hCap x hxY)

/-- The completion tails common to two disjoint roots lie in the actual
common-prefix cell. -/
theorem root_completion_tails_inter_subset_common_prefix_tails
    {H : Family α} {W P Q : Edge α} {t : ℕ} :
    rootCompletionTails H W P t ∩ rootCompletionTails H W Q t ⊆
      commonPrefixTails H W P Q t := by
  intro T hT
  rcases Finset.mem_inter.mp hT with ⟨hP, hQ⟩
  obtain ⟨hTW, hTcard, hTP, hPE⟩ := mem_root_completion_tails.mp hP
  obtain ⟨_, _, hTQ, hQE⟩ := mem_root_completion_tails.mp hQ
  rw [mem_common_prefix_tails]
  refine ⟨hTW, hTcard, ?_, hPE, hQE⟩
  exact Finset.disjoint_union_right.mpr ⟨hTP, hTQ⟩

/-- Actual common-prefix cells obey the all-rank codegree cap outside the
fixed prefix; vertices inside the prefix have empty completion fibers. -/
theorem common_prefix_tails_card_le_actual_codegree
    {H : Family α} {W P Q : Edge α} {t D : ℕ}
    (hH : Admissible H) (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hPQ : Disjoint P Q) (ht : 1 ≤ t)
    (hCap : ∀ x : α, x ∉ P →
      (H.filter fun E => P ∪ {x} ⊆ E).card ≤ D) :
    (commonPrefixTails H W P Q t).card ≤ t * D := by
  by_cases hEmpty : commonPrefixTails H W P Q t = ∅
  · simp [hEmpty]
  · have hA : (commonPrefixTails H W P Q t).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hEmpty
    obtain ⟨A, hA⟩ := hA
    exact common_prefix_tails_card_le_vertex_degree_off_prefix_actual
      hH hP hQ hPQ ht hA hCap

/-- The actual intersection of two disjoint-root completion links is bounded
by the common-prefix theorem, hence by the natural vertex codegree cap. -/
theorem root_completion_tails_inter_card_le_codegree
    {H : Family α} {W P Q : Edge α} {t D : ℕ}
    (hH : Admissible H) (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hPQ : Disjoint P Q) (ht : 1 ≤ t)
    (hCap : ∀ x : α, x ∉ P →
      (H.filter fun E => P ∪ {x} ⊆ E).card ≤ D) :
    (rootCompletionTails H W P t ∩ rootCompletionTails H W Q t).card ≤ t * D := by
  calc
    _ ≤ (commonPrefixTails H W P Q t).card :=
      Finset.card_le_card (root_completion_tails_inter_subset_common_prefix_tails)
    _ ≤ t * D := common_prefix_tails_card_le_actual_codegree
      hH hP hQ hPQ ht hCap

/-- Link tails have exactly the actual root codegree when the parent edges
are uniform and lie in the ambient vertex set. -/
theorem root_completion_tails_card_eq_degree
    {H : Family α} {V P : Edge α} {r s t : ℕ}
    (hUniform : Uniform r H) (hGround : ∀ E ∈ H, E ⊆ V)
    (hPcard : P.card = s) (hst : s + t = r) :
    (rootCompletionTails H V P t).card =
      (H.filter fun E => P ⊆ E).card := by
  classical
  let C := H.filter fun E => P ⊆ E
  let T := rootCompletionTails H V P t
  let f : Edge α → Edge α := fun A => P ∪ A
  have hf : ∀ A ∈ T, f A ∈ C := by
    intro A hA
    have hA' := mem_root_completion_tails.mp hA
    exact Finset.mem_filter.mpr ⟨hA'.2.2.2, Finset.subset_union_left⟩
  have hfinj : Set.InjOn f (↑T : Set (Edge α)) := by
    intro A hA B hB hEq
    have hDisjA := (mem_root_completion_tails.mp hA).2.2.1
    have hDisjB := (mem_root_completion_tails.mp hB).2.2.1
    have hAeq : (P ∪ A) \ P = A := Finset.union_sdiff_cancel_left hDisjA.symm
    have hBeq : (P ∪ B) \ P = B := Finset.union_sdiff_cancel_left hDisjB.symm
    calc
      A = (P ∪ A) \ P := hAeq.symm
      _ = (P ∪ B) \ P := by change P ∪ A = P ∪ B at hEq; rw [hEq]
      _ = B := hBeq
  have hTle : T.card ≤ C.card := Finset.card_le_card_of_injOn f hf hfinj
  let g : Edge α → Edge α := fun E => E \ P
  have hg : ∀ E ∈ C, g E ∈ T := by
    intro E hE
    have hE' := Finset.mem_filter.mp hE
    have hSub : P ⊆ E := hE'.2
    have hTailGround : E \ P ⊆ V := (Finset.sdiff_subset).trans (hGround E hE'.1)
    have hTailCard : (E \ P).card = t := by
      rw [Finset.card_sdiff_of_subset hSub, hUniform hE'.1, hPcard]
      omega
    have hTailDisj : Disjoint (E \ P) P := Finset.disjoint_left.mpr
      (by intro x hx hxP; exact (Finset.mem_sdiff.mp hx).2 hxP)
    have hUnion : P ∪ (E \ P) = E := by
      rw [Finset.union_comm]
      exact Finset.sdiff_union_of_subset hSub
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
      ⟨hTailGround, hTailCard⟩, hTailDisj, ?_⟩
    rw [hUnion]
    exact hE'.1
  have hginj : Set.InjOn g (↑C : Set (Edge α)) := by
    intro E hE F hF hEq
    have hESub := (Finset.mem_filter.mp hE).2
    have hFSub := (Finset.mem_filter.mp hF).2
    have hEU : (E \ P) ∪ P = E := Finset.sdiff_union_of_subset hESub
    have hFU : (F \ P) ∪ P = F := Finset.sdiff_union_of_subset hFSub
    calc
      E = (E \ P) ∪ P := hEU.symm
      _ = (F \ P) ∪ P := by change E \ P = F \ P at hEq; rw [hEq]
      _ = F := hFU
  have hCle : C.card ≤ T.card := Finset.card_le_card_of_injOn g hg hginj
  exact Nat.le_antisymm hTle hCle

/-- Every finite family of nonempty roots has a maximal disjoint subfamily;
maximality means every root meets one of the selected roots. -/
theorem exists_maximal_root_matching
    (R : Family α) (s : ℕ) (hs : 1 ≤ s)
    (hSize : ∀ P ∈ R, P.card = s) :
    ∃ M : Family α, M ⊆ R ∧ RootMatching M ∧
      ∀ P ∈ R, ∃ Q ∈ M, (P ∩ Q).Nonempty := by
  classical
  let C := R.powerset.filter RootMatching
  have hC : C.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [C, RootMatching]
  obtain ⟨M, hMC, hMax⟩ := Finset.exists_max_image C Finset.card hC
  have hMR : M ⊆ R := (Finset.mem_powerset.mp (Finset.mem_filter.mp hMC).1)
  have hMatch : RootMatching M := (Finset.mem_filter.mp hMC).2
  refine ⟨M, hMR, hMatch, ?_⟩
  intro P hP
  by_contra hNo
  have hPnot : P ∉ M := by
    intro hPM
    have hNonempty : P.Nonempty := Finset.card_pos.mp (by rw [hSize P hP]; omega)
    have hPP : (P ∩ P).Nonempty := by simpa using hNonempty
    exact hNo ⟨P, hPM, hPP⟩
  let N := insert P M
  have hNsub : N ⊆ R := by
    intro Q hQ
    rcases Finset.mem_insert.mp hQ with hQ | hQ
    · simpa [hQ] using hP
    · exact hMR hQ
  have hNmatch : RootMatching N := by
    intro Q hQ S hS
    rcases Finset.mem_insert.mp hQ with hQ | hQ
    · subst Q
      have hSN : S ∈ N := (Finset.mem_erase.mp hS).2
      have hSNe : S ≠ P := (Finset.mem_erase.mp hS).1
      have hSP : S ∈ M := by
        rcases Finset.mem_insert.mp hSN with hSP | hSM
        · exact False.elim (hSNe hSP)
        · exact hSM
      have hDisj : Disjoint P S := by
        apply Finset.disjoint_iff_inter_eq_empty.mpr
        by_contra hNe
        have hInter : (P ∩ S).Nonempty := Finset.nonempty_iff_ne_empty.mpr hNe
        exact hNo ⟨S, hSP, hInter⟩
      exact hDisj
    · have hSN : S ∈ N := (Finset.mem_erase.mp hS).2
      have hQS : S ≠ Q := (Finset.mem_erase.mp hS).1
      rcases Finset.mem_insert.mp hSN with hSP | hSM
      · subst S
        apply Finset.disjoint_iff_inter_eq_empty.mpr
        by_contra hNe
        have hInter : (Q ∩ P).Nonempty := Finset.nonempty_iff_ne_empty.mpr hNe
        obtain ⟨x, hx⟩ := hInter
        exact hNo ⟨Q, hQ, ⟨x, Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp hx).2, (Finset.mem_inter.mp hx).1⟩⟩⟩
      · exact hMatch Q hQ S (Finset.mem_erase.mpr ⟨hQS, hSM⟩)
  have hNC : N ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hNsub, hNmatch⟩
  have hMaxN := hMax N hNC
  simp [N, hPnot] at hMaxN

/-- A matching of heavy roots with large tail fibers and bounded pairwise
tail intersections has fewer than `a` members whenever the displayed
finite numerical gap holds. -/
theorem actual_heavy_root_matching_card_lt
    (U M : Family α) (tails : Edge α → Family α)
    (d c a : ℕ)
    (hTailsInside : ∀ P ∈ M, tails P ⊆ U)
    (hTailLarge : ∀ P ∈ M, d ≤ (tails P).card)
    (hTailOverlap : ∀ P ∈ M, ∀ Q ∈ M.erase P,
      ((tails P) ∩ (tails Q)).card ≤ c)
    (hGap : U.card + a * a * c < a * d) : M.card < a := by
  exact large_fibers_card_lt_of_gap M U tails d c a
    hTailsInside hTailLarge hTailOverlap hGap

/-- A maximal matching in a family of fixed-size roots supplies a small
vertex cover. The maximality condition is stated concretely: every heavy
root intersects a matched root. `hGap` bounds the matching through the
actual tail fibers and explicit codegree cap `c`.
-/
theorem actual_heavy_root_vertex_cover
    (V : Edge α) (R M U : Family α) (tails : Edge α → Family α)
    (s d c a : ℕ)
    (hRootsInside : ∀ P ∈ R, P ⊆ V)
    (hRootSize : ∀ P ∈ R, P.card = s)
    (hMatchingSub : M ⊆ R)
    (hMatchingDisjoint : ∀ P ∈ M, ∀ Q ∈ M.erase P, Disjoint P Q)
    (hMaximalCover : ∀ P ∈ R, ∃ Q ∈ M, (P ∩ Q).Nonempty)
    (hTailsInside : ∀ P ∈ M, tails P ⊆ U)
    (hTailLarge : ∀ P ∈ M, d ≤ (tails P).card)
    (hTailOverlap : ∀ P ∈ M, ∀ Q ∈ M.erase P,
      ((tails P) ∩ (tails Q)).card ≤ c)
    (hGap : U.card + a * a * c < a * d) :
    ∃ X : Edge α, X ⊆ V ∧
      (∀ P ∈ R, (P ∩ X).Nonempty) ∧ X.card ≤ s * (a - 1) := by
  classical
  have hM : M.card < a :=
    actual_heavy_root_matching_card_lt U M tails d c a
      hTailsInside hTailLarge hTailOverlap hGap
  let X : Edge α := M.biUnion id
  have hPairwise : (M : Set (Edge α)).PairwiseDisjoint id := by
    intro P hP Q hQ hPQ
    exact hMatchingDisjoint P hP Q
      (Finset.mem_erase.mpr ⟨hPQ.symm, hQ⟩)
  refine ⟨X, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨Q, hQ, hxQ⟩ := Finset.mem_biUnion.mp hx
    exact hRootsInside Q (hMatchingSub hQ) hxQ
  · intro P hP
    obtain ⟨Q, hQ, hPQ⟩ := hMaximalCover P hP
    obtain ⟨x, hx⟩ := hPQ
    have hx' : x ∈ P ∧ x ∈ Q := Finset.mem_inter.mp hx
    exact ⟨x, Finset.mem_inter.mpr
      ⟨hx'.1, Finset.mem_biUnion.mpr ⟨Q, hQ, hx'.2⟩⟩⟩
  · calc
      X.card = ∑ P ∈ M, P.card := by
        dsimp [X]
        exact Finset.card_biUnion hPairwise
      _ = M.card * s := by
        calc
          (∑ P ∈ M, P.card) = ∑ P ∈ M, s := by
            apply Finset.sum_congr rfl
            intro P hP
            exact hRootSize P (hMatchingSub hP)
          _ = M.card * s := by simp
      _ ≤ (a - 1) * s := Nat.mul_le_mul_right s (Nat.le_sub_one_of_lt hM)
      _ = s * (a - 1) := Nat.mul_comm _ _

/-- Combined maximal-matching construction and numerical estimate.  This
form needs no matching or maximality witness from the caller: it constructs
the actual finite matching, bounds it from the explicit tail overlap cap,
and returns its vertex cover. -/
theorem exists_small_actual_heavy_root_vertex_cover
    (V : Edge α) (R U : Family α) (tails : Edge α → Family α)
    (s d c a : ℕ)
    (hs : 1 ≤ s)
    (hRootsInside : ∀ P ∈ R, P ⊆ V)
    (hRootSize : ∀ P ∈ R, P.card = s)
    (hTailsInside : ∀ P ∈ R, tails P ⊆ U)
    (hTailLarge : ∀ P ∈ R, d ≤ (tails P).card)
    (hTailOverlap : ∀ P ∈ R, ∀ Q ∈ R.erase P,
      ((tails P) ∩ (tails Q)).card ≤ c)
    (hGap : U.card + a * a * c < a * d) :
    ∃ X : Edge α, X ⊆ V ∧
      (∀ P ∈ R, (P ∩ X).Nonempty) ∧ X.card ≤ s * (a - 1) := by
  obtain ⟨M, hMR, hMatch, hCover⟩ := exists_maximal_root_matching R s hs hRootSize
  exact actual_heavy_root_vertex_cover V R M U tails s d c a hRootsInside
    hRootSize hMR hMatch hCover
    (fun P hP => hTailsInside P (hMR hP))
    (fun P hP => hTailLarge P (hMR hP))
    (by
      intro P hP Q hQ
      have hQP : Q ∈ R.erase P := by
        rcases Finset.mem_erase.mp hQ with ⟨hNe, hQM⟩
        exact Finset.mem_erase.mpr ⟨hNe, hMR hQM⟩
      exact hTailOverlap P (hMR hP) Q hQP)
    hGap

/-- IV.4 heavy-root cover with the pairwise tail cap derived from
admissibility and the off-prefix vertex codegrees through `CommonPrefixTails`.
The root tail families are genuine completions in `W`; their common part is
the common-prefix cell, whose size is at most `t * D`.
-/
theorem exists_actual_common_prefix_heavy_root_cover
    (H : Family α) (V W : Edge α) (R : Family α) (s t d D a : ℕ)
    (hAdm : Admissible H) (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hRootsInside : ∀ P ∈ R, P ⊆ V)
    (hRootSize : ∀ P ∈ R, P.card = s)
    (hTailLarge : ∀ P ∈ R,
      d ≤ (rootCompletionTails H W P t).card)
    (hDegreeCap : ∀ P ∈ R, ∀ x : α, x ∉ P →
      (H.filter fun E => P ∪ {x} ⊆ E).card ≤ D)
    (hGap : (W.powersetCard t).card + a * a * (t * D) < a * d) :
    ∃ X : Edge α, X ⊆ V ∧
      (∀ P ∈ R, (P ∩ X).Nonempty) ∧ X.card ≤ s * (a - 1) := by
  obtain ⟨M, hMR, hMatch, hCover⟩ := exists_maximal_root_matching R s hs hRootSize
  exact actual_heavy_root_vertex_cover V R M (W.powersetCard t)
    (rootCompletionTails H W · t) s d (t * D) a hRootsInside hRootSize
    hMR hMatch hCover
    (by
      intro P hP T hT
      obtain ⟨hTW, hTc, _, _⟩ := mem_root_completion_tails.mp hT
      exact Finset.mem_powersetCard.mpr ⟨hTW, hTc⟩)
    (fun P hP => hTailLarge P (hMR hP))
    (by
      intro P hP Q hQ
      have hPQ : Disjoint P Q := hMatch P hP Q hQ
      have hPn : P.Nonempty := Finset.card_pos.mp (by rw [hRootSize P (hMR hP)]; omega)
      have hQn : Q.Nonempty := Finset.card_pos.mp
        (by rw [hRootSize Q (hMR (Finset.mem_erase.mp hQ).2)]; omega)
      exact root_completion_tails_inter_card_le_codegree hAdm hPn hQn hPQ ht
        (hDegreeCap P (hMR hP)))
    hGap

/-- Fixed-rank `hCover` corollary for regularization assembly. Uniformity
identifies tail counts with actual root codegrees; the common-prefix argument
supplies the pair overlap cap, and the resulting cover forces every root
disjoint from `X` to obey the chosen codegree cap. -/
theorem actual_common_prefix_cover_degree_cap
    (H : Family α) (V : Edge α) (R : Family α) (r s t d D a : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hGround : ∀ E ∈ H, E ⊆ V) (hst : s + t = r)
    (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hRootsInside : ∀ P ∈ R, P ⊆ V)
    (hRootSize : ∀ P ∈ R, P.card = s)
    (hRootHeavy : ∀ P ∈ R,
      d < (H.filter fun E => P ⊆ E).card)
    (hHeavyComplete : ∀ S ∈ V.powersetCard s,
      d < (H.filter fun E => S ⊆ E).card → S ∈ R)
    (hDegreeCap : ∀ P ∈ R, ∀ x : α, x ∉ P →
      (H.filter fun E => P ∪ {x} ⊆ E).card ≤ D)
    (hGap : (V.powersetCard t).card + a * a * (t * D) < a * d) :
    ∃ X : Edge α, X ⊆ V ∧
      (∀ P ∈ R, (P ∩ X).Nonempty) ∧ X.card ≤ s * (a - 1) ∧
      (∀ S ∈ V.powersetCard s, Disjoint S X →
        (H.filter fun E => S ⊆ E).card ≤ d) := by
  obtain ⟨X, hXV, hXR, hXcard⟩ :=
    exists_actual_common_prefix_heavy_root_cover H V V R s t d D a
      hAdm hs ht hRootsInside hRootSize
      (by
        intro P hP
        rw [root_completion_tails_card_eq_degree hUniform hGround
          (hRootSize P hP) hst]
        exact Nat.le_of_lt (hRootHeavy P hP))
      hDegreeCap hGap
  refine ⟨X, hXV, hXR, hXcard, ?_⟩
  intro S hS hSX
  by_contra hLarge
  have hR : S ∈ R := hHeavyComplete S hS (by omega)
  obtain ⟨x, hx⟩ := hXR S hR
  exact (Finset.disjoint_left.mp hSX) (Finset.mem_inter.mp hx).1
    (Finset.mem_inter.mp hx).2

end JSP523.Rank5
