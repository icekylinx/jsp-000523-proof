import JSP523.Counting.BadSetIncidence
import JSP523.Counting.DistancePacking
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite deletion accounting for the local exact theorem

This module isolates the quantitative combinatorial step used in (IV.2.5):
once a family of bad roots is fixed and every root is contained in at most
`C` outside edges of the class under consideration, deleting all edges that
contain a bad root costs at most `C` times the number of bad roots.
The distance-packing estimates needed to establish those fiber bounds are
available in `Counting.DistancePacking`.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

/-- Edges containing at least one recorded bad root. -/
def edgesMeetingBadRoot (B Bad : Family α) : Family α :=
  Bad.biUnion fun P => B.filter fun E => P ⊆ E

/-- A finite union bound for deleting edges through bad roots.  This exact
form is the reusable accounting interface for each bad-set size in (IV.2.5).
The incidence fiber bound is the place where the paper's distance-packing
lemma is applied. -/
theorem bad_root_deletion_cost
    {B Bad : Family α} {C : ℕ}
    (hFiber : ∀ P ∈ Bad, (B.filter fun E => P ⊆ E).card ≤ C) :
    (edgesMeetingBadRoot B Bad).card ≤ Bad.card * C := by
  classical
  unfold edgesMeetingBadRoot
  exact Finset.card_biUnion_le_card_mul Bad
    (fun P => B.filter fun E => P ⊆ E) C hFiber

/-- Apply a quantitative bad-root count and a per-root tail estimate to get
the deletion cost.  Keeping these two estimates as separate hypotheses lets
applications instantiate the incidence estimate (IV.2.3) and the relevant
distance-packing bound independently. -/
theorem bad_root_deletion_cost_of_bounds
    {B Bad : Family α} {A C : ℕ}
    (hBad : Bad.card ≤ A)
    (hFiber : ∀ P ∈ Bad, (B.filter fun E => P ⊆ E).card ≤ C) :
    (edgesMeetingBadRoot B Bad).card ≤ A * C := by
  calc
    (edgesMeetingBadRoot B Bad).card ≤ Bad.card * C :=
      bad_root_deletion_cost hFiber
    _ ≤ A * C := Nat.mul_le_mul_right C hBad

/-- Edges containing exactly one member of a designated bad-pair family. -/
def uniqueBadPairEdges (B Bad₂ : Family α) : Family α :=
  Bad₂.biUnion fun P =>
    B.filter fun E =>
      P ⊆ E ∧ (Bad₂.filter fun Q => Q ⊆ E).card = 1

/-- All edges containing at least one bad pair. -/
def badPairEdges (B Bad₂ : Family α) : Family α :=
  Bad₂.biUnion fun P => B.filter fun E => P ⊆ E

/-- Edges containing a specified pair of distinct bad pairs whose
intersection has the requested status.  The root recorded by the union is
P ∪ Q, so it is contained in every edge in the corresponding fiber. -/
def twoBadPairEdges (B Bad₂ : Family α)
    (status : Edge α → Edge α → Prop) [DecidableRel status] : Family α :=
  Bad₂.biUnion fun P =>
    (Bad₂.filter fun Q => status P Q).biUnion fun Q =>
      B.filter fun E => P ∪ Q ⊆ E

/-- A two-level finite union bound: if each ordered root pair supports at
most C edges, the total is at most |Bad₂|² C. -/
theorem two_bad_pair_union_cost
    {B Bad₂ : Family α} {C : ℕ}
    (hFiber : ∀ P ∈ Bad₂, ∀ Q ∈ Bad₂,
      (B.filter fun E => P ∪ Q ⊆ E).card ≤ C) :
    (twoBadPairEdges B Bad₂ (fun _ _ => True)).card ≤
      Bad₂.card * (Bad₂.card * C) := by
  classical
  unfold twoBadPairEdges
  apply Finset.card_biUnion_le_card_mul
  intro P hP
  have hInner : ((Bad₂.filter fun _Q => True).biUnion
      fun Q => B.filter fun E => P ∪ Q ⊆ E).card ≤
      (Bad₂.filter fun _Q => True).card * C :=
    Finset.card_biUnion_le_card_mul _ _ C (by
      intro Q hQ
      exact hFiber P hP Q (Finset.mem_filter.mp hQ).1)
  have hFilter : (Bad₂.filter fun _Q => True).card ≤ Bad₂.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  exact hInner.trans (Nat.mul_le_mul_right C hFilter)

/-- The pair strata used in (IV.2.5) have a direct finite deletion bound.
The three fiber bounds correspond respectively to one bad pair, two
disjoint bad pairs, and two intersecting bad pairs. -/
theorem bad_pair_three_strata_deletion_bound
    {B Bad₂ : Family α} {C₁ C₂ C₃ : ℕ}
    (hUnique : ∀ P ∈ Bad₂,
      (B.filter fun E =>
        P ⊆ E ∧ (Bad₂.filter fun Q => Q ⊆ E).card = 1).card ≤ C₁)
    (hDisjoint : ∀ P ∈ Bad₂, ∀ Q ∈ Bad₂, Disjoint P Q →
      (B.filter fun E => P ∪ Q ⊆ E).card ≤ C₂)
    (hIntersect : ∀ P ∈ Bad₂, ∀ Q ∈ Bad₂, P ≠ Q →
      ¬ Disjoint P Q →
      (B.filter fun E => P ∪ Q ⊆ E).card ≤ C₃) :
    (uniqueBadPairEdges B Bad₂ ∪
      twoBadPairEdges B Bad₂ (fun P Q => Disjoint P Q) ∪
      twoBadPairEdges B Bad₂ (fun P Q => P ≠ Q ∧ ¬ Disjoint P Q)).card ≤
      Bad₂.card * C₁ +
        Bad₂.card * (Bad₂.card * C₂) +
        Bad₂.card * (Bad₂.card * C₃) := by
  classical
  have hU : (uniqueBadPairEdges B Bad₂).card ≤ Bad₂.card * C₁ := by
    unfold uniqueBadPairEdges
    exact Finset.card_biUnion_le_card_mul Bad₂ _ C₁ hUnique
  have hD : (twoBadPairEdges B Bad₂ (fun P Q => Disjoint P Q)).card ≤
      Bad₂.card * (Bad₂.card * C₂) := by
    unfold twoBadPairEdges
    apply Finset.card_biUnion_le_card_mul
    intro P hP
    have hInner := Finset.card_biUnion_le_card_mul
      (Bad₂.filter fun Q => Disjoint P Q)
      (fun Q => B.filter fun E => P ∪ Q ⊆ E) C₂ (by
        intro Q hQ
        exact hDisjoint P hP Q (Finset.mem_filter.mp hQ).1
          (Finset.mem_filter.mp hQ).2)
    exact hInner.trans (Nat.mul_le_mul_right C₂
      (Finset.card_le_card (Finset.filter_subset _ _)))
  have hI : (twoBadPairEdges B Bad₂
      (fun P Q => P ≠ Q ∧ ¬ Disjoint P Q)).card ≤
      Bad₂.card * (Bad₂.card * C₃) := by
    unfold twoBadPairEdges
    apply Finset.card_biUnion_le_card_mul
    intro P hP
    have hInner := Finset.card_biUnion_le_card_mul
      (Bad₂.filter fun Q => P ≠ Q ∧ ¬ Disjoint P Q)
      (fun Q => B.filter fun E => P ∪ Q ⊆ E) C₃ (by
        intro Q hQ
        exact hIntersect P hP Q (Finset.mem_filter.mp hQ).1
          (Finset.mem_filter.mp hQ).2.1 (Finset.mem_filter.mp hQ).2.2)
    exact hInner.trans (Nat.mul_le_mul_right C₃
      (Finset.card_le_card (Finset.filter_subset _ _)))
  have hUnion := Finset.card_union_le
    (uniqueBadPairEdges B Bad₂)
    (twoBadPairEdges B Bad₂ (fun P Q => Disjoint P Q))
  have hUnion' := Finset.card_union_le
    (uniqueBadPairEdges B Bad₂ ∪
      twoBadPairEdges B Bad₂ (fun P Q => Disjoint P Q))
    (twoBadPairEdges B Bad₂ (fun P Q => P ≠ Q ∧ ¬ Disjoint P Q))
  omega

/-- The three strata cover every edge containing a bad pair: either its
bad-pair multiplicity is one, or two distinct witnesses are disjoint or
intersect. -/
theorem bad_pair_edges_covered_by_three_strata
    {B Bad₂ : Family α} :
    badPairEdges B Bad₂ ⊆
      uniqueBadPairEdges B Bad₂ ∪
        twoBadPairEdges B Bad₂ (fun P Q => Disjoint P Q) ∪
        twoBadPairEdges B Bad₂ (fun P Q => P ≠ Q ∧ ¬ Disjoint P Q) := by
  classical
  intro E hE
  obtain ⟨P, hP, hPE⟩ := Finset.mem_biUnion.mp hE
  have hEB : E ∈ B := (Finset.mem_filter.mp hPE).1
  let S := Bad₂.filter fun Q => Q ⊆ E
  have hPEsub : P ⊆ E := (Finset.mem_filter.mp hPE).2
  have hPS : P ∈ S := Finset.mem_filter.mpr ⟨hP, hPEsub⟩
  by_cases hOne : S.card = 1
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨P, hP, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨hEB, ⟨hPEsub, by simpa [S] using hOne⟩⟩
  · have hTwo : 2 ≤ S.card := by
      have hPos : 0 < S.card := Finset.card_pos.mpr ⟨P, hPS⟩
      omega
    obtain ⟨Q, hQ, R, hR, hQR⟩ := Finset.one_lt_card.mp hTwo
    have hQE : Q ⊆ E := (Finset.mem_filter.mp hQ).2
    have hRE : R ⊆ E := (Finset.mem_filter.mp hR).2
    by_cases hDisj : Disjoint Q R
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨Q, (Finset.mem_filter.mp hQ).1, ?_⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨R, Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hR).1, hDisj⟩, ?_⟩
      exact Finset.mem_filter.mpr
        ⟨hEB, Finset.union_subset hQE hRE⟩
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨Q, (Finset.mem_filter.mp hQ).1, ?_⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨R, Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hR).1, ⟨hQR, hDisj⟩⟩, ?_⟩
      exact Finset.mem_filter.mpr
        ⟨hEB, Finset.union_subset hQE hRE⟩

/-- Consequently, once the three fiber estimates have been established,
the total number of edges containing any bad pair has the explicit
three-term bound. -/
theorem bad_pair_edges_deletion_bound
    {B Bad₂ : Family α} {C₁ C₂ C₃ : ℕ}
    (hUnique : ∀ P ∈ Bad₂,
      (B.filter fun E =>
        P ⊆ E ∧ (Bad₂.filter fun Q => Q ⊆ E).card = 1).card ≤ C₁)
    (hDisjoint : ∀ P ∈ Bad₂, ∀ Q ∈ Bad₂, Disjoint P Q →
      (B.filter fun E => P ∪ Q ⊆ E).card ≤ C₂)
    (hIntersect : ∀ P ∈ Bad₂, ∀ Q ∈ Bad₂, P ≠ Q →
      ¬ Disjoint P Q →
      (B.filter fun E => P ∪ Q ⊆ E).card ≤ C₃) :
    (badPairEdges B Bad₂).card ≤
      Bad₂.card * C₁ +
        Bad₂.card * (Bad₂.card * C₂) +
        Bad₂.card * (Bad₂.card * C₃) := by
  calc
    (badPairEdges B Bad₂).card ≤
      (uniqueBadPairEdges B Bad₂ ∪
        twoBadPairEdges B Bad₂ (fun P Q => Disjoint P Q) ∪
        twoBadPairEdges B Bad₂ (fun P Q => P ≠ Q ∧ ¬ Disjoint P Q)).card :=
      Finset.card_le_card bad_pair_edges_covered_by_three_strata
    _ ≤ Bad₂.card * C₁ +
        Bad₂.card * (Bad₂.card * C₂) +
        Bad₂.card * (Bad₂.card * C₃) :=
      bad_pair_three_strata_deletion_bound hUnique hDisjoint hIntersect

/-- Sum the deletion costs for any finite collection of bad-set sizes.
This is the finite (non-asymptotic) form of summing the k ≥ 3 strata in
(IV.2.5); applications supply the incidence bound for each size and the
tail packing bound for each bad root. -/
theorem bad_set_size_strata_deletion_bound
    {B : Family α} {K : Finset ℕ}
    (Bad : ℕ → Family α) (A C : ℕ → ℕ)
    (hBad : ∀ k ∈ K, (Bad k).card ≤ A k)
    (hFiber : ∀ k ∈ K, ∀ P ∈ Bad k,
      (B.filter fun E => P ⊆ E).card ≤ C k) :
    (K.biUnion fun k => edgesMeetingBadRoot B (Bad k)).card ≤
      ∑ k ∈ K, A k * C k := by
  classical
  calc
    (K.biUnion fun k => edgesMeetingBadRoot B (Bad k)).card ≤
        ∑ k ∈ K, (edgesMeetingBadRoot B (Bad k)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ k ∈ K, A k * C k := by
      apply Finset.sum_le_sum
      intro k hk
      exact bad_root_deletion_cost_of_bounds (hBad k hk)
        (hFiber k hk)

/-- Combine the three pair strata with all larger bad-set strata into one
finite bound for the total number of edges scheduled for deletion. -/
theorem local_exact_total_deletion_bound
    {B Bad₂ : Family α} {K : Finset ℕ}
    (Bad : ℕ → Family α) (A C : ℕ → ℕ)
    {C₁ C₂ C₃ : ℕ}
    (hUnique : ∀ P ∈ Bad₂,
      (B.filter fun E =>
        P ⊆ E ∧ (Bad₂.filter fun Q => Q ⊆ E).card = 1).card ≤ C₁)
    (hDisjoint : ∀ P ∈ Bad₂, ∀ Q ∈ Bad₂, Disjoint P Q →
      (B.filter fun E => P ∪ Q ⊆ E).card ≤ C₂)
    (hIntersect : ∀ P ∈ Bad₂, ∀ Q ∈ Bad₂, P ≠ Q →
      ¬ Disjoint P Q →
      (B.filter fun E => P ∪ Q ⊆ E).card ≤ C₃)
    (hBad : ∀ k ∈ K, (Bad k).card ≤ A k)
    (hFiber₂ : ∀ k ∈ K, ∀ P ∈ Bad k,
      (B.filter fun E => P ⊆ E).card ≤ C k) :
    (badPairEdges B Bad₂ ∪
      K.biUnion fun k => edgesMeetingBadRoot B (Bad k)).card ≤
      Bad₂.card * C₁ +
        Bad₂.card * (Bad₂.card * C₂) +
        Bad₂.card * (Bad₂.card * C₃) +
        ∑ k ∈ K, A k * C k := by
  have hPair := bad_pair_edges_deletion_bound hUnique hDisjoint hIntersect
  have hLarge := bad_set_size_strata_deletion_bound Bad A C hBad hFiber₂
  calc
    (badPairEdges B Bad₂ ∪
      K.biUnion fun k => edgesMeetingBadRoot B (Bad k)).card ≤
      (badPairEdges B Bad₂).card +
        (K.biUnion fun k => edgesMeetingBadRoot B (Bad k)).card :=
      Finset.card_union_le _ _
    _ ≤ Bad₂.card * C₁ +
        Bad₂.card * (Bad₂.card * C₂) +
        Bad₂.card * (Bad₂.card * C₃) +
        ∑ k ∈ K, A k * C k := by omega

/-- Geometric core of the tail separation argument in (IV.2.5).  If two
outside edges share a fixed `k`-set, and neither edge contains a bad
difference set of size below `k`, their tails cannot differ in fewer than
`k` points.  The contradiction is precisely the overlap trade (IV.2.2). -/
theorem fixed_bad_root_tails_distance
    {H : Family α} {W E F P : Edge α} {v : α} {r k : ℕ}
    (hH : Admissible H)
    (hE : E ∈ H) (hF : F ∈ H)
    (hEF : E ≠ F)
    (hEsub : E ⊆ W) (hFsub : F ⊆ W)
    (hEcard : E.card = r) (hFcard : F.card = r)
    (hvW : v ∉ W)
    (hP_E : P ⊆ E) (hP_F : P ⊆ F) (hPcard : P.card = k)
    (hk : 1 ≤ k) (hkr : k ≤ r - 1)
    (hCleanE : ∀ j : ℕ, 1 ≤ j → j < k →
      ∀ Q : Edge α, Q ⊆ E \ P → Q.card = j →
        Q ∉ badMissingSets H W v r j
          ((W.card - r - j).choose (r - 1 - j)))
    (hCleanF : ∀ j : ℕ, 1 ≤ j → j < k →
      ∀ Q : Edge α, Q ⊆ F \ P → Q.card = j →
        Q ∉ badMissingSets H W v r j
          ((W.card - r - j).choose (r - 1 - j))) :
    k ≤ (E \ F).card := by
  by_contra hlt
  have hShared : (E ∩ F).Nonempty := by
    have hPpos : P.Nonempty := Finset.card_pos.mp (by omega : 0 < P.card)
    obtain ⟨x, hx⟩ := hPpos
    exact ⟨x, Finset.mem_inter.mpr ⟨hP_E hx, hP_F hx⟩⟩
  have hDiffPos : 1 ≤ (E \ F).card := by
    by_contra hzero
    have hEmpty : E \ F = ∅ := Finset.card_eq_zero.mp (by omega)
    have hSub : E ⊆ F := Finset.sdiff_eq_empty_iff_subset.mp hEmpty
    have hEq := Finset.eq_of_subset_of_card_le hSub (by rw [hEcard, hFcard])
    exact hEF hEq
  have hDiffSmall : (E \ F).card < k := by omega
  have hDiffBound : (E \ F).card ≤ r - 2 := by omega
  have hDiffSubE : E \ F ⊆ E \ P := by
    intro x hx
    have hxE := (Finset.mem_sdiff.mp hx).1
    have hxNotF := (Finset.mem_sdiff.mp hx).2
    refine Finset.mem_sdiff.mpr ⟨hxE, ?_⟩
    intro hxP
    exact hxNotF (hP_F hxP)
  have hDiffSubF : F \ E ⊆ F \ P := by
    intro x hx
    have hxF := (Finset.mem_sdiff.mp hx).1
    have hxNotE := (Finset.mem_sdiff.mp hx).2
    refine Finset.mem_sdiff.mpr ⟨hxF, ?_⟩
    intro hxP
    exact hxNotE (hP_E hxP)
  have hOverlap := overlapping_edges_have_bad_missing_set
    hH hE hF hEsub hFsub hEcard hFcard hEF hShared hvW
  rcases hOverlap with hL | hR
  · exact (hCleanE (E \ F).card hDiffPos hDiffSmall
      (E \ F) hDiffSubE rfl) hL
  · have hSame : (F \ E).card = (E \ F).card := by
      have h1 := Finset.card_sdiff_add_card_inter E F
      have h2 := Finset.card_sdiff_add_card_inter F E
      rw [Finset.inter_comm] at h2
      omega
    rw [← hSame] at hR
    have hNotBad := hCleanF (F \ E).card
      (by rw [hSame]; exact hDiffPos) (by rw [hSame]; exact hDiffSmall)
      (F \ E) hDiffSubF rfl
    exact hNotBad hR

/-- A tail family of size `r-k` with mutual distance at least `k` has the
finite distance-packing bound used in §IV.2.1.  This is the explicit
binomial estimate after applying `fixed_bad_root_tails_distance` to show
the distance hypothesis for concrete tails. -/
theorem fixed_root_tail_packing_bound
    {W : Edge α} {T : Family α} {r k : ℕ}
    (hSub : ∀ A ∈ T, A ⊆ W)
    (hUniform : Uniform (r - k) T)
    (hDistance : ∀ ⦃A B : Edge α⦄, A ∈ T → B ∈ T → A ≠ B →
      k ≤ (A \ B).card)
    (hk : k ≤ r - k) :
    T.card * (r - k).choose (r - k - k + 1) ≤
      W.card.choose (r - k - k + 1) := by
  exact distance_packing_choose_bound hSub hUniform hDistance hk

/-- The actual tail-family application: if each member of T is the tail
E \ P of an outside edge containing the fixed root P, and edges in the
class have no bad subsets below size k, then the tails have distance at
least k.  Distance packing gives the explicit finite binomial bound. -/
theorem fixed_bad_root_tail_family_bound
    {H B T : Family α} {W P : Edge α} {v : α} {r k : ℕ}
    (hH : Admissible H) (hBH : B ⊆ H) (hBuniform : Uniform r B)
    (hW : ∀ E ∈ B, E ⊆ W) (hvW : v ∉ W)
    (hPcard : P.card = k) (hk : 1 ≤ k) (hkr : k ≤ r - 1)
    (hTail : ∀ T₀ ∈ T, ∃ E ∈ B, P ⊆ E ∧ E \ P = T₀)
    (hTsub : ∀ A ∈ T, A ⊆ W)
    (hTuniform : Uniform (r - k) T)
    (hClean : ∀ E ∈ B, P ⊆ E → ∀ j : ℕ, 1 ≤ j → j < k →
      ∀ Q : Edge α, Q ⊆ E \ P → Q.card = j →
        Q ∉ badMissingSets H W v r j
          ((W.card - r - j).choose (r - 1 - j)))
    (hPackRank : k ≤ r - k) :
    T.card * (r - k).choose (r - k - k + 1) ≤
      W.card.choose (r - k - k + 1) := by
  apply fixed_root_tail_packing_bound hTsub hTuniform ?_ hPackRank
  intro A B₀ hA hB hAB
  obtain ⟨E, hEB, hPE, hET⟩ := hTail A hA
  obtain ⟨F, hFB, hPF, hFS⟩ := hTail B₀ hB
  have hEF : E ≠ F := by
    intro hEq
    subst F
    have hEqTail : A = B₀ := by rw [← hET, ← hFS]
    exact hAB hEqTail
  have hEcard : E.card = r := by
    exact hBuniform hEB
  have hFcard : F.card = r := by
    exact hBuniform hFB
  have hDist := fixed_bad_root_tails_distance hH (hBH hEB) (hBH hFB)
    hEF (hW E hEB) (hW F hFB) hEcard hFcard hvW hPE hPF hPcard hk hkr
    (fun j hj hjs Q hQE hQcard =>
      hClean E hEB hPE j hj hjs Q hQE hQcard)
    (fun j hj hjs Q hQF hQcard =>
      hClean F hFB hPF j hj hjs Q hQF hQcard)
  have hDiffTail : (E \ P) \ (F \ P) = E \ F := by
    ext x
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hxE, hxnotP⟩, hxnotF⟩
      refine ⟨hxE, ?_⟩
      intro hxF
      exact hxnotF ⟨hxF, hxnotP⟩
    · rintro ⟨hxE, hxnotF⟩
      refine ⟨⟨hxE, ?_⟩, ?_⟩
      · intro hxP
        exact hxnotF (hPF hxP)
      · intro hxTailF
        exact hxnotF hxTailF.1
  rw [← hDiffTail, hET, hFS] at hDist
  exact hDist

/-- When the required distance exceeds the tail size, a fixed-root tail
family has at most one member.  This supplies the constant bound in the
negative-exponent range of Lemma IV.1.2. -/
theorem fixed_bad_root_tail_family_at_most_one
    {H B T : Family α} {W P : Edge α} {v : α} {r k : ℕ}
    (hH : Admissible H) (hBH : B ⊆ H) (hBuniform : Uniform r B)
    (hW : ∀ E ∈ B, E ⊆ W) (hvW : v ∉ W)
    (hPcard : P.card = k) (hk : 1 ≤ k) (hkr : k ≤ r - 1)
    (hTail : ∀ T₀ ∈ T, ∃ E ∈ B, P ⊆ E ∧ E \ P = T₀)
    (hTuniform : Uniform (r - k) T)
    (hClean : ∀ E ∈ B, P ⊆ E → ∀ j : ℕ, 1 ≤ j → j < k →
      ∀ Q : Edge α, Q ⊆ E \ P → Q.card = j →
        Q ∉ badMissingSets H W v r j
          ((W.card - r - j).choose (r - 1 - j)))
    (hRank : r - k < k) :
    T.card ≤ 1 := by
  have hDistance : ∀ ⦃A B₀ : Edge α⦄, A ∈ T → B₀ ∈ T →
      A ≠ B₀ → k ≤ (A \ B₀).card := by
    intro A B₀ hA hB hAB
    obtain ⟨E, hEB, hPE, hET⟩ := hTail A hA
    obtain ⟨F, hFB, hPF, hFS⟩ := hTail B₀ hB
    have hEF : E ≠ F := by
      intro hEq
      subst F
      have hEqTail : A = B₀ := by rw [← hET, ← hFS]
      exact hAB hEqTail
    have hEcard : E.card = r := hBuniform hEB
    have hFcard : F.card = r := hBuniform hFB
    have hDist := fixed_bad_root_tails_distance hH (hBH hEB) (hBH hFB)
      hEF (hW E hEB) (hW F hFB) hEcard hFcard hvW hPE hPF hPcard hk hkr
      (fun j hj hjs Q hQE hQcard =>
        hClean E hEB hPE j hj hjs Q hQE hQcard)
      (fun j hj hjs Q hQF hQcard =>
        hClean F hFB hPF j hj hjs Q hQF hQcard)
    have hDiffTail : (E \ P) \ (F \ P) = E \ F := by
      ext x
      simp only [Finset.mem_sdiff]
      constructor
      · rintro ⟨⟨hxE, hxnotP⟩, hxnotF⟩
        refine ⟨hxE, ?_⟩
        intro hxF
        exact hxnotF ⟨hxF, hxnotP⟩
      · rintro ⟨hxE, hxnotF⟩
        refine ⟨⟨hxE, ?_⟩, ?_⟩
        · intro hxP
          exact hxnotF (hPF hxP)
        · intro hxTailF
          exact hxnotF hxTailF.1
    rw [← hDiffTail, hET, hFS] at hDist
    exact hDist
  exact distance_packing_at_most_one (_W := W) hTuniform hDistance hRank

/-- Tails of members of B containing a fixed root P. -/
def fixedRootTailFamily (B : Family α) (P : Edge α) : Family α :=
  (B.filter fun E => P ⊆ E).image fun E => E \ P

/-- The distance-packing inequality gives a concrete per-root fiber bound
for any rank k satisfying k ≤ r-k (the polynomial-exponent range in the
k ≥ 3 part of §IV.2.1). -/
theorem fixed_bad_root_fiber_binomial_bound
    {H B : Family α} {W P : Edge α} {v : α} {r k : ℕ}
    (hH : Admissible H) (hBH : B ⊆ H) (hBuniform : Uniform r B)
    (hW : ∀ E ∈ B, E ⊆ W) (hvW : v ∉ W)
    (hPcard : P.card = k) (hk : 1 ≤ k) (hkr : k ≤ r - 1)
    (hClean : ∀ E ∈ B, P ⊆ E → ∀ j : ℕ, 1 ≤ j → j < k →
      ∀ Q : Edge α, Q ⊆ E \ P → Q.card = j →
        Q ∉ badMissingSets H W v r j
          ((W.card - r - j).choose (r - 1 - j)))
    (hPackRank : k ≤ r - k) :
    (B.filter fun E => P ⊆ E).card ≤
      W.card.choose (r - k - k + 1) := by
  classical
  let T := fixedRootTailFamily B P
  have hRealize : ∀ T₀ ∈ T, ∃ E ∈ B, P ⊆ E ∧ E \ P = T₀ := by
    intro T₀ hT
    obtain ⟨E, hE, hEq⟩ := Finset.mem_image.mp hT
    exact ⟨E, (Finset.mem_filter.mp hE).1,
      (Finset.mem_filter.mp hE).2, hEq⟩
  have hSub : ∀ A ∈ T, A ⊆ W := by
    intro A hA
    obtain ⟨E, hE, hEq⟩ := Finset.mem_image.mp hA
    rw [← hEq]
    exact Finset.sdiff_subset.trans (hW E (Finset.mem_filter.mp hE).1)
  have hUniform : Uniform (r - k) T := by
    intro A hA
    obtain ⟨E, hE, hEq⟩ := Finset.mem_image.mp hA
    rw [← hEq, Finset.card_sdiff_of_subset (Finset.mem_filter.mp hE).2,
      hBuniform (Finset.mem_filter.mp hE).1, hPcard]
  have hBound := fixed_bad_root_tail_family_bound hH hBH hBuniform hW hvW
    hPcard hk hkr hRealize hSub hUniform hClean hPackRank
  have hInj : Set.InjOn (fun E : Edge α => E \ P)
      (↑(B.filter fun E => P ⊆ E) : Set (Edge α)) := by
    intro E hE F hF hEq
    have hPE := (Finset.mem_filter.mp hE).2
    have hPF := (Finset.mem_filter.mp hF).2
    calc
      E = (E \ P) ∪ P := (Finset.sdiff_union_of_subset hPE).symm
      _ = (F \ P) ∪ P := congrArg (fun X => X ∪ P) hEq
      _ = F := Finset.sdiff_union_of_subset hPF
  have hCard : T.card = (B.filter fun E => P ⊆ E).card := by
    dsimp [T, fixedRootTailFamily]
    exact Finset.card_image_iff.mpr hInj
  rw [hCard] at hBound
  have hChoosePos : 1 ≤ (r - k).choose (r - k - k + 1) := by
    have hpos := Nat.choose_pos (show r - k - k + 1 ≤ r - k by omega)
    omega
  have hMul : (B.filter fun E => P ⊆ E).card ≤
      (B.filter fun E => P ⊆ E).card *
        (r - k).choose (r - k - k + 1) := by
    exact Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- Fixed-root fibers have size at most one in the range k > r-k. -/
theorem fixed_bad_root_fiber_at_most_one
    {H B : Family α} {W P : Edge α} {v : α} {r k : ℕ}
    (hH : Admissible H) (hBH : B ⊆ H) (hBuniform : Uniform r B)
    (hW : ∀ E ∈ B, E ⊆ W) (hvW : v ∉ W)
    (hPcard : P.card = k) (hk : 1 ≤ k) (hkr : k ≤ r - 1)
    (hClean : ∀ E ∈ B, P ⊆ E → ∀ j : ℕ, 1 ≤ j → j < k →
      ∀ Q : Edge α, Q ⊆ E \ P → Q.card = j →
        Q ∉ badMissingSets H W v r j
          ((W.card - r - j).choose (r - 1 - j)))
    (hRank : r - k < k) :
    (B.filter fun E => P ⊆ E).card ≤ 1 := by
  classical
  let T := fixedRootTailFamily B P
  have hRealize : ∀ T₀ ∈ T, ∃ E ∈ B, P ⊆ E ∧ E \ P = T₀ := by
    intro T₀ hT
    obtain ⟨E, hE, hEq⟩ := Finset.mem_image.mp hT
    exact ⟨E, (Finset.mem_filter.mp hE).1,
      (Finset.mem_filter.mp hE).2, hEq⟩
  have hUniform : Uniform (r - k) T := by
    intro A hA
    obtain ⟨E, hE, hEq⟩ := Finset.mem_image.mp hA
    rw [← hEq, Finset.card_sdiff_of_subset (Finset.mem_filter.mp hE).2,
      hBuniform (Finset.mem_filter.mp hE).1, hPcard]
  have hBound := fixed_bad_root_tail_family_at_most_one hH hBH hBuniform
    hW hvW hPcard hk hkr hRealize hUniform hClean hRank
  have hInj : Set.InjOn (fun E : Edge α => E \ P)
      (↑(B.filter fun E => P ⊆ E) : Set (Edge α)) := by
    intro E hE F hF hEq
    have hPE := (Finset.mem_filter.mp hE).2
    have hPF := (Finset.mem_filter.mp hF).2
    calc
      E = (E \ P) ∪ P := (Finset.sdiff_union_of_subset hPE).symm
      _ = (F \ P) ∪ P := congrArg (fun X => X ∪ P) hEq
      _ = F := Finset.sdiff_union_of_subset hPF
  have hCard : T.card = (B.filter fun E => P ⊆ E).card := by
    dsimp [T, fixedRootTailFamily]
    exact Finset.card_image_iff.mpr hInj
  rw [hCard] at hBound
  exact hBound

/-- A fully instantiated finite deletion bound for one k ≥ 3 stratum.
The bad-root count is the incidence estimate (IV.2.3), while the fiber
bound is obtained from fixed-root tail packing when k ≤ r-k and from
distance exceeding the tail size otherwise. -/
theorem higher_bad_set_stratum_deletion_bound
    {H B : Family α} {W : Edge α} {v : α} {r k Λ : ℕ}
    (hH : Admissible H) (hBH : B ⊆ H) (hBuniform : Uniform r B)
    (hW : ∀ E ∈ B, E ⊆ W) (hvW : v ∉ W)
    (hk3 : 3 ≤ k) (hkr : k ≤ r - 1)
    (hLambda : 0 < Λ)
    (hClean : ∀ E ∈ B, ∀ P : Edge α, P ⊆ E → P.card = k →
      ∀ j : ℕ, 1 ≤ j → j < k →
        ∀ Q : Edge α, Q ⊆ E \ P → Q.card = j →
          Q ∉ badMissingSets H W v r j
            ((W.card - r - j).choose (r - 1 - j))) :
    (edgesMeetingBadRoot B (badMissingSets H W v r k Λ)).card ≤
      (2 * (r - 1).choose k *
        (missingStarFacets H W v r).card / Λ) *
        (if k ≤ r - k then W.card.choose (r - k - k + 1) else 1) := by
  let Bad := badMissingSets H W v r k Λ
  have hInc := badMissingSets_card_bound H W v r k Λ
  have hBadCount : Bad.card ≤
      (2 * (r - 1).choose k *
        (missingStarFacets H W v r).card) / Λ := by
    apply (Nat.le_div_iff_mul_le hLambda).2
    calc
      Bad.card * Λ = Λ * Bad.card := Nat.mul_comm _ _
      _ ≤ 2 * (r - 1).choose k *
          (missingStarFacets H W v r).card := hInc
  apply bad_root_deletion_cost_of_bounds hBadCount
  intro P hP
  have hPdata := Finset.mem_powersetCard.mp
    (Finset.mem_filter.mp hP).1
  by_cases hRank : k ≤ r - k
  · have hFiber := fixed_bad_root_fiber_binomial_bound
      hH hBH hBuniform hW hvW hPdata.2 (by omega) hkr
      (fun E hE hPE j hj hjs Q hQ hQcard =>
        hClean E hE P hPE hPdata.2 j hj hjs Q hQ hQcard)
      hRank
    simpa [hRank] using hFiber
  · have hFiber := fixed_bad_root_fiber_at_most_one
      hH hBH hBuniform hW hvW hPdata.2 (by omega) hkr
      (fun E hE hPE j hj hjs Q hQ hQcard =>
        hClean E hE P hPE hPdata.2 j hj hjs Q hQ hQcard)
      (by omega)
    simpa only [ite_eq_right hRank] using hFiber

/-- Sum all higher bad-set sizes with their actual incidence and tail
binomial estimates.  No abstract Aₖ or Cₖ remains: the summand is the
integer-safe form of
2 * choose(r-1,k) * q / Λₖ times the distance-packing tail bound. -/
theorem all_higher_bad_set_strata_deletion_bound
    {H B : Family α} {W : Edge α} {v : α} {r : ℕ}
    {K : Finset ℕ} (Λ : ℕ → ℕ)
    (hH : Admissible H) (hBH : B ⊆ H) (hBuniform : Uniform r B)
    (hW : ∀ E ∈ B, E ⊆ W) (hvW : v ∉ W)
    (hRankRange : ∀ k ∈ K, 3 ≤ k ∧ k ≤ r - 1)
    (hLambda : ∀ k ∈ K, 0 < Λ k)
    (hClean : ∀ k ∈ K, ∀ E ∈ B, ∀ P : Edge α,
      P ⊆ E → P.card = k →
      ∀ j : ℕ, 1 ≤ j → j < k →
        ∀ Q : Edge α, Q ⊆ E \ P → Q.card = j →
          Q ∉ badMissingSets H W v r j
            ((W.card - r - j).choose (r - 1 - j))) :
    ((K.biUnion fun k => edgesMeetingBadRoot B
      (badMissingSets H W v r k (Λ k)))).card ≤
      ∑ k ∈ K,
        ((2 * (r - 1).choose k *
          (missingStarFacets H W v r).card / Λ k) *
          (if k ≤ r - k then W.card.choose (r - k - k + 1) else 1)) := by
  let Bad : ℕ → Family α :=
    fun k => badMissingSets H W v r k (Λ k)
  let A : ℕ → ℕ :=
    fun k => 2 * (r - 1).choose k *
      (missingStarFacets H W v r).card / Λ k
  let C : ℕ → ℕ :=
    fun k => if k ≤ r - k then W.card.choose (r - k - k + 1) else 1
  have hBad : ∀ k ∈ K, (Bad k).card ≤ A k := by
    intro k hk
    have hInc := badMissingSets_card_bound H W v r k (Λ k)
    change (badMissingSets H W v r k (Λ k)).card ≤ A k
    apply (Nat.le_div_iff_mul_le (hLambda k hk)).2
    calc
      (Bad k).card * Λ k = Λ k * (Bad k).card := Nat.mul_comm _ _
      _ ≤ 2 * (r - 1).choose k *
          (missingStarFacets H W v r).card := hInc
  have hFiber : ∀ k ∈ K, ∀ P ∈ Bad k,
      (B.filter fun E => P ⊆ E).card ≤ C k := by
    intro k hk P hP
    obtain ⟨hk3, hkr⟩ := hRankRange k hk
    change P ∈ badMissingSets H W v r k (Λ k) at hP
    have hPdata := Finset.mem_powersetCard.mp
      (Finset.mem_filter.mp hP).1
    by_cases hPack : k ≤ r - k
    · have hBound := fixed_bad_root_fiber_binomial_bound
        hH hBH hBuniform hW hvW hPdata.2 (by omega) hkr
        (fun E hE hPE j hj hjs Q hQ hQcard =>
          hClean k hk E hE P hPE hPdata.2 j hj hjs Q hQ hQcard)
        hPack
      simpa [C, hPack] using hBound
    · have hBound := fixed_bad_root_fiber_at_most_one
        hH hBH hBuniform hW hvW hPdata.2 (by omega) hkr
        (fun E hE hPE j hj hjs Q hQ hQcard =>
          hClean k hk E hE P hPE hPdata.2 j hj hjs Q hQ hQcard)
        (by omega)
      simpa [C, hPack] using hBound
  have hTotal := bad_set_size_strata_deletion_bound Bad A C hBad hFiber
  simpa [Bad, A, C] using hTotal

/-- Tail separation with independent root size and required distance.
This generalization is needed for the bad-pair strata: a disjoint pair of
bad pairs has a four-point root but only requires tail distance two. -/
theorem fixed_root_tails_distance_threshold
    {H : Family α} {W E F P : Edge α} {v : α} {r s d : ℕ}
    (hH : Admissible H) (hE : E ∈ H) (hF : F ∈ H)
    (hEF : E ≠ F) (hEsub : E ⊆ W) (hFsub : F ⊆ W)
    (hEcard : E.card = r) (hFcard : F.card = r) (hvW : v ∉ W)
    (hPE : P ⊆ E) (hPF : P ⊆ F) (hPcard : P.card = s)
    (hs : 1 ≤ s)
    (hCleanE : ∀ j : ℕ, 1 ≤ j → j < d →
      ∀ Q : Edge α, Q ⊆ E \ P → Q.card = j →
        Q ∉ badMissingSets H W v r j
          ((W.card - r - j).choose (r - 1 - j)))
    (hCleanF : ∀ j : ℕ, 1 ≤ j → j < d →
      ∀ Q : Edge α, Q ⊆ F \ P → Q.card = j →
        Q ∉ badMissingSets H W v r j
          ((W.card - r - j).choose (r - 1 - j))) :
    d ≤ (E \ F).card := by
  by_contra hlt
  have hShared : (E ∩ F).Nonempty := by
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < P.card)
    exact ⟨x, Finset.mem_inter.mpr ⟨hPE hx, hPF hx⟩⟩
  have hDiffPos : 1 ≤ (E \ F).card := by
    by_contra hzero
    have hEmpty : E \ F = ∅ := Finset.card_eq_zero.mp (by omega)
    have hSub : E ⊆ F := Finset.sdiff_eq_empty_iff_subset.mp hEmpty
    have hEq := Finset.eq_of_subset_of_card_le hSub (by rw [hEcard, hFcard])
    exact hEF hEq
  have hSmall : (E \ F).card < d := by omega
  have hDiffSubE : E \ F ⊆ E \ P := by
    intro x hx
    refine Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1, ?_⟩
    intro hxP
    exact (Finset.mem_sdiff.mp hx).2 (hPF hxP)
  have hDiffSubF : F \ E ⊆ F \ P := by
    intro x hx
    refine Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1, ?_⟩
    intro hxP
    exact (Finset.mem_sdiff.mp hx).2 (hPE hxP)
  have hOverlap := overlapping_edges_have_bad_missing_set
    hH hE hF hEsub hFsub hEcard hFcard hEF hShared hvW
  rcases hOverlap with hL | hR
  · exact (hCleanE (E \ F).card hDiffPos hSmall (E \ F) hDiffSubE rfl) hL
  · have hSame : (F \ E).card = (E \ F).card := by
      have h1 := Finset.card_sdiff_add_card_inter E F
      have h2 := Finset.card_sdiff_add_card_inter F E
      rw [Finset.inter_comm] at h2
      omega
    rw [← hSame] at hR
    have hNotBad := hCleanF (F \ E).card
      (by rw [hSame]; exact hDiffPos) (by rw [hSame]; exact hSmall)
      (F \ E) hDiffSubF rfl
    exact hNotBad hR

/-- A real outside-edge fiber through P is bounded by distance packing,
with the constant-tail case included automatically.  The root cardinality
s and separation d are independent. -/
theorem fixed_root_fiber_packing_bound_general
    {H B : Family α} {W P : Edge α} {v : α} {r s d : ℕ}
    (hH : Admissible H) (hBH : B ⊆ H) (hBuniform : Uniform r B)
    (hW : ∀ E ∈ B, E ⊆ W) (hvW : v ∉ W)
    (hPcard : P.card = s) (hs : 1 ≤ s) (hd : 1 ≤ d)
    (hClean : ∀ E ∈ B, P ⊆ E → ∀ j : ℕ, 1 ≤ j → j < d →
      ∀ Q : Edge α, Q ⊆ E \ P → Q.card = j →
        Q ∉ badMissingSets H W v r j
          ((W.card - r - j).choose (r - 1 - j))) :
    (B.filter fun E => P ⊆ E).card ≤
      if d ≤ r - s then W.card.choose (r - s - d + 1) else 1 := by
  classical
  let T := fixedRootTailFamily B P
  have hRealize : ∀ T₀ ∈ T, ∃ E ∈ B, P ⊆ E ∧ E \ P = T₀ := by
    intro T₀ hT
    obtain ⟨E, hE, hEq⟩ := Finset.mem_image.mp hT
    exact ⟨E, (Finset.mem_filter.mp hE).1,
      (Finset.mem_filter.mp hE).2, hEq⟩
  have hSub : ∀ A ∈ T, A ⊆ W := by
    intro A hA
    obtain ⟨E, hE, hEq⟩ := Finset.mem_image.mp hA
    rw [← hEq]
    exact Finset.sdiff_subset.trans (hW E (Finset.mem_filter.mp hE).1)
  have hUniform : Uniform (r - s) T := by
    intro A hA
    obtain ⟨E, hE, hEq⟩ := Finset.mem_image.mp hA
    rw [← hEq, Finset.card_sdiff_of_subset (Finset.mem_filter.mp hE).2,
      hBuniform (Finset.mem_filter.mp hE).1, hPcard]
  have hDistance : ∀ ⦃A B₀ : Edge α⦄, A ∈ T → B₀ ∈ T →
      A ≠ B₀ → d ≤ (A \ B₀).card := by
    intro A B₀ hA hB hAB
    obtain ⟨E, hEB, hPE, hET⟩ := hRealize A hA
    obtain ⟨F, hFB, hPF, hFS⟩ := hRealize B₀ hB
    have hEF : E ≠ F := by
      intro hEq
      subst F
      have hEqTail : A = B₀ := by rw [← hET, ← hFS]
      exact hAB hEqTail
    have hDist := fixed_root_tails_distance_threshold hH
      (hBH hEB) (hBH hFB) hEF (hW E hEB) (hW F hFB)
      (hBuniform hEB) (hBuniform hFB) hvW hPE hPF hPcard hs
      (fun j hj hjs Q hQE hQcard =>
        hClean E hEB hPE j hj hjs Q hQE hQcard)
      (fun j hj hjs Q hQF hQcard =>
        hClean F hFB hPF j hj hjs Q hQF hQcard)
    have hDiffTail : (E \ P) \ (F \ P) = E \ F := by
      ext x
      simp only [Finset.mem_sdiff]
      constructor
      · rintro ⟨⟨hxE, hxnotP⟩, hxnotF⟩
        refine ⟨hxE, ?_⟩
        intro hxF
        exact hxnotF ⟨hxF, hxnotP⟩
      · rintro ⟨hxE, hxnotF⟩
        refine ⟨⟨hxE, ?_⟩, ?_⟩
        · intro hxP
          exact hxnotF (hPF hxP)
        · intro hxTailF
          exact hxnotF hxTailF.1
    rw [← hDiffTail, hET, hFS] at hDist
    exact hDist
  have hBound :
      T.card ≤ if d ≤ r - s then W.card.choose (r - s - d + 1) else 1 := by
    by_cases hRank : d ≤ r - s
    · have hPack := distance_packing_choose_bound hSub hUniform hDistance hRank
      have hChoosePos : 1 ≤ (r - s).choose (r - s - d + 1) := by
        have := Nat.choose_pos (show r - s - d + 1 ≤ r - s by omega)
        omega
      have hMul : T.card ≤
          T.card * (r - s).choose (r - s - d + 1) :=
        Nat.le_mul_of_pos_right _ (by omega)
      simp only [ite_eq_left hRank]
      omega
    · have hOne := distance_packing_at_most_one (_W := W)
        hUniform hDistance (by omega)
      simpa only [ite_eq_right hRank] using hOne
  have hInj : Set.InjOn (fun E : Edge α => E \ P)
      (↑(B.filter fun E => P ⊆ E) : Set (Edge α)) := by
    intro E hE F hF hEq
    have hPE := (Finset.mem_filter.mp hE).2
    have hPF := (Finset.mem_filter.mp hF).2
    calc
      E = (E \ P) ∪ P := (Finset.sdiff_union_of_subset hPE).symm
      _ = (F \ P) ∪ P := congrArg (fun X => X ∪ P) hEq
      _ = F := Finset.sdiff_union_of_subset hPF
  have hCard : T.card = (B.filter fun E => P ⊆ E).card := by
    dsimp [T, fixedRootTailFamily]
    exact Finset.card_image_iff.mpr hInj
  rw [hCard] at hBound
  exact hBound

/-- Conditional distance-packing caps for the three bad-pair classes.
The intersecting-pair premise here is stronger than the manuscript's
actual third class: it asks every edge in `B` to have a clean tail.
The actual application first filters out edges containing two disjoint
bad pairs; see `BadPairTailPackingActual`. -/
theorem bad_pair_strata_actual_fiber_bounds
    {H B Bad₂ : Family α} {W : Edge α} {v : α} {r : ℕ}
    (hH : Admissible H) (hBH : B ⊆ H) (hBuniform : Uniform r B)
    (hW : ∀ E ∈ B, E ⊆ W) (hvW : v ∉ W)
    (hBadPairUniform : ∀ P ∈ Bad₂, P.card = 2)
    (hUniqueClean : ∀ P ∈ Bad₂, ∀ E ∈ B, P ⊆ E →
      (Bad₂.filter fun Q => Q ⊆ E).card = 1 →
      ∀ j : ℕ, 1 ≤ j → j < 3 →
        ∀ Q : Edge α, Q ⊆ E \ P → Q.card = j →
          Q ∉ badMissingSets H W v r j
            ((W.card - r - j).choose (r - 1 - j)))
    (hDisjointClean : ∀ P ∈ Bad₂, ∀ R ∈ Bad₂, Disjoint P R →
      ∀ E ∈ B, P ∪ R ⊆ E →
        ∀ j : ℕ, 1 ≤ j → j < 2 →
          ∀ Q : Edge α, Q ⊆ E \ (P ∪ R) → Q.card = j →
            Q ∉ badMissingSets H W v r j
              ((W.card - r - j).choose (r - 1 - j)))
    (hIntersectClean : ∀ P ∈ Bad₂, ∀ R ∈ Bad₂, P ≠ R →
      ¬ Disjoint P R →
      ∀ E ∈ B, P ∪ R ⊆ E →
        ∀ j : ℕ, 1 ≤ j → j < 3 →
          ∀ Q : Edge α, Q ⊆ E \ (P ∪ R) → Q.card = j →
            Q ∉ badMissingSets H W v r j
              ((W.card - r - j).choose (r - 1 - j))) :
    (∀ P ∈ Bad₂,
      (B.filter fun E =>
        P ⊆ E ∧ (Bad₂.filter fun Q => Q ⊆ E).card = 1).card ≤
        if 3 ≤ r - 2 then W.card.choose (r - 2 - 3 + 1) else 1) ∧
    (∀ P ∈ Bad₂, ∀ R ∈ Bad₂, Disjoint P R →
      (B.filter fun E => P ∪ R ⊆ E).card ≤
        if 2 ≤ r - 4 then W.card.choose (r - 4 - 2 + 1) else 1) ∧
    (∀ P ∈ Bad₂, ∀ R ∈ Bad₂, P ≠ R → ¬ Disjoint P R →
      (B.filter fun E => P ∪ R ⊆ E).card ≤
        if 3 ≤ r - 3 then W.card.choose (r - 3 - 3 + 1) else 1) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro P hP
    let B₁ := B.filter fun E => (Bad₂.filter fun Q => Q ⊆ E).card = 1
    have hB₁H : B₁ ⊆ H := fun _ hx => hBH (Finset.mem_filter.mp hx).1
    have hB₁U : Uniform r B₁ := by
      intro E hE
      exact hBuniform (Finset.mem_filter.mp hE).1
    have hB₁W : ∀ E ∈ B₁, E ⊆ W := fun E hx =>
      hW E (Finset.mem_filter.mp hx).1
    have hClean₁ : ∀ E ∈ B₁, P ⊆ E → ∀ j : ℕ, 1 ≤ j → j < 3 →
        ∀ Q : Edge α, Q ⊆ E \ P → Q.card = j →
          Q ∉ badMissingSets H W v r j
            ((W.card - r - j).choose (r - 1 - j)) := by
      intro E hE hPE j hj hjs Q hQ hQcard
      exact hUniqueClean P hP E (Finset.mem_filter.mp hE).1 hPE
        (Finset.mem_filter.mp hE).2 j hj hjs Q hQ hQcard
    have hBound := fixed_root_fiber_packing_bound_general
      hH hB₁H hB₁U hB₁W hvW (hBadPairUniform P hP)
      (by omega) (by omega) hClean₁
    have hEq : (B₁.filter fun E => P ⊆ E) =
        B.filter fun E =>
          P ⊆ E ∧ (Bad₂.filter fun Q => Q ⊆ E).card = 1 := by
      ext E
      simp [B₁, and_comm, and_left_comm]
    rw [← hEq]
    exact hBound
  · intro P hP R hR hDisj
    let S := P ∪ R
    let B₂ := B.filter fun E => S ⊆ E
    have hSCard : S.card = 4 := by
      dsimp [S]
      rw [Finset.card_union_of_disjoint hDisj,
        hBadPairUniform P hP, hBadPairUniform R hR]
    have hB₂H : B₂ ⊆ H := fun _ hx => hBH (Finset.mem_filter.mp hx).1
    have hB₂U : Uniform r B₂ := by
      intro E hE
      exact hBuniform (Finset.mem_filter.mp hE).1
    have hB₂W : ∀ E ∈ B₂, E ⊆ W := fun E hx =>
      hW E (Finset.mem_filter.mp hx).1
    have hClean₂ : ∀ E ∈ B₂, S ⊆ E → ∀ j : ℕ, 1 ≤ j → j < 2 →
        ∀ Q : Edge α, Q ⊆ E \ S → Q.card = j →
          Q ∉ badMissingSets H W v r j
            ((W.card - r - j).choose (r - 1 - j)) := by
      intro E hE hSE j hj hjs Q hQ hQcard
      exact hDisjointClean P hP R hR hDisj E
        (Finset.mem_filter.mp hE).1 (Finset.mem_filter.mp hE).2
        j hj hjs Q hQ hQcard
    have hBound := fixed_root_fiber_packing_bound_general
      hH hB₂H hB₂U hB₂W hvW hSCard (by omega) (by omega) hClean₂
    have hEq : (B₂.filter fun E => S ⊆ E) = B₂ := by
      ext E
      simp [B₂, S]
    rw [hEq] at hBound
    simpa [B₂, S, hSCard] using hBound
  · intro P hP R hR hPR hNotDisj
    let S := P ∪ R
    have hInterCard : (P ∩ R).card = 1 := by
      have hPos : 0 < (P ∩ R).card :=
        Finset.card_pos.mpr (Finset.not_disjoint_iff_nonempty_inter.mp hNotDisj)
      have hLe : (P ∩ R).card ≤ 2 :=
        (Finset.card_le_card (Finset.inter_subset_left)).trans_eq
          (hBadPairUniform P hP)
      by_contra hNotOne
      have hTwo : (P ∩ R).card = 2 := by omega
      have hInterEq : P ∩ R = P :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left
          (by rw [hTwo, hBadPairUniform P hP])
      have hSub : P ⊆ R := by
        intro x hx
        have hxI : x ∈ P ∩ R := by rw [hInterEq]; exact hx
        exact (Finset.mem_inter.mp hxI).2
      have hEq := Finset.eq_of_subset_of_card_le hSub
        (by rw [hBadPairUniform P hP, hBadPairUniform R hR])
      exact hPR hEq
    have hSCard : S.card = 3 := by
      dsimp [S]
      have h := Finset.card_union_add_card_inter P R
      rw [hBadPairUniform P hP, hBadPairUniform R hR, hInterCard] at h
      omega
    let B₃ := B.filter fun E => S ⊆ E
    have hB₃H : B₃ ⊆ H := fun _ hx => hBH (Finset.mem_filter.mp hx).1
    have hB₃U : Uniform r B₃ := by
      intro E hE
      exact hBuniform (Finset.mem_filter.mp hE).1
    have hB₃W : ∀ E ∈ B₃, E ⊆ W := fun E hx =>
      hW E (Finset.mem_filter.mp hx).1
    have hClean₃ : ∀ E ∈ B₃, S ⊆ E → ∀ j : ℕ, 1 ≤ j → j < 3 →
        ∀ Q : Edge α, Q ⊆ E \ S → Q.card = j →
          Q ∉ badMissingSets H W v r j
            ((W.card - r - j).choose (r - 1 - j)) := by
      intro E hE hSE j hj hjs Q hQ hQcard
      exact hIntersectClean P hP R hR hPR hNotDisj E
        (Finset.mem_filter.mp hE).1 (Finset.mem_filter.mp hE).2
        j hj hjs Q hQ hQcard
    have hBound := fixed_root_fiber_packing_bound_general
      hH hB₃H hB₃U hB₃W hvW hSCard (by omega) (by omega) hClean₃
    have hEq : (B₃.filter fun E => S ⊆ E) = B₃ := by
      ext E
      simp [B₃, S]
    rw [hEq] at hBound
    simpa [B₃, S, hSCard] using hBound

/-- A conditional pair-edge deletion bound with binomial packing caps.
For the actual §IV.2.1 deletion classes, use the filtered version in
`BadPairTailPackingActual`, which imposes the no-disjoint-pair condition
before the intersecting-pair cap is applied. -/
theorem bad_pair_edges_explicit_deletion_bound
    {H B Bad₂ : Family α} {W : Edge α} {v : α} {r : ℕ}
    (hH : Admissible H) (hBH : B ⊆ H) (hBuniform : Uniform r B)
    (hW : ∀ E ∈ B, E ⊆ W) (hvW : v ∉ W)
    (hBadPairUniform : ∀ P ∈ Bad₂, P.card = 2)
    (hUniqueClean : ∀ P ∈ Bad₂, ∀ E ∈ B, P ⊆ E →
      (Bad₂.filter fun Q => Q ⊆ E).card = 1 →
      ∀ j : ℕ, 1 ≤ j → j < 3 →
        ∀ Q : Edge α, Q ⊆ E \ P → Q.card = j →
          Q ∉ badMissingSets H W v r j
            ((W.card - r - j).choose (r - 1 - j)))
    (hDisjointClean : ∀ P ∈ Bad₂, ∀ R ∈ Bad₂, Disjoint P R →
      ∀ E ∈ B, P ∪ R ⊆ E →
        ∀ j : ℕ, 1 ≤ j → j < 2 →
          ∀ Q : Edge α, Q ⊆ E \ (P ∪ R) → Q.card = j →
            Q ∉ badMissingSets H W v r j
              ((W.card - r - j).choose (r - 1 - j)))
    (hIntersectClean : ∀ P ∈ Bad₂, ∀ R ∈ Bad₂, P ≠ R →
      ¬ Disjoint P R →
      ∀ E ∈ B, P ∪ R ⊆ E →
        ∀ j : ℕ, 1 ≤ j → j < 3 →
          ∀ Q : Edge α, Q ⊆ E \ (P ∪ R) → Q.card = j →
            Q ∉ badMissingSets H W v r j
              ((W.card - r - j).choose (r - 1 - j))) :
    (badPairEdges B Bad₂).card ≤
      Bad₂.card * (if 3 ≤ r - 2 then W.card.choose (r - 2 - 3 + 1) else 1) +
        Bad₂.card * (Bad₂.card *
          (if 2 ≤ r - 4 then W.card.choose (r - 4 - 2 + 1) else 1)) +
        Bad₂.card * (Bad₂.card *
          (if 3 ≤ r - 3 then W.card.choose (r - 3 - 3 + 1) else 1)) := by
  have hCaps := bad_pair_strata_actual_fiber_bounds hH hBH hBuniform
    hW hvW hBadPairUniform hUniqueClean hDisjointClean hIntersectClean
  rcases hCaps with ⟨hC₁, hC₂, hC₃⟩
  have hBound := bad_pair_edges_deletion_bound hC₁ hC₂ hC₃
  exact hBound

end JSP523
