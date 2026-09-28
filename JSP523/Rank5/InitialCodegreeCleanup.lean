import JSP523.Rank5.FarStarTail
import JSP523.Rank5.HeavyRootActual
import JSP523.Rank5.RegularizationFinite
import JSP523.Rank5.RegularizationNatural
import Mathlib.Order.Interval.Finset.Nat

set_option linter.style.haveILetI false

/-!
# Initial codegree cleanup for IV.5.1

The cap on a root extended by one vertex follows from uniformity alone.
The actual heavy-root matching theorem then covers every heavy root,
including facets of size `r-1`. Removing the cover costs at most its size
times the maximum vertex degree of the current family.
-/

namespace JSP523.Rank5

open Finset
open scoped BigOperators

/-- Uniformity alone gives the off-root cap needed for the initial heavy-root
matching, with no codegree hypothesis on the parent family. -/
theorem initial_off_root_codegree_cap
    {n r s : ℕ} (H : Family (Fin n))
    (hUniform : Uniform r H)
    (P : Edge (Fin n)) (hP : P.card = s)
    (x : Fin n) (hx : x ∉ P) :
    (H.filter (fun E => P ∪ {x} ⊆ E)).card ≤
      (n - (s + 1)).choose (r - (s + 1)) := by
  have hCard : (P ∪ {x}).card = s + 1 := by
    rw [Finset.union_singleton, Finset.card_insert_of_notMem hx, hP]
  exact uniform_codegree_le_ambient_choose H (P ∪ {x}) hUniform hCard

/-- A concrete small cover of every oversized codegree, including facets.
The finite scalar gap is precisely the Bonferroni matching check. -/
theorem exists_initial_all_ranks_codegree_cover
    {n r : ℕ} (H : Family (Fin n))
    (d a : ℕ → ℕ)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hr : 4 ≤ r)
    (hGap : ∀ s, 1 ≤ s → s ≤ r - 1 →
      n.choose (r - s) +
        a s * a s * ((r - s) *
          ((n - (s + 1)).choose (r - (s + 1)))) < a s * d s) :
    ∃ Y : Edge (Fin n),
      Y.card ≤ ∑ s ∈ Finset.Icc 1 (r - 1), s * (a s - 1) ∧
      (∀ s, 1 ≤ s → s ≤ r - 1 →
        ∀ S : Edge (Fin n), S.card = s → Disjoint S Y →
          (H.filter (fun E => S ⊆ E)).card ≤ d s) := by
  classical
  let V : Edge (Fin n) := Finset.univ
  let I := Finset.Icc 1 (r - 1)
  have hRank : ∀ s ∈ I,
      ∃ Ys : Edge (Fin n), Ys.card ≤ s * (a s - 1) ∧
        (∀ S : Edge (Fin n), S.card = s → Disjoint S Ys →
          (H.filter (fun E => S ⊆ E)).card ≤ d s) := by
    intro s hsI
    have hs : 1 ≤ s := (Finset.mem_Icc.mp hsI).1
    have hsr : s ≤ r - 1 := (Finset.mem_Icc.mp hsI).2
    let R : Family (Fin n) :=
      (V.powersetCard s).filter
        (fun P => d s < (H.filter (fun E => P ⊆ E)).card)
    have hRinside : ∀ P ∈ R, P ⊆ V := by
      intro P hP
      exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hP).1).1
    have hRsize : ∀ P ∈ R, P.card = s := by
      intro P hP
      exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hP).1).2
    have hRheavy : ∀ P ∈ R,
        d s < (H.filter (fun E => P ⊆ E)).card := by
      intro P hP
      exact (Finset.mem_filter.mp hP).2
    have hComplete : ∀ S ∈ V.powersetCard s,
        d s < (H.filter (fun E => S ⊆ E)).card → S ∈ R := by
      intro S hS hD
      exact Finset.mem_filter.mpr ⟨hS, hD⟩
    have hOff : ∀ P ∈ R, ∀ x : Fin n, x ∉ P →
        (H.filter (fun E => P ∪ {x} ⊆ E)).card ≤
          (n - (s + 1)).choose (r - (s + 1)) := by
      intro P hP x hx
      exact initial_off_root_codegree_cap H hUniform P (hRsize P hP) x hx
    have hst : s + (r - s) = r := by omega
    have ht : 1 ≤ r - s := by omega
    have hGap' : (V.powersetCard (r - s)).card +
        a s * a s * ((r - s) *
          ((n - (s + 1)).choose (r - (s + 1)))) < a s * d s := by
      simpa only [V, Finset.card_powersetCard, Finset.card_univ,
        Fintype.card_fin] using hGap s hs hsr
    obtain ⟨Ys, _, _, hYsize, hYcap⟩ :=
      actual_common_prefix_cover_degree_cap H V R r s (r - s)
        (d s) ((n - (s + 1)).choose (r - (s + 1))) (a s)
        hAdm hUniform (by intro E hE; exact Finset.subset_univ E)
        hst hs ht hRinside hRsize hRheavy hComplete hOff hGap'
    refine ⟨Ys, hYsize, ?_⟩
    intro S hS hSY
    exact hYcap S (Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ S, hS⟩) hSY
  let Ys : ℕ → Edge (Fin n) := fun s =>
    if hs : s ∈ I then Classical.choose (hRank s hs) else ∅
  have hYs : ∀ s ∈ I,
      (Ys s).card ≤ s * (a s - 1) ∧
      (∀ S : Edge (Fin n), S.card = s → Disjoint S (Ys s) →
        (H.filter (fun E => S ⊆ E)).card ≤ d s) := by
    intro s hs
    dsimp [Ys]
    rw [dite_eq_left hs]
    exact Classical.choose_spec (hRank s hs)
  let Y : Edge (Fin n) := I.biUnion Ys
  have hYsize : Y.card ≤ ∑ s ∈ I, s * (a s - 1) := by
    calc
      Y.card ≤ ∑ s ∈ I, (Ys s).card := Finset.card_biUnion_le
      _ ≤ ∑ s ∈ I, s * (a s - 1) := by
        apply Finset.sum_le_sum
        intro s hs
        exact (hYs s hs).1
  refine ⟨Y, hYsize, ?_⟩
  intro s hs hsr S hS hSY
  have hsI : s ∈ I := Finset.mem_Icc.mpr ⟨hs, hsr⟩
  have hSYs : Disjoint S (Ys s) := by
    apply Finset.disjoint_left.mpr
    intro x hxS hxYs
    exact (Finset.disjoint_left.mp hSY) hxS
      (Finset.mem_biUnion.mpr ⟨s, hsI, hxYs⟩)
  exact (hYs s hsI).2 S hS hSYs

/-- Deleting every edge meeting a vertex set costs at most the set size
times the actual maximum vertex degree. -/
theorem edges_meeting_set_le_max_vertex_degree
    {n : ℕ} (H : Family (Fin n)) (Y : Edge (Fin n)) (M : ℕ)
    (hMax : ∀ z : Fin n,
      (H.filter (fun E => z ∈ E)).card ≤ M) :
    H.card - (H.filter (fun E => Disjoint E Y)).card ≤ Y.card * M := by
  classical
  let K := H.filter (fun E => Disjoint E Y)
  let R := H \ K
  have hSub : R ⊆ Y.biUnion (fun z => H.filter (fun E => z ∈ E)) := by
    intro E hE
    obtain ⟨hEH, hEK⟩ := Finset.mem_sdiff.mp hE
    have hNotDisj : ¬ Disjoint E Y := by
      intro hDisj
      exact hEK (Finset.mem_filter.mpr ⟨hEH, hDisj⟩)
    have hInter : (E ∩ Y).Nonempty := by
      by_contra hEmpty
      have hEmpty' : E ∩ Y = ∅ := Finset.not_nonempty_iff_eq_empty.mp hEmpty
      exact hNotDisj (Finset.disjoint_iff_inter_eq_empty.mpr hEmpty')
    obtain ⟨z, hz⟩ := hInter
    obtain ⟨hzE, hzY⟩ := Finset.mem_inter.mp hz
    exact Finset.mem_biUnion.mpr
      ⟨z, hzY, Finset.mem_filter.mpr ⟨hEH, hzE⟩⟩
  have hRcard : R.card = H.card - K.card := by
    have hKsub : K ⊆ H := Finset.filter_subset _ _
    have hEq := Finset.card_sdiff_add_card_eq_card hKsub
    change R.card + K.card = H.card at hEq
    omega
  calc
    H.card - K.card = R.card := hRcard.symm
    _ ≤ (Y.biUnion (fun z => H.filter (fun E => z ∈ E))).card :=
      Finset.card_le_card hSub
    _ ≤ Y.card * M :=
      Finset.card_biUnion_le_card_mul Y _ M (by intro z hz; exact hMax z)

/-- Exact degree-sum identity for an actual uniform family. -/
theorem sum_vertex_degrees_eq_rank_mul_card
    {n r : ℕ} (H : Family (Fin n)) (hUniform : Uniform r H) :
    (∑ z : Fin n, (H.filter (fun E => z ∈ E)).card) = r * H.card := by
  classical
  calc
    (∑ z : Fin n, (H.filter (fun E => z ∈ E)).card) =
        ∑ z : Fin n, ∑ E ∈ H, if z ∈ E then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ E ∈ H, ∑ z : Fin n, if z ∈ E then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ E ∈ H, E.card := by
      apply Finset.sum_congr rfl
      intro E hE
      rw [← Finset.sum_filter]
      simp
    _ = r * H.card := by
      calc
        (∑ E ∈ H, E.card) = ∑ E ∈ H, r := by
          apply Finset.sum_congr rfl
          intro E hE
          exact hUniform hE
        _ = r * H.card := by simp [mul_comm]

/-- The vertices above a degree threshold form a small actual set whenever
the threshold exceeds the average on `h+1` vertices. This gives the
finite replacement for choosing the `h` largest-degree vertices. -/
theorem exists_high_degree_vertex_cover
    {n r h T : ℕ} (H : Family (Fin n))
    (hUniform : Uniform r H)
    (hBudget : r * H.card < (h + 1) * T) :
    ∃ X : Edge (Fin n), X.card ≤ h ∧
      ∀ z : Fin n, z ∉ X →
        (H.filter (fun E => z ∈ E)).card < T := by
  classical
  let X : Edge (Fin n) :=
    Finset.univ.filter (fun z => T ≤ (H.filter (fun E => z ∈ E)).card)
  have hLower : X.card * T ≤
      ∑ z ∈ X, (H.filter (fun E => z ∈ E)).card := by
    calc
      X.card * T = ∑ z ∈ X, T := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro z hz
        exact (Finset.mem_filter.mp hz).2
  have hUpper : (∑ z ∈ X, (H.filter (fun E => z ∈ E)).card) ≤
      r * H.card := by
    calc
      _ ≤ ∑ z : Fin n, (H.filter (fun E => z ∈ E)).card :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = r * H.card := sum_vertex_degrees_eq_rank_mul_card H hUniform
  have hXcard : X.card ≤ h := by
    by_contra hneg
    have hge : h + 1 ≤ X.card := by omega
    have hprod := Nat.mul_le_mul_right T hge
    omega
  refine ⟨X, hXcard, ?_⟩
  intro z hz
  have hznot : ¬ T ≤ (H.filter (fun E => z ∈ E)).card := by
    intro hT
    exact hz (Finset.mem_filter.mpr ⟨Finset.mem_univ z, hT⟩)
  omega

/-- Avoiding a set that contains all high-degree vertices reduces the
maximum degree of the actual filtered family to the chosen threshold. -/
theorem avoiding_high_degree_cover_max_degree
    {n T : ℕ} (H : Family (Fin n)) (X : Edge (Fin n))
    (hOutside : ∀ z : Fin n, z ∉ X →
      (H.filter (fun E => z ∈ E)).card < T) :
    ∀ z : Fin n,
      ((H.filter (fun E => Disjoint E X)).filter
        (fun E => z ∈ E)).card ≤ T := by
  classical
  intro z
  by_cases hzX : z ∈ X
  · have hEmpty :
        (H.filter (fun E => Disjoint E X)).filter
          (fun E => z ∈ E) = ∅ := by
      ext E
      constructor
      · intro hE
        obtain ⟨hEF, hzE⟩ := Finset.mem_filter.mp hE
        have hDisj := (Finset.mem_filter.mp hEF).2
        exact False.elim ((Finset.disjoint_left.mp hDisj) hzE hzX)
      · intro hE
        simp at hE
    simp [hEmpty]
  · have hD : (H.filter (fun E => ({z} : Edge (Fin n)) ⊆ E)).card ≤ T := by
      simpa only [Finset.singleton_subset_iff] using
        Nat.le_of_lt (hOutside z hzX)
    simpa only [Finset.singleton_subset_iff] using
      (completion_codegree_mono (Finset.filter_subset _ _)
        ({z} : Edge (Fin n))).trans hD

/-- Finite IV.5.1 cleanup from an actual admissible family with a maximum
vertex-degree cap. All higher codegree caps, including facets, hold for the
retained actual subfamily; its deletion cost is explicit. -/
theorem initial_codegree_cleanup_from_max_degree
    {n r M : ℕ} (H : Family (Fin n)) (d a : ℕ → ℕ)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hr : 4 ≤ r)
    (hMax : ∀ z : Fin n,
      (H.filter (fun E => z ∈ E)).card ≤ M)
    (hGap : ∀ s, 1 ≤ s → s ≤ r - 1 →
      n.choose (r - s) +
        a s * a s * ((r - s) *
          ((n - (s + 1)).choose (r - (s + 1)))) < a s * d s) :
    ∃ K : Family (Fin n), K ⊆ H ∧ Admissible K ∧ Uniform r K ∧
      (∀ s, 1 ≤ s → s ≤ r - 1 →
        ∀ S : Edge (Fin n), S.card = s →
          (K.filter (fun E => S ⊆ E)).card ≤ d s) ∧
      H.card - K.card ≤
        (∑ s ∈ Finset.Icc 1 (r - 1), s * (a s - 1)) * M := by
  classical
  obtain ⟨Y, hYsize, hYcap⟩ :=
    exists_initial_all_ranks_codegree_cover H d a hAdm hUniform hr hGap
  let K := H.filter (fun E => Disjoint E Y)
  have hKH : K ⊆ H := Finset.filter_subset _ _
  have hAdmK : Admissible K := admissible_mono hKH hAdm
  have hUniformK : Uniform r K := fun E hE => hUniform (hKH hE)
  refine ⟨K, hKH, hAdmK, hUniformK, ?_, ?_⟩
  · intro s hs hsr S hS
    exact avoiding_cover_codegree_le H Finset.univ Y s (d s)
      (by intro E hE; exact Finset.subset_univ E)
      (by
        intro T hT hTY
        exact hYcap s hs hsr T ((Finset.mem_powersetCard.mp hT).2) hTY)
      S hS
  · have hLoss := edges_meeting_set_le_max_vertex_degree H Y M hMax
    exact hLoss.trans (Nat.mul_le_mul_right M hYsize)

/-- The finite IV.5.1 two-stage cleanup. First remove the high-degree
vertices, then cover every heavy root of size `1` through `r-1` in the
remaining actual family. The two deletion costs are charged separately. -/
theorem initial_codegree_cleanup_after_high_degree_removal
    {n r h M T : ℕ} (H : Family (Fin n)) (d a : ℕ → ℕ)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hr : 4 ≤ r)
    (hMax : ∀ z : Fin n,
      (H.filter (fun E => z ∈ E)).card ≤ M)
    (hBudget : r * H.card < (h + 1) * T)
    (hGap : ∀ s, 1 ≤ s → s ≤ r - 1 →
      n.choose (r - s) +
        a s * a s * ((r - s) *
          ((n - (s + 1)).choose (r - (s + 1)))) < a s * d s) :
    ∃ K : Family (Fin n), K ⊆ H ∧ Admissible K ∧ Uniform r K ∧
      (∀ s, 1 ≤ s → s ≤ r - 1 →
        ∀ S : Edge (Fin n), S.card = s →
          (K.filter (fun E => S ⊆ E)).card ≤ d s) ∧
      H.card - K.card ≤ h * M +
        (∑ s ∈ Finset.Icc 1 (r - 1), s * (a s - 1)) * T := by
  classical
  obtain ⟨X, hXsize, hOutside⟩ :=
    exists_high_degree_vertex_cover H hUniform hBudget
  let H₀ := H.filter (fun E => Disjoint E X)
  have hH₀sub : H₀ ⊆ H := Finset.filter_subset _ _
  have hAdm₀ : Admissible H₀ := admissible_mono hH₀sub hAdm
  have hUniform₀ : Uniform r H₀ := fun E hE => hUniform (hH₀sub hE)
  have hMax₀ : ∀ z : Fin n,
      (H₀.filter (fun E => z ∈ E)).card ≤ T := by
    exact avoiding_high_degree_cover_max_degree H X hOutside
  obtain ⟨K, hKH₀, hAdmK, hUniformK, hCaps, hLoss₁⟩ :=
    initial_codegree_cleanup_from_max_degree H₀ d a hAdm₀ hUniform₀
      hr hMax₀ hGap
  have hLoss₀ := edges_meeting_set_le_max_vertex_degree H X M hMax
  have hLoss₀' : H.card - H₀.card ≤ h * M :=
    hLoss₀.trans (Nat.mul_le_mul_right M hXsize)
  have hSplit : H.card - K.card =
      (H.card - H₀.card) + (H₀.card - K.card) := by
    have hHK := Finset.card_le_card (hKH₀.trans hH₀sub)
    have hH₀H := Finset.card_le_card hH₀sub
    have hKH₀card := Finset.card_le_card hKH₀
    omega
  refine ⟨K, hKH₀.trans hH₀sub, hAdmK, hUniformK, hCaps, ?_⟩
  rw [hSplit]
  exact Nat.add_le_add hLoss₀' hLoss₁

/-- A rank-uniform sufficient condition for every initial matching gap.
This is the finite arithmetic behind the manuscript's choice
`τ ≍ log³(n)/√n`: `a` is of order `n/T`, while `a²r < n`. -/
theorem initial_sqrt_scale_gap
    (n r s T a : ℕ) (hn : 1 ≤ n) (hr : 4 ≤ r)
    (hs : 1 ≤ s) (hsr : s ≤ r - 1)
    (haT : 3 * n ≤ a * T)
    (haSq : a * a * r < n) :
    n.choose (r - s) +
      a * a * ((r - s) *
        ((n - (s + 1)).choose (r - (s + 1)))) <
      a * (T * n ^ (r - s - 1)) := by
  let t := r - s
  have ht : 1 ≤ t := by dsimp [t]; omega
  have hExp : t - 1 = r - (s + 1) := by dsimp [t]; omega
  have hChoose : n.choose t ≤ n ^ t := Nat.choose_le_pow n t
  have hOff : (n - (s + 1)).choose (r - (s + 1)) ≤ n ^ (t - 1) := by
    rw [← hExp]
    exact (Nat.choose_le_pow _ _).trans
      (Nat.pow_le_pow_left (Nat.sub_le n (s + 1)) _)
  have hCoef : a * a * t < n := by
    have htr : t ≤ r := by dsimp [t]; omega
    exact (Nat.mul_le_mul_left (a * a) htr).trans_lt haSq
  have hPow : n * n ^ (t - 1) = n ^ t := by
    have he : t - 1 + 1 = t := by omega
    rw [Nat.mul_comm, ← pow_succ, he]
  have hOverlap :
      a * a * (t * ((n - (s + 1)).choose (r - (s + 1)))) < n ^ t := by
    have hPos : 0 < n ^ (t - 1) := pow_pos (by omega) _
    calc
      a * a * (t * ((n - (s + 1)).choose (r - (s + 1)))) ≤
          (a * a * t) * n ^ (t - 1) := by
        rw [← mul_assoc]
        exact Nat.mul_le_mul_left _ hOff
      _ < n * n ^ (t - 1) :=
        (Nat.mul_lt_mul_right hPos).2 hCoef
      _ = n ^ t := hPow
  have hTail : 3 * n ^ t ≤ a * (T * n ^ (t - 1)) := by
    calc
      3 * n ^ t = (3 * n) * n ^ (t - 1) := by rw [← hPow]; ring
      _ ≤ (a * T) * n ^ (t - 1) := Nat.mul_le_mul_right _ haT
      _ = a * (T * n ^ (t - 1)) := by ring
  dsimp [t] at hChoose hOverlap hTail ⊢
  omega

/-- A simple rank-only estimate for the size of the union of all matched
heavy roots. -/
theorem initial_cover_size_le_rank_square
    (r a : ℕ) :
    (∑ s ∈ Finset.Icc 1 (r - 1), s * (a - 1)) ≤ r * r * a := by
  have hEach : ∀ s ∈ Finset.Icc 1 (r - 1), s * (a - 1) ≤ r * a := by
    intro s hs
    have hsr : s ≤ r := (Finset.mem_Icc.mp hs).2.trans (Nat.sub_le r 1)
    exact (Nat.mul_le_mul hsr (Nat.sub_le a 1)).trans_eq (by rfl)
  have hSum := Finset.sum_le_card_nsmul (Finset.Icc 1 (r - 1))
    (fun s => s * (a - 1)) (r * a) hEach
  have hCard : (Finset.Icc 1 (r - 1)).card ≤ r := by
    rw [Nat.card_Icc]
    omega
  calc
    _ ≤ (Finset.Icc 1 (r - 1)).card * (r * a) := by
      simpa using hSum
    _ ≤ r * (r * a) := Nat.mul_le_mul_right _ hCard
    _ = r * r * a := by ring

/-- The natural-round heavy-root cover obeys its expected `n/T` scale,
using the same rank-square counting lemma as the initial cleanup. -/
theorem discrete_round_cover_times_root_bound
    (n r R : ℕ)
    (hTn : discreteRoundRoot R ≤ n) :
    discreteRoundCoverSize n r R * discreteRoundRoot R ≤
      3 * r * r * n := by
  let T := discreteRoundRoot R
  let a := discreteRoundMultiplier n R
  have hCover : discreteRoundCoverSize n r R ≤ r * r * a := by
    have hSubset : Finset.Icc 1 (r - 2) ⊆ Finset.Icc 1 (r - 1) := by
      intro s hs
      simp only [Finset.mem_Icc] at hs ⊢
      omega
    have hSum : (∑ s ∈ Finset.Icc 1 (r - 2), s * (a - 1)) ≤
        ∑ s ∈ Finset.Icc 1 (r - 1), s * (a - 1) :=
      Finset.sum_le_sum_of_subset hSubset
    change discreteRoundCoverSize n r R ≤
      ∑ s ∈ Finset.Icc 1 (r - 1), s * (a - 1) at hSum
    exact hSum.trans (initial_cover_size_le_rank_square r a)
  have hDiv := Nat.mod_add_div (2 * n) T
  have haHi : a * T ≤ 2 * n + T := by
    dsimp [a, T, discreteRoundMultiplier]
    rw [Nat.add_mul, Nat.one_mul]
    rw [Nat.mul_comm (discreteRoundRoot R)
      (2 * n / discreteRoundRoot R)] at hDiv
    omega
  have haN : a * T ≤ 3 * n := by dsimp [T] at hTn haHi ⊢; omega
  calc
    discreteRoundCoverSize n r R * T ≤ (r * r * a) * T :=
      Nat.mul_le_mul_right T hCover
    _ = (r * r) * (a * T) := by ring
    _ ≤ (r * r) * (3 * n) := Nat.mul_le_mul_left _ haN
    _ = 3 * r * r * n := by ring

/-- The cover-pair term of one natural round has an arbitrary fixed
integer saving against `n^(r-1)` once the current scale is large. -/
theorem discrete_round_cover_pair_rate
    (n r R m : ℕ) (hr : 4 ≤ r)
    (hRpos : 1 ≤ R) (hTn : discreteRoundRoot R ≤ n)
    (hmR : (4 * m) ^ 4 ≤ R) :
    m * ((discreteRoundCoverSize n r R).choose 2 *
      (R * n ^ (r - 3))) ≤ 9 * r ^ 4 * n ^ (r - 1) := by
  let T := discreteRoundRoot R
  let h := discreteRoundCoverSize n r R
  have hRatio := discrete_round_root_square_ratio_bound R (4 * m)
    hRpos hmR
  have hmRT : m * R ≤ T ^ 2 := by
    dsimp [T] at hRatio ⊢
    nlinarith [hRatio]
  have hCoverT : h * T ≤ 3 * r * r * n :=
    discrete_round_cover_times_root_bound n r R hTn
  have hCoverSq := Nat.pow_le_pow_left hCoverT 2
  have hChoose : h.choose 2 ≤ h ^ 2 := Nat.choose_le_pow h 2
  have hExp : 2 + (r - 3) = r - 1 := by omega
  have hNpow : n ^ 2 * n ^ (r - 3) = n ^ (r - 1) := by
    rw [← pow_add, hExp]
  calc
    m * (h.choose 2 * (R * n ^ (r - 3))) ≤
        m * (h ^ 2 * (R * n ^ (r - 3))) :=
      Nat.mul_le_mul_left m (Nat.mul_le_mul_right _ hChoose)
    _ = (h ^ 2 * (m * R)) * n ^ (r - 3) := by ring
    _ ≤ (h ^ 2 * T ^ 2) * n ^ (r - 3) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hmRT)
    _ = (h * T) ^ 2 * n ^ (r - 3) := by ring
    _ ≤ (3 * r * r * n) ^ 2 * n ^ (r - 3) :=
      Nat.mul_le_mul_right _ hCoverSq
    _ = 9 * r ^ 4 * n ^ (r - 1) := by rw [← hNpow]; ring

theorem discrete_round_cover_pair_star_rate
    (n r R m : ℕ) (hr : 4 ≤ r)
    (hn : 2 * (r - 1) + 1 ≤ n)
    (hRpos : 1 ≤ R) (hTn : discreteRoundRoot R ≤ n)
    (hmR : (4 * m) ^ 4 ≤ R) :
    m * ((discreteRoundCoverSize n r R).choose 2 *
      (R * n ^ (r - 3))) ≤
        9 * r ^ 4 * (2 ^ (r - 1) * (r - 1).factorial) *
          (n - 1).choose (r - 1) := by
  have hPair := discrete_round_cover_pair_rate n r R m hr hRpos hTn hmR
  have hStar := far_star_power_le_choose_multiple n (r - 1) hn
  calc
    _ ≤ 9 * r ^ 4 * n ^ (r - 1) := hPair
    _ ≤ 9 * r ^ 4 * (2 ^ (r - 1) * (r - 1).factorial) *
        (n - 1).choose (r - 1) := by
      have hMul := Nat.mul_le_mul_left (9 * r ^ 4) hStar
      nlinarith [hMul]

/-- A direct arbitrary-factor saving for the natural-round radius layer.
The scalar condition `m^(r-1)(r-1)! R ≤ n` follows from `R³ ≤ n²`
once `n` is sufficiently large for a fixed `m` and rank. -/
theorem discrete_round_radius_layer_rate
    (n r R m : ℕ) (hr : 4 ≤ r)
    (hScale : m ^ (r - 1) * (r - 1).factorial * R ≤ n)
    (hmn : m * r ≤ n) :
    m * (((discreteRoundRadius n r R + (r - 1)) *
      n.choose (r - 2)) / (r - 1)) ≤ 2 * n ^ (r - 1) := by
  let k := r - 1
  let U := Nat.nthRoot k (k.factorial * (R * n ^ (k - 1)))
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hU : U ^ k ≤ k.factorial * (R * n ^ (k - 1)) :=
    Nat.pow_nthRoot_le (Or.inl (by omega))
  have hPow : (m * U) ^ k ≤ n ^ k := by
    calc
      (m * U) ^ k = m ^ k * U ^ k := by rw [mul_pow]
      _ ≤ m ^ k * (k.factorial * (R * n ^ (k - 1))) :=
        Nat.mul_le_mul_left _ hU
      _ = (m ^ k * k.factorial * R) * n ^ (k - 1) := by ring
      _ ≤ n * n ^ (k - 1) := Nat.mul_le_mul_right _ hScale
      _ = n ^ k := by
        have he : k - 1 + 1 = k := by omega
        rw [Nat.mul_comm, ← pow_succ, he]
  have hmU : m * U ≤ n := by
    by_contra h
    have hlt : n < m * U := by omega
    have hltPow := Nat.pow_lt_pow_left hlt (by omega : k ≠ 0)
    omega
  have hL : discreteRoundRadius n r R = U + 1 := by
    dsimp [discreteRoundRadius, U, k]
    congr 1
  have hRadius : m * (discreteRoundRadius n r R + (r - 1)) ≤ 2 * n := by
    rw [hL]
    have he : 1 + (r - 1) = r := by omega
    have hRewrite : m * (U + 1 + (r - 1)) = m * U + m * r := by
      rw [add_assoc, he]
      ring
    rw [hRewrite]
    omega
  have hChoose : n.choose (r - 2) ≤ n ^ (r - 2) :=
    Nat.choose_le_pow n (r - 2)
  have hDiv : ((discreteRoundRadius n r R + (r - 1)) *
      n.choose (r - 2)) / (r - 1) ≤
      (discreteRoundRadius n r R + (r - 1)) * n.choose (r - 2) :=
    Nat.div_le_self _ _
  have hExp : 1 + (r - 2) = r - 1 := by omega
  calc
    m * (((discreteRoundRadius n r R + (r - 1)) *
        n.choose (r - 2)) / (r - 1)) ≤
      m * ((discreteRoundRadius n r R + (r - 1)) *
        n.choose (r - 2)) := Nat.mul_le_mul_left _ hDiv
    _ = (m * (discreteRoundRadius n r R + (r - 1))) *
        n.choose (r - 2) := by ring
    _ ≤ (2 * n) * n.choose (r - 2) :=
      Nat.mul_le_mul_right _ hRadius
    _ ≤ (2 * n) * n ^ (r - 2) :=
      Nat.mul_le_mul_left _ hChoose
    _ = 2 * n ^ (r - 1) := by
      calc
        (2 * n) * n ^ (r - 2) = 2 * (n ^ (r - 2) * n) := by ring
        _ = 2 * n ^ (r - 1) := by
          rw [← pow_succ]
          rw [show r - 2 + 1 = r - 1 by omega]

theorem scale_cube_separation
    (n R c : ℕ) (hR23 : R ^ 3 ≤ n ^ 2)
    (hLarge : c ^ 3 ≤ n) :
    c * R ≤ n := by
  by_contra h
  have hlt : n < c * R := by omega
  have hltCube := Nat.pow_lt_pow_left hlt (by norm_num : 3 ≠ 0)
  have hUpper : (c * R) ^ 3 ≤ n ^ 3 := by
    calc
      (c * R) ^ 3 = c ^ 3 * R ^ 3 := by ring
      _ ≤ n * n ^ 2 := Nat.mul_le_mul hLarge hR23
      _ = n ^ 3 := by ring
  omega

/-- The radius saving follows directly from the manuscript's
`R³ ≤ n²` scale condition and one fixed finite threshold. -/
theorem discrete_round_radius_layer_rate_at_natural_scale
    (n r R m : ℕ) (hr : 4 ≤ r)
    (hR23 : R ^ 3 ≤ n ^ 2)
    (hLarge : (m ^ (r - 1) * (r - 1).factorial) ^ 3 ≤ n)
    (hmn : m * r ≤ n) :
    m * (((discreteRoundRadius n r R + (r - 1)) *
      n.choose (r - 2)) / (r - 1)) ≤ 2 * n ^ (r - 1) := by
  exact discrete_round_radius_layer_rate n r R m hr
    (scale_cube_separation n R _ hR23 hLarge) hmn

theorem discrete_round_collision_inner_bound
    (n r R : ℕ) (hn : 1 ≤ n) (hr : 4 ≤ r) :
    (r - 1) * (r - 1) * (R * n ^ (r - 3)) +
      n * (n - 1) * (r - 2) * (R * n ^ (r - 4)) ≤
        2 * r ^ 2 * (R * n ^ (r - 2)) := by
  have hRank₁ : (r - 1) * (r - 1) ≤ r ^ 2 := by
    have hSub : r - 1 ≤ r := Nat.sub_le r 1
    nlinarith
  have hRank₂ : r - 2 ≤ r ^ 2 :=
    (Nat.sub_le r 2).trans
      (le_self_pow (by omega : 1 ≤ r) (by norm_num : 2 ≠ 0))
  have hPow₁ : n ^ (r - 3) ≤ n ^ (r - 2) :=
    Nat.pow_le_pow_right hn (by omega)
  have hPow₂ : n * (n - 1) * n ^ (r - 4) ≤ n ^ (r - 2) := by
    have hSub : n - 1 ≤ n := Nat.sub_le n 1
    have hMul := Nat.mul_le_mul_left n hSub
    have hExp : 2 + (r - 4) = r - 2 := by omega
    calc
      n * (n - 1) * n ^ (r - 4) ≤ n * n * n ^ (r - 4) :=
        Nat.mul_le_mul_right _ hMul
      _ = n ^ (r - 2) := by
        calc
          n * n * n ^ (r - 4) = n ^ 2 * n ^ (r - 4) := by ring
          _ = n ^ (r - 2) := by rw [← pow_add, hExp]
  have hFirst : (r - 1) * (r - 1) * (R * n ^ (r - 3)) ≤
      r ^ 2 * (R * n ^ (r - 2)) := by
    exact (Nat.mul_le_mul_right _ hRank₁).trans
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left R hPow₁))
  have hSecond : n * (n - 1) * (r - 2) * (R * n ^ (r - 4)) ≤
      r ^ 2 * (R * n ^ (r - 2)) := by
    have hExp : n * (n - 1) * (r - 2) * (R * n ^ (r - 4)) =
        (r - 2) * R * (n * (n - 1) * n ^ (r - 4)) := by ring
    rw [hExp]
    calc
      _ ≤ (r - 2) * R * n ^ (r - 2) :=
        Nat.mul_le_mul_left _ hPow₂
      _ ≤ r ^ 2 * R * n ^ (r - 2) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right R hRank₂)
      _ = r ^ 2 * (R * n ^ (r - 2)) := by ring
  nlinarith [hFirst, hSecond]

/-- The collision square root has the same arbitrary-factor saving as
the cover-pair term. The final `+1` from integer rounding is absorbed by
`m ≤ n`. -/
theorem discrete_round_collision_rate
    (n r R m : ℕ) (hn : 1 ≤ n) (hr : 4 ≤ r)
    (hRpos : 1 ≤ R) (hTn : discreteRoundRoot R ≤ n)
    (hmn : m ≤ n) (hmR : (4 * m ^ 2) ^ 4 ≤ R) :
    m * (Nat.nthRoot 2 (discreteRoundCollision n r R) + 1) ≤
      6 * r ^ 3 * n ^ (r - 1) := by
  let h := discreteRoundCoverSize n r R
  let T := discreteRoundRoot R
  let C := discreteRoundCollision n r R
  let U := Nat.nthRoot 2 C
  let N := n ^ (r - 1)
  have hCoverT : h * T ≤ 3 * r * r * n :=
    discrete_round_cover_times_root_bound n r R hTn
  have hRatio := discrete_round_root_square_ratio_bound R (4 * m ^ 2)
    hRpos hmR
  have hmRT : m ^ 2 * R ≤ T ^ 2 := by
    dsimp [T] at hRatio ⊢
    nlinarith [hRatio]
  have hChoose : n.choose (r - 2) ≤ n ^ (r - 2) :=
    Nat.choose_le_pow n (r - 2)
  have hH : h * (h - 1) ≤ h ^ 2 := by
    have hSub : h - 1 ≤ h := Nat.sub_le h 1
    nlinarith
  have hInner := discrete_round_collision_inner_bound n r R hn hr
  have hC : C ≤ 2 * r ^ 2 * (h ^ 2 * R) * (n ^ (r - 2)) ^ 2 := by
    calc
      C = n.choose (r - 2) * (h * (h - 1) *
          ((r - 1) * (r - 1) * (R * n ^ (r - 3)) +
            n * (n - 1) * (r - 2) * (R * n ^ (r - 4)))) := by
        rfl
      _ ≤ n ^ (r - 2) * (h ^ 2 *
          ((r - 1) * (r - 1) * (R * n ^ (r - 3)) +
            n * (n - 1) * (r - 2) * (R * n ^ (r - 4)))) := by
        apply Nat.mul_le_mul hChoose
        exact Nat.mul_le_mul_right _ hH
      _ ≤ n ^ (r - 2) * (h ^ 2 *
          (2 * r ^ 2 * (R * n ^ (r - 2)))) := by
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hInner)
      _ = 2 * r ^ 2 * (h ^ 2 * R) * (n ^ (r - 2)) ^ 2 := by ring
  have hCScaled : m ^ 2 * C ≤
      2 * r ^ 2 * (h * T) ^ 2 * (n ^ (r - 2)) ^ 2 := by
    calc
      m ^ 2 * C ≤ m ^ 2 *
          (2 * r ^ 2 * (h ^ 2 * R) * (n ^ (r - 2)) ^ 2) :=
        Nat.mul_le_mul_left _ hC
      _ = 2 * r ^ 2 * (h ^ 2 * (m ^ 2 * R)) *
          (n ^ (r - 2)) ^ 2 := by ring
      _ ≤ 2 * r ^ 2 * (h ^ 2 * T ^ 2) *
          (n ^ (r - 2)) ^ 2 := by
        exact Nat.mul_le_mul_right _
          (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hmRT))
      _ = 2 * r ^ 2 * (h * T) ^ 2 * (n ^ (r - 2)) ^ 2 := by ring
  have hCoverSq := Nat.pow_le_pow_left hCoverT 2
  have hNExp : 1 + (r - 2) = r - 1 := by omega
  have hCN : m ^ 2 * C ≤ 18 * r ^ 6 * N ^ 2 := by
    calc
      m ^ 2 * C ≤ 2 * r ^ 2 * (h * T) ^ 2 *
          (n ^ (r - 2)) ^ 2 := hCScaled
      _ ≤ 2 * r ^ 2 * (3 * r * r * n) ^ 2 *
          (n ^ (r - 2)) ^ 2 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hCoverSq)
      _ = 18 * r ^ 6 * N ^ 2 := by
        dsimp [N]
        rw [← hNExp]
        ring
  have hU : U ^ 2 ≤ C := Nat.pow_nthRoot_le (Or.inl (by norm_num))
  have hUScaled : (m * U) ^ 2 ≤ (5 * r ^ 3 * N) ^ 2 := by
    calc
      (m * U) ^ 2 = m ^ 2 * U ^ 2 := by ring
      _ ≤ m ^ 2 * C := Nat.mul_le_mul_left _ hU
      _ ≤ 18 * r ^ 6 * N ^ 2 := hCN
      _ ≤ (5 * r ^ 3 * N) ^ 2 := by nlinarith
  have hmU : m * U ≤ 5 * r ^ 3 * N := by
    by_contra h
    have hlt : 5 * r ^ 3 * N < m * U := by omega
    have hltSq := Nat.pow_lt_pow_left hlt (by norm_num : 2 ≠ 0)
    omega
  have hnN : n ≤ N := by
    dsimp [N]
    exact le_self_pow hn (by omega : r - 1 ≠ 0)
  have hRcube : 1 ≤ r ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hmN : m ≤ r ^ 3 * N :=
    (hmn.trans hnN).trans (by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right N hRcube)
  calc
    m * (U + 1) = m * U + m := by ring
    _ ≤ 5 * r ^ 3 * N + r ^ 3 * N := Nat.add_le_add hmU hmN
    _ = 6 * r ^ 3 * N := by ring

theorem natural_scale_le_ambient
    (n R : ℕ) (hn : 1 ≤ n) (hR23 : R ^ 3 ≤ n ^ 2) :
    R ≤ n := by
  by_contra h
  have hlt : n < R := by omega
  have hltCube := Nat.pow_lt_pow_left hlt (by norm_num : 3 ≠ 0)
  have hNpow : n ^ 2 ≤ n ^ 3 := by
    calc
      n ^ 2 = n ^ 2 * 1 := by simp
      _ ≤ n ^ 2 * n := Nat.mul_le_mul_left _ hn
      _ = n ^ 3 := by ring
  omega

/-- Every component of the exact additive round loss has an arbitrary
fixed-factor saving against the extremal star size. -/
theorem discrete_round_additive_loss_star_rate
    (n r R m : ℕ) (hr : 4 ≤ r) (hm : 1 ≤ m)
    (hn : 2 * (r - 1) + 1 ≤ n)
    (hR23 : R ^ 3 ≤ n ^ 2)
    (hRlarge : (4 * m ^ 2) ^ 4 ≤ R)
    (hnlarge : (m ^ (r - 1) * (r - 1).factorial) ^ 3 ≤ n)
    (hmn : m * r ≤ n) :
    m * discreteRoundAdditiveLoss n r R ≤
      (6 * r ^ 3 + 2 + 9 * r ^ 4 + 2 * (r - 1)) *
        (2 ^ (r - 1) * (r - 1).factorial) *
          (n - 1).choose (r - 1) := by
  have hnpos : 1 ≤ n := by omega
  have hRpos : 1 ≤ R := by
    have hBase : 1 ≤ 4 * m ^ 2 := by nlinarith [hm]
    have hPow : 1 ≤ (4 * m ^ 2) ^ 4 := Nat.one_le_pow _ _ hBase
    omega
  have hRn : R ≤ n := natural_scale_le_ambient n R hnpos hR23
  have hTn : discreteRoundRoot R ≤ n :=
    ((discrete_round_root_le_target R hRpos).trans
      (discrete_round_target_le_self R)).trans hRn
  have hmn' : m ≤ n := by nlinarith [hmn, hr]
  have hmPair : (4 * m) ^ 4 ≤ R := by
    have hmSq : m ≤ m ^ 2 := le_self_pow hm (by norm_num : 2 ≠ 0)
    have hBase : 4 * m ≤ 4 * m ^ 2 := Nat.mul_le_mul_left 4 hmSq
    exact (Nat.pow_le_pow_left hBase 4).trans hRlarge
  have hmFacet : (2 * m) ^ 8 ≤ R := by
    have he : (2 * m) ^ 8 = (4 * m ^ 2) ^ 4 := by ring
    simpa only [he] using hRlarge
  have hCollision := discrete_round_collision_rate n r R m hnpos hr
    hRpos hTn hmn' hRlarge
  have hRadius := discrete_round_radius_layer_rate_at_natural_scale
    n r R m hr hR23 hnlarge hmn
  have hPair := discrete_round_cover_pair_rate n r R m hr hRpos hTn hmPair
  have hFacet := discrete_round_facet_quotient_bound n r R m hm hmFacet
  have hFacetN : 2 * (n.choose 2 * ((r - 1) * n ^ (r - 3))) ≤
      2 * (r - 1) * n ^ (r - 1) := by
    have hChoose : n.choose 2 ≤ n ^ 2 := Nat.choose_le_pow n 2
    have hExp : 2 + (r - 3) = r - 1 := by omega
    calc
      _ = 2 * (r - 1) * (n.choose 2 * n ^ (r - 3)) := by ring
      _ ≤ 2 * (r - 1) * (n ^ 2 * n ^ (r - 3)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hChoose)
      _ = 2 * (r - 1) * n ^ (r - 1) := by rw [← pow_add, hExp]
  have hLossPower : m * discreteRoundAdditiveLoss n r R ≤
      (6 * r ^ 3 + 2 + 9 * r ^ 4 + 2 * (r - 1)) *
        n ^ (r - 1) := by
    have hDecomp : m * discreteRoundAdditiveLoss n r R =
        m * (Nat.nthRoot 2 (discreteRoundCollision n r R) + 1) +
        m * (((discreteRoundRadius n r R + (r - 1)) *
          n.choose (r - 2)) / (r - 1)) +
        m * ((discreteRoundCoverSize n r R).choose 2 *
          (R * n ^ (r - 3))) +
        m * (2 * (n.choose 2 * ((r - 1) *
          (discreteRoundRoot R * n ^ (r - 3)))) /
            (discreteRoundTarget R - 1)) := by
      dsimp [discreteRoundAdditiveLoss, discreteRoundLayerBudget]
      ring
    rw [hDecomp]
    have hBound :
        m * (Nat.nthRoot 2 (discreteRoundCollision n r R) + 1) +
        m * (((discreteRoundRadius n r R + (r - 1)) *
          n.choose (r - 2)) / (r - 1)) +
        m * ((discreteRoundCoverSize n r R).choose 2 *
          (R * n ^ (r - 3))) +
        m * (2 * (n.choose 2 * ((r - 1) *
          (discreteRoundRoot R * n ^ (r - 3)))) /
            (discreteRoundTarget R - 1)) ≤
          6 * r ^ 3 * n ^ (r - 1) + 2 * n ^ (r - 1) +
            9 * r ^ 4 * n ^ (r - 1) +
              2 * (r - 1) * n ^ (r - 1) := by
      omega
    calc
      _ ≤ _ := hBound
      _ = (6 * r ^ 3 + 2 + 9 * r ^ 4 + 2 * (r - 1)) *
          n ^ (r - 1) := by ring
  have hStar := far_star_power_le_choose_multiple n (r - 1) hn
  calc
    _ ≤ (6 * r ^ 3 + 2 + 9 * r ^ 4 + 2 * (r - 1)) *
        n ^ (r - 1) := hLossPower
    _ ≤ (6 * r ^ 3 + 2 + 9 * r ^ 4 + 2 * (r - 1)) *
        (2 ^ (r - 1) * (r - 1).factorial) *
          (n - 1).choose (r - 1) := by
      have hMul := Nat.mul_le_mul_left
        (6 * r ^ 3 + 2 + 9 * r ^ 4 + 2 * (r - 1)) hStar
      nlinarith [hMul]

/-- The complete loss of any fixed finite number of natural rounds is
arbitrarily small compared with the extremal star, with one explicit
threshold shared by all rounds. -/
theorem discrete_round_iterated_loss_star_rate
    (n r R steps m : ℕ) (hr : 4 ≤ r) (hm : 1 ≤ m)
    (hn : 2 * (r - 1) + 1 ≤ n)
    (hR23 : R ^ 3 ≤ n ^ 2)
    (hLarge : ∀ i < steps,
      (4 * m ^ 2) ^ 4 ≤ discreteRoundIterate R i)
    (hnlarge : (m ^ (r - 1) * (r - 1).factorial) ^ 3 ≤ n)
    (hmn : m * r ≤ n) :
    m * (∑ i ∈ Finset.range steps,
      discreteRoundAdditiveLoss n r (discreteRoundIterate R i)) ≤
        steps * ((6 * r ^ 3 + 2 + 9 * r ^ 4 + 2 * (r - 1)) *
          (2 ^ (r - 1) * (r - 1).factorial)) *
            (n - 1).choose (r - 1) := by
  rw [Finset.mul_sum]
  calc
    (∑ i ∈ Finset.range steps,
      m * discreteRoundAdditiveLoss n r (discreteRoundIterate R i)) ≤
      ∑ _i ∈ Finset.range steps,
        (6 * r ^ 3 + 2 + 9 * r ^ 4 + 2 * (r - 1)) *
          (2 ^ (r - 1) * (r - 1).factorial) *
            (n - 1).choose (r - 1) := by
          apply Finset.sum_le_sum
          intro i hi
          have hScale : (discreteRoundIterate R i) ^ 3 ≤ n ^ 2 :=
            (Nat.pow_le_pow_left (discrete_round_iterate_le_start R i) 3).trans hR23
          exact discrete_round_additive_loss_star_rate n r
            (discreteRoundIterate R i) m hr hm hn hScale
              (hLarge i (Finset.mem_range.mp hi)) hnlarge hmn
    _ = steps * ((6 * r ^ 3 + 2 + 9 * r ^ 4 + 2 * (r - 1)) *
        (2 ^ (r - 1) * (r - 1).factorial)) *
          (n - 1).choose (r - 1) := by simp [mul_assoc]

/-- Exact finite degree threshold obtained from the degree sum. -/
def initialVertexCap (r h edgeCount : ℕ) : ℕ :=
  r * edgeCount / (h + 1) + 1

theorem initial_vertex_cap_budget (r h edgeCount : ℕ) :
    r * edgeCount < (h + 1) * initialVertexCap r h edgeCount := by
  have hMod := Nat.mod_add_div (r * edgeCount) (h + 1)
  have hRem := Nat.mod_lt (r * edgeCount) (by omega : 0 < h + 1)
  unfold initialVertexCap
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- The high-degree threshold costs only the ratio between the matching
parameter and the removed-set size. This is the exact finite estimate
used for the polynomial scale choice. -/
theorem initial_vertex_cap_loss_rate
    (r h a edgeCount star m C D : ℕ)
    (hGap : m * (r * r * a) ≤ h + 1)
    (hFamily : edgeCount ≤ C * star)
    (hSet : h + 1 ≤ D * star) :
    m * (r * r * a * initialVertexCap r h edgeCount) ≤
      (r * C + D) * star := by
  let q := h + 1
  have hDiv : q * (r * edgeCount / q) ≤ r * edgeCount := by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self (r * edgeCount) q
  have hCap : q * initialVertexCap r h edgeCount ≤
      r * edgeCount + q := by
    calc
      q * initialVertexCap r h edgeCount =
          q * (r * edgeCount / q) + q := by
        dsimp [initialVertexCap, q]
        ring
      _ ≤ r * edgeCount + q := Nat.add_le_add_right hDiv q
  have hMain : m * (r * r * a * initialVertexCap r h edgeCount) ≤
      q * initialVertexCap r h edgeCount := by
    have hMul := Nat.mul_le_mul_right
      (initialVertexCap r h edgeCount) hGap
    simpa only [mul_assoc] using hMul
  calc
    _ ≤ q * initialVertexCap r h edgeCount := hMain
    _ ≤ r * edgeCount + q := hCap
    _ ≤ r * (C * star) + D * star := by
      exact Nat.add_le_add (Nat.mul_le_mul_left r hFamily) hSet
    _ = (r * C + D) * star := by ring

/-- The rounded number of heavy roots in the initial cleanup. -/
def initialScaleMultiplier (n Scale : ℕ) : ℕ :=
  3 * n / Scale + 1

/-- A single finite separation hypothesis makes the rounded matching
parameter satisfy both conditions of `initial_sqrt_scale_gap`. -/
theorem initial_scale_multiplier_bounds
    (n r Scale : ℕ) (hn : 1 ≤ n) (hScalePos : 0 < Scale)
    (hScaleN : Scale ≤ n) (hSeparation : 16 * r * n < Scale ^ 2) :
    3 * n ≤ initialScaleMultiplier n Scale * Scale ∧
      initialScaleMultiplier n Scale * initialScaleMultiplier n Scale * r < n := by
  let a := initialScaleMultiplier n Scale
  have hDiv := Nat.mod_add_div (3 * n) Scale
  have hRem := Nat.mod_lt (3 * n) hScalePos
  have hLower : 3 * n ≤ a * Scale := by
    dsimp [a, initialScaleMultiplier]
    rw [Nat.add_mul, Nat.one_mul]
    rw [Nat.mul_comm Scale (3 * n / Scale)] at hDiv
    omega
  have hUpper : a * Scale ≤ 4 * n := by
    dsimp [a, initialScaleMultiplier]
    rw [Nat.add_mul, Nat.one_mul]
    rw [Nat.mul_comm Scale (3 * n / Scale)] at hDiv
    omega
  have hASquare : (a * Scale) ^ 2 ≤ (4 * n) ^ 2 :=
    Nat.pow_le_pow_left hUpper 2
  have hBound : a * a * r * Scale ^ 2 ≤ 16 * r * n ^ 2 := by
    calc
      a * a * r * Scale ^ 2 = r * (a * Scale) ^ 2 := by ring
      _ ≤ r * (4 * n) ^ 2 := Nat.mul_le_mul_left _ hASquare
      _ = 16 * r * n ^ 2 := by ring
  have hStrict : 16 * r * n ^ 2 < n * Scale ^ 2 := by
    have h := (Nat.mul_lt_mul_left hn).2 hSeparation
    nlinarith
  refine ⟨hLower, ?_⟩
  change a * a * r < n
  by_contra h
  have hge : n ≤ a * a * r := by omega
  have hMul : n * Scale ^ 2 ≤ a * a * r * Scale ^ 2 :=
    Nat.mul_le_mul_right _ hge
  omega

/-- Initial cleanup at a single square-root-type scale. All `j`-codegree
caps now use one explicit factor `T`, and the Bonferroni gaps are discharged
from two scalar inequalities. -/
theorem initial_codegree_cleanup_at_sqrt_scale
    {n r h M VCap Scale a : ℕ} (H : Family (Fin n))
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hn : 1 ≤ n) (hr : 4 ≤ r)
    (hMax : ∀ z : Fin n,
      (H.filter (fun E => z ∈ E)).card ≤ M)
    (hBudget : r * H.card < (h + 1) * VCap)
    (haT : 3 * n ≤ a * Scale) (haSq : a * a * r < n) :
    ∃ K : Family (Fin n), K ⊆ H ∧ Admissible K ∧ Uniform r K ∧
      (∀ s, 1 ≤ s → s ≤ r - 1 →
        ∀ S : Edge (Fin n), S.card = s →
          (K.filter (fun E => S ⊆ E)).card ≤
            Scale * n ^ (r - s - 1)) ∧
      H.card - K.card ≤ h * M +
        (∑ s ∈ Finset.Icc 1 (r - 1), s * (a - 1)) * VCap := by
  exact initial_codegree_cleanup_after_high_degree_removal H
    (fun s => Scale * n ^ (r - s - 1)) (fun _ => a)
    hAdm hUniform hr hMax hBudget
    (by intro s hs hsr; exact initial_sqrt_scale_gap n r s Scale a hn hr hs hsr haT haSq)

/-- The top-degree threshold and cover-size budget are now chosen from the
actual edge count. This leaves only the square-root separation conditions
on `Scale` and `a`. -/
theorem initial_codegree_cleanup_canonical
    {n r M Scale a h : ℕ} (H : Family (Fin n))
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hn : 1 ≤ n) (hr : 4 ≤ r)
    (hMax : ∀ z : Fin n,
      (H.filter (fun E => z ∈ E)).card ≤ M)
    (haT : 3 * n ≤ a * Scale) (haSq : a * a * r < n) :
    ∃ K : Family (Fin n), K ⊆ H ∧ Admissible K ∧ Uniform r K ∧
      (∀ s, 1 ≤ s → s ≤ r - 1 →
        ∀ S : Edge (Fin n), S.card = s →
          (K.filter (fun E => S ⊆ E)).card ≤
            Scale * n ^ (r - s - 1)) ∧
      H.card - K.card ≤ h * M +
        r * r * a * initialVertexCap r h H.card := by
  obtain ⟨K, hKH, hAdmK, hUniformK, hCaps, hLoss⟩ :=
    initial_codegree_cleanup_at_sqrt_scale H hAdm hUniform hn hr
      hMax (initial_vertex_cap_budget r h H.card) haT haSq
  refine ⟨K, hKH, hAdmK, hUniformK, hCaps, ?_⟩
  exact hLoss.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (initial_cover_size_le_rank_square r a)) _)

/-- Fully specified integer parameters for the initial IV.5.1 cleanup.
Only the scale separation `16rn < Scale²` and `Scale ≤ n` remain numeric
inputs; the high-degree threshold and matching size are computed. -/
theorem initial_codegree_cleanup_explicit_scale
    {n r M Scale h : ℕ} (H : Family (Fin n))
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hn : 1 ≤ n) (hr : 4 ≤ r)
    (hMax : ∀ z : Fin n,
      (H.filter (fun E => z ∈ E)).card ≤ M)
    (hScalePos : 0 < Scale) (hScaleN : Scale ≤ n)
    (hSeparation : 16 * r * n < Scale ^ 2) :
    ∃ K : Family (Fin n), K ⊆ H ∧ Admissible K ∧ Uniform r K ∧
      (∀ s, 1 ≤ s → s ≤ r - 1 →
        ∀ S : Edge (Fin n), S.card = s →
          (K.filter (fun E => S ⊆ E)).card ≤
            Scale * n ^ (r - s - 1)) ∧
      H.card - K.card ≤ h * M +
        r * r * initialScaleMultiplier n Scale *
          initialVertexCap r h H.card := by
  obtain ⟨haT, haSq⟩ :=
    initial_scale_multiplier_bounds n r Scale hn hScalePos hScaleN hSeparation
  exact initial_codegree_cleanup_canonical H hAdm hUniform hn hr hMax haT haSq

/-- The actual far-star tail feeds the initial codegree cleanup. Every
combinatorial input is derived from the original admissible uniform family;
the remaining conditions are scalar choices of the two cleanup scales. -/
theorem far_star_initial_codegree_extraction
    {n r h₀ h₁ M VCap Scale a : ℕ} [Inhabited (Fin n)]
    (H : Family (Fin n)) (X₀ : Edge (Fin n))
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hn : 1 ≤ n) (hr : 4 ≤ r) (hX₀ : X₀.card ≤ h₀)
    (hMax : ∀ z : Fin n,
      (H.filter (fun E => z ∈ E)).card ≤ M)
    (hBudget : r * H.card < (h₁ + 1) * VCap)
    (haT : 3 * n ≤ a * Scale) (haSq : a * a * r < n) :
    ∃ K : Family (Fin n), K ⊆ H ∧ Admissible K ∧ Uniform r K ∧
      (∀ s, 1 ≤ s → s ≤ r - 1 →
        ∀ S : Edge (Fin n), S.card = s →
          (K.filter (fun E => S ⊆ E)).card ≤
            Scale * n ^ (r - s - 1)) ∧
      H.card ≤ K.card +
        farStarDeletion n r h₀ +
        ((farStarRadius r M + (r - 1)) * n.choose (r - 2)) / (r - 1) +
        h₀.choose 2 * (n - 2).choose (r - 2) +
        h₁ * M +
        (∑ s ∈ Finset.Icc 1 (r - 1), s * (a - 1)) * VCap := by
  classical
  let F₀ : Family (Fin n) := H.filter (fun E => Disjoint E X₀)
  have hF₀H : F₀ ⊆ H := Finset.filter_subset _ _
  have hAdm₀ : Admissible F₀ := admissible_mono hF₀H hAdm
  have hUniform₀ : Uniform r F₀ := fun E hE => hUniform (hF₀H hE)
  have hMax₀ : ∀ z : Fin n,
      (F₀.filter (fun E => z ∈ E)).card ≤ M := by
    intro z
    simpa only [Finset.singleton_subset_iff] using
      (completion_codegree_mono hF₀H ({z} : Edge (Fin n))).trans
        (by simpa only [Finset.singleton_subset_iff] using hMax z)
  have hBudget₀ : r * F₀.card < (h₁ + 1) * VCap :=
    (Nat.mul_le_mul_left r (Finset.card_le_card hF₀H)).trans_lt hBudget
  obtain ⟨K, hKF₀, hAdmK, hUniformK, hCaps, hLoss⟩ :=
    initial_codegree_cleanup_at_sqrt_scale F₀ hAdm₀ hUniform₀
      hn hr hMax₀ hBudget₀ haT haSq
  have hTail := finite_far_star_tail_from_max_degree H X₀
    hAdm hUniform hr hX₀ hMax
  have hKF₀card := Finset.card_le_card hKF₀
  refine ⟨K, hKF₀.trans hF₀H, hAdmK, hUniformK, hCaps, ?_⟩
  change H.card ≤ F₀.card + farStarDeletion n r h₀ +
    ((farStarRadius r M + (r - 1)) * n.choose (r - 2)) / (r - 1) +
    h₀.choose 2 * (n - 2).choose (r - 2) at hTail
  omega

/-- Choose the first removed vertex set as the actual high-degree cover.
The far tail then has maximum degree at most `⌊r|H|/(h₀+1)⌋+1` before
the heavy-root cleanup. This avoids the second high-degree deletion stage
and its `h₁*M` charge. -/
theorem far_star_initial_codegree_extraction_from_actual_cover
    {n r h₀ M Scale : ℕ}
    (H : Family (Fin n))
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hn : 1 ≤ n) (hr : 4 ≤ r)
    (hMax : ∀ z : Fin n,
      (H.filter (fun E => z ∈ E)).card ≤ M)
    (hScalePos : 0 < Scale) (hScaleN : Scale ≤ n)
    (hSeparation : 16 * r * n < Scale ^ 2) :
    ∃ X₀ : Edge (Fin n), ∃ K : Family (Fin n),
      X₀.card ≤ h₀ ∧ K ⊆ H ∧ Admissible K ∧ Uniform r K ∧
      (∀ s, 1 ≤ s → s ≤ r - 1 →
        ∀ S : Edge (Fin n), S.card = s →
          (K.filter (fun E => S ⊆ E)).card ≤
            Scale * n ^ (r - s - 1)) ∧
      H.card ≤ K.card +
        farStarDeletion n r h₀ +
        ((farStarRadius r M + (r - 1)) * n.choose (r - 2)) / (r - 1) +
        h₀.choose 2 * (n - 2).choose (r - 2) +
        r * r * initialScaleMultiplier n Scale *
          initialVertexCap r h₀ H.card := by
  classical
  letI : Inhabited (Fin n) := ⟨⟨0, by omega⟩⟩
  let T := initialVertexCap r h₀ H.card
  let a := initialScaleMultiplier n Scale
  obtain ⟨X₀, hX₀, hOutside⟩ :=
    exists_high_degree_vertex_cover H hUniform
      (initial_vertex_cap_budget r h₀ H.card)
  let F₀ : Family (Fin n) := H.filter (fun E => Disjoint E X₀)
  have hF₀H : F₀ ⊆ H := Finset.filter_subset _ _
  have hAdm₀ : Admissible F₀ := admissible_mono hF₀H hAdm
  have hUniform₀ : Uniform r F₀ := fun E hE => hUniform (hF₀H hE)
  have hMax₀ : ∀ z : Fin n,
      (F₀.filter (fun E => z ∈ E)).card ≤ T :=
    avoiding_high_degree_cover_max_degree H X₀ hOutside
  obtain ⟨haT, haSq⟩ :=
    initial_scale_multiplier_bounds n r Scale hn hScalePos hScaleN hSeparation
  obtain ⟨K, hKF₀, hAdmK, hUniformK, hCapsK, hCleanup⟩ :=
    initial_codegree_cleanup_from_max_degree F₀
      (fun s => Scale * n ^ (r - s - 1)) (fun _ => a)
      hAdm₀ hUniform₀ hr hMax₀
      (by
        intro s hs hsr
        exact initial_sqrt_scale_gap n r s Scale a hn hr hs hsr haT haSq)
  have hCleanup' : F₀.card - K.card ≤ r * r * a * T :=
    hCleanup.trans (Nat.mul_le_mul_right T
      (initial_cover_size_le_rank_square r a))
  have hTail := finite_far_star_tail_from_max_degree H X₀
    hAdm hUniform hr hX₀ hMax
  have hKcard := Finset.card_le_card hKF₀
  refine ⟨X₀, K, hX₀, hKF₀.trans hF₀H,
    hAdmK, hUniformK, hCapsK, ?_⟩
  change H.card ≤ F₀.card + farStarDeletion n r h₀ +
    ((farStarRadius r M + (r - 1)) * n.choose (r - 2)) / (r - 1) +
    h₀.choose 2 * (n - 2).choose (r - 2) at hTail
  dsimp [T, a] at hCleanup'
  omega

/-- After the actual far-star and initial cleanup stages, the retained
family satisfies every hypothesis of the natural-scale IV.4 round. The
first contraction is constructed here with both deletion ledgers retained. -/
theorem far_star_initial_natural_first_round
    {n r h₀ h₁ M VCap Scale a : ℕ} [Inhabited (Fin n)]
    (H : Family (Fin n)) (X₀ : Edge (Fin n))
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hn : 1 ≤ n) (hr : 4 ≤ r) (hX₀ : X₀.card ≤ h₀)
    (hMax : ∀ z : Fin n,
      (H.filter (fun E => z ∈ E)).card ≤ M)
    (hBudget : r * H.card < (h₁ + 1) * VCap)
    (haT : 3 * n ≤ a * Scale) (haSq : a * a * r < n)
    (hScale23 : Scale ^ 3 ≤ n ^ 2)
    (hScaleLarge : (16 * (36 * r) ^ 3) ^ 8 ≤ Scale ^ 5) :
    ∃ K K' : Family (Fin n),
      K ⊆ H ∧ K' ⊆ K ∧ Admissible K' ∧ Uniform r K' ∧
      (∀ j, 1 ≤ j → j ≤ r - 1 →
        ∀ S : Edge (Fin n), S.card = j →
          (K'.filter (fun E => S ⊆ E)).card ≤
            discreteRoundTarget Scale * n ^ (r - j - 1)) ∧
      H.card ≤ K.card +
        farStarDeletion n r h₀ +
        ((farStarRadius r M + (r - 1)) * n.choose (r - 2)) / (r - 1) +
        h₀.choose 2 * (n - 2).choose (r - 2) +
        h₁ * M +
        (∑ s ∈ Finset.Icc 1 (r - 1), s * (a - 1)) * VCap ∧
      (discreteRoundTarget Scale - 1) * (K.card - K'.card) ≤
        (discreteRoundTarget Scale - 1) *
          discreteRoundLayerBudget n r Scale +
        2 * (n.choose 2 *
          ((r - 1) * (discreteRoundRoot Scale * n ^ (r - 3)))) := by
  obtain ⟨K, hKH, hAdmK, hUniformK, hCapsK, hInitialLoss⟩ :=
    far_star_initial_codegree_extraction H X₀ hAdm hUniform
      hn hr hX₀ hMax hBudget haT haSq
  obtain ⟨K', hK'K, hAdmK', hUniformK', hCapsK', hRoundLoss⟩ :=
    natural_scale_finite_regularization K hr hn hScale23 hScaleLarge
      hAdmK hUniformK hCapsK
  exact ⟨K, K', hKH, hK'K, hAdmK', hUniformK', hCapsK',
    hInitialLoss, hRoundLoss⟩

/-- A direct applicability statement for the first natural regularization
round. Both auxiliary parameters are computed from `H` and `Scale`; no
parent codegree hypothesis remains at the theorem boundary. -/
theorem far_star_first_natural_round_exists
    {n r h₀ h₁ M Scale : ℕ} [Inhabited (Fin n)]
    (H : Family (Fin n)) (X₀ : Edge (Fin n))
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hn : 1 ≤ n) (hr : 4 ≤ r) (hX₀ : X₀.card ≤ h₀)
    (hMax : ∀ z : Fin n,
      (H.filter (fun E => z ∈ E)).card ≤ M)
    (hScalePos : 0 < Scale) (hScaleN : Scale ≤ n)
    (hSeparation : 16 * r * n < Scale ^ 2)
    (hScale23 : Scale ^ 3 ≤ n ^ 2)
    (hScaleLarge : (16 * (36 * r) ^ 3) ^ 8 ≤ Scale ^ 5) :
    ∃ K' : Family (Fin n), K' ⊆ H ∧ Admissible K' ∧ Uniform r K' ∧
      ∀ j, 1 ≤ j → j ≤ r - 1 →
        ∀ S : Edge (Fin n), S.card = j →
          (K'.filter (fun E => S ⊆ E)).card ≤
            discreteRoundTarget Scale * n ^ (r - j - 1) := by
  obtain ⟨haT, haSq⟩ :=
    initial_scale_multiplier_bounds n r Scale hn hScalePos hScaleN hSeparation
  obtain ⟨K, K', hKH, hK'K, hAdmK', hUniformK', hCapsK', _, _⟩ :=
    far_star_initial_natural_first_round H X₀ hAdm hUniform
      hn hr hX₀ hMax
      (initial_vertex_cap_budget r h₁ H.card)
      haT haSq hScale23 hScaleLarge
  exact ⟨K', hK'K.trans hKH, hAdmK', hUniformK', hCapsK'⟩

/-- The far-star extraction and initial cleanup feed any finite sequence
of natural regularization rounds on the actual family. The theorem keeps
all deletion costs in one additive ledger. -/
theorem far_star_initial_natural_iterate
    {n r h₀ h₁ M VCap Scale a : ℕ} [Inhabited (Fin n)]
    (steps : ℕ) (H : Family (Fin n)) (X₀ : Edge (Fin n))
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hn : 1 ≤ n) (hr : 4 ≤ r) (hX₀ : X₀.card ≤ h₀)
    (hMax : ∀ z : Fin n,
      (H.filter (fun E => z ∈ E)).card ≤ M)
    (hBudget : r * H.card < (h₁ + 1) * VCap)
    (haT : 3 * n ≤ a * Scale) (haSq : a * a * r < n)
    (hScale23 : Scale ^ 3 ≤ n ^ 2)
    (hLarge : ∀ i < steps,
      (16 * (36 * r) ^ 3) ^ 8 ≤
        (discreteRoundIterate Scale i) ^ 5) :
    ∃ K : Family (Fin n), K ⊆ H ∧ Admissible K ∧ Uniform r K ∧
      (∀ j, 1 ≤ j → j ≤ r - 1 →
        ∀ S : Edge (Fin n), S.card = j →
          (K.filter (fun E => S ⊆ E)).card ≤
            discreteRoundIterate Scale steps * n ^ (r - j - 1)) ∧
      H.card ≤ K.card +
        farStarDeletion n r h₀ +
        ((farStarRadius r M + (r - 1)) * n.choose (r - 2)) / (r - 1) +
        h₀.choose 2 * (n - 2).choose (r - 2) +
        h₁ * M +
        (∑ s ∈ Finset.Icc 1 (r - 1), s * (a - 1)) * VCap +
        ∑ i ∈ Finset.range steps,
          discreteRoundAdditiveLoss n r (discreteRoundIterate Scale i) := by
  obtain ⟨K₀, hK₀H, hAdm₀, hUniform₀, hCaps₀, hInitialLoss⟩ :=
    far_star_initial_codegree_extraction H X₀ hAdm hUniform hn hr hX₀
      hMax hBudget haT haSq
  obtain ⟨K, hKK₀, hAdmK, hUniformK, hCapsK, hRoundLoss⟩ :=
    natural_scale_finite_regularization_iterate steps K₀ hr hn hScale23
      hLarge hAdm₀ hUniform₀ hCaps₀
  refine ⟨K, hKK₀.trans hK₀H, hAdmK, hUniformK, hCapsK, ?_⟩
  omega

/-- The high-degree set is chosen from the actual initial family, and
its complement feeds all requested natural rounds with one exact ledger. -/
theorem far_star_initial_natural_iterate_from_actual_cover
    {n r h₀ M Scale : ℕ}
    (steps : ℕ) (H : Family (Fin n))
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hn : 1 ≤ n) (hr : 4 ≤ r)
    (hMax : ∀ z : Fin n,
      (H.filter (fun E => z ∈ E)).card ≤ M)
    (hScalePos : 0 < Scale) (hScaleN : Scale ≤ n)
    (hSeparation : 16 * r * n < Scale ^ 2)
    (hScale23 : Scale ^ 3 ≤ n ^ 2)
    (hLarge : ∀ i < steps,
      (16 * (36 * r) ^ 3) ^ 8 ≤
        (discreteRoundIterate Scale i) ^ 5) :
    ∃ X₀ : Edge (Fin n), ∃ K : Family (Fin n),
      X₀.card ≤ h₀ ∧ K ⊆ H ∧ Admissible K ∧ Uniform r K ∧
      (∀ j, 1 ≤ j → j ≤ r - 1 →
        ∀ S : Edge (Fin n), S.card = j →
          (K.filter (fun E => S ⊆ E)).card ≤
            discreteRoundIterate Scale steps * n ^ (r - j - 1)) ∧
      H.card ≤ K.card +
        farStarDeletion n r h₀ +
        ((farStarRadius r M + (r - 1)) * n.choose (r - 2)) / (r - 1) +
        h₀.choose 2 * (n - 2).choose (r - 2) +
        r * r * initialScaleMultiplier n Scale *
          initialVertexCap r h₀ H.card +
        ∑ i ∈ Finset.range steps,
          discreteRoundAdditiveLoss n r (discreteRoundIterate Scale i) := by
  obtain ⟨X₀, K₀, hX₀, hK₀H, hAdm₀, hUniform₀, hCaps₀,
      hInitialLoss⟩ :=
    far_star_initial_codegree_extraction_from_actual_cover H
      hAdm hUniform hn hr hMax hScalePos hScaleN hSeparation
  obtain ⟨K, hKK₀, hAdmK, hUniformK, hCapsK, hRoundLoss⟩ :=
    natural_scale_finite_regularization_iterate steps K₀ hr hn hScale23
      hLarge hAdm₀ hUniform₀ hCaps₀
  refine ⟨X₀, K, hX₀, hKK₀.trans hK₀H,
    hAdmK, hUniformK, hCapsK, ?_⟩
  omega

end JSP523.Rank5
