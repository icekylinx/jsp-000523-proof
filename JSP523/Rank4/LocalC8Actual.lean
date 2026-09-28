import JSP523.Rank4.LocalC7Counting
import JSP523.Rank4.LocalExceptionalArithmetic
import JSP523.Rank4.LocalEqualityForward
import JSP523.Rank4.LocalEqualityConstruction
import JSP523.Rank4.LocalC8Arithmetic
import Mathlib.Analysis.Real.Sqrt

namespace JSP523.Rank4

/-- The two outside-family forms in the rank-four near-star equality case. -/
def RankFourNearStarEqualityFamily {α : Type*} [DecidableEq α]
    (H : Family α) (W : Edge α) (v : α) : Prop :=
  ((missingStarTriples H W v).card = 0 ∧
    IsMatching (outsideEdges H W) ∧
    (outsideEdges H W).card = W.card / 4) ∨
  ((missingStarTriples H W v).card = 1 ∧
    ∃ P x Q M,
      missingStarTriples H W v = {P} ∧ P.card = 3 ∧ W.card % 4 = 3 ∧
      x ∈ W ∧ x ∉ P ∧ Q.card = 3 ∧ Disjoint P Q ∧ x ∉ Q ∧
      outsideEdges H W = insert (insert x P) (insert (insert x Q) M) ∧
      IsMatching M ∧
      (∀ E ∈ M, Disjoint E (insert x P ∪ insert x Q)) ∧
      M.biUnion (fun E => E) = W \ (insert x P ∪ insert x Q) ∧
      (outsideEdges H W).card = W.card / 4 + 1)

/-- The cubic-root substitution used in the actual C7-to-C8 estimate. -/
theorem near_star_C8_bad_pair_sqrt
    {w q h : ℝ} (hw : 0 < w) (hq : 0 ≤ q) (hh0 : 0 ≤ h)
    (hh : h ≤ 9 * q / w) :
    Real.sqrt (h ^ 3) ≤ 27 * q * Real.sqrt (q / w ^ 3) := by
  let x := q / w ^ 3
  have hx : 0 ≤ x := div_nonneg hq (by positivity)
  have hbase : h ≤ 9 * w ^ 2 * x := by
    dsimp [x]
    have heq : 9 * q / w = 9 * w ^ 2 * (q / w ^ 3) := by
      field_simp [ne_of_gt hw]
    rw [← heq]
    exact hh
  have hc : h ^ 3 ≤ (9 * w ^ 2 * x) ^ 3 :=
    pow_le_pow_left₀ hh0 hbase 3
  have hrootid : (27 * w ^ 3 * x * Real.sqrt x) ^ 2 =
      (9 * w ^ 2 * x) ^ 3 := by
    have hs := Real.sq_sqrt hx
    calc
      (27 * w ^ 3 * x * Real.sqrt x) ^ 2 =
          729 * w ^ 6 * x ^ 2 * (Real.sqrt x) ^ 2 := by ring
      _ = (9 * w ^ 2 * x) ^ 3 := by rw [hs]; ring
  have hroot : Real.sqrt (h ^ 3) ≤ 27 * w ^ 3 * x * Real.sqrt x := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith [hc, hrootid]
  have hscale : w ^ 3 * x = q := by
    dsimp [x]
    field_simp [ne_of_gt hw]
  have hroot' : Real.sqrt (h ^ 3) ≤ 27 * q * Real.sqrt x := by
    calc
      Real.sqrt (h ^ 3) ≤ 27 * w ^ 3 * x * Real.sqrt x := hroot
      _ = 27 * q * Real.sqrt x := by rw [show 27 * w ^ 3 * x = 27 * (w ^ 3 * x) by ring, hscale]
  simpa [x] using hroot'

/-- Scalar substitution proving the displayed C8 coefficient from the real
versions of the actual C7 incidence bounds. -/
theorem near_star_C8_numeric
    {w q b qU qD u d h J Δ : ℝ}
    (hw : 1000 ≤ w) (hwpos : 0 < w) (hq : 0 ≤ q)
    (hqSplit : qU + qD = q) (hqU : 0 ≤ qU)
    (hu : u ≤ w) (hd : 0 ≤ d) (hh : 0 ≤ h)
    (hD : d ≤ 24 * q / w ^ 2) (hPairs : h ≤ 9 * q / w)
    (hJbound : J ≤ d ^ 2 * w / 2) (hDelta : Δ ≤ 5 * w)
    (hC7 : b ≤ qU / 4 + 2 * qD / 3 + u / 4 + 5 * h / 4 +
      Real.sqrt (h ^ 3) / 2 + 5 * J / 3 + d * Δ / 3 + 32 * d ^ 3) :
    b ≤ w / 4 + q * (2 / 3 + 205 / (4 * w) +
      27 / 2 * Real.sqrt (q / w ^ 3) +
      480 * (q / w ^ 3) + 442368 * (q / w ^ 3) ^ 2) := by
  have hFive : 5 * h / 4 ≤ 45 * q / (4 * w) := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4)
      (by positivity : (0 : ℝ) < 4 * w)]
    rw [le_div_iff₀ hwpos] at hPairs
    nlinarith
  have hDpoly : d * w ^ 2 ≤ 24 * q := by
    rw [le_div_iff₀ (sq_pos_of_pos hwpos)] at hD
    nlinarith
  have hJterm : 5 * J / 3 ≤ 480 * q ^ 2 / w ^ 3 := by
    have hdsq : (d * w ^ 2) ^ 2 ≤ (24 * q) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hDpoly 2
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3)
      (by positivity : (0 : ℝ) < w ^ 3)]
    have hJmul := mul_le_mul_of_nonneg_right hJbound (by positivity : 0 ≤ 3 * w ^ 3)
    nlinarith [hJmul, hdsq]
  have hDeltaterm : d * Δ / 3 ≤ 40 * q / w := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3)
      (by positivity : (0 : ℝ) < w)]
    have hDeltamul := mul_le_mul_of_nonneg_left hDelta (by positivity : 0 ≤ d)
    have hProduct := mul_le_mul_of_nonneg_right hDpoly (by norm_num : (0 : ℝ) ≤ 5)
    nlinarith [hDeltamul, hProduct]
  have hDcube : (d * w ^ 2) ^ 3 ≤ (24 * q) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hDpoly 3
  have hB4 : 32 * d ^ 3 ≤ 442368 * q ^ 3 / w ^ 6 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < w ^ 6)]
    nlinarith [hDpoly, hDcube]
  have hRoot := near_star_C8_bad_pair_sqrt hwpos hq hh hPairs
  have hQlin : qU / 4 + 2 * qD / 3 ≤ 2 * q / 3 := by nlinarith [hqSplit]
  have hRootTerm : 27 * q * Real.sqrt (q / w ^ 3) / 2 =
      q * (27 / 2 * Real.sqrt (q / w ^ 3)) := by ring
  have hRootHalf := mul_le_mul_of_nonneg_right hRoot (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hJnorm : 480 * q ^ 2 / w ^ 3 = q * (480 * (q / w ^ 3)) := by
    field_simp [ne_of_gt hwpos]
  have hB4norm : 442368 * q ^ 3 / w ^ 6 =
      q * (442368 * (q / w ^ 3) ^ 2) := by
    field_simp [ne_of_gt hwpos]
  have hDeltanorm : 45 * q / (4 * w) + 40 * q / w =
      205 * q / (4 * w) := by ring
  have hExpand : w / 4 + q * (2 / 3 + 205 / (4 * w) +
      27 / 2 * Real.sqrt (q / w ^ 3) + 480 * (q / w ^ 3) +
      442368 * (q / w ^ 3) ^ 2) =
      w / 4 + 2 * q / 3 + 205 * q / (4 * w) +
      27 * q * Real.sqrt (q / w ^ 3) / 2 +
      480 * q ^ 2 / w ^ 3 + 442368 * q ^ 3 / w ^ 6 := by
    field_simp [ne_of_gt hwpos]
    ring
  rw [hExpand]
  linarith [hC7, hu, hFive, hJterm, hDeltaterm, hB4, hRoot, hRootHalf,
    hQlin, hRootTerm, hJnorm, hB4norm, hDeltanorm]

/-- The actual near-star C7 estimate and exceptional-set incidences imply the
displayed C8 inequality. -/
theorem near_star_C8_actual
    {H : Family α} {W : Edge α} {v : α} [Fintype α] [DecidableEq α]
    (hH : Admissible H) (hUniform : Uniform 4 H) (hvW : v ∉ W)
    (hw : 1000 ≤ W.card) :
    ((outsideEdges H W).card : ℝ) ≤
      (W.card : ℝ) / 4 + (missingStarTriples H W v).card *
        (2 / 3 + 205 / (4 * W.card) +
          27 / 2 * Real.sqrt ((missingStarTriples H W v).card / (W.card : ℝ) ^ 3) +
          480 * ((missingStarTriples H W v).card / (W.card : ℝ) ^ 3) +
          442368 * ((missingStarTriples H W v).card / (W.card : ℝ) ^ 3) ^ 2) := by
  classical
  let D := badSingletonVertices H W v 4
  let q := (missingStarTriples H W v).card
  let qU := (nearStarUMissingTriples H W v).card
  let qD := (nearStarDMissingTriples H W v).card
  let d := D.card
  let h := (nearStarBadPairs H W v).card
  let J := d.choose 2 * (W.card - 2)
  let Δ := W.card.choose 2 - (W.card - 5).choose 2
  let u := (W \ D).card
  let wr : ℝ := W.card
  let qr : ℝ := q
  let dr : ℝ := d
  let hr : ℝ := h
  let Jr : ℝ := J
  let Δr : ℝ := Δ
  let ur : ℝ := u
  let qUr : ℝ := qU
  let qDr : ℝ := qD
  let br : ℝ := (outsideEdges H W).card
  have hPartsNat := near_star_missing_triples_partition (H := H) (W := W) (v := v)
  have hParts : qU + qD = q := by simpa [qU, qD, q] using hPartsNat
  have hw5 : 5 ≤ W.card := by omega
  have hDeltaCast : (Δ : ℝ) =
      (W.card.choose 2 : ℝ) - ((W.card - 5).choose 2 : ℝ) := by
    dsimp [Δ]
    rw [Nat.cast_sub (Nat.choose_le_choose 2 (Nat.sub_le W.card 5))]
  have hC7 := near_star_C7_actual hH hUniform hvW
  have hC7r : br ≤ qUr / 4 + 2 * qDr / 3 + ur / 4 +
      5 * hr / 4 + Real.sqrt (hr ^ 3) / 2 + 5 * Jr / 3 +
      dr * Δr / 3 + 32 * dr ^ 3 := by
    dsimp [br, qUr, qDr, ur, hr, Jr, Δr, dr, D, qU, qD, u, h, J, Δ, d]
    rw [hDeltaCast]
    exact hC7
  have hwpos : 0 < wr := by dsimp [wr]; exact_mod_cast (show 0 < W.card by omega)
  have hqnonneg : 0 ≤ qr := by positivity
  have hDnat := near_star_exceptional_vertices_quadratic H W v (by omega)
  have hDreal : dr ≤ 24 * qr / wr ^ 2 := by
    have hpoly : dr * wr * wr ≤ 24 * qr := by
      dsimp [dr, wr, qr, d, q]
      exact_mod_cast hDnat
    rw [le_div_iff₀ (sq_pos_of_pos hwpos)]
    dsimp [dr, wr, qr]
    nlinarith [hpoly]
  have hpairNat := near_star_bad_pairs_incidence H W v
  have hpairReal : hr ≤ 9 * qr / wr := by
    have hcast : ((W.card - 6 : ℕ) : ℝ) * hr ≤ 6 * qr := by
      dsimp [hr, qr, h, q]
      exact_mod_cast hpairNat
    have hsub : ((W.card - 6 : ℕ) : ℝ) = wr - 6 := by
      dsimp [wr]
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [le_div_iff₀ hwpos]
    rw [hsub] at hcast
    have hLower : 2 * wr / 3 ≤ wr - 6 := by
      have hlarge : (18 : ℝ) ≤ wr := by dsimp [wr]; exact_mod_cast (show 18 ≤ W.card by omega)
      linarith
    nlinarith [hcast, hLower]
  have hDeltaNat : Δ ≤ 5 * W.card := by
    dsimp [Δ]
    have h := JSP523.Counting.choose_drop_difference_le W.card 2 5 (by omega) (by omega)
    simpa using h
  have hDeltaReal : Δr ≤ 5 * wr := by
    dsimp [Δr, wr]
    exact_mod_cast hDeltaNat
  have hJNat : 2 * J ≤ d ^ 2 * W.card := by
    dsimp [J]
    have hChoose : 2 * d.choose 2 ≤ d ^ 2 := by
      rw [Nat.choose_two_right]
      have hEven : Even (d * (d - 1)) := by simpa using Nat.even_mul_pred_self d
      have hCancel := Nat.div_two_mul_two_of_even hEven
      nlinarith [Nat.sub_le d 1]
    have hSub : W.card - 2 ≤ W.card := Nat.sub_le _ _
    nlinarith
  have hJReal : Jr ≤ dr ^ 2 * wr / 2 := by
    have hc : 2 * Jr ≤ dr ^ 2 * wr := by
      dsimp [Jr, dr, wr]
      exact_mod_cast hJNat
    dsimp [Jr, dr, wr]
    nlinarith
  have huReal : ur ≤ wr := by
    dsimp [ur, wr, u, D]
    exact_mod_cast (Finset.card_le_card (Finset.sdiff_subset : W \ badSingletonVertices H W v 4 ⊆ W))
  have hqUreal : qUr + qDr = qr := by
    dsimp [qUr, qDr, qr]
    exact_mod_cast hParts
  have hqUpos : 0 ≤ qUr := by positivity
  have hhpos : 0 ≤ hr := by positivity
  have hwReal : 1000 ≤ wr := by
    dsimp [wr]
    exact_mod_cast hw
  have hC8 := near_star_C8_numeric hwReal hwpos hqnonneg hqUreal hqUpos
    huReal (by positivity) hhpos hDreal hpairReal hJReal hDeltaReal hC7r
  simpa [br, wr, qr, q, u, ur] using hC8

/-- The C8 range contracts its coefficient to the coarse interface used in
the final numerical close. -/
theorem near_star_C8_actual_coarse
    {H : Family α} {W : Edge α} {v : α} [Fintype α] [DecidableEq α]
    (hH : Admissible H) (hUniform : Uniform 4 H) (hvW : v ∉ W)
    (hw : 1000 ≤ W.card)
    (hq : 10000 * (missingStarTriples H W v).card ≤ W.card ^ 3) :
    12 * (outsideEdges H W).card ≤
      3 * W.card + 11 * (missingStarTriples H W v).card := by
  exact c8_implies_coarse_interface hw hq
    (near_star_C8_actual hH hUniform hvW hw)

/-- The actual near-star estimates close the rank-four local upper bound in
the C8 range. -/
theorem rank_four_local_upper_of_near_star_C8
    {H : Family α} {W : Edge α} {v : α} [Fintype α] [DecidableEq α]
    (hH : Admissible H) (hUniform : Uniform 4 H)
    (hSupport : ∀ E ∈ H, E ⊆ insert v W) (hvW : v ∉ W)
    (hw : 1000 ≤ W.card)
    (hq : 10000 * (missingStarTriples H W v).card ≤ W.card ^ 3) :
    H.card ≤ W.card.choose 3 + W.card / 4 := by
  apply rank_four_local_upper_of_edge_count_interfaces
    hH hUniform hSupport hvW hw
  · exact near_star_C8_actual_coarse hH hUniform hvW hw hq
  · intro hD hBad
    exact near_star_outside_refined_244 hH hUniform hvW hD hBad

/-- The complete finite near-star conclusion of Theorem III.2: the exact
upper bound, and whenever the family reaches the complete-star threshold,
linearity of the outside family together with its sharp incidence bound. -/
theorem rank_four_near_star_exactness
    {H : Family α} {W : Edge α} {v : α} [Fintype α] [DecidableEq α]
    (hH : Admissible H) (hUniform : Uniform 4 H)
    (hSupport : ∀ E ∈ H, E ⊆ insert v W) (hvW : v ∉ W)
    (hw : 1000 ≤ W.card)
    (hq : 10000 * (missingStarTriples H W v).card ≤ W.card ^ 3) :
    H.card ≤ W.card.choose 3 + W.card / 4 ∧
      (W.card.choose 3 ≤ H.card →
        LinearFamily (outsideEdges H W) ∧
        4 * (outsideEdges H W).card ≤
          (missingStarTriples H W v).card + W.card) := by
  have hUpper := rank_four_local_upper_of_near_star_C8
    hH hUniform hSupport hvW hw hq
  refine ⟨hUpper, ?_⟩
  intro hThreshold
  have hCoarse := near_star_C8_actual_coarse hH hUniform hvW hw hq
  have hVertex := near_star_exceptional_vertices_quadratic H W v (by omega)
  have hPair := near_star_bad_pairs_incidence H W v
  let B := outsideEdges H W
  have hStar := rank_four_star_outside_card hUniform hSupport hvW
  have hPartition := present_add_missing_star H W v
  have hDecomp : H.card + (missingStarTriples H W v).card =
      W.card.choose 3 + B.card := by
    rw [hStar]
    change (presentStarTriples H W v).card + B.card +
      (missingStarTriples H W v).card = _
    omega
  have hbq : (missingStarTriples H W v).card ≤ B.card := by omega
  have hPair' : (nearStarBadPairs H W v).card * (W.card - 6) ≤
      6 * (missingStarTriples H W v).card := by
    have hPair0 := hPair
    change (W.card - 6) * (nearStarBadPairs H W v).card ≤
      6 * (missingStarTriples H W v).card at hPair0
    nlinarith [hPair0]
  have hCounts := near_star_coarse_bounds_exceptional_counts
    hw hbq hCoarse hVertex hPair'
  have hRefined := near_star_outside_refined_244 hH hUniform hvW
    hCounts.2.1 hCounts.2.2
  have hSmall := near_star_refined_implies_small_missing
    hw hbq hRefined
  have hBH : B ⊆ H := Finset.filter_subset _ _
  have hBU : Uniform 4 B := by
    intro E hE
    exact hUniform (hBH hE)
  have hBW : ∀ E ∈ B, E ⊆ W := by
    intro E hE
    exact (Finset.mem_filter.mp hE).2
  have hLinear : LinearFamily B := small_missing_implies_outside_linear
    hH hBH hBU hBW hvW (by omega) hSmall
  have hIncidence := linear_outside_edges_incidence_bound
    hH hBH hBU hLinear hBW hvW
  exact ⟨hLinear, by simpa [B, Nat.add_comm] using hIncidence⟩

/-- Equality necessity in Theorem III.2: the outside family is either a
maximum matching, or has the unique missing-star-triple exceptional-pair
normal form. -/
theorem rank_four_near_star_equality_necessary
    {H : Family α} {W : Edge α} {v : α} [Fintype α] [DecidableEq α]
    (hH : Admissible H) (hUniform : Uniform 4 H)
    (hSupport : ∀ E ∈ H, E ⊆ insert v W) (hvW : v ∉ W)
    (hw : 1000 ≤ W.card)
    (hq : 10000 * (missingStarTriples H W v).card ≤ W.card ^ 3)
    (hEquality : H.card = W.card.choose 3 + W.card / 4) :
    ((missingStarTriples H W v).card = 0 ∧
      IsMatching (outsideEdges H W) ∧
      (outsideEdges H W).card = W.card / 4) ∨
    ((missingStarTriples H W v).card = 1 ∧
      ∃ P x Q M,
        missingStarTriples H W v = {P} ∧ P.card = 3 ∧ W.card % 4 = 3 ∧
        x ∈ W ∧ x ∉ P ∧ Q.card = 3 ∧ Disjoint P Q ∧ x ∉ Q ∧
        outsideEdges H W = insert (insert x P) (insert (insert x Q) M) ∧
        IsMatching M ∧
        (∀ E ∈ M, Disjoint E (insert x P ∪ insert x Q)) ∧
        M.biUnion (fun E => E) = W \ (insert x P ∪ insert x Q)) := by
  have hLin := (rank_four_near_star_exactness
    hH hUniform hSupport hvW hw hq).2 (by omega)
  have hRestriction := linear_outside_equality_missing_restriction
    hH hUniform hSupport hvW hLin.1 hEquality
  by_cases hMissing : (missingStarTriples H W v).card = 0
  · have hMatch := complete_star_equality_matching
      hH hUniform hSupport hvW (by omega) hMissing hEquality
    exact Or.inl ⟨hMissing, hMatch.1, hMatch.2⟩
  · have hOne : (missingStarTriples H W v).card = 1 := by
      have hBound := hRestriction.1
      omega
    have hMod : W.card % 4 = 3 := hRestriction.2 hOne
    have hClass := rank_four_one_missing_equality_classification
      hH hUniform hSupport hvW hLin.1 hEquality hOne
    exact Or.inr ⟨hOne, hClass⟩

/-- Theorem III.2 equality is equivalent to one of the two stated local
outside-family forms. -/
theorem rank_four_near_star_equality_iff
    {H : Family α} {W : Edge α} {v : α} [Fintype α] [DecidableEq α]
    (hH : Admissible H) (hUniform : Uniform 4 H)
    (hSupport : ∀ E ∈ H, E ⊆ insert v W) (hvW : v ∉ W)
    (hw : 1000 ≤ W.card)
    (hq : 10000 * (missingStarTriples H W v).card ≤ W.card ^ 3) :
    H.card = W.card.choose 3 + W.card / 4 ↔
      RankFourNearStarEqualityFamily H W v := by
  constructor
  · intro hEquality
    rcases rank_four_near_star_equality_necessary
        hH hUniform hSupport hvW hw hq hEquality with hZero | hOne
    · simpa [RankFourNearStarEqualityFamily] using (Or.inl hZero)
    · rcases hOne with ⟨hMissing, P, x, Q, M, hP, hPcard, hMod,
        hxW, hxP, hQcard, hPQ, hxQ, hBform, hMatch, hMdisj, hCover⟩
      have hStar := rank_four_star_outside_card hUniform hSupport hvW
      have hPartition := present_add_missing_star H W v
      let B := outsideEdges H W
      have hDecomp : H.card + (missingStarTriples H W v).card =
          W.card.choose 3 + B.card := by
        rw [hStar]
        calc
          (presentStarTriples H W v).card + B.card +
              (missingStarTriples H W v).card =
              ((presentStarTriples H W v).card +
                (missingStarTriples H W v).card) + B.card := by omega
          _ = W.card.choose 3 + B.card := by rw [hPartition]
      have hBcard : B.card = W.card / 4 + 1 := by
        omega
      exact Or.inr ⟨hMissing, P, x, Q, M, hP, hPcard, hMod,
        hxW, hxP, hQcard, hPQ, hxQ, hBform, hMatch, hMdisj, hCover,
        hBcard⟩
  · intro hForm
    have hStar := rank_four_star_outside_card hUniform hSupport hvW
    have hPartition := present_add_missing_star H W v
    let B := outsideEdges H W
    have hDecomp : H.card + (missingStarTriples H W v).card =
        W.card.choose 3 + B.card := by
      rw [hStar]
      calc
        (presentStarTriples H W v).card + B.card +
            (missingStarTriples H W v).card =
            ((presentStarTriples H W v).card +
              (missingStarTriples H W v).card) + B.card := by omega
        _ = W.card.choose 3 + B.card := by rw [hPartition]
    rcases hForm with ⟨hMissing, _, hBcard⟩ | ⟨hMissing, P, x, Q, M,
      _, _, _, _, _, _, _, _, _, _, _, _, hBcard⟩
    · omega
    · omega

/-- Combined Lean interface for all conclusions of Theorem III.2. -/
theorem rank_four_near_star_theorem_III2
    {H : Family α} {W : Edge α} {v : α} [Fintype α] [DecidableEq α]
    (hH : Admissible H) (hUniform : Uniform 4 H)
    (hSupport : ∀ E ∈ H, E ⊆ insert v W) (hvW : v ∉ W)
    (hw : 1000 ≤ W.card)
    (hq : 10000 * (missingStarTriples H W v).card ≤ W.card ^ 3) :
    (H.card + (missingStarTriples H W v).card =
      W.card.choose 3 + (outsideEdges H W).card) ∧
    H.card ≤ W.card.choose 3 + W.card / 4 ∧
    (W.card.choose 3 ≤ H.card →
      LinearFamily (outsideEdges H W) ∧
      4 * (outsideEdges H W).card ≤
        (missingStarTriples H W v).card + W.card) ∧
    (H.card = W.card.choose 3 + W.card / 4 →
      ((missingStarTriples H W v).card = 0 ∧
        IsMatching (outsideEdges H W) ∧
        (outsideEdges H W).card = W.card / 4) ∨
      ((missingStarTriples H W v).card = 1 ∧
        ∃ P x Q M,
          missingStarTriples H W v = {P} ∧ P.card = 3 ∧ W.card % 4 = 3 ∧
          x ∈ W ∧ x ∉ P ∧ Q.card = 3 ∧ Disjoint P Q ∧ x ∉ Q ∧
          outsideEdges H W = insert (insert x P) (insert (insert x Q) M) ∧
          IsMatching M ∧
          (∀ E ∈ M, Disjoint E (insert x P ∪ insert x Q)) ∧
          M.biUnion (fun E => E) = W \ (insert x P ∪ insert x Q))) := by
  have hStar := rank_four_star_outside_card hUniform hSupport hvW
  have hPartition := present_add_missing_star H W v
  have hIdentity : H.card + (missingStarTriples H W v).card =
      W.card.choose 3 + (outsideEdges H W).card := by
    rw [hStar]
    calc
      (presentStarTriples H W v).card + (outsideEdges H W).card +
          (missingStarTriples H W v).card =
          ((presentStarTriples H W v).card +
            (missingStarTriples H W v).card) + (outsideEdges H W).card := by omega
      _ = W.card.choose 3 + (outsideEdges H W).card := by rw [hPartition]
  have hExact := rank_four_near_star_exactness hH hUniform hSupport hvW hw hq
  refine ⟨hIdentity, hExact.1, hExact.2, ?_⟩
  intro hEquality
  exact rank_four_near_star_equality_necessary
    hH hUniform hSupport hvW hw hq hEquality

end JSP523.Rank4
