import JSP523.Rank4.LocalExactLinear

/-!
# Numerical close of the rank-four near-star argument

§III.C of the all-rank manuscript first obtains (III.C.8), then bounds the
exceptional vertex and pair counts, and finally applies (III.C.6).
The lemmas here formalize the numerical implications. The combinatorial
derivations of (III.C.6) and (III.C.8) remain separate obligations.
-/

namespace JSP523.Rank4

/-- The coefficient `11/12` in equation (III.C.8) gives `q ≤ 3w` whenever
the outside edges compensate for every missing star triple.  The stated
exceptional-count estimates then force no exceptional vertices and at most
eighteen bad pairs. -/
theorem near_star_coarse_bounds_exceptional_counts
    {w q b d h : ℕ}
    (hw : 1000 ≤ w)
    (hbq : q ≤ b)
    (hCoarse : 12 * b ≤ 3 * w + 11 * q)
    (hVertex : d * w * w ≤ 24 * q)
    (hPair : h * (w - 6) ≤ 6 * q) :
    q ≤ 3 * w ∧ d = 0 ∧ h ≤ 18 := by
  have hq : q ≤ 3 * w := by omega
  have hd : d = 0 := by
    by_contra hdn
    have hd1 : 1 ≤ d := by omega
    have hWsq : 1000 * w ≤ w * w :=
      Nat.mul_le_mul_right w hw
    have hDsq : w * w ≤ d * w * w := by
      have h := Nat.mul_le_mul_right (w * w) hd1
      simpa only [one_mul, mul_assoc] using h
    have hwPos : 0 < w := by omega
    omega
  have hh : h ≤ 18 := by
    by_contra hhn
    have hh19 : 19 ≤ h := by omega
    have h19 : 19 * (w - 6) ≤ h * (w - 6) :=
      Nat.mul_le_mul_right (w - 6) hh19
    omega
  exact ⟨hq, hd, hh⟩

/-- Once the exceptional sets vanish or are bounded, estimate (III.C.6)
makes the missing-star budget small enough
to force outside linearity. -/
theorem near_star_refined_implies_small_missing
    {w q b : ℕ}
    (hw : 1000 ≤ w)
    (hbq : q ≤ b)
    (hRefined : 4 * b ≤ q + w + 244) :
    q < w - 6 := by
  omega

/-- The exact local upper bound follows from the numerical coarse and
refined interfaces together with the already proved small-budget
linearity theorem. -/
theorem rank_four_local_upper_of_numerical_interfaces
    {α : Type*} [DecidableEq α]
    {H : Family α} {W : Edge α} {v : α} {d h : ℕ}
    (hH : Admissible H) (hU : Uniform 4 H)
    (hSupport : ∀ E ∈ H, E ⊆ insert v W)
    (hvW : v ∉ W) (hw : 1000 ≤ W.card)
    (hCoarse :
      12 * (outsideEdges H W).card ≤
        3 * W.card + 11 * (missingStarTriples H W v).card)
    (hVertex : d * W.card * W.card ≤
      24 * (missingStarTriples H W v).card)
    (hPair : h * (W.card - 6) ≤
      6 * (missingStarTriples H W v).card)
    (hRefined :
      d = 0 → h ≤ 18 →
        4 * (outsideEdges H W).card ≤
          (missingStarTriples H W v).card + W.card + 244) :
    H.card ≤ W.card.choose 3 + W.card / 4 := by
  by_cases hBelow : H.card < W.card.choose 3
  · omega
  · have hStar := rank_four_star_outside_card hU hSupport hvW
    have hMissing := present_add_missing_star H W v
    have hbq : (missingStarTriples H W v).card ≤
        (outsideEdges H W).card := by omega
    obtain ⟨_, hd, hh⟩ := near_star_coarse_bounds_exceptional_counts
      hw hbq hCoarse hVertex hPair
    have hSmall := near_star_refined_implies_small_missing
      hw hbq (hRefined hd hh)
    exact rank_four_local_upper_of_small_missing
      hH hU hSupport hvW (by omega) hSmall

end JSP523.Rank4
