import JSP523.Rank4.LocalExceptionalSets

/-!
# Pair-root tail restriction in the rank-four near-star argument
-/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- For a fixed pair root, two distinct outside completions cannot both have
nonexceptional pair tails. This is the `s = 2` missing-difference incidence
fact from (III.C.2), specialized to rank four. -/
theorem near_star_pair_root_at_most_one_nonbad_tail
    {H : Family α} {W : Edge α} {v : α} {E F T T' : Edge α}
    (hH : Admissible H) (hvW : v ∉ W)
    (hE : E ∈ H) (hF : F ∈ H)
    (hEsub : E ⊆ W) (hFsub : F ⊆ W)
    (hEcard : E.card = 4) (hFcard : F.card = 4)
    (hShared : (E ∩ F).Nonempty) (hEF : E ≠ F)
    (hDiffE : E \ F = T) (hDiffF : F \ E = T')
    (hTcard : T.card = 2)
    (hTnotBad : T ∉ nearStarBadPairs H W v)
    (hT'notBad : T' ∉ nearStarBadPairs H W v) : False := by
  have hBad := overlapping_edges_have_bad_missing_set
    hH hE hF hEsub hFsub hEcard hFcard hEF hShared hvW
  dsimp only at hBad
  rw [hDiffE, hDiffF, hTcard] at hBad
  have hchoose : (W.card - 4 - 2).choose (4 - 1 - 2) = W.card - 6 := by
    simp only [show 4 - 1 - 2 = 1 by omega, Nat.choose_one_right]
    omega
  rw [hchoose] at hBad
  exact hBad.elim
    (by simpa [nearStarBadPairs] using hTnotBad)
    (by simpa [nearStarBadPairs] using hT'notBad)

end JSP523.Rank4
