import JSP523.Rank5.ActualBadPairDeletion
import JSP523.Rank5.BadRootPowerBounds
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

/-!
# Polynomial-scale error estimate for actual bad-pair edges

Combines the actual three-stratum deletion estimate with the k=2 bad-root
incidence bound. The estimate is cleared of all denominators and includes
the endpoint rank `r = 5`.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

/-- The actual bad-pair edge count has a denominator-free polynomial error
bound. Here `q` is the number of missing-star facets and
`C(r) = 2 (4r)^(r-1) choose(r-1,2)`. -/
theorem actual_bad_pair_error_power_bound
    (H : Family α) (W : Edge α) (v : α) (r : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hr : 5 ≤ r) (hvW : v ∉ W) (hw : 4 * r ≤ W.card) :
    let Bad₂ := badMissingSets H W v r 2
      ((W.card - r - 2).choose (r - 3))
    let q := (missingStarFacets H W v r).card
    let C := 2 * (4 * r) ^ (r - 1) * (r - 1).choose 2
    W.card ^ (r - 1) * (badPairEdges (ordinaryOutsideFamily H W v r) Bad₂).card
      ≤ C * q * W.card ^ (r - 2) + 2 * C ^ 2 * q ^ 2 := by
  classical
  let w := W.card
  let Λ := (w - r - 2).choose (r - 3)
  let Bad₂ := badMissingSets H W v r 2 Λ
  let q := (missingStarFacets H W v r).card
  let h := (r - 1).choose 2
  let C := 2 * (4 * r) ^ (r - 1) * h
  have hr3 : 3 ≤ r := by omega
  have hk₂ : 2 ≤ r - 2 := by omega
  have hRoot := actual_bad_root_power_bound H W v r 2 hr3 (by omega) hk₂ hw
  change Bad₂.card * w ^ (r - 3) ≤ C * q at hRoot
  have hDel := actual_ordinary_bad_pair_deletion_bound H W v r
    hAdm hUniform hr hvW
  have hEdges : (badPairEdges (ordinaryOutsideFamily H W v r) Bad₂).card ≤
      Bad₂.card * w.choose (r - 4) +
        Bad₂.card * (Bad₂.card * w.choose (r - 5)) +
        Bad₂.card * (Bad₂.card * w.choose (r - 5)) := by
    simpa [Bad₂, Λ, w] using hDel.1
  have hChoose₁ : w.choose (r - 4) ≤ w ^ (r - 4) := Nat.choose_le_pow w _
  have hChoose₂ : w.choose (r - 5) ≤ w ^ (r - 5) := Nat.choose_le_pow w _
  have hwpos : 0 < w := by omega
  have hFirst : w ^ (r - 1) *
      (Bad₂.card * w.choose (r - 4)) ≤ C * q * w ^ (r - 2) := by
    have hbase : Bad₂.card * w ^ (r - 3) * w ^ 2 ≤
        C * q * w ^ 2 := Nat.mul_le_mul_right _ hRoot
    have hpow1 : r - 1 = (r - 3) + 2 := by omega
    have hpow2 : r - 2 = 2 + (r - 4) := by omega
    calc
      w ^ (r - 1) * (Bad₂.card * w.choose (r - 4))
          ≤ w ^ (r - 1) * (Bad₂.card * w ^ (r - 4)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hChoose₁)
      _ = (Bad₂.card * w ^ (r - 3)) * w ^ 2 * w ^ (r - 4) := by
        rw [hpow1, pow_add]
        ac_rfl
      _ ≤ (C * q * w ^ 2) * w ^ (r - 4) :=
        Nat.mul_le_mul_right _ hbase
      _ = C * q * w ^ (r - 2) := by
        rw [hpow2, pow_add]
        ac_rfl
  have hSquare : Bad₂.card ^ 2 * w ^ (2 * (r - 3)) ≤ (C * q) ^ 2 := by
    have hs := Nat.mul_le_mul hRoot hRoot
    simpa [pow_two, Nat.pow_mul, Nat.mul_pow, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm] using hs
  have hScaled : w ^ (r - 1) *
      (Bad₂.card * (Bad₂.card * w.choose (r - 5))) ≤ C ^ 2 * q ^ 2 := by
    -- The extra two powers in the factorization above cancel against the
    -- two powers saved by the `r-5` tail cap; this also works when `r=5`.
    have hCore : w ^ (r - 1) * w ^ (r - 5) = w ^ (2 * (r - 3)) := by
      rw [← pow_add]
      congr 1
      omega
    calc
      w ^ (r - 1) * (Bad₂.card * (Bad₂.card * w.choose (r - 5)))
          ≤ w ^ (r - 1) * (Bad₂.card * (Bad₂.card * w ^ (r - 5))) := by
            exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
              (Nat.mul_le_mul_left _ hChoose₂))
      _ = Bad₂.card ^ 2 * w ^ (2 * (r - 3)) := by
        calc
          _ = Bad₂.card ^ 2 * (w ^ (r - 1) * w ^ (r - 5)) := by
            simp only [pow_two]
            ac_rfl
          _ = _ := by rw [hCore]
      _ ≤ (C * q) ^ 2 := hSquare
      _ = C ^ 2 * q ^ 2 := by ring
  have hBoth : w ^ (r - 1) *
        (Bad₂.card * (Bad₂.card * w.choose (r - 5))) +
      w ^ (r - 1) *
        (Bad₂.card * (Bad₂.card * w.choose (r - 5))) ≤
        2 * C ^ 2 * q ^ 2 := by
    calc
      _ ≤ C ^ 2 * q ^ 2 + C ^ 2 * q ^ 2 := Nat.add_le_add hScaled hScaled
      _ = _ := by ring
  change w ^ (r - 1) *
    (badPairEdges (ordinaryOutsideFamily H W v r) Bad₂).card ≤
      C * q * w ^ (r - 2) + 2 * C ^ 2 * q ^ 2
  calc
    _ ≤ w ^ (r - 1) *
        (Bad₂.card * w.choose (r - 4) +
          Bad₂.card * (Bad₂.card * w.choose (r - 5)) +
          Bad₂.card * (Bad₂.card * w.choose (r - 5))) :=
      Nat.mul_le_mul_left _ hEdges
    _ = w ^ (r - 1) * (Bad₂.card * w.choose (r - 4)) +
        w ^ (r - 1) * (Bad₂.card * (Bad₂.card * w.choose (r - 5))) +
        w ^ (r - 1) * (Bad₂.card * (Bad₂.card * w.choose (r - 5))) := by ring
    _ ≤ C * q * w ^ (r - 2) + 2 * C ^ 2 * q ^ 2 := by
      nlinarith [hFirst, hScaled]

end JSP523
