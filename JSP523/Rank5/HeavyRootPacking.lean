import JSP523.Rank5.ShadowExtraction

/-!
# Finite packing of heavy roots for Part IV regularization

The first stage of §IV.4 covers heavy roots by a small vertex set. A direct
union-and-overlap estimate gives the finite matching bound needed there.
It has the same asymptotic strength as the manuscript's Cauchy estimate in
the regime `T²/R → ∞`.
-/

namespace JSP523.Rank5

variable {ι β : Type*} [DecidableEq ι] [DecidableEq β]

/-- A finite family of large fibers with small pairwise intersections
cannot have too many members. The overlap term is deliberately ordered. -/
theorem large_fibers_union_overlap_bound
    (X : Finset ι) (U : Finset β) (A : ι → Finset β)
    (d c : ℕ)
    (hInside : ∀ x ∈ X, A x ⊆ U)
    (hLarge : ∀ x ∈ X, d ≤ (A x).card)
    (hPair : ∀ x ∈ X, ∀ y ∈ X.erase x,
      (A x ∩ A y).card ≤ c) :
    X.card * d ≤ U.card + X.card * X.card * c := by
  classical
  have hLower : X.card * d ≤ ∑ x ∈ X, (A x).card := by
    have hSum := Finset.sum_le_sum hLarge
    simpa [nsmul_eq_mul] using hSum
  have hUnion : (X.biUnion A).card ≤ U.card := by
    apply Finset.card_le_card
    intro z hz
    obtain ⟨x, hx, hzx⟩ := Finset.mem_biUnion.mp hz
    exact hInside x hx hzx
  have hOverlap : orderedOverlap X A ≤ X.card * X.card * c := by
    let C := c
    have hInner : ∀ x ∈ X,
        (∑ y ∈ X.erase x, (A x ∩ A y).card) ≤ X.card * C := by
      intro x hx
      have hSum := Finset.sum_le_card_nsmul (X.erase x)
        (fun y => (A x ∩ A y).card) C (hPair x hx)
      have hCard : (X.erase x).card ≤ X.card :=
        Finset.card_le_card (Finset.erase_subset x X)
      calc
        _ ≤ (X.erase x).card * C := by simpa [nsmul_eq_mul] using hSum
        _ ≤ X.card * C := Nat.mul_le_mul_right C hCard
    have hSum := Finset.sum_le_card_nsmul X
      (fun x => ∑ y ∈ X.erase x, (A x ∩ A y).card)
      (X.card * C) hInner
    unfold orderedOverlap
    simpa [nsmul_eq_mul, mul_assoc, C] using hSum
  have hBudget := sum_card_le_union_add_orderedOverlap X A
  omega

/-- If the displayed numerical gap holds at size `a`, no matching of
`a` large fibers can exist. -/
theorem large_fibers_card_lt_of_gap
    (X : Finset ι) (U : Finset β) (A : ι → Finset β)
    (d c a : ℕ)
    (hInside : ∀ x ∈ X, A x ⊆ U)
    (hLarge : ∀ x ∈ X, d ≤ (A x).card)
    (hPair : ∀ x ∈ X, ∀ y ∈ X.erase x,
      (A x ∩ A y).card ≤ c)
    (hGap : U.card + a * a * c < a * d) : X.card < a := by
  by_contra hNot
  have hSize : a ≤ X.card := by omega
  obtain ⟨Y, hYX, hYcard⟩ := Finset.exists_subset_card_eq hSize
  have hBound := large_fibers_union_overlap_bound Y U A d c
    (fun x hx => hInside x (hYX hx))
    (fun x hx => hLarge x (hYX hx))
    (by
      intro x hx y hy
      have hyX := (Finset.mem_erase.mp hy).2
      have hxy := (Finset.mem_erase.mp hy).1
      exact hPair x (hYX hx) y
        (Finset.mem_erase.mpr ⟨hxy, hYX hyX⟩))
  rw [hYcard] at hBound
  omega

end JSP523.Rank5
