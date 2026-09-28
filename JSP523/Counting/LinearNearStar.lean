import JSP523.Counting.PrefixCommonSystem
import JSP523.Matching
import Mathlib.Data.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Linear outside edges near a star

The incidence injection below proves (IV.2.6) of
`jsp-000523-proof/paper/proof.md`
for every rank `r ≥ 3`.  At rank four it also recovers (III.C.3).
Each incidence `(E,a)` is sent either to its missing opposite star facet
or to the vertex `a`.  The forbidden switch supplies injectivity in the
second case; linearity supplies it in the first.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

/-- Missing facets of the star with center `v` and outside set `W`. -/
def missingStarFacets (H : Family α) (W : Edge α) (v : α)
    (r : ℕ) : Family α :=
  (W.powersetCard (r - 1)).filter fun T => insert v T ∉ H

private theorem erase_card_pred
    {E : Edge α} {a : α} {r : ℕ}
    (hEcard : E.card = r) (ha : a ∈ E) :
    (E.erase a).card = r - 1 := by
  have h := Finset.card_erase_add_one ha
  omega

private theorem equal_erases_same_vertex
    {E : Edge α} {a b : α}
    (hb : b ∈ E) (hEq : E.erase a = E.erase b) : a = b := by
  by_contra hne
  have hbEraseA : b ∈ E.erase a := Finset.mem_erase.mpr ⟨Ne.symm hne, hb⟩
  rw [hEq] at hbEraseA
  exact (Finset.notMem_erase b E) hbEraseA

private theorem linear_equal_erases
    {B : Family α} {E F : Edge α} {a b : α} {r : ℕ}
    (hU : Uniform r B) (hLin : LinearFamily B) (hr : 3 ≤ r)
    (hE : E ∈ B) (hF : F ∈ B)
    (ha : a ∈ E) (hb : b ∈ F)
    (hEq : E.erase a = F.erase b) : E = F ∧ a = b := by
  have hTcard : (E.erase a).card = r - 1 :=
    erase_card_pred (hU hE) ha
  have hEF : E = F := by
    by_contra hne
    have hSub : E.erase a ⊆ E ∩ F := by
      intro x hx
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_of_mem_erase hx, by
          rw [hEq] at hx
          exact Finset.mem_of_mem_erase hx⟩
    have hBound := Finset.card_le_card hSub
    have hOne := hLin hE hF hne
    omega
  subst F
  exact ⟨rfl, equal_erases_same_vertex hb hEq⟩

private theorem present_erases_force_same_edge
    {H B : Family α} {W E F : Edge α} {v a : α} {r : ℕ}
    (hH : Admissible H) (hBH : B ⊆ H)
    (hU : Uniform r B) (hLin : LinearFamily B) (hr : 3 ≤ r)
    (hW : ∀ G ∈ B, G ⊆ W) (hvW : v ∉ W)
    (hE : E ∈ B) (hF : F ∈ B)
    (haE : a ∈ E) (haF : a ∈ F)
    (hStarE : insert v (E.erase a) ∈ H)
    (hStarF : insert v (F.erase a) ∈ H) : E = F := by
  by_contra hEF
  let T := E.erase a
  let S := F.erase a
  have haW : a ∈ W := hW E hE haE
  have hav : a ≠ v := by
    intro h
    exact hvW (h ▸ haW)
  have hTcard : T.card = r - 1 := erase_card_pred (hU hE) haE
  have hScard : S.card = r - 1 := erase_card_pred (hU hF) haF
  have hTnon : T.Nonempty := Finset.card_pos.mp (by omega)
  have hSnon : S.Nonempty := Finset.card_pos.mp (by omega)
  have hTa : Disjoint T ({a} : Edge α) :=
    Finset.disjoint_singleton_right.mpr (Finset.notMem_erase a E)
  have hSa : Disjoint S ({a} : Edge α) :=
    Finset.disjoint_singleton_right.mpr (Finset.notMem_erase a F)
  have hTv : Disjoint T ({v} : Edge α) := by
    apply Finset.disjoint_singleton_right.mpr
    intro hvT
    exact hvW (hW E hE (Finset.mem_of_mem_erase hvT))
  have hSv : Disjoint S ({v} : Edge α) := by
    apply Finset.disjoint_singleton_right.mpr
    intro hvS
    exact hvW (hW F hF (Finset.mem_of_mem_erase hvS))
  have hTS : Disjoint T S := by
    apply Finset.disjoint_left.mpr
    intro x hxT hxS
    have hxa : x ≠ a := Finset.ne_of_mem_erase hxT
    have hPair : ({a, x} : Edge α) ⊆ E ∩ F := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hya
      · exact Finset.mem_inter.mpr ⟨haE, haF⟩
      · have hyx : y = x := Finset.mem_singleton.mp hya
        exact Finset.mem_inter.mpr
          ⟨hyx ▸ Finset.mem_of_mem_erase hxT,
           hyx ▸ Finset.mem_of_mem_erase hxS⟩
    have hTwo := Finset.card_le_card hPair
    have hCardPair : ({a, x} : Edge α).card = 2 :=
      Finset.card_pair hxa.symm
    have hOne := hLin hE hF hEF
    omega
  have hQuad : ForbiddenQuad
      (({a} : Edge α) ∪ T) (({v} : Edge α) ∪ S)
      (({a} : Edge α) ∪ S) (({v} : Edge α) ∪ T) :=
    prefix_switch_forbidden (by simp) (by simp) hTnon hSnon
      (Finset.disjoint_singleton.mpr hav) hTa hTv hSa hSv hTS
  have hEeq : ({a} : Edge α) ∪ T = E := by
    simpa [T, Finset.singleton_union] using Finset.insert_erase haE
  have hFeq : ({a} : Edge α) ∪ S = F := by
    simpa [S, Finset.singleton_union] using Finset.insert_erase haF
  have hQuad' : ForbiddenQuad E (insert v S) F (insert v T) := by
    simpa only [hEeq, hFeq, Finset.singleton_union] using hQuad
  exact hH (hBH hE) hStarF (hBH hF) hStarE hQuad'

/-- The exact linear incidence inequality for any rank `r ≥ 3`.
Specializing to `U ⊆ W` yields (IV.2.6). -/
theorem linear_near_star_incidence_bound
    {H B : Family α} {W : Edge α} {v : α} {r : ℕ}
    (hH : Admissible H) (hBH : B ⊆ H)
    (hU : Uniform r B) (hLin : LinearFamily B) (hr : 3 ≤ r)
    (hW : ∀ E ∈ B, E ⊆ W) (hvW : v ∉ W) :
    r * B.card ≤ W.card + (missingStarFacets H W v r).card := by
  classical
  let I : Finset (Σ _E : Edge α, α) := B.sigma fun E => E
  have hIcard : I.card = r * B.card := by
    calc
      I.card = ∑ E ∈ B, E.card := Finset.card_sigma B (fun E => E)
      _ = ∑ _E ∈ B, r := by
        apply Finset.sum_congr rfl
        intro E hE
        exact hU hE
      _ = r * B.card := by simp [Finset.sum_const, mul_comm]
  let target : Finset (α ⊕ Edge α) :=
    W.disjSum (missingStarFacets H W v r)
  let f : (Σ _E : Edge α, α) → α ⊕ Edge α := fun p =>
    if insert v (p.1.erase p.2) ∈ H then Sum.inl p.2
    else Sum.inr (p.1.erase p.2)
  have hmem (p : Σ _E : Edge α, α) (hp : p ∈ I) :
      p.1 ∈ B ∧ p.2 ∈ p.1 := by
    simpa only [I, Finset.mem_sigma] using hp
  have hmap : ∀ p ∈ I, f p ∈ target := by
    intro ⟨E, a⟩ hp
    obtain ⟨hE, ha⟩ := hmem ⟨E, a⟩ hp
    have haW : a ∈ W := hW E hE ha
    by_cases hStar : insert v (E.erase a) ∈ H
    · simpa [f, target, hStar] using
        (Finset.inl_mem_disjSum.mpr haW :
          Sum.inl a ∈ W.disjSum (missingStarFacets H W v r))
    · have hSub : E.erase a ⊆ W :=
        (Finset.erase_subset a E).trans (hW E hE)
      have hCard : (E.erase a).card = r - 1 :=
        erase_card_pred (hU hE) ha
      have hMissing : E.erase a ∈ missingStarFacets H W v r :=
        Finset.mem_filter.mpr
          ⟨Finset.mem_powersetCard.mpr ⟨hSub, hCard⟩, hStar⟩
      simpa [f, target, hStar] using
        (Finset.inr_mem_disjSum.mpr hMissing :
          Sum.inr (E.erase a) ∈ W.disjSum (missingStarFacets H W v r))
  have hinj : Set.InjOn f (↑I : Set (Σ _E : Edge α, α)) := by
    intro ⟨E, a⟩ hp ⟨F, b⟩ hq hEq
    obtain ⟨hE, ha⟩ := hmem ⟨E, a⟩ hp
    obtain ⟨hF, hb⟩ := hmem ⟨F, b⟩ hq
    by_cases hStarE : insert v (E.erase a) ∈ H
    · by_cases hStarF : insert v (F.erase b) ∈ H
      · have hab : a = b := by
          simpa [f, hStarE, hStarF] using hEq
        subst b
        have hEF := present_erases_force_same_edge
          hH hBH hU hLin hr hW hvW hE hF ha hb hStarE hStarF
        cases hEF
        rfl
      · simp [f, hStarE, hStarF] at hEq
    · by_cases hStarF : insert v (F.erase b) ∈ H
      · simp [f, hStarE, hStarF] at hEq
      · have hTailEq : E.erase a = F.erase b := by
          simpa [f, hStarE, hStarF] using hEq
        obtain ⟨hEF, hab⟩ :=
          linear_equal_erases hU hLin hr hE hF ha hb hTailEq
        cases hEF
        cases hab
        rfl
  have hBound : I.card ≤ target.card :=
    Finset.card_le_card_of_injOn f hmap hinj
  rw [hIcard, Finset.card_disjSum] at hBound
  exact hBound

end JSP523
