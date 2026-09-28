import JSP523.Counting.BadSetIncidence
import JSP523.Counting.StarDecomposition
import JSP523.Rank5.ExceptionalVertexIncidence

/-!
# The `b₁` incidence bound in (IV.2.9)

The family below is the manuscript's `B₁`, defined by filtering the actual
outside family. The final theorem proves the first inequality in (IV.2.9),
`(r - 1) * b₁ ≤ |D| * choose(|U|, r - 2)`, by counting incidences between
an outside edge in `B₁` and one of its ordinary vertices.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

/-- Actual outside edges with exactly one bad singleton vertex. -/
def outsideOneBadSingleton (H : Family α) (W : Edge α) (v : α)
    (r : ℕ) : Family α :=
  (outsideFamily H W).filter fun E =>
    (E ∩ badSingletonVertices H W v r).card = 1

/-- Every `B₁` edge has a unique exceptional vertex, and each of its other
vertices is ordinary. -/
theorem outside_one_bad_singleton_structure
    (H : Family α) (W : Edge α) (v : α) (r : ℕ)
    {E : Edge α} (hE : E ∈ outsideOneBadSingleton H W v r) :
    ∃ x ∈ E ∩ badSingletonVertices H W v r,
      (∀ y ∈ E, y ∈ badSingletonVertices H W v r → y = x) ∧
      (∀ y ∈ E, y ≠ x → y ∈ W \ badSingletonVertices H W v r) := by
  classical
  have hOut : E ∈ outsideFamily H W := (Finset.mem_filter.mp hE).1
  have hEW : E ⊆ W := (Finset.mem_filter.mp hOut).2
  have hOne : (E ∩ badSingletonVertices H W v r).card = 1 :=
    (Finset.mem_filter.mp hE).2
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hOne
  refine ⟨x, ?_, ?_, ?_⟩
  · rw [hx]
    simp
  · intro y hy hyD
    have hyI : y ∈ E ∩ badSingletonVertices H W v r :=
      Finset.mem_inter.mpr ⟨hy, hyD⟩
    rw [hx] at hyI
    simpa using hyI
  · intro y hy hyx
    refine Finset.mem_sdiff.mpr ⟨hEW hy, ?_⟩
    intro hyD
    have hyI : y ∈ E ∩ badSingletonVertices H W v r :=
      Finset.mem_inter.mpr ⟨hy, hyD⟩
    rw [hx] at hyI
    have : y = x := by simpa using hyI
    exact hyx this

/-- Exact finite form of the first inequality in (IV.2.9). -/
theorem outside_one_bad_singleton_incidence_bound
    (H : Family α) (W : Edge α) (v : α) (r : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hr : 3 ≤ r) (hvW : v ∉ W) :
    let D := badSingletonVertices H W v r
    let U := W \ D
    let B₁ := outsideOneBadSingleton H W v r
    (r - 1) * B₁.card ≤ D.card * U.card.choose (r - 2) := by
  classical
  let D := badSingletonVertices H W v r
  let U := W \ D
  let B₁ := outsideOneBadSingleton H W v r
  let I := B₁.sigma fun E => E \ D
  let T := D.sigma fun _ => U.powersetCard (r - 2)
  have hB (E : Edge α) (hE : E ∈ B₁) :
      E ∈ H ∧ E ⊆ W ∧ (E ∩ D).card = 1 := by
    obtain ⟨hOut, hOne⟩ := Finset.mem_filter.mp hE
    obtain ⟨hEH, hEW⟩ := Finset.mem_filter.mp hOut
    exact ⟨hEH, hEW, hOne⟩
  have hTailCard (E : Edge α) (hE : E ∈ B₁) :
      (E \ D).card = r - 1 := by
    have hCount := Finset.card_sdiff_add_card_inter E D
    have hInter := (hB E hE).2.2
    have hSize := hUniform (hB E hE).1
    omega
  have hIcard : I.card = B₁.card * (r - 1) := by
    rw [show I = B₁.sigma (fun E => E \ D) by rfl, Finset.card_sigma]
    calc
      (∑ E ∈ B₁, (E \ D).card) = ∑ _E ∈ B₁, (r - 1) := by
        apply Finset.sum_congr rfl
        intro E hE
        rw [hTailCard E hE]
      _ = B₁.card * (r - 1) := by simp [Finset.sum_const]
  let root : ↥I → α := fun p =>
    Classical.choose (Finset.card_eq_one.mp
      (hB p.1.1 ((Finset.mem_sigma.mp p.2).1)).2.2)
  have hRoot (p : ↥I) :
      root p ∈ p.1.1 ∩ D ∧ p.1.1 ∩ D = {root p} := by
    have hs := Classical.choose_spec (Finset.card_eq_one.mp
      (hB p.1.1 ((Finset.mem_sigma.mp p.2).1)).2.2)
    constructor
    · have heq := congrArg (fun S : Edge α => root p ∈ S) hs
      exact heq.mpr (Finset.mem_singleton_self _)
    · exact hs
  let tail (p : ↥I) : Edge α :=
    (p.1.1.erase (root p)).erase p.1.2
  let f : ↥I → Σ a : α, Edge α := fun p => ⟨root p, tail p⟩
  have hMap : ∀ p ∈ I.attach, f p ∈ T := by
    intro p _hp
    have hpI : p.1 ∈ I := p.2
    obtain ⟨hE, hy⟩ := Finset.mem_sigma.mp hpI
    have hEdge := hB p.1.1 hE
    have hRootP := hRoot p
    have hxE : root p ∈ p.1.1 := (Finset.mem_inter.mp hRootP.1).1
    have hxD : root p ∈ D := (Finset.mem_inter.mp hRootP.1).2
    have hyE : p.1.2 ∈ p.1.1 := (Finset.mem_sdiff.mp hy).1
    have hyNotD : p.1.2 ∉ D := (Finset.mem_sdiff.mp hy).2
    have hxy : root p ≠ p.1.2 := by
      intro h
      exact hyNotD (h ▸ hxD)
    have hTailSub : tail p ⊆ U := by
      intro z hz
      have hzy := (Finset.mem_erase.mp hz).1
      have hzxE := (Finset.mem_erase.mp hz).2
      have hzx := (Finset.mem_erase.mp hzxE).1
      have hzE := (Finset.mem_erase.mp hzxE).2
      have hzNotD : z ∉ D := by
        intro hzD
        have hzI : z ∈ p.1.1 ∩ D := Finset.mem_inter.mpr ⟨hzE, hzD⟩
        have heq := congrArg (fun S : Edge α => z ∈ S) hRootP.2
        have hzSingleton : z ∈ ({root p} : Edge α) := heq.mp hzI
        have hzEq : z = root p := Finset.mem_singleton.mp hzSingleton
        exact hzx hzEq
      exact Finset.mem_sdiff.mpr ⟨hEdge.2.1 hzE, hzNotD⟩
    have hyErase : p.1.2 ∈ p.1.1.erase (root p) :=
      Finset.mem_erase.mpr ⟨hxy.symm, hyE⟩
    have hTailCard : (tail p).card = r - 2 := by
      dsimp [tail]
      rw [Finset.card_erase_of_mem hyErase,
        Finset.card_erase_of_mem hxE]
      have hSize := hUniform hEdge.1
      omega
    exact Finset.mem_sigma.mpr ⟨hxD,
      Finset.mem_powersetCard.mpr ⟨hTailSub, hTailCard⟩⟩
  have hInj : Set.InjOn f (↑I.attach : Set ↥I) := by
    intro p _hp q _hq hImage
    have hpI : p.1 ∈ I := p.2
    have hqI : q.1 ∈ I := q.2
    obtain ⟨hEp, hy⟩ := Finset.mem_sigma.mp hpI
    obtain ⟨hF, hz⟩ := Finset.mem_sigma.mp hqI
    have hxEq : root p = root q := congrArg Sigma.fst hImage
    have hTailEq : tail p = tail q := congrArg Sigma.snd hImage
    have he := hB p.1.1 hEp
    have hg := hB q.1.1 hF
    have hRootP := hRoot p
    have hRootQ := hRoot q
    have hxp : root p ∈ p.1.1 := (Finset.mem_inter.mp hRootP.1).1
    have hxq : root q ∈ q.1.1 := (Finset.mem_inter.mp hRootQ.1).1
    have hyp : p.1.2 ∈ p.1.1 := (Finset.mem_sdiff.mp hy).1
    have hyq : q.1.2 ∈ q.1.1 := (Finset.mem_sdiff.mp hz).1
    have hyU : p.1.2 ∈ U :=
      Finset.mem_sdiff.mpr ⟨he.2.1 (Finset.mem_sdiff.mp hy).1,
        (Finset.mem_sdiff.mp hy).2⟩
    have hzU : q.1.2 ∈ U :=
      Finset.mem_sdiff.mpr ⟨hg.2.1 (Finset.mem_sdiff.mp hz).1,
        (Finset.mem_sdiff.mp hz).2⟩
    have hxy : root p ≠ p.1.2 := by
      intro h
      exact (Finset.mem_sdiff.mp hy).2 (h ▸
        (Finset.mem_inter.mp hRootP.1).2)
    have hxqOrd : root q ≠ q.1.2 := by
      intro h
      exact (Finset.mem_sdiff.mp hz).2 (h ▸
        (Finset.mem_inter.mp hRootQ.1).2)
    have hxz : root p ≠ q.1.2 := by
      rw [hxEq]
      intro h
      exact (Finset.mem_sdiff.mp hz).2 (h ▸
        (Finset.mem_inter.mp hRootQ.1).2)
    have hTailMem := (Finset.mem_powersetCard.mp
      ((Finset.mem_sigma.mp (hMap p (by simp))).2))
    have hPsub : insert (root p) (tail p) ⊆ W := by
      intro z hz'
      rcases Finset.mem_insert.mp hz' with rfl | hz'
      · exact (Finset.filter_subset _ _)
          ((Finset.mem_inter.mp hRootP.1).2)
      · exact (Finset.mem_sdiff.mp (hTailMem.1 hz')).1
    have hPcard : (insert (root p) (tail p)).card = r - 1 := by
      rw [Finset.card_insert_of_notMem]
      · have ht := hTailMem.2
        change (tail p).card = r - 2 at ht
        omega
      · intro h
        exact (Finset.mem_sdiff.mp (hTailMem.1 h)).2
          ((Finset.mem_inter.mp hRootP.1).2)
    have hRec (a : ↥I) (haI : a.1 ∈ I)
        (hxa : root a ∈ a.1.1) (hya : a.1.2 ∈ a.1.1)
        (hne : root a ≠ a.1.2) :
        a.1.1 = insert (a.1.2) (insert (root a) (tail a)) := by
      calc
        a.1.1 = insert (root a) (a.1.1.erase (root a)) :=
          (Finset.insert_erase hxa).symm
        _ = insert (root a) (insert (a.1.2) (tail a)) := by
          have hmem : a.1.2 ∈ a.1.1.erase (root a) :=
            Finset.mem_erase.mpr ⟨hne.symm, hya⟩
          rw [(Finset.insert_erase hmem).symm]
        _ = insert (a.1.2) (insert (root a) (tail a)) := by
          rw [Finset.insert_comm]
    by_cases hyz : p.1.2 = q.1.2
    · have hEdgeEq : p.1.1 = q.1.1 := by
        rw [hRec p hpI hxp hyp hxy,
        hRec q hqI hxq hyq hxqOrd, hxEq, hyz, hTailEq]
      have hSecond : HEq p.1.2 q.1.2 := heq_of_eq hyz
      exact Subtype.ext (Sigma.ext hEdgeEq hSecond)
    · let P := insert (root p) (tail p)
      have hEdgeP : insert (p.1.2) P ∈ H := by
        have hrec := hRec p hpI hxp hyp hxy
        simpa [P] using hrec ▸ he.1
      have hEdgeQ : insert (q.1.2) P ∈ H := by
        have hrec := hRec q hqI hxq hyq hxqOrd
        have hrec' : q.1.1 = insert (q.1.2) P := by
          simpa [P, hxEq, hTailEq] using hrec
        exact hrec' ▸ hg.1
      exact False.elim (ordinary_vertices_unique_facet_completion hAdm
        hUniform hPsub hPcard hr hvW hyU hzU (by intro h; exact hyz h)
        hEdgeP hEdgeQ)
  have hCard : I.card ≤ T.card := by
    have hCard' := Finset.card_le_card_of_injOn f hMap hInj
    simpa using hCard'
  have hTcard : T.card = D.card * U.card.choose (r - 2) := by
    dsimp [T]
    rw [Finset.card_sigma]
    simp [Finset.card_powersetCard, Finset.sum_const]
  rw [hIcard, hTcard] at hCard
  simpa [Nat.mul_comm] using hCard

end JSP523
