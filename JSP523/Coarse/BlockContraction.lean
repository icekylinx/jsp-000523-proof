import JSP523.Basic
import Mathlib.Data.Finset.Union

/-!
# Expanding disjoint prefix blocks

The finite reduction in Part I contracts each disjoint `(r-2)`-block to
one tagged index vertex.  These lemmas isolate the set-theoretic fact that
equal unions and disjointness of contracted edges lift back to the
original family.
-/

namespace JSP523.Coarse

variable {ι β : Type*} [DecidableEq ι] [DecidableEq β]

/-- Replace a tagged index by its original block and an ordinary tagged
vertex by its singleton. -/
def expandBlock (B : ι → Edge β) (S : Edge (ι ⊕ β)) : Edge β :=
  S.biUnion fun a => match a with
    | Sum.inl i => B i
    | Sum.inr v => {v}

theorem expand_block_union (B : ι → Edge β)
    (S T : Edge (ι ⊕ β)) :
    expandBlock B (S ∪ T) =
      expandBlock B S ∪ expandBlock B T := by
  ext v
  simp [expandBlock, Finset.mem_biUnion, Finset.mem_union]
  aesop

omit [DecidableEq ι] in
theorem expand_block_disjoint_of_atom_disjoint
    (B : ι → Edge β) {S T : Edge (ι ⊕ β)}
    (hAtom : ∀ a ∈ S, ∀ b ∈ T,
      Disjoint (expandBlock B {a}) (expandBlock B {b})) :
    Disjoint (expandBlock B S) (expandBlock B T) := by
  apply Finset.disjoint_left.mpr
  intro v hvS hvT
  obtain ⟨a, ha, hva⟩ := Finset.mem_biUnion.mp hvS
  obtain ⟨b, hb, hvb⟩ := Finset.mem_biUnion.mp hvT
  have hDisj := hAtom a ha b hb
  exact (Finset.disjoint_left.mp hDisj)
    (by simpa [expandBlock] using hva)
    (by simpa [expandBlock] using hvb)

/-- An admissible parent family remains admissible after a contraction
whenever expansion is injective on the represented family and preserves
disjoint edge pairs. -/
theorem admissible_of_expand_block
    (B : ι → Edge β)
    (T : Family (ι ⊕ β)) (H : Family β)
    (hH : Admissible H)
    (hmem : ∀ S ∈ T, expandBlock B S ∈ H)
    (hinj : ∀ S ∈ T, ∀ U ∈ T,
      expandBlock B S = expandBlock B U → S = U)
    (hdisj : ∀ S ∈ T, ∀ U ∈ T,
      Disjoint S U → Disjoint (expandBlock B S) (expandBlock B U)) :
    Admissible T := by
  intro A C D E hA hC hD hE hq
  have hDistinct : FourDistinct
      (expandBlock B A) (expandBlock B C)
      (expandBlock B D) (expandBlock B E) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun h => hq.distinct.ab (hinj A hA C hC h)
    · exact fun h => hq.distinct.ac (hinj A hA D hD h)
    · exact fun h => hq.distinct.ad (hinj A hA E hE h)
    · exact fun h => hq.distinct.bc (hinj C hC D hD h)
    · exact fun h => hq.distinct.bd (hinj C hC E hE h)
    · exact fun h => hq.distinct.cd (hinj D hD E hE h)
  have hUnion : expandBlock B A ∪ expandBlock B C =
      expandBlock B D ∪ expandBlock B E := by
    rw [← expand_block_union, ← expand_block_union, hq.sameUnion]
  exact hH (hmem A hA) (hmem C hC) (hmem D hD) (hmem E hE)
    ⟨hDistinct, hdisj A hA C hC hq.disjAB,
      hdisj D hD E hE hq.disjCD, hUnion⟩

end JSP523.Coarse
