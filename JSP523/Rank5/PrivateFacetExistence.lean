import JSP523.Rank5.FourFaceCoherence

/-!
# Two genuinely private four-faces of an unrooted five-edge

The coherence criterion gives two *intrinsically* incoherent deletion faces
on a five-edge with no triple root.  An explicit shared-face coherence
hypothesis then turns each of these faces into a private facet: no other
edge of the family can contain it. The all-rank manuscript supplies this
coherence through §§IV.8–IV.9; it remains an explicit Lean assumption here.
-/

namespace JSP523.Rank5

section PrivateFacetExistence

variable {α : Type*} [DecidableEq α]

/-- Coherence of a deletion face, with its center chosen existentially. -/
def CoherentDeletedFace (E : Edge α) (z : Edge α → α) (a : α) : Prop :=
  ∃ w : α, DeletedFaceCoherent E z (fun _ => w) a

/-- Four intrinsically coherent faces permit a simultaneous choice of their
    centers, so the five-face criterion supplies a triple root. -/
theorem four_intrinsically_coherent_faces_imply_root
    {E U : Edge α} {z : Edge α → α}
    (hEcard : E.card = 5)
    (hUE : U ⊆ E)
    (hUcard : 4 ≤ U.card)
    (hcoh : ∀ a ∈ U, CoherentDeletedFace E z a) :
    ∃ v ∈ E, ∀ S : Edge α, S ⊆ E → S.card = 3 →
      v ∈ S → z S = v := by
  classical
  let f : α → α := fun a =>
    if h : CoherentDeletedFace E z a then Classical.choose h else a
  have hchosen : ∀ a ∈ U, DeletedFaceCoherent E z f a := by
    intro a ha
    have hc : CoherentDeletedFace E z a := hcoh a ha
    have hspec : DeletedFaceCoherent E z
        (fun _ => Classical.choose hc) a := Classical.choose_spec hc
    simpa only [DeletedFaceCoherent, f, dite_eq_left hc] using hspec
  exact four_coherent_deleted_faces_imply_triple_root
    hEcard hUE hUcard hchosen

/-- Without a triple root, at least two of the five deletion faces lack
    *any* coherent center.  This does not depend on a preset center map. -/
theorem two_incoherent_deleted_faces_of_no_root
    {E : Edge α} {z : Edge α → α}
    (hEcard : E.card = 5)
    (hnoroot : ¬ ∃ v ∈ E, ∀ S : Edge α,
      S ⊆ E → S.card = 3 → v ∈ S → z S = v) :
    ∃ a ∈ E, ∃ b ∈ E,
      a ≠ b ∧ ¬ CoherentDeletedFace E z a ∧
      ¬ CoherentDeletedFace E z b := by
  classical
  by_cases hbad : ∃ a ∈ E, ¬ CoherentDeletedFace E z a
  · obtain ⟨a, ha, hna⟩ := hbad
    by_contra htwo
    have hgood : ∀ b ∈ E.erase a, CoherentDeletedFace E z b := by
      intro b hb
      by_contra hnb
      have hba : b ≠ a := (Finset.mem_erase.mp hb).1
      have hbE : b ∈ E := (Finset.mem_erase.mp hb).2
      exact htwo ⟨a, ha, b, hbE, Ne.symm hba, hna, hnb⟩
    have hrest : 4 ≤ (E.erase a).card := by
      have hcard : (E.erase a).card = E.card - 1 :=
        Finset.card_erase_of_mem ha
      omega
    have hroot := four_intrinsically_coherent_faces_imply_root
      hEcard (Finset.erase_subset a E) hrest hgood
    exact False.elim (hnoroot hroot)
  · have hgood : ∀ a ∈ E, CoherentDeletedFace E z a := by
      intro a ha
      by_contra hna
      exact hbad ⟨a, ha, hna⟩
    have hfour : 4 ≤ E.card := by omega
    have hroot := four_intrinsically_coherent_faces_imply_root
      hEcard (by intro a ha; exact ha) hfour hgood
    exact False.elim (hnoroot hroot)

/-- Private means that no other member of `all` contains this particular
    deleted four-face. -/
def PrivateDeletedFace (all : Family α) (E : Edge α) (a : α) : Prop :=
  ∀ F ∈ all, E.erase a ⊆ F → F = E

/-- The two private facets, conditional only on the precise local repair
    input that a face occurring in a second edge is coherent.  Each facet
    has four vertices and the two facets are distinct. -/
theorem two_private_facets_of_rootless_edge
    {all : Family α} {E : Edge α} {z : Edge α → α}
    (hEcard : E.card = 5)
    (hnoroot : ¬ ∃ v ∈ E, ∀ S : Edge α,
      S ⊆ E → S.card = 3 → v ∈ S → z S = v)
    (hshared : ∀ a ∈ E,
      (∃ F ∈ all, F ≠ E ∧ E.erase a ⊆ F) →
      CoherentDeletedFace E z a) :
    ∃ a ∈ E, ∃ b ∈ E,
      a ≠ b ∧ E.erase a ≠ E.erase b ∧
      (E.erase a).card = 4 ∧ (E.erase b).card = 4 ∧
      PrivateDeletedFace all E a ∧ PrivateDeletedFace all E b := by
  obtain ⟨a, ha, b, hb, hab, hna, hnb⟩ :=
    two_incoherent_deleted_faces_of_no_root hEcard hnoroot
  have hfaces : E.erase a ≠ E.erase b := by
    intro heq
    have hbFace : b ∈ E.erase a :=
      Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
    have hbOther : b ∈ E.erase b := heq ▸ hbFace
    exact (Finset.mem_erase.mp hbOther).1 rfl
  have hcardA : (E.erase a).card = 4 := by
    have h := Finset.card_erase_of_mem ha
    omega
  have hcardB : (E.erase b).card = 4 := by
    have h := Finset.card_erase_of_mem hb
    omega
  refine ⟨a, ha, b, hb, hab, hfaces, hcardA, hcardB, ?_, ?_⟩
  · intro F hF hface
    by_contra hFE
    exact hna (hshared a ha ⟨F, hF, hFE, hface⟩)
  · intro F hF hface
    by_contra hFE
    exact hnb (hshared b hb ⟨F, hF, hFE, hface⟩)

end PrivateFacetExistence

end JSP523.Rank5
