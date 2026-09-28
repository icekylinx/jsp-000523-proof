import JSP523.Rank5.PartialRootExistence

/-!
# The five-vertex four-face coherence criterion

For a five-set `E`, the deletion face `E.erase a` is coherent with center
`f a` if the center belongs to the face and every triple of that face
containing it has the same assigned triple center.  Four coherent deletion
faces force a triple root of `E`, and a triple root supplies four coherent
deletion faces.  The argument uses the finite partial-root theorem and
elementary finset membership and cardinality facts.
-/

namespace JSP523.Rank5

section FourFaceCoherence

variable {α : Type*} [DecidableEq α]

/-- A center certificate on the four-face obtained by deleting `a`. -/
def DeletedFaceCoherent
    (E : Edge α) (z : Edge α → α) (f : α → α) (a : α) : Prop :=
  f a ∈ E.erase a ∧
    ∀ S : Edge α, S ⊆ E.erase a → S.card = 3 →
      f a ∈ S → z S = f a

/-- Four coherent deletion faces give compatible arrows between their
    deleted vertices.  The common triple is `E.erase a |>.erase b`. -/
theorem coherent_deleted_faces_compatible
    {E U : Edge α} {z : Edge α → α} {f : α → α}
    (hEcard : E.card = 5)
    (hUE : U ⊆ E)
    (hcoh : ∀ a ∈ U, DeletedFaceCoherent E z f a) :
    PartialCompatible U f := by
  intro a b ha hb hab hfab hfba
  let S : Edge α := (E.erase a).erase b
  have haE : a ∈ E := hUE ha
  have hbE : b ∈ E := hUE hb
  have hbEa : b ∈ E.erase a :=
    Finset.mem_erase.mpr ⟨Ne.symm hab, hbE⟩
  have hcardA : (E.erase a).card = E.card - 1 :=
    Finset.card_erase_of_mem haE
  have hcardS : S.card = (E.erase a).card - 1 :=
    Finset.card_erase_of_mem hbEa
  have hS3 : S.card = 3 := by omega
  have hSa : S ⊆ E.erase a := Finset.erase_subset b (E.erase a)
  have hSb : S ⊆ E.erase b := by
    intro x hx
    have hxb : x ≠ b := (Finset.mem_erase.mp hx).1
    have hxEa : x ∈ E.erase a := (Finset.mem_erase.mp hx).2
    have hxE : x ∈ E := (Finset.mem_erase.mp hxEa).2
    exact Finset.mem_erase.mpr ⟨hxb, hxE⟩
  have hfaS : f a ∈ S :=
    Finset.mem_erase.mpr ⟨hfab, (hcoh a ha).1⟩
  have hfbEb : f b ∈ E.erase b := (hcoh b hb).1
  have hfbEa : f b ∈ E.erase a :=
    Finset.mem_erase.mpr ⟨hfba, (Finset.mem_erase.mp hfbEb).2⟩
  have hfbS : f b ∈ S :=
    Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hfbEb).1, hfbEa⟩
  have hza : z S = f a := (hcoh a ha).2 S hSa hS3 hfaS
  have hzb : z S = f b := (hcoh b hb).2 S hSb hS3 hfbS
  exact hza.symm.trans hzb

/-- The actual five-vertex hard direction: four coherent four-faces force
    a vertex which centers every triple containing it. -/
theorem four_coherent_deleted_faces_imply_triple_root
    {E U : Edge α} {z : Edge α → α} {f : α → α}
    (hEcard : E.card = 5)
    (hUE : U ⊆ E)
    (hUcard : 4 ≤ U.card)
    (hcoh : ∀ a ∈ U, DeletedFaceCoherent E z f a) :
    ∃ v ∈ E, ∀ S : Edge α, S ⊆ E → S.card = 3 →
      v ∈ S → z S = v := by
  have hmap : ∀ a ∈ U, f a ∈ E := by
    intro a ha
    exact (Finset.mem_erase.mp (hcoh a ha).1).2
  have hnofix : ∀ a ∈ U, f a ≠ a := by
    intro a ha
    exact (Finset.mem_erase.mp (hcoh a ha).1).1
  have hcomp : PartialCompatible U f :=
    coherent_deleted_faces_compatible hEcard hUE hcoh
  obtain ⟨v, ⟨hvE, hvroot⟩, _⟩ :=
    partial_root_existsUnique_in_ambient hUcard hmap hcomp hnofix
  refine ⟨v, hvE, ?_⟩
  intro S hSE hS3 hvS
  have hout : ∃ a ∈ U, a ∉ S := by
    by_contra h
    have hsub : U ⊆ S := by
      intro a ha
      by_contra haS
      exact h ⟨a, ha, haS⟩
    have hbound := Finset.card_le_card hsub
    omega
  obtain ⟨a, ha, haS⟩ := hout
  have hav : a ≠ v := by
    intro heq
    apply haS
    exact heq.symm ▸ hvS
  have hSa : S ⊆ E.erase a := by
    intro x hx
    apply Finset.mem_erase.mpr
    constructor
    · intro heq
      apply haS
      exact heq ▸ hx
    · exact hSE hx
  have hfa : f a = v := hvroot a ha hav
  have hfaS : f a ∈ S := by
    rw [hfa]
    exact hvS
  exact ((hcoh a ha).2 S hSa hS3 hfaS).trans hfa

/-- A triple root centers every triple in each deletion face that still
    contains the root. -/
theorem triple_root_makes_deleted_face_coherent
    {E : Edge α} {z : Edge α → α} {v a : α}
    (hvE : v ∈ E)
    (hav : a ≠ v)
    (hroot : ∀ S : Edge α, S ⊆ E → S.card = 3 →
      v ∈ S → z S = v) :
    DeletedFaceCoherent E z (fun _ => v) a := by
  constructor
  · exact Finset.mem_erase.mpr ⟨Ne.symm hav, hvE⟩
  · intro S hSa hS3 hvS
    exact hroot S (hSa.trans (Finset.erase_subset a E)) hS3 hvS

/-- A five-set has a triple root exactly when at least four deletion faces
    carry coherent center certificates.  The map `f` chooses their centers;
    its values outside `U` are irrelevant. -/
theorem five_face_coherence_iff_triple_root
    {E : Edge α} {z : Edge α → α}
    (hEcard : E.card = 5) :
    (∃ v ∈ E, ∀ S : Edge α, S ⊆ E → S.card = 3 →
      v ∈ S → z S = v) ↔
    (∃ U : Edge α, ∃ f : α → α,
      U ⊆ E ∧ 4 ≤ U.card ∧
      ∀ a ∈ U, DeletedFaceCoherent E z f a) := by
  constructor
  · rintro ⟨v, hvE, hroot⟩
    refine ⟨E.erase v, (fun _ => v), Finset.erase_subset v E, ?_, ?_⟩
    · have hcard : (E.erase v).card = E.card - 1 :=
        Finset.card_erase_of_mem hvE
      omega
    · intro a ha
      have hav : a ≠ v := (Finset.mem_erase.mp ha).1
      exact triple_root_makes_deleted_face_coherent hvE hav hroot
  · rintro ⟨U, f, hUE, hUcard, hcoh⟩
    exact four_coherent_deleted_faces_imply_triple_root hEcard hUE hUcard hcoh

end FourFaceCoherence

end JSP523.Rank5
