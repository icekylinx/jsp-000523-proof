import JSP523.Rank5.RootedPartition
import JSP523.Rank5.SharedFaceCenters
import Lean.Elab.Tactic.Omega

/-!
# Rooted five-edges and shared-facet centers

Every deleted face retaining a triple root is coherent with that root.
Coherent centers imported from another parent on the same face must agree.
This also proves that a five-edge has at most one triple root, making the
rooted subfamily's center an intrinsic vertex whenever it exists.
-/

namespace JSP523.Rank5

section RootedFacetCenters

variable {α : Type*} [DecidableEq α]

/-- Deleting a nonroot vertex from a rooted edge leaves a coherent face. -/
theorem triple_root_coherent_deleted_face
    {E : Edge α} {z : Edge α → α} {v a : α}
    (hv : TripleRoot E z v) (hav : a ≠ v) :
    DeletedFaceCoherent E z (fun _ => v) a :=
  triple_root_makes_deleted_face_coherent hv.1 hav hv.2

/-- A coherent center assigned to a face retaining the edge root must be
    that root. -/
theorem coherent_deleted_face_center_eq_triple_root
    {E : Edge α} {z : Edge α → α} {v w a : α}
    (hEcard : E.card = 5) (ha : a ∈ E)
    (hv : TripleRoot E z v) (hav : a ≠ v)
    (hw : DeletedFaceCoherent E z (fun _ => w) a) :
    w = v := by
  have hfacecard : 3 ≤ (E.erase a).card := by
    have hcardErase := Finset.card_erase_add_one ha
    omega
  exact coherent_deleted_face_unique_center hfacecard hw
    (triple_root_coherent_deleted_face hv hav)

/-- When a rooted edge shares a face retaining its root with another edge,
    any coherent center of that same face agrees with the root. -/
theorem rooted_shared_facet_center_agrees
    {E F : Edge α} {z : Edge α → α} {v w a b : α}
    (hEcard : E.card = 5) (ha : a ∈ E)
    (hv : TripleRoot E z v) (hav : a ≠ v)
    (hface : E.erase a = F.erase b)
    (hw : DeletedFaceCoherent F z (fun _ => w) b) :
    w = v := by
  have hfacecard : 3 ≤ (E.erase a).card := by
    have hcardErase := Finset.card_erase_add_one ha
    omega
  exact (shared_deleted_face_centers_agree hface hfacecard
    (triple_root_coherent_deleted_face hv hav) hw).symm

/-- If two rooted edges share a facet containing both roots, their roots
    coincide on the shared facet. -/
theorem rooted_shared_facet_roots_agree
    {E F : Edge α} {z : Edge α → α} {v w a b : α}
    (hEcard : E.card = 5) (ha : a ∈ E)
    (hv : TripleRoot E z v) (hw : TripleRoot F z w)
    (hav : a ≠ v) (hbw : b ≠ w)
    (hface : E.erase a = F.erase b) :
    v = w := by
  have hfacecard : 3 ≤ (E.erase a).card := by
    have hcardErase := Finset.card_erase_add_one ha
    omega
  exact shared_deleted_face_centers_agree hface hfacecard
    (triple_root_coherent_deleted_face hv hav)
    (triple_root_coherent_deleted_face hw hbw)

/-- A five-edge cannot have two distinct vertices each centering every
    triple through itself: delete a third vertex and compare face centers. -/
theorem five_edge_triple_root_unique
    {E : Edge α} {z : Edge α → α} {v w : α}
    (hEcard : E.card = 5)
    (hv : TripleRoot E z v) (hw : TripleRoot E z w) :
    v = w := by
  by_contra hvw
  have hpair : ({v, w} : Edge α).card = 2 := Finset.card_pair hvw
  have hthird : ∃ a ∈ E, a ∉ ({v, w} : Edge α) := by
    by_contra h
    have hsub : E ⊆ ({v, w} : Edge α) := by
      intro a ha
      by_contra hnot
      exact h ⟨a, ha, hnot⟩
    have hbound := Finset.card_le_card hsub
    omega
  obtain ⟨a, haE, haPair⟩ := hthird
  have hav : a ≠ v := by
    intro heq
    apply haPair
    simpa only [heq] using (by simp : v ∈ ({v, w} : Edge α))
  have haw : a ≠ w := by
    intro heq
    apply haPair
    simpa only [heq] using (by simp : w ∈ ({v, w} : Edge α))
  exact hvw ((coherent_deleted_face_center_eq_triple_root
    hEcard haE hv hav (triple_root_coherent_deleted_face hw haw)).symm)

/-- Each member of the actual rooted subfamily has exactly one triple
    root when the ambient family is five-uniform. -/
theorem rooted_edge_unique_triple_root
    (all : Family α) (z : Edge α → α)
    (hUniform : Uniform 5 all)
    {E : Edge α} (hE : E ∈ rootedEdges all z) :
    ∃ v : α, TripleRoot E z v ∧
      ∀ w : α, TripleRoot E z w → w = v := by
  obtain ⟨hAll, v, hv⟩ := (mem_rootedEdges_iff all z E).mp hE
  refine ⟨v, hv, ?_⟩
  intro w hw
  exact (five_edge_triple_root_unique (hUniform hAll) hv hw).symm

end RootedFacetCenters

end JSP523.Rank5
