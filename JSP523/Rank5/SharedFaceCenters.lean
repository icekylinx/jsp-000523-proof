import JSP523.Rank5.FourFaceCoherence
import Lean.Elab.Tactic.Omega

/-!
# Uniqueness of coherent four-face centers

Two distinct vertices of a face of size at least three lie in a common
triple of that face.  If both vertices centered every triple containing
them, this triple would have two different prescribed centers.  In
particular, centers inherited from different parent edges on one shared
four-face must agree.
-/

namespace JSP523.Rank5

section SharedFaceCenters

variable {α : Type*} [DecidableEq α]

/-- A coherent face of size at least three has at most one coherent
    center, regardless of which candidate center map was used. -/
theorem coherent_deleted_face_unique_center
    {E : Edge α} {z : Edge α → α} {a w v : α}
    (hcard : 3 ≤ (E.erase a).card)
    (hw : DeletedFaceCoherent E z (fun _ => w) a)
    (hv : DeletedFaceCoherent E z (fun _ => v) a) :
    w = v := by
  by_contra hwv
  have hpair : ({w, v} : Edge α).card = 2 := Finset.card_pair hwv
  have hthird : ∃ u ∈ E.erase a, u ∉ ({w, v} : Edge α) := by
    by_contra h
    have hsub : E.erase a ⊆ ({w, v} : Edge α) := by
      intro u hu
      by_contra hnot
      exact h ⟨u, hu, hnot⟩
    have hbound := Finset.card_le_card hsub
    omega
  obtain ⟨u, hu, hnot⟩ := hthird
  have huw : u ≠ w := by
    intro heq
    apply hnot
    simpa only [heq] using (by simp : w ∈ ({w, v} : Edge α))
  have huv : u ≠ v := by
    intro heq
    apply hnot
    simpa only [heq] using (by simp : v ∈ ({w, v} : Edge α))
  let S : Edge α := {w, v, u}
  have hSsub : S ⊆ E.erase a := by
    intro t ht
    have ht' : t = w ∨ t = v ∨ t = u := by
      simpa only [S, Finset.mem_insert, Finset.mem_singleton] using ht
    rcases ht' with rfl | rfl | rfl
    · exact hw.1
    · exact hv.1
    · exact hu
  have hScard : S.card = 3 := by
    exact Finset.card_triple_eq_three_iff.mpr
      ⟨hwv, Ne.symm huw, Ne.symm huv⟩
  have hwS : w ∈ S := by simp [S]
  have hvS : v ∈ S := by simp [S]
  have hzw : z S = w := hw.2 S hSsub hScard hwS
  have hzv : z S = v := hv.2 S hSsub hScard hvS
  exact hwv (hzw.symm.trans hzv)

/-- When two edges have the same deleted face, their coherent centers
    agree.  The proof uses the actual equality of faces, not a separately
    chosen global label. -/
theorem shared_deleted_face_centers_agree
    {E F : Edge α} {z : Edge α → α} {a b w v : α}
    (hface : E.erase a = F.erase b)
    (hcard : 3 ≤ (E.erase a).card)
    (hw : DeletedFaceCoherent E z (fun _ => w) a)
    (hv : DeletedFaceCoherent F z (fun _ => v) b) :
    w = v := by
  have hv' : DeletedFaceCoherent E z (fun _ => v) a := by
    simpa only [DeletedFaceCoherent, hface] using hv
  exact coherent_deleted_face_unique_center hcard hw hv'

end SharedFaceCenters

end JSP523.Rank5
