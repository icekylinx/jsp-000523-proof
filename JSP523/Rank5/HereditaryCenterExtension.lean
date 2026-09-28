import JSP523.Rank5.PartialRootExistence
import Lean.Elab.Tactic.Omega

/-!
# Completing a center from hereditary codimension-one centers

§IV.9 of the all-rank manuscript completes centers of free facets for
`r ≥ 6` by
applying the partial functional-root lemma to the centers of their deletion
faces.  This file verifies the missing bridge: noncenter deletion inheritance
on those faces implies the function's compatibility hypothesis.  The result
is stated for any finite set of size at least four and can be used again to
construct an edge center from its facet centers.
-/

namespace JSP523.Rank5

section HereditaryCenterExtension

variable {α : Type*} [DecidableEq α]

/-- A center on every deletion face lies in that face, and removing a
    noncenter vertex preserves its center on the next smaller face. -/
def HereditaryDeletionCenters (T : Edge α) (z : Edge α → α) : Prop :=
  (∀ a ∈ T, z (T.erase a) ∈ T.erase a) ∧
    ∀ a ∈ T, ∀ b ∈ T.erase a,
      b ≠ z (T.erase a) →
        z ((T.erase a).erase b) = z (T.erase a)

/-- The deletion-face centers form a fixed-point-free compatible map. -/
theorem hereditary_deletion_centers_compatible
    {T : Edge α} {z : Edge α → α}
    (h : HereditaryDeletionCenters T z) :
    PartialCompatible T (fun a => z (T.erase a)) := by
  intro a b ha hb hab hfab hfba
  have hbA : b ∈ T.erase a :=
    Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
  have haB : a ∈ T.erase b :=
    Finset.mem_erase.mpr ⟨hab, ha⟩
  have hA := h.2 a ha b hbA (Ne.symm hfab)
  have hB := h.2 b hb a haB (Ne.symm hfba)
  calc
    z (T.erase a) = z ((T.erase a).erase b) := hA.symm
    _ = z ((T.erase b).erase a) := by rw [Finset.erase_right_comm]
    _ = z (T.erase b) := hB

/-- Every hereditary system of deletion-face centers extends uniquely to
    a center of the whole set.  It lies in the set, even when this was not
    assumed in advance for a free facet. -/
theorem hereditary_center_existsUnique
    {T : Edge α} {z : Edge α → α}
    (hcard : 4 ≤ T.card)
    (h : HereditaryDeletionCenters T z) :
    ∃! v : α, v ∈ T ∧
      ∀ a ∈ T, a ≠ v → z (T.erase a) = v := by
  let f : α → α := fun a => z (T.erase a)
  have hmap : ∀ a ∈ T, f a ∈ T := by
    intro a ha
    exact Finset.erase_subset a T (h.1 a ha)
  have hnofix : ∀ a ∈ T, f a ≠ a := by
    intro a ha
    exact (Finset.mem_erase.mp (h.1 a ha)).1
  have hcomp : PartialCompatible T f :=
    hereditary_deletion_centers_compatible h
  exact partial_root_existsUnique_in_ambient hcard hmap hcomp hnofix

/-- An already assigned center that agrees with every deletion face is
    exactly the center produced by the extension theorem. -/
theorem hereditary_center_agrees_with_existing
    {T : Edge α} {z : Edge α → α} {v w : α}
    (hcard : 4 ≤ T.card)
    (hv : ∀ a ∈ T, a ≠ v → z (T.erase a) = v)
    (hw : ∀ a ∈ T, a ≠ w → z (T.erase a) = w) :
    v = w := by
  exact partial_root_unique (by omega : 3 ≤ T.card) hv hw

end HereditaryCenterExtension

end JSP523.Rank5
