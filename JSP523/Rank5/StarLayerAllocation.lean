import JSP523.Rank5.ShadowAllocationDiscrete
import JSP523.Rank5.StarLayerCollisionGlobal

/-!
# Actual surviving star layers and their allocation

The owner is chosen by the already proved collision/deletion theorem.
Here the surviving links are constructed, their shadows are proved
pairwise disjoint, and their total size is bounded by the all-size
integer-radius estimate.  All deleted objects are actual colored star
members; the accounting identity does not replace edges by incidences.
-/

namespace JSP523.Rank5

open Finset
open scoped BigOperators
open JSP523.Rank5

variable {α : Type*} [DecidableEq α]

/-- The deletion test in the existing actual ownership theorem. -/
def starMemberLost (U : Edge α) (r : ℕ) (owner : Edge α → α)
    (z : α) (T : Edge α) : Prop :=
  ∃ P ∈ actualStarLayerFacets U T r,
    P ∈ U.powersetCard (r - 2) ∧ owner P ≠ z

/-- Keep exactly those link members passing every ownership test. -/
noncomputable def ownedStarLink (H : Family α) (U : Edge α)
    (r : ℕ) (owner : Edge α → α) (z : α) : Family α := by
  classical
  exact (actualStarLink H U z r).filter (fun T => ¬ starMemberLost U r owner z T)

/-- The discarded colored members, with precisely the old deletion test. -/
noncomputable def lostStarObjects (H : Family α) (U Centers : Edge α)
    (r : ℕ) (owner : Edge α → α) : Finset (α × Edge α) := by
  classical
  exact (actualStarLayerObjects H U Centers r).filter
    (fun zT : α × Edge α => starMemberLost U r owner zT.1 zT.2)

/-- The retained colored members are the complement of the deletion test. -/
noncomputable def survivingStarObjects (H : Family α) (U Centers : Edge α)
    (r : ℕ) (owner : Edge α → α) : Finset (α × Edge α) := by
  classical
  exact (actualStarLayerObjects H U Centers r).filter
    (fun zT : α × Edge α => ¬ starMemberLost U r owner zT.1 zT.2)

theorem ownedStarLink_subset (H : Family α) (U : Edge α)
    (r : ℕ) (owner : Edge α → α) (z : α) :
    ownedStarLink H U r owner z ⊆ actualStarLink H U z r := by
  classical
  exact Finset.filter_subset _ _

theorem actualStarLink_uniform (H : Family α) (U : Edge α)
    (r : ℕ) (z : α) : Uniform (r - 1) (actualStarLink H U z r) := by
  intro T hT
  exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).2

theorem ownedStarLink_uniform (H : Family α) (U : Edge α)
    (r : ℕ) (owner : Edge α → α) (z : α) :
    Uniform (r - 1) (ownedStarLink H U r owner z) := by
  intro T hT
  exact actualStarLink_uniform H U r z (ownedStarLink_subset H U r owner z hT)

/-- Each surviving shadow point has the center of its own link as owner. -/
theorem ownedStarLink_shadow_owner (H : Family α) (U : Edge α)
    (r : ℕ) (owner : Edge α → α) (z : α)
    {P : Edge α} (hP : P ∈ Finset.shadow (ownedStarLink H U r owner z)) :
    owner P = z := by
  classical
  obtain ⟨T, hT, x, hx, hErase⟩ := Finset.mem_shadow_iff.mp hP
  have hTlink := ownedStarLink_subset H U r owner z hT
  have hTpow := Finset.mem_powersetCard.mp (Finset.mem_filter.mp hTlink).1
  have hEraseCard := Finset.card_erase_add_one hx
  have hPT : P ⊆ T := by rw [← hErase]; exact Finset.erase_subset _ _
  have hPc : P.card = r - 2 := by rw [← hErase]; omega
  have hPpow : P ∈ U.powersetCard (r - 2) :=
    Finset.mem_powersetCard.mpr ⟨hPT.trans hTpow.1, hPc⟩
  have hPfacet : P ∈ actualStarLayerFacets U T r :=
    Finset.mem_filter.mpr ⟨hPpow, hPT⟩
  by_contra hne
  exact (Finset.mem_filter.mp hT).2 ⟨P, hPfacet, hPpow, hne⟩

/-- Ownership, not an extra hypothesis, separates the actual shadows. -/
theorem ownedStarLink_shadows_disjoint (H : Family α) (U : Edge α)
    (r : ℕ) (owner : Edge α → α) {z w : α} (hzw : z ≠ w) :
    Disjoint (Finset.shadow (ownedStarLink H U r owner z))
      (Finset.shadow (ownedStarLink H U r owner w)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro P hP hQ
  exact hzw ((ownedStarLink_shadow_owner H U r owner z hP).symm.trans
    (ownedStarLink_shadow_owner H U r owner w hQ))

/-- Reindex the retained colored objects by their centers. -/
theorem surviving_star_objects_card
    (H : Family α) (U Centers : Edge α) (r : ℕ) (owner : Edge α → α) :
    (survivingStarObjects H U Centers r owner).card =
      ∑ z ∈ Centers, (ownedStarLink H U r owner z).card := by
  classical
  let O := survivingStarObjects H U Centers r owner
  have hMaps : (O : Set (α × Edge α)).MapsTo Prod.fst (Centers : Finset α) := by
    intro zT hzT
    exact (Finset.mem_product.mp
      (Finset.mem_filter.mp (Finset.mem_filter.mp hzT).1).1).1
  change O.card = _
  rw [Finset.card_eq_sum_card_fiberwise hMaps]
  apply Finset.sum_congr rfl
  intro z hz
  let L := ownedStarLink H U r owner z
  have hFiber : {zT ∈ O | zT.1 = z} = L.image (fun T => (z, T)) := by
    ext ⟨w, T⟩
    by_cases hwz : w = z
    · subst w
      simp [O, L, survivingStarObjects, ownedStarLink, starMemberLost,
        actualStarLayerObjects, actualStarLink,
        Finset.mem_filter, Finset.mem_product, hz,
        and_assoc, and_left_comm, and_comm]
    · have hzw : z ≠ w := fun h => hwz h.symm
      simp [O, L, actualStarLayerObjects, actualStarLink,
        survivingStarObjects, ownedStarLink, starMemberLost,
        Finset.mem_filter, Finset.mem_product, hzw, eq_comm,
        and_assoc, and_left_comm, and_comm]
  rw [hFiber, Finset.card_image_of_injective]
  · intro T S hTS
    exact congrArg Prod.snd hTS

/-- Exact conservation of original colored members: discard plus survive. -/
theorem star_layer_ownership_card_partition
    (H : Family α) (U Centers : Edge α) (r : ℕ) (owner : Edge α → α) :
    (lostStarObjects H U Centers r owner).card +
      (∑ z ∈ Centers, (ownedStarLink H U r owner z).card) =
      (actualStarLayerObjects H U Centers r).card := by
  classical
  have hSurvivors := surviving_star_objects_card H U Centers r owner
  have hPartition := Finset.card_filter_add_card_filter_not
    (s := actualStarLayerObjects H U Centers r)
    (fun zT : α × Edge α => starMemberLost U r owner zT.1 zT.2)
  rw [← hSurvivors]
  simpa [lostStarObjects, survivingStarObjects, starMemberLost] using hPartition

/-- A finite actual-star-layer theorem: an internally chosen deletion has
its proved collision budget, the survivors are genuine sublinks with
pairwise disjoint shadows, and the original count includes that exact loss.
The integer radius is the sole link-size input. -/
theorem actual_star_layer_radius_bound
    {n r D₂ D₃ L : ℕ} [Inhabited (Fin n)]
    {H : Family (Fin n)} {U Centers : Edge (Fin n)}
    (hH : Admissible H) (hCenters : ∀ z ∈ Centers, z ∉ U)
    (hr : 4 ≤ r)
    (hD₂ : ∀ S : Edge (Fin n), S.card = 2 →
      (H.filter (fun E => S ⊆ E)).card ≤ D₂)
    (hD₃ : ∀ S : Edge (Fin n), S.card = 3 →
      (H.filter (fun E => S ⊆ E)).card ≤ D₃)
    (hSize : ∀ z ∈ Centers,
      (r - 1).factorial * (actualStarLink H U z r).card ≤ L ^ (r - 1)) :
    ∃ owner : Edge (Fin n) → Fin n,
      (lostStarObjects H U Centers r owner).card ^ 2 ≤
        (U.powersetCard (r - 2)).card *
          (Centers.card * (Centers.card - 1) *
            ((r - 1) * (r - 1) * D₂ +
              U.card * (U.card - 1) * (r - 2) * D₃)) ∧
      (∀ z ∈ Centers, ∀ w ∈ Centers, z ≠ w →
        Disjoint (Finset.shadow (ownedStarLink H U r owner z))
          (Finset.shadow (ownedStarLink H U r owner w))) ∧
      (r - 1) * (actualStarLayerObjects H U Centers r).card ≤
        (r - 1) * (lostStarObjects H U Centers r owner).card +
          (L + (r - 1)) * n.choose (r - 2) := by
  classical
  obtain ⟨owner, hLoss⟩ := actualStarLayerOwnershipDeletion_card_sq_le_exists_max
    hH hCenters hr hD₂ hD₃
  refine ⟨owner, ?_, ?_, ?_⟩
  · simpa [lostStarObjects, starMemberLost] using hLoss
  · intro z hz w hw hzw
    exact ownedStarLink_shadows_disjoint H U r owner hzw
  · have hAlloc := disjoint_shadow_radius_allocation Centers
      (ownedStarLink H U r owner) (by omega : 2 ≤ r - 1)
      (by intro z hz; exact ownedStarLink_uniform H U r owner z)
      (by
        intro z hz
        exact (Nat.mul_le_mul_left _ (Finset.card_le_card
          (ownedStarLink_subset H U r owner z))).trans (hSize z hz))
      (by
        intro z hz w hw hzw
        exact ownedStarLink_shadows_disjoint H U r owner hzw)
    have hIndex : r - 1 - 1 = r - 2 := by omega
    rw [hIndex] at hAlloc
    rw [← star_layer_ownership_card_partition H U Centers r owner, Nat.mul_add]
    exact Nat.add_le_add_left hAlloc _

end JSP523.Rank5
