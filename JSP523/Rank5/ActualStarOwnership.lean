import JSP523.Basic
import JSP523.Rank5.ShadowOwnership

/-!
# Ownership deletion for actual star links

This instantiates the finite ownership count on the `(r-1)`-sets in the
links of centers outside a fixed ground set `U`, using their actual
`(r-2)`-subsets as facets.
-/

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α]

/-- Colored members of the star layers through `Centers`, restricted to U. -/
def actualStarLayerObjects (H : Family α) (U Centers : Edge α) (r : ℕ) :
    Finset (α × Edge α) :=
  (Centers ×ˢ U.powersetCard (r - 1)).filter fun zT : α × Edge α =>
    insert zT.1 zT.2 ∈ H

/-- The immediate shadow facets of a member of an actual star link. -/
def actualStarLayerFacets (U T : Edge α) (r : ℕ) : Edge (Edge α) :=
  (U.powersetCard (r - 2)).filter fun P => P ⊆ T

/-- Ownership deletion for real star-link members. A link member is deleted
if it contains a pair-shadow set whose assigned owner is another center. -/
theorem actual_star_layer_ownership_deletion_bound
    (H : Family α) (U Centers : Edge α) (r : ℕ) (owner : Edge α → α) :
    ((actualStarLayerObjects H U Centers r).filter fun zT : α × Edge α =>
      ∃ P ∈ actualStarLayerFacets U zT.2 r,
        P ∈ U.powersetCard (r - 2) ∧ owner P ≠ zT.1).card ≤
      ∑ P ∈ U.powersetCard (r - 2),
        badShadowDegree (actualStarLayerObjects H U Centers r)
          Prod.fst
          (fun zT : α × Edge α => actualStarLayerFacets U zT.2 r)
          owner P := by
  classical
  simpa [actualStarLayerObjects, actualStarLayerFacets, badShadowDegree,
    Finset.mem_filter, and_assoc, and_left_comm, and_comm] using
    (shadow_ownership_deletion_bound_on
      (E := actualStarLayerObjects H U Centers r)
      (P := U.powersetCard (r - 2))
      (color := Prod.fst)
      (facets := fun zT => actualStarLayerFacets U zT.2 r)
      (owner := owner))

/-- Every actual star-link member is a uniform `(r-1)`-set. -/
theorem actual_star_layer_links_uniform
    (H : Family α) (U Centers : Edge α) (r : ℕ) :
    Uniform (r - 1) ((actualStarLayerObjects H U Centers r).image Prod.snd) := by
  intro T hT
  obtain ⟨zT, hzT, rfl⟩ := Finset.mem_image.mp hT
  have hTpow : zT.2 ∈ U.powersetCard (r - 1) :=
    (Finset.mem_product.mp (Finset.mem_filter.mp hzT).1).2
  exact (Finset.mem_powersetCard.mp hTpow).2

end JSP523.Rank5
