import JSP523.Basic
import Mathlib.Data.Finset.Prod
import Lean.Elab.Tactic.Omega

set_option linter.unusedSectionVars false

/-!
# Two private facets per unrooted rank-five edge

This is the finite counting step after the four-face/root criterion has
established two distinct private facets for every unrooted edge.  The map from
an edge and a Boolean choice to an actual facet is explicit; uniqueness of a
private facet is supplied as the injection hypothesis.  Nothing here assumes
that a face is private merely because it belongs to the shadow.
-/

namespace JSP523.Rank5

section PrivateFacets

variable {α : Type*} [DecidableEq α]

/-- Private means that the chosen face is contained in no *other* edge of
    `all`.  Together with two distinct choices on one edge this supplies the
    injection used by the shadow count. -/
theorem private_certificates_injective
    {all unrooted : Family α}
    (facet : Edge α → Bool → Edge α)
    (hsub : unrooted ⊆ all)
    (hface : ∀ E ∈ unrooted, ∀ b : Bool, facet E b ⊆ E)
    (hprivate : ∀ E ∈ unrooted, ∀ b : Bool,
      ∀ F ∈ all, facet E b ⊆ F → F = E)
    (hchoice : ∀ E ∈ unrooted, ∀ b b' : Bool,
      facet E b = facet E b' → b = b') :
    ∀ E ∈ unrooted, ∀ E' ∈ unrooted,
      ∀ b b' : Bool, facet E b = facet E' b' → E = E' ∧ b = b' := by
  intro E hE E' hE' b b' heq
  have hface' : facet E b ⊆ E' := by
    rw [heq]
    exact hface E' hE' b'
  have hEE' : E' = E := hprivate E hE b E' (hsub hE') hface'
  have hbb' : b = b' := by
    rw [hEE'] at heq
    exact hchoice E hE b b' heq
  exact ⟨hEE'.symm, hbb'⟩

/-- An injection of two facet certificates per unrooted edge gives the
    cardinal inequality `2 * unrooted.card ≤ shadow.card`. -/
theorem two_private_facets_card
    {unrooted shadow : Family α}
    (facet : Edge α → Bool → Edge α)
    (hmem : ∀ E ∈ unrooted, ∀ b : Bool, facet E b ∈ shadow)
    (hinj : ∀ E ∈ unrooted, ∀ E' ∈ unrooted,
      ∀ b b' : Bool, facet E b = facet E' b' → E = E' ∧ b = b') :
    2 * unrooted.card ≤ shadow.card := by
  let D : Finset (Edge α × Bool) :=
    unrooted.product (Finset.univ : Finset Bool)
  let encode : Edge α × Bool → Edge α := fun p => facet p.1 p.2
  have hmap : Set.MapsTo encode (↑D : Set (Edge α × Bool))
      (↑shadow : Set (Edge α)) := by
    intro p hp
    have hp' : p ∈ unrooted.product (Finset.univ : Finset Bool) := hp
    obtain ⟨hpU, _⟩ := Finset.mem_product.mp hp'
    exact hmem p.1 hpU p.2
  have hinjOn : Set.InjOn encode (↑D : Set (Edge α × Bool)) := by
    intro p hp q hq heq
    have hp' : p ∈ unrooted.product (Finset.univ : Finset Bool) := hp
    have hq' : q ∈ unrooted.product (Finset.univ : Finset Bool) := hq
    have hpU := (Finset.mem_product.mp hp').1
    have hqU := (Finset.mem_product.mp hq').1
    obtain ⟨hE, hb⟩ := hinj p.1 hpU q.1 hqU p.2 q.2 heq
    exact Prod.ext hE hb
  have hbound : D.card ≤ shadow.card :=
    Finset.card_le_card_of_injOn encode hmap hinjOn
  have hBool : (Finset.univ : Finset Bool).card = 2 := by decide
  have hDcard : D.card =
      unrooted.card * (Finset.univ : Finset Bool).card := by
    simp [D, Finset.card_product]
  have hD : D.card = 2 * unrooted.card := by
    calc
      D.card = unrooted.card * (Finset.univ : Finset Bool).card := hDcard
      _ = unrooted.card * 2 := by rw [hBool]
      _ = 2 * unrooted.card := Nat.mul_comm _ _
  exact hD ▸ hbound

/-- The rank-five shadow deficit from two private facets per unrooted edge.
    `hdecomp` is the separate rooted/unrooted edge partition. -/
theorem shadow_bound_of_private_facets
    {all rooted unrooted shadow : Family α}
    (hdecomp : all.card = rooted.card + unrooted.card)
    (hprivate : 2 * unrooted.card ≤ shadow.card) :
    2 * all.card ≤ shadow.card + 2 * rooted.card := by
  omega

/-- Combined finite interface used before the already formalized real-valued
    `private_facet_surplus` algebra. -/
theorem shadow_bound_of_private_injection
    {all rooted unrooted shadow : Family α}
    (facet : Edge α → Bool → Edge α)
    (hdecomp : all.card = rooted.card + unrooted.card)
    (hmem : ∀ E ∈ unrooted, ∀ b : Bool, facet E b ∈ shadow)
    (hinj : ∀ E ∈ unrooted, ∀ E' ∈ unrooted,
      ∀ b b' : Bool, facet E b = facet E' b' → E = E' ∧ b = b') :
    2 * all.card ≤ shadow.card + 2 * rooted.card := by
  have hprivate := two_private_facets_card facet hmem hinj
  exact shadow_bound_of_private_facets hdecomp hprivate

/-- The count in terms of concrete private-face certificates.  This is the
    finite interface to the rank-five four-face coherence theorem. -/
theorem shadow_bound_of_private_certificates
    {all rooted unrooted shadow : Family α}
    (facet : Edge α → Bool → Edge α)
    (hdecomp : all.card = rooted.card + unrooted.card)
    (hsub : unrooted ⊆ all)
    (hmem : ∀ E ∈ unrooted, ∀ b : Bool, facet E b ∈ shadow)
    (hface : ∀ E ∈ unrooted, ∀ b : Bool, facet E b ⊆ E)
    (hprivate : ∀ E ∈ unrooted, ∀ b : Bool,
      ∀ F ∈ all, facet E b ⊆ F → F = E)
    (hchoice : ∀ E ∈ unrooted, ∀ b b' : Bool,
      facet E b = facet E b' → b = b') :
    2 * all.card ≤ shadow.card + 2 * rooted.card := by
  have hinj := private_certificates_injective facet hsub hface hprivate hchoice
  exact shadow_bound_of_private_injection facet hdecomp hmem hinj

end PrivateFacets

end JSP523.Rank5
