module

public import Section6.FunctionalClosure
public import Section4.DefinableGeometry

@[expose] public section

/-! Functional closure for the actual full-graph maps of Section 4.
The target presentation must have unique real codes; the assertion is not
made for arbitrary imaginary presentations with many representatives. -/

open FirstOrder FirstOrder.Language
set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section6
open DefinableGeometry

variable {L : Language} {M : Type} [L.Structure M]

def RepresentedIn (P : Space L M) (X : Set M) (p : P.Carrier) : Prop :=
  ∃ c : P.domain, P.decode c = p ∧ ∀ i, c.val i ∈ X

theorem map_preserves_represented {P Q : Space L M} {S X : Set M}
    (hX : DclClosed (L := L) X) (hSX : S ⊆ X)
    (hQ : Function.Injective Q.decode)
    {A : DefSet P S} {B : DefSet Q S} (f : Map A B) (a : A)
    (ha : RepresentedIn P X a.val) : RepresentedIn Q X (f a).val := by
  obtain ⟨ca, hca, hcaX⟩ := ha
  obtain ⟨cb, hcb⟩ := Q.onto (f a).val
  have hR := Set.Definable.mono f.graph_definable hSX
  have hs : X.Definable L {cb.val} :=
    singleton_of_unique_relation hR ca.val hcaX cb.val (by
      intro y
      change (∃ hx : (Sum.elim ca.val y) ∘ Sum.inl ∈ P.domain,
        ∃ hy : (Sum.elim ca.val y) ∘ Sum.inr ∈ Q.domain,
        ∃ a' : A, a'.val = P.decode ⟨_, hx⟩ ∧
          (f a').val = Q.decode ⟨_, hy⟩) ↔ y = cb.val
      simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
      constructor
      · rintro ⟨_, hy, a', ha', hf⟩
        have haa : a' = a := Subtype.ext (ha'.trans hca)
        have hdec : Q.decode ⟨y, hy⟩ = Q.decode cb := by
          rw [← hf, haa, hcb]
        exact congrArg Subtype.val (hQ hdec)
      · rintro rfl
        exact ⟨ca.property, cb.property, a, hca.symm, hcb.symm⟩)
  exact ⟨cb, hcb, fun i => hX _ (singleton_tuple_coordinates hs i)⟩

end SpecialTransformations.Section6
