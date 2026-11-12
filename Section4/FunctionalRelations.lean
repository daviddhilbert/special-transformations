module

public import Section4.DefinableGeometry

@[expose] public section

open Classical FirstOrder FirstOrder.Language

noncomputable section

namespace SpecialTransformations.DefinableGeometry.Map

variable {L : Language} {M : Type} [L.Structure M]
variable {P Q : Space L M} {S : Set M} {A : DefSet P S} {B : DefSet Q S}

/-- A total single-valued definable relation supplies a genuine definable
function. Uniqueness proves that its entire graph is the original relation. -/
def ofFunctionalRelation {R : P.Carrier → Q.Carrier → Prop}
    (hR : P.RelationDefinable Q S R)
    (hdom : ∀ x y, R x y → x ∈ A.carrier ∧ y ∈ B.carrier)
    (htotal : ∀ a : A, ∃ y, R a.val y)
    (hunique : ∀ x y z, R x y → R x z → y = z) : Map A B where
  toFun a := ⟨Classical.choose (htotal a),
    (hdom a.val _ (Classical.choose_spec (htotal a))).2⟩
  graph_definable := hR.congr P Q (by
    intro x y
    constructor
    · intro hxy
      let a : A := ⟨x, (hdom x y hxy).1⟩
      exact ⟨a, rfl, hunique x _ y (Classical.choose_spec (htotal a)) hxy⟩
    · rintro ⟨a, rfl, he⟩
      exact he ▸ Classical.choose_spec (htotal a))

theorem ofFunctionalRelation_graph {R : P.Carrier → Q.Carrier → Prop}
    (hR : P.RelationDefinable Q S R)
    (hdom : ∀ x y, R x y → x ∈ A.carrier ∧ y ∈ B.carrier)
    (htotal : ∀ a : A, ∃ y, R a.val y)
    (hunique : ∀ x y z, R x y → R x z → y = z) (a : A) :
    R a.val (ofFunctionalRelation hR hdom htotal hunique a).val :=
  Classical.choose_spec (htotal a)

end SpecialTransformations.DefinableGeometry.Map

end
