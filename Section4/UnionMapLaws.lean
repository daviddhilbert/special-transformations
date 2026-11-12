module

public import Section4.FiniteGluing
public import Section4.DefinableCategory

@[expose] public section

open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.DefinableGeometry.Map

variable {L : Language} {M : Type} [L.Structure M]
variable {P Q : Space L M} {S : Set M}
variable {A B : DefSet P S} {C : DefSet Q S}

theorem union_on_left (f : Map A C) (g : Map B C) (a : A) :
    f.union g ⟨a.val, Or.inl a.property⟩ = f a := by
  simp [Map.union, a.property]

theorem union_on_right (f : Map A C) (g : Map B C)
    (hd : Disjoint A.carrier B.carrier) (b : B) :
    f.union g ⟨b.val, Or.inr b.property⟩ = g b := by
  have hb : b.val ∉ A.carrier := fun h => Set.disjoint_left.mp hd h b.property
  simp [Map.union, hb]

theorem inverse_injective {R : Space L M} {D : DefSet R S}
    (f : Map A D) (hf : Function.Bijective f) : Function.Injective (f.inverse hf) := by
  intro a b he
  have h := congrArg f he
  simpa only [Map.apply_inverse] using h

end SpecialTransformations.DefinableGeometry.Map
