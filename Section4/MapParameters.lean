module

public import Section4.FiniteMaps

@[expose] public section

open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.DefinableGeometry

variable {L : Language} {M : Type} [L.Structure M]
variable {P Q : Space L M} {S T : Set M}

theorem DefSet.eq_of_carrier_eq {A B : DefSet P S} (h : A.carrier = B.carrier) : A = B := by
  cases A
  cases B
  cases h
  rfl

def DefSet.extend (A : DefSet P S) (hST : S ⊆ T) : DefSet P T :=
  ⟨A.carrier, A.definable.mono P hST⟩

namespace Map

variable {A : DefSet P S} {B : DefSet Q S}

def extend (f : Map A B) (hST : S ⊆ T) : Map (A.extend hST) (B.extend hST) where
  toFun := f
  graph_definable := f.graph_definable.mono P Q hST

theorem FiniteFibres.extend {f : Map A B} (hf : f.FiniteFibres) (hST : S ⊆ T) :
    (f.extend hST).FiniteFibres := hf

/-- Each value set of a genuine function graph is empty or a singleton. -/
theorem graph_values_finite (f : Map A B) (x : P.Carrier) : {y | f.graph x y}.Finite := by
  apply Set.Subsingleton.finite
  rintro y ⟨a, ha, hay⟩ z ⟨b, hb, hbz⟩
  have hab : a = b := Subtype.ext (ha.trans hb.symm)
  subst b
  exact hay.symm.trans hbz

end Map

end SpecialTransformations.DefinableGeometry
