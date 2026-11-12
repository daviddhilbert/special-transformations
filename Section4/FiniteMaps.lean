module

public import Section4.Products
public import Mathlib.Data.Set.Finite.Lattice

@[expose] public section
set_option linter.style.haveILetI false

open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.DefinableGeometry

variable {L : Language} {M : Type} [L.Structure M]

namespace Map

variable {P Q R : Space L M} {S : Set M}
variable {A : DefSet P S} {B : DefSet Q S} {C : DefSet R S}

def FiniteFibres (f : Map A B) : Prop := ∀ b : B, {a : A | f a = b}.Finite

theorem finiteFibres_of_injective {f : Map A B} (hf : Function.Injective f) :
    f.FiniteFibres := by
  intro b
  exact (Set.finite_singleton b).preimage hf.injOn

theorem FiniteFibres.comp {g : Map B C} {f : Map A B}
    (hg : g.FiniteFibres) (hf : f.FiniteFibres) : (g.comp f).FiniteFibres := by
  intro c
  have h := (hg c).biUnion (fun b _ => hf b)
  apply h.subset
  intro a ha
  exact Set.mem_iUnion.mpr ⟨f a, Set.mem_iUnion.mpr ⟨ha, rfl⟩⟩

theorem finiteFibres_of_finite (f : Map A B) (hA : A.carrier.Finite) : f.FiniteFibres := by
  haveI : Finite A := hA.to_subtype
  intro b
  exact Set.toFinite _

noncomputable def toSubsingleton (A : DefSet P S) (Q : Space L M)
    [Nonempty Q.Carrier] [Subsingleton Q.Carrier] : Map A (DefSet.univ Q S) where
  toFun _ := ⟨Classical.choice inferInstance, Set.mem_univ _⟩
  graph_definable := (A.definable.left_relation P Q).congr P Q (by
    intro x y
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl, Subsingleton.elim _ _⟩
    · rintro ⟨a, rfl, _⟩
      exact a.property)

def empty (P Q : Space L M) (S : Set M) :
    Map (DefSet.empty P S) (DefSet.univ Q S) where
  toFun a := False.elim a.property
  graph_definable := by
    change S.Definable L _
    have h : S.Definable L (∅ : Set (P.Index ⊕ Q.Index → M)) := Set.definable_empty
    convert h using 1
    ext z
    constructor
    · rintro ⟨hx, hy, a, ha, he⟩
      exact False.elim a.property
    · exact False.elim

end Map

end SpecialTransformations.DefinableGeometry
