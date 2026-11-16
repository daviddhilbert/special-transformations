module

public import Section4.MapCorestrict
public import Section4.CodeMaps

@[expose] public section

open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.DefinableGeometry.Map

variable {L : Language} {M : Type} [L.Structure M]
variable {P Q R T : Space L M} {S : Set M}
variable {A : DefSet P S} {B : DefSet Q S} {C : DefSet R S} {D : DefSet T S}

def prodFst (A : DefSet P S) (B : DefSet Q S) : Map (A.prod B) A :=
  (Map.fst P Q S (A.prod B)).corestrict (fun a => a.property.1)

def prodSnd (A : DefSet P S) (B : DefSet Q S) : Map (A.prod B) B :=
  (Map.snd P Q S (A.prod B)).corestrict (fun a => a.property.2)

def prodMap (f : Map A C) (g : Map B D) : Map (A.prod B) (C.prod D) :=
  (f.comp (prodFst A B)).pair (g.comp (prodSnd A B))

@[simp] theorem prodMap_apply (f : Map A C) (g : Map B D) (a : A.prod B) :
    (prodMap f g a).val = ((f ⟨a.val.1, a.property.1⟩).val,
      (g ⟨a.val.2, a.property.2⟩).val) := rfl

theorem FiniteFibres.prodMap {f : Map A C} {g : Map B D}
    (hf : f.FiniteFibres) (hg : g.FiniteFibres) : (prodMap f g).FiniteFibres := by
  intro z
  let c : C := ⟨z.val.1, z.property.1⟩
  let d : D := ⟨z.val.2, z.property.2⟩
  let merge : A × B → A.prod B :=
    fun ab => ⟨(ab.1.val, ab.2.val), ab.1.property, ab.2.property⟩
  apply (((hf c).prod (hg d)).image merge).subset
  intro a ha
  have he := congrArg Subtype.val ha
  refine ⟨(⟨a.val.1, a.property.1⟩, ⟨a.val.2, a.property.2⟩), ?_, ?_⟩
  · exact ⟨Subtype.ext (congrArg Prod.fst he), Subtype.ext (congrArg Prod.snd he)⟩
  · exact Subtype.ext rfl

end SpecialTransformations.DefinableGeometry.Map
