import Section4.MapProduct

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language

namespace SpecialTransformations.DefinableGeometry.Map

variable {L : Language} {M : Type} [L.Structure M]
variable {P Q R T : Space L M} {S : Set M}
variable {A : DefSet P S} {B : DefSet Q S} {C : DefSet R S} {D : DefSet T S}

theorem prodMap_bijective (f : Map A C) (g : Map B D)
    (hf : Function.Bijective f) (hg : Function.Bijective g) :
    Function.Bijective (prodMap f g) := by
  constructor
  · intro a b he
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val (hf.1 (Subtype.ext
        (congrArg (fun x : C.prod D => x.val.1) he)))
    · exact congrArg Subtype.val (hg.1 (Subtype.ext
        (congrArg (fun x : C.prod D => x.val.2) he)))
  · intro c
    obtain ⟨a, ha⟩ := hf.2 ⟨c.val.1, c.property.1⟩
    obtain ⟨b, hb⟩ := hg.2 ⟨c.val.2, c.property.2⟩
    refine ⟨⟨(a.val, b.val), a.property, b.property⟩, Subtype.ext ?_⟩
    exact Prod.ext (congrArg Subtype.val ha) (congrArg Subtype.val hb)

@[simp] theorem prodMap_mk (f : Map A C) (g : Map B D) (a : A) (b : B) :
    prodMap f g ⟨(a.val, b.val), a.property, b.property⟩ =
      ⟨((f a).val, (g b).val), (f a).property, (g b).property⟩ := rfl

def prodSwap (A : DefSet P S) (B : DefSet Q S) : Map (A.prod B) (B.prod A) :=
  (prodSnd A B).pair (prodFst A B)

theorem prodSwap_bijective (A : DefSet P S) (B : DefSet Q S) :
    Function.Bijective (prodSwap A B) := by
  constructor
  · intro a b he
    apply Subtype.ext
    exact congrArg Prod.swap (congrArg Subtype.val he)
  · intro b
    exact ⟨⟨(b.val.2, b.val.1), b.property.2, b.property.1⟩, Subtype.ext rfl⟩

def prodAssoc (A : DefSet P S) (B : DefSet Q S) (C : DefSet R S) :
    Map ((A.prod B).prod C) (A.prod (B.prod C)) :=
  ((prodFst A B).comp (prodFst (A.prod B) C)).pair
    (((prodSnd A B).comp (prodFst (A.prod B) C)).pair (prodSnd (A.prod B) C))

@[simp] theorem prodAssoc_mk (A : DefSet P S) (B : DefSet Q S) (C : DefSet R S)
    (a : A) (b : B) (c : C) :
    prodAssoc A B C ⟨((a.val, b.val), c.val), ⟨a.property, b.property⟩, c.property⟩ =
      ⟨(a.val, (b.val, c.val)), a.property, b.property, c.property⟩ := rfl

theorem prodAssoc_bijective (A : DefSet P S) (B : DefSet Q S) (C : DefSet R S) :
    Function.Bijective (prodAssoc A B C) := by
  constructor
  · intro a b he
    apply Subtype.ext
    exact congrArg (fun x : P.Carrier × (Q.Carrier × R.Carrier) =>
      ((x.1, x.2.1), x.2.2)) (congrArg Subtype.val he)
  · intro b
    exact ⟨⟨((b.val.1, b.val.2.1), b.val.2.2),
      ⟨b.property.1, b.property.2.1⟩, b.property.2.2⟩, Subtype.ext rfl⟩

end SpecialTransformations.DefinableGeometry.Map
