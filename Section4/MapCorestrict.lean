import Section4.MapParameters

open FirstOrder FirstOrder.Language

namespace SpecialTransformations.DefinableGeometry.Map

variable {L : Language} {M : Type} [L.Structure M]
variable {P Q : Space L M} {S : Set M}
variable {A : DefSet P S} {B B' : DefSet Q S}

def corestrict (f : Map A B) (h : ∀ a, (f a).val ∈ B'.carrier) : Map A B' where
  toFun a := ⟨(f a).val, h a⟩
  graph_definable := f.graph_definable

theorem corestrict_injective {f : Map A B} (hf : Function.Injective f)
    (h : ∀ a, (f a).val ∈ B'.carrier) : Function.Injective (f.corestrict h) := by
  intro a b he
  apply hf
  exact Subtype.ext (congrArg (fun y : B' => y.val) he)

end SpecialTransformations.DefinableGeometry.Map
