module

public import Section5.Assembly
public import Section4.MapParameters

@[expose] public section

/-! Parameter extension changes the definability certificate, while keeping
the actual primitive geometries and maps. This is used internally when a
named-Gamma domain is presented using real codes; the later Gamma graph
certificate must still establish definability over the original base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section5

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S R : Set M} {n m l : ℕ}

namespace PresentedSet
abbrev eq_of_carrier_eq := @DefinableGeometry.DefSet.eq_of_carrier_eq LRV M (CanonicalStructure.normalize (M := M))
end PresentedSet

namespace SetDefinable
abbrev mono := @DefinableGeometry.Space.Definable.mono LRV M (CanonicalStructure.normalize (M := M))
end SetDefinable

namespace RelationDefinable
abbrev mono := @DefinableGeometry.Space.RelationDefinable.mono LRV M (CanonicalStructure.normalize (M := M))
end RelationDefinable

abbrev extendBase {P : PresentedSpace (M := M)} (A : PresentedSet P S) (hSR : S ⊆ R) :=
  @DefinableGeometry.DefSet.extend LRV M (CanonicalStructure.normalize (M := M)) P S R A hSR

def Focus.extendBase {A : DefSet (M := M) S n m} {j : Fin n} {k : Fin m}
    (D : Focus A j k) (hSR : S ⊆ R) : Focus (extendBase A hSR) j k where
  toFocusGeometry := D.toFocusGeometry
  locus_definable := SetDefinable.mono _ D.locus_definable hSR
  center_graph := RelationDefinable.mono _ _ D.center_graph hSR

namespace Primitive

variable {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}

def extendBase (p : Primitive S n A B) (hSR : S ⊆ R) :
    Primitive R n (Section5.extendBase A hSR) (Section5.extendBase B hSR) := by
  cases p with
  | canonical A =>
    have he : canonicalImage (Section5.extendBase A hSR) =
        Section5.extendBase (canonicalImage A) hSR :=
      PresentedSet.eq_of_carrier_eq rfl
    exact he ▸ Primitive.canonical (Section5.extendBase A hSR)
  | centripetal D =>
    have he : (D.extendBase hSR).etaImage = Section5.extendBase D.etaImage hSR :=
      PresentedSet.eq_of_carrier_eq rfl
    exact he ▸ Primitive.centripetal (D.extendBase hSR)

theorem extendBase_apply (p : Primitive S n A B) (hSR : S ⊆ R)
    (a : Section5.extendBase A hSR) :
    ((p.extendBase hSR).toMap a).val = (p.toMap ⟨a.val, a.property⟩).val := by
  cases p <;> rfl

theorem extendBase_kind (p : Primitive S n A B) (hSR : S ⊆ R) :
    (p.extendBase hSR).kind = p.kind := by
  cases p <;> rfl

end Primitive

namespace Chain

variable {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}

public def extendBaseAux (hSR : S ⊆ R) {a b : ℕ}
    {X : DefSet (M := M) S n a} {Y : DefSet (M := M) S n b} :
    Chain S n X Y → Chain R n (Section5.extendBase X hSR) (Section5.extendBase Y hSR)
  | .nil A => .nil (Section5.extendBase A hSR)
  | .cons p tail => .cons (p.extendBase hSR) (extendBaseAux hSR tail)

def extendBase (T : Chain S n A B) (hSR : S ⊆ R) :
    Chain R n (Section5.extendBase A hSR) (Section5.extendBase B hSR) := extendBaseAux hSR T

theorem extendBase_alternating (T : Chain S n A B) (hSR : S ⊆ R) (previous : Option Bool)
    (hT : T.Alternating previous) : (T.extendBase hSR).Alternating previous := by
  induction T generalizing previous with
  | nil _ => trivial
  | cons p tail ih =>
    change (Chain.cons (p.extendBase hSR) (tail.extendBase hSR)).Alternating previous
    rw [cons_alternating_iff] at hT ⊢
    exact ⟨by simpa only [Primitive.extendBase_kind] using hT.1,
      by simpa only [Primitive.extendBase_kind] using ih (some p.kind) hT.2⟩

theorem extendBase_apply (T : Chain S n A B) (hSR : S ⊆ R)
    (a : Section5.extendBase A hSR) :
    ((T.extendBase hSR).toMap a).val = (T.toMap ⟨a.val, a.property⟩).val := by
  induction T with
  | nil _ => rfl
  | cons p tail ih =>
    change ((tail.extendBase hSR).toMap ((p.extendBase hSR).toMap a)).val = _
    have he : (⟨((p.extendBase hSR).toMap a).val,
        ((p.extendBase hSR).toMap a).property⟩ : _) = p.toMap ⟨a.val, a.property⟩ :=
      Subtype.ext (p.extendBase_apply hSR a)
    exact (ih ((p.extendBase hSR).toMap a)).trans
      (congrArg (fun b => (tail.toMap b).val) he)

theorem lastKind_cons {a b c : ℕ} {A : DefSet (M := M) S n a}
    {B : DefSet (M := M) S n b} {C : DefSet (M := M) S n c}
    (p : Primitive S n A B) (T : Chain S n B C) (previous : Option Bool) :
    (Chain.cons p T).lastKind previous = T.lastKind (some p.kind) := by
  cases p <;> rfl

theorem extendBase_lastKind (T : Chain S n A B) (hSR : S ⊆ R) (previous : Option Bool) :
    (T.extendBase hSR).lastKind previous = T.lastKind previous := by
  induction T generalizing previous with
  | nil _ => rfl
  | cons p tail ih =>
    change (Chain.cons (p.extendBase hSR) (tail.extendBase hSR)).lastKind previous = _
    rw [lastKind_cons, lastKind_cons, ih, Primitive.extendBase_kind]

end Chain

def SpecialBijection.extendBase {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}
    (T : SpecialBijection A B) (hSR : S ⊆ R) :
    SpecialBijection (extendBase A hSR) (extendBase B hSR) :=
  ⟨T.chain.extendBase hSR, T.chain.extendBase_alternating hSR none T.alternating⟩

theorem SpecialBijection.extendBase_inverse {A : DefSet (M := M) S n m}
    {B : DefSet (M := M) S n l} (T : SpecialBijection A B) (hSR : S ⊆ R)
    (b : Section5.extendBase B hSR) :
    ((T.extendBase hSR).inverseMap b).val = (T.inverseMap ⟨b.val, b.property⟩).val := by
  let a := (T.extendBase hSR).inverseMap b
  have he : T.toMap ⟨a.val, a.property⟩ = (⟨b.val, b.property⟩ : B) := by
    apply Subtype.ext
    exact (T.chain.extendBase_apply hSR a).symm.trans
      (congrArg Subtype.val ((T.extendBase hSR).apply_inverse b))
  have hi := congrArg T.inverseMap he
  rw [T.inverse_apply] at hi
  exact congrArg Subtype.val hi

end SpecialTransformations.Section5
