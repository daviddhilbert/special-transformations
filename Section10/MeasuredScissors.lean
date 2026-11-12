module

public import Section10.MeasuredVFCategory
public import Section4.RVFiniteScissors
public import Section7.LiftedIsomorphism

@[expose] public section

/-! Positive additive presentations for weighted scissors. Every piece
inherits its form by restriction, and lift commutes with these restrictions. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.Section9

noncomputable section

namespace SpecialTransformations.Section10

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CommMonoidWithZero G]
variable {C : BaseContext M} {hc : CanonicalStructure.IsCanonical (M := M)}
variable {d : VolumeScale M G} {k : ℕ}
local notation "S" => (C.base : Set M)
local notation "n" => (k + 1)

namespace MeasuredVF

def empty : MeasuredVF C hc d k where
  arity := 0
  domain := DefSet.empty _ S
  finite _ := Set.finite_empty
  form := Map.empty _ _ S
  allowed a := False.elim a.property

def restrict (A : MeasuredVF C hc d k)
    (E : DefSet (rawMixedSpace (M := M) n A.arity) S) (hE : E.carrier ⊆ A.domain.carrier) :
    MeasuredVF C hc d k where
  arity := A.arity
  domain := E
  finite a := (A.finite a).subset (fun _ h => hE h)
  form := A.form.restrict hE
  allowed a := A.allowed ⟨a.val, hE a.property⟩

theorem restrict_congr (A : MeasuredVF C hc d k)
    {E F : DefSet (rawMixedSpace (M := M) n A.arity) S}
    (hE : E.carrier ⊆ A.domain.carrier) (hF : F.carrier ⊆ A.domain.carrier) (he : E = F) :
    A.restrict E hE = A.restrict F hF := by
  subst F
  rfl

def Scissor (A B D E : MeasuredVF C hc d k) : Prop :=
  ∃ (U : MeasuredVF C hc d k)
    (X Y : DefSet (rawMixedSpace (M := M) n U.arity) S)
    (hX : X.carrier ⊆ U.domain.carrier) (hY : Y.carrier ⊆ U.domain.carrier),
    A = U.restrict X hX ∧ B = U.restrict Y hY ∧
    D = U.restrict (X.union Y) (fun _ h => h.elim (fun h => hX h) (fun h => hY h)) ∧
    E = U.restrict (X.inter Y) (fun _ h => hX h.1)

def presentation [CharZero (VFType (M := M))] :
    PositiveAdditiveGrothendieck.Presentation (MeasuredVF C hc d k) where
  iso A B := Nonempty (A ≅ B)
  empty := empty
  scissor := Scissor

end MeasuredVF

/-- The finite-volume RV labels and their definable form. -/
structure MeasuredRV (C : BaseContext M) (d : VolumeScale M G) (k : ℕ) where
  underlying : RVFiniteObject (M := M) (C.base : Set M) (k + 1)
  form : Map underlying.obj.domain (DefSet.univ d.space (C.base : Set M))
  allowed : ∀ a, d.allowed (form a).val

namespace MeasuredRV

def empty : MeasuredRV C d k where
  underlying := rvFiniteEmpty S n
  form := Map.empty _ _ S
  allowed a := False.elim a.property

def restrict (U : MeasuredRV C d k)
    (E : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) S)
    (hE : E.carrier ⊆ U.underlying.obj.domain.carrier) : MeasuredRV C d k where
  underlying := rvFiniteRestrict U.underlying E hE
  form := U.form.restrict hE
  allowed a := U.allowed ⟨a.val, hE a.property⟩

def Scissor (A B D E : MeasuredRV C d k) : Prop :=
  ∃ (U : MeasuredRV C d k)
    (X Y : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) S)
    (hX : X.carrier ⊆ U.underlying.obj.domain.carrier) (hY : Y.carrier ⊆ U.underlying.obj.domain.carrier),
    A = U.restrict X hX ∧ B = U.restrict Y hY ∧
    D = U.restrict (X.union Y) (fun _ h => h.elim (fun h => hX h) (fun h => hY h)) ∧
    E = U.restrict (X.inter Y) (fun _ h => hX h.1)

def presentation (iso : MeasuredRV C d k → MeasuredRV C d k → Prop) :
    PositiveAdditiveGrothendieck.Presentation (MeasuredRV C d k) where
  iso := iso
  empty := empty
  scissor := Scissor

def lift (hc : CanonicalStructure.IsCanonical (M := M)) (U : MeasuredRV C d k) : MeasuredVF C hc d k where
  arity := U.underlying.obj.arity
  domain := rvLift U.underlying.obj
  finite := rvLift_finite_rv_fibres U.underlying.obj U.underlying.property
  form := U.form.comp (liftLabelMap U.underlying.obj)
  allowed a := U.allowed (liftLabelMap U.underlying.obj a)

private theorem lift_empty (hc : CanonicalStructure.IsCanonical (M := M)) :
    lift hc (empty : MeasuredRV C d k) = MeasuredVF.empty := by
  let A : DefSet (rawMixedSpace (M := M) n 0) S := rvLift (RVObject.empty S n)
  have he : A = DefSet.empty _ S := DefSet.eq_of_carrier_eq (Set.eq_empty_iff_forall_notMem.mpr (by
    rintro p ⟨u, _, _⟩
    exact u.property))
  have h {D : DefSet (rawMixedSpace (M := M) n 0) S}
      (hD : D = DefSet.empty _ S) (fin : ∀ a, {t | (a, t) ∈ D.carrier}.Finite)
      (f : Map D (DefSet.univ d.space S)) (hf : ∀ a, d.allowed (f a).val) :
      (⟨0, D, fin, f, hf⟩ : MeasuredVF C hc d k) = MeasuredVF.empty := by
    subst D
    have hm : f = Map.empty _ _ S := Map.ext (fun a => False.elim a.property)
    cases hm
    rfl
  exact h he _ _ _

private theorem lift_restrict (hc : CanonicalStructure.IsCanonical (M := M)) (U : MeasuredRV C d k)
    (E : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) S)
    (hE : E.carrier ⊆ U.underlying.obj.domain.carrier) :
    lift hc (U.restrict E hE) = (lift hc U).restrict (rvLift (U.underlying.obj.restrict E hE))
      (fun p hp => ((rvLift_restrict_mem_iff U.underlying.obj E hE p).mp hp).1) := by
  have he : (lift hc (U.restrict E hE)).form =
      ((lift hc U).restrict (rvLift (U.underlying.obj.restrict E hE))
        (fun p hp => ((rvLift_restrict_mem_iff U.underlying.obj E hE p).mp hp).1)).form := by
    apply Map.ext
    intro a
    exact congrArg U.form (Subtype.ext rfl)
  unfold lift MeasuredVF.restrict at he ⊢
  congr 1

theorem lift_scissor (hc : CanonicalStructure.IsCanonical (M := M))
    {A B D E : MeasuredRV C d k} (h : Scissor A B D E) :
    MeasuredVF.Scissor (lift hc A) (lift hc B) (lift hc D) (lift hc E) := by
  obtain ⟨U, X, Y, hX, hY, rfl, rfl, rfl, rfl⟩ := h
  let V := U.underlying.obj
  let P := rvLift (V.restrict X hX)
  let Q := rvLift (V.restrict Y hY)
  have hP : P.carrier ⊆ (rvLift V).carrier := fun p hp => ((rvLift_restrict_mem_iff V X hX p).mp hp).1
  have hQ : Q.carrier ⊆ (rvLift V).carrier := fun p hp => ((rvLift_restrict_mem_iff V Y hY p).mp hp).1
  refine ⟨lift hc U, P, Q, hP, hQ, lift_restrict hc U X hX, lift_restrict hc U Y hY, ?_, ?_⟩
  · refine (lift_restrict hc U _ _).trans ?_
    exact (lift hc U).restrict_congr _ _ (rvLift_restrict_union V X Y hX hY)
  · refine (lift_restrict hc U _ _).trans ?_
    exact (lift hc U).restrict_congr _ _ (rvLift_restrict_inter V X Y hX hY)

variable [CharZero (VFType (M := M))]

def liftHom (hc : CanonicalStructure.IsCanonical (M := M))
    (iso : MeasuredRV C d k → MeasuredRV C d k → Prop)
    (hi : ∀ {U V}, iso U V → Nonempty (lift hc U ≅ lift hc V)) :
    PositiveAdditiveGrothendieck.KPlus (presentation iso) →+
      PositiveAdditiveGrothendieck.KPlus (MeasuredVF.presentation (C := C) (hc := hc) (d := d) (k := k)) :=
  PositiveAdditiveGrothendieck.lift _ {
    toFun U := PositiveAdditiveGrothendieck.of MeasuredVF.presentation (lift hc U)
    iso h := PositiveAdditiveGrothendieck.of_iso _ (hi h)
    empty := by
      change PositiveAdditiveGrothendieck.of MeasuredVF.presentation (lift hc empty) = 0
      rw [lift_empty]
      exact PositiveAdditiveGrothendieck.of_empty _
    scissor h := PositiveAdditiveGrothendieck.of_scissor _ (lift_scissor hc h) }

theorem liftHom_generator (hc : CanonicalStructure.IsCanonical (M := M))
    (iso : MeasuredRV C d k → MeasuredRV C d k → Prop)
    (hi : ∀ {U V}, iso U V → Nonempty (lift hc U ≅ lift hc V)) (U : MeasuredRV C d k) :
    liftHom hc iso hi (PositiveAdditiveGrothendieck.of (presentation iso) U) =
      PositiveAdditiveGrothendieck.of MeasuredVF.presentation (lift hc U) :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

theorem liftHom_surjective (hc : CanonicalStructure.IsCanonical (M := M))
    (iso : MeasuredRV C d k → MeasuredRV C d k → Prop)
    (hi : ∀ {U V}, iso U V → Nonempty (lift hc U ≅ lift hc V))
    (hrep : ∀ A : MeasuredVF C hc d k, ∃ U : MeasuredRV C d k, Nonempty (A ≅ lift hc U)) :
    Function.Surjective (liftHom hc iso hi) := by
  let T := MeasuredVF.presentation (C := C) (hc := hc) (d := d) (k := k)
  intro z
  obtain ⟨p, rfl⟩ := (PositiveAdditiveGrothendieck.congruence T).mk'_surjective z
  change PositiveAdditiveGrothendieck.quotientHom T p ∈ Set.range (liftHom hc iso hi)
  refine Finsupp.induction_linear
    (motive := fun p => PositiveAdditiveGrothendieck.quotientHom T p ∈ Set.range (liftHom hc iso hi))
    p ?_ ?_ ?_
  · exact ⟨0, by simp only [map_zero]⟩
  · intro p q hp hq
    obtain ⟨x, hx⟩ := hp
    obtain ⟨y, hy⟩ := hq
    exact ⟨x + y, by rw [map_add, hx, hy, map_add]⟩
  · intro A m
    obtain ⟨U, hU⟩ := hrep A
    let u := PositiveAdditiveGrothendieck.of (presentation iso) U
    have hu : liftHom hc iso hi u = PositiveAdditiveGrothendieck.of T A :=
      (liftHom_generator hc iso hi U).trans (PositiveAdditiveGrothendieck.of_iso T hU).symm
    refine ⟨m • u, ?_⟩
    rw [map_nsmul, hu]
    induction m with
    | zero => simp only [zero_nsmul, Finsupp.single_zero, map_zero]
    | succ m ih =>
      rw [succ_nsmul, ih, show PositiveAdditiveGrothendieck.of T A =
        PositiveAdditiveGrothendieck.quotientHom T (Finsupp.single A 1) from rfl,
        ← map_add, Finsupp.single_add]

end MeasuredRV
end SpecialTransformations.Section10
