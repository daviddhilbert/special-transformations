import Section10.WeightedZeroRepresentation
import Section4.RVFiniteScissors
import Section7.LiftedIsomorphism

/-! Weighted zero scissors use restrictions of the same actual form.
The zero lift respects these relations and therefore descends to the
positive additive presentations, retaining every generator's density. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section7

noncomputable section

namespace SpecialTransformations.Section10

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CommMonoidWithZero G]
variable {S : Set M} {d : VolumeScale M G}
variable {hc : CanonicalStructure.IsCanonical (M := M)}

namespace MeasuredVFZero

def empty (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (d : VolumeScale M G) :
    MeasuredVFZero hc S d :=
  ⟨⟨⟨⟨(0, 0), DefSet.empty _ S⟩, vfDim_le_arity (volumeGammaSpace hc) _⟩,
      fun _ => Set.finite_empty⟩,
    ⟨Map.empty _ _ S, fun a => False.elim a.property⟩⟩

def restrict (A : MeasuredVFZero hc S d)
    (E : DefSet (mixedFamily A.underlying.obj.obj.index) S)
    (hE : E.carrier ⊆ A.domain.carrier) : MeasuredVFZero hc S d :=
  ⟨⟨⟨⟨A.underlying.obj.obj.index, E⟩,
      (Dimension.dim_mono rawVFSpace (AuxiliaryCoordinates.space (volumeGammaSpace hc)) hE
        ⟨_, mixed_has_dimension_bound (volumeGammaSpace hc) A.domain⟩).trans
          A.underlying.obj.property⟩,
      fun a => (A.underlying.property a).subset (fun _ h => hE h)⟩,
    A.form.restrict E hE⟩

@[simp] theorem restrict_weight (A : MeasuredVFZero hc S d)
    (E : DefSet (mixedFamily A.underlying.obj.obj.index) S)
    (hE : E.carrier ⊆ A.domain.carrier) (a : E) :
    (A.restrict E hE).weight a = A.weight ⟨a.val, hE a.property⟩ := rfl

theorem restrict_congr (A : MeasuredVFZero hc S d)
    {E F : DefSet (mixedFamily A.underlying.obj.obj.index) S}
    (hE : E.carrier ⊆ A.domain.carrier) (hF : F.carrier ⊆ A.domain.carrier) (he : E = F) :
    A.restrict E hE = A.restrict F hF := by subst F; rfl

def Scissor (A B D E : MeasuredVFZero hc S d) : Prop :=
  ∃ (U : MeasuredVFZero hc S d)
    (X Y : DefSet (mixedFamily U.underlying.obj.obj.index) S)
    (hX : X.carrier ⊆ U.domain.carrier) (hY : Y.carrier ⊆ U.domain.carrier),
    A = U.restrict X hX ∧ B = U.restrict Y hY ∧
    D = U.restrict (X.union Y) (fun _ h => h.elim (fun h => hX h) (fun h => hY h)) ∧
    E = U.restrict (X.inter Y) (fun _ h => hX h.1)

def presentation : PositiveAdditiveGrothendieck.Presentation (MeasuredVFZero hc S d) where
  iso A B := Nonempty (A ≅ B)
  empty := empty hc S d
  scissor := Scissor

end MeasuredVFZero

namespace MeasuredRVZero

def empty (S : Set M) (d : VolumeScale M G) : MeasuredRVZero S d :=
  ⟨rvFiniteEmpty S 0, ⟨Map.empty _ _ S, fun a => False.elim a.property⟩⟩

def restrict (U : MeasuredRVZero S d)
    (E : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) S)
    (hE : E.carrier ⊆ U.domain.carrier) : MeasuredRVZero S d :=
  ⟨rvFiniteRestrict U.underlying E hE, U.form.restrict E hE⟩

@[simp] theorem restrict_weight (U : MeasuredRVZero S d)
    (E : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) S)
    (hE : E.carrier ⊆ U.domain.carrier) (a : E) :
    (U.restrict E hE).weight a = U.weight ⟨a.val, hE a.property⟩ := rfl

def Scissor (A B D E : MeasuredRVZero S d) : Prop :=
  ∃ (U : MeasuredRVZero S d)
    (X Y : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) S)
    (hX : X.carrier ⊆ U.domain.carrier) (hY : Y.carrier ⊆ U.domain.carrier),
    A = U.restrict X hX ∧ B = U.restrict Y hY ∧
    D = U.restrict (X.union Y) (fun _ h => h.elim (fun h => hX h) (fun h => hY h)) ∧
    E = U.restrict (X.inter Y) (fun _ h => hX h.1)

def presentation : PositiveAdditiveGrothendieck.Presentation (MeasuredRVZero S d) where
  iso U V := Nonempty (U ≅ V)
  empty := empty S d
  scissor := Scissor

theorem lift_empty_iso (hc : CanonicalStructure.IsCanonical (M := M)) :
    Nonempty ((empty S d).lift hc ≅ MeasuredVFZero.empty hc S d) := by
  have he : ((empty S d).lift hc).domain.carrier = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro p ⟨u, _, _⟩
    exact u.property
  let f := Map.fromEmpty he (MeasuredVFZero.empty hc S d).domain
  refine ⟨WeightedZero.isoOfExactMap ⟨f, Map.bijective_of_empty f he rfl, ?_⟩⟩
  intro a
  exact False.elim (he.le a.property)

theorem lift_restrict (hc : CanonicalStructure.IsCanonical (M := M)) (U : MeasuredRVZero S d)
    (E : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) S)
    (hE : E.carrier ⊆ U.domain.carrier) :
    (U.restrict E hE).lift hc = (U.lift hc).restrict (rvLift (U.underlying.obj.restrict E hE))
      (fun p hp => ((rvLift_restrict_mem_iff U.underlying.obj E hE p).mp hp).1) := by
  have hf : ((U.restrict E hE).lift hc).form.map =
      ((U.lift hc).restrict (rvLift (U.underlying.obj.restrict E hE))
        (fun p hp => ((rvLift_restrict_mem_iff U.underlying.obj E hE p).mp hp).1)).form.map := by
    apply Map.ext
    intro a
    exact congrArg U.form.map (Subtype.ext rfl)
  have hz : ((U.restrict E hE).lift hc).form =
      ((U.lift hc).restrict (rvLift (U.underlying.obj.restrict E hE))
        (fun p hp => ((rvLift_restrict_mem_iff U.underlying.obj E hE p).mp hp).1)).form := by
    cases hf
    rfl
  exact congrArg (fun ω => (⟨((U.restrict E hE).lift hc).underlying, ω⟩ : MeasuredVFZero hc S d)) hz

theorem lift_scissor (hc : CanonicalStructure.IsCanonical (M := M))
    {A B D E : MeasuredRVZero S d} (h : Scissor A B D E) :
    MeasuredVFZero.Scissor (A.lift hc) (B.lift hc) (D.lift hc) (E.lift hc) := by
  obtain ⟨U, X, Y, hX, hY, rfl, rfl, rfl, rfl⟩ := h
  let V := U.underlying.obj
  let P := rvLift (V.restrict X hX)
  let Q := rvLift (V.restrict Y hY)
  have hP : P.carrier ⊆ (rvLift V).carrier := fun p hp => ((rvLift_restrict_mem_iff V X hX p).mp hp).1
  have hQ : Q.carrier ⊆ (rvLift V).carrier := fun p hp => ((rvLift_restrict_mem_iff V Y hY p).mp hp).1
  refine ⟨U.lift hc, P, Q, hP, hQ, lift_restrict hc U X hX, lift_restrict hc U Y hY, ?_, ?_⟩
  · exact (lift_restrict hc U _ _).trans
      ((U.lift hc).restrict_congr _ _ (rvLift_restrict_union V X Y hX hY))
  · exact (lift_restrict hc U _ _).trans
      ((U.lift hc).restrict_congr _ _ (rvLift_restrict_inter V X Y hX hY))

def liftHom (hc : CanonicalStructure.IsCanonical (M := M)) :
    PositiveAdditiveGrothendieck.KPlus (presentation (S := S) (d := d)) →+
      PositiveAdditiveGrothendieck.KPlus (MeasuredVFZero.presentation (hc := hc) (S := S) (d := d)) :=
  PositiveAdditiveGrothendieck.lift _ {
    toFun U := PositiveAdditiveGrothendieck.of MeasuredVFZero.presentation (U.lift hc)
    iso h := PositiveAdditiveGrothendieck.of_iso _ (theorem_10_5_weighted_zero hc h.some)
    empty := (PositiveAdditiveGrothendieck.of_iso _ (lift_empty_iso hc)).trans
      (PositiveAdditiveGrothendieck.of_empty _)
    scissor h := PositiveAdditiveGrothendieck.of_scissor _ (lift_scissor hc h) }

@[simp] theorem liftHom_generator (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVZero S d) :
    liftHom hc (PositiveAdditiveGrothendieck.of presentation U) =
      PositiveAdditiveGrothendieck.of MeasuredVFZero.presentation (U.lift hc) :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

theorem corollary_10_6_weighted_zero
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk S < κ) : Function.Surjective (liftHom (S := S) (d := d) hc) := by
  let T := MeasuredVFZero.presentation (hc := hc) (S := S) (d := d)
  intro z
  obtain ⟨p, rfl⟩ := (PositiveAdditiveGrothendieck.congruence T).mk'_surjective z
  change PositiveAdditiveGrothendieck.quotientHom T p ∈ Set.range (liftHom hc)
  refine Finsupp.induction_linear
    (motive := fun p => PositiveAdditiveGrothendieck.quotientHom T p ∈ Set.range (liftHom hc))
    p ?_ ?_ ?_
  · exact ⟨0, by simp only [map_zero]⟩
  · rintro p q ⟨x, hx⟩ ⟨y, hy⟩
    exact ⟨x + y, by rw [map_add, hx, hy, map_add]⟩
  · intro A m
    obtain ⟨U, hU⟩ := theorem_10_4_weighted_zero hc hκ hs h00 hsmall A
    let u := PositiveAdditiveGrothendieck.of presentation U
    have hu : liftHom hc u = PositiveAdditiveGrothendieck.of T A :=
      (liftHom_generator hc U).trans (PositiveAdditiveGrothendieck.of_iso T hU).symm
    refine ⟨m • u, ?_⟩
    rw [map_nsmul, hu]
    induction m with
    | zero => simp only [zero_nsmul, Finsupp.single_zero, map_zero]
    | succ m ih =>
      rw [succ_nsmul, ih, show PositiveAdditiveGrothendieck.of T A =
        PositiveAdditiveGrothendieck.quotientHom T (Finsupp.single A 1) from rfl,
        ← map_add, Finsupp.single_add]

end MeasuredRVZero
end SpecialTransformations.Section10
