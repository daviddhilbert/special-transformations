module

public import Section5.ParameterExtension
public import Section3.GammaParameters

@[expose] public section

/-!
# Original-base Gamma graph certificates

Real codes may be used inside a presentation, but every locus and complete
focus graph below must be definable over the actual Gamma base. The
certificate uses the full invariant preimage from Section 3; it does not
name an RV representative in that base. These are definitions and elementary
projections of the certificate, not an existence proof for Gamma preparation.
-/

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
variable {S : Set M} {n m l : ℕ}

def gammaPointCode (p : Point (M := M) n m) : Fin (n + m) → M :=
  Fin.append (fun i => (vfAt p i).val) (fun i => (p.2 i).val)

def gammaPointSort (n m : ℕ) : Fin (n + m) → SortTag :=
  Fin.append (fun _ => .vf) (fun _ => .rv)

def GammaSetDefinable (B : Section3.GammaParameters.Base (M := M))
    (A : Set (Point (M := M) n m)) : Prop :=
  Section3.GammaParameters.DefinableOverBase B (gammaPointSort n m) (gammaPointCode '' A)

def GammaGraphDefinable (B : Section3.GammaParameters.Base (M := M)) {u w : ℕ}
    (r : Point (M := M) n m → Point (M := M) u w → Prop) : Prop :=
  Section3.GammaParameters.DefinableOverBase B
    (Fin.append (gammaPointSort n m) (gammaPointSort u w))
    {z | ∃ p q, r p q ∧ Fin.append (gammaPointCode p) (gammaPointCode q) = z}

def GammaFocusDefinable (B : Section3.GammaParameters.Base (M := M))
    {A : DefSet (M := M) S n m} {j : Fin n} {k : Fin m} (D : Focus A j k) : Prop :=
  GammaSetDefinable B D.locus ∧
    GammaGraphDefinable B (fun (p : Point (M := M) n m) (z : Point (M := M) 1 0) =>
      p ∈ carrier A ∩ D.locus ∧ vfAt z 0 = D.center p)

def GammaPrimitiveDefinable (B : Section3.GammaParameters.Base (M := M))
    {A : DefSet (M := M) S n m} {C : DefSet (M := M) S n l} : Primitive S n A C → Prop
  | .canonical A => GammaSetDefinable B (carrier A)
  | .centripetal D => GammaSetDefinable B (carrier A) ∧ GammaFocusDefinable B D

def GammaChainDefinable (B : Section3.GammaParameters.Base (M := M))
    {a b : ℕ} {A : DefSet (M := M) S n a} {C : DefSet (M := M) S n b} : Chain S n A C → Prop
  | .nil A => GammaSetDefinable B (carrier A)
  | .cons p tail => GammaPrimitiveDefinable B p ∧ GammaChainDefinable B tail

theorem GammaChainDefinable.source (B : Section3.GammaParameters.Base (M := M))
    {A : DefSet (M := M) S n m} {C : DefSet (M := M) S n l}
    (T : Chain S n A C) (hT : GammaChainDefinable B T) : GammaSetDefinable B (carrier A) := by
  cases T with
  | nil _ => exact hT
  | cons p tail => cases p <;> first | exact hT.1 | exact hT.1.1

theorem GammaChainDefinable.target (B : Section3.GammaParameters.Base (M := M))
    {A : DefSet (M := M) S n m} {C : DefSet (M := M) S n l}
    (T : Chain S n A C) (hT : GammaChainDefinable B T) : GammaSetDefinable B (carrier C) := by
  induction T with
  | nil _ => exact hT
  | cons p tail ih => exact ih hT.2

theorem GammaPrimitiveDefinable.extendBase {R : Set M}
    (B : Section3.GammaParameters.Base (M := M))
    {A : DefSet (M := M) S n m} {C : DefSet (M := M) S n l}
    (p : Primitive S n A C) (hSR : S ⊆ R) (hp : GammaPrimitiveDefinable B p) :
    GammaPrimitiveDefinable B (p.extendBase hSR) := by
  cases p <;> exact hp

theorem GammaChainDefinable.extendBase {R : Set M}
    (B : Section3.GammaParameters.Base (M := M))
    {A : DefSet (M := M) S n m} {C : DefSet (M := M) S n l}
    (T : Chain S n A C) (hSR : S ⊆ R) (hT : GammaChainDefinable B T) :
    GammaChainDefinable B (T.extendBase hSR) := by
  induction T with
  | nil _ => exact hT
  | cons p tail ih => exact ⟨GammaPrimitiveDefinable.extendBase B p hSR hT.1, ih hT.2⟩

/-- A genuine existing special-bijection chain, with complete invariant
Gamma graph certificates for every primitive. The real presentation is
internal data; its parameters do not replace the named Gamma base. -/
structure GammaSpecialBijection (B : Section3.GammaParameters.Base (M := M))
    (A : Set (Point (M := M) n m)) (C : Set (Point (M := M) n l)) where
  codes : Set M
  real_contains : B.real ⊆ codes
  source : DefSet (M := M) codes n m
  target : DefSet (M := M) codes n l
  source_eq : carrier source = A
  target_eq : carrier target = C
  special : SpecialBijection source target
  invariant_graphs : GammaChainDefinable B special.chain

theorem GammaSpecialBijection.source_definable
    {B : Section3.GammaParameters.Base (M := M)}
    {A : Set (Point (M := M) n m)} {C : Set (Point (M := M) n l)}
    (T : GammaSpecialBijection B A C) : GammaSetDefinable B A := by
  exact T.source_eq ▸ GammaChainDefinable.source B T.special.chain T.invariant_graphs

theorem GammaSpecialBijection.target_definable
    {B : Section3.GammaParameters.Base (M := M)}
    {A : Set (Point (M := M) n m)} {C : Set (Point (M := M) n l)}
    (T : GammaSpecialBijection B A C) : GammaSetDefinable B C := by
  exact T.target_eq ▸ GammaChainDefinable.target B T.special.chain T.invariant_graphs

end SpecialTransformations.Section5
