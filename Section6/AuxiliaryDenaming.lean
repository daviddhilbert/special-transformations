module

public import Section6.ExpandedLogic

@[expose] public section

/-! Remove auxiliary parameter names by actual RV terms in the original
free-variable context. This is the syntactic step needed when the base
is enlarged by free VF parameters. It introduces only RV binders; the
replacement terms may contain free VF variables. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.AuxiliaryDenaming
open RVTermSupport RVAbstraction

variable {E : Language} {P R B : Type}

def reassociate : Auxiliary (E.sum (constantsOn P)) →ᴸ (Auxiliary E)[[P]] where
  onFunction := fun {_} f => match f with
    | .inl f => .inl (.inl f)
    | .inr (.inl f) => .inl (.inr f)
    | .inr (.inr c) => .inr c
  onRelation := fun {_} r => match r with
    | .inl r => .inl (.inl r)
    | .inr (.inl r) => .inl (.inr r)
    | .inr (.inr r) => isEmptyElim r

def unname (φ : (Auxiliary (E.sum (constantsOn P))).Formula R) :
    (Auxiliary E).Formula (P ⊕ R) :=
  BoundedFormula.constantsVarsEquiv (reassociate.onBoundedFormula φ)

def formula (σ : P ⊕ R → (Expanded E).Term B)
    (φ : (Auxiliary (E.sum (constantsOn P))).Formula R) : (Expanded E).Formula B :=
  GuardedLift.formula σ (unname φ)

theorem formula_isVFQF (σ : P ⊕ R → (Expanded E).Term B)
    (φ : (Auxiliary (E.sum (constantsOn P))).Formula R) :
    ExpandedLogic.IsVFQF (formula σ φ) := GuardedLift.formula_isVFQF _ _

theorem formula_wellSorted (sB : B → SortTag) (σ : P ⊕ R → (Expanded E).Term B)
    (hσ : ∀ p, termSort sB (σ p) = some .rv)
    (φ : (Auxiliary (E.sum (constantsOn P))).Formula R) :
    ExpandedLogic.WellSorted sB (fun _ => .rv) (formula σ φ) :=
  GuardedLift.formula_wellSorted _ _ hσ _

section Semantics
variable {M Q : Type} [(Expanded E).Structure M] [(Auxiliary E).Structure Q]
variable [E.Structure Q]

@[instance_reducible] def namedStructure (p : P → Q) :
    (Auxiliary (E.sum (constantsOn P))).Structure Q where
  funMap := fun {_} f z => match f with
    | .inl f => Structure.funMap (L := Auxiliary E) (.inl f) z
    | .inr (.inl f) => Structure.funMap (L := Auxiliary E) (.inr f) z
    | .inr (.inr c) => @Structure.funMap (constantsOn P) Q
        (constantsOn.structure p) _ c z
  RelMap := fun {_} r z => match r with
    | .inl r => Structure.RelMap (L := Auxiliary E) (.inl r) z
    | .inr (.inl r) => Structure.RelMap (L := Auxiliary E) (.inr r) z
    | .inr (.inr r) => isEmptyElim r

theorem reassociate_expansion (p : P → Q) :
    letI := namedStructure (E := E) p
    letI : (constantsOn P).Structure Q := constantsOn.structure p
    (reassociate (E := E) (P := P)).IsExpansionOn Q := by
  letI := namedStructure (E := E) p
  letI : (constantsOn P).Structure Q := constantsOn.structure p
  constructor
  · intro n f z
    cases f with
    | inl f => rfl
    | inr f => cases f <;> rfl
  · intro n r z
    cases r with
    | inl r => rfl
    | inr r => cases r with
      | inl r => rfl
      | inr r => exact isEmptyElim r

theorem unname_realize (p : P → Q)
    (φ : (Auxiliary (E.sum (constantsOn P))).Formula R) (b : R → Q) :
    (unname φ).Realize (Sum.elim p b) ↔
      @Formula.Realize _ _ (namedStructure (E := E) p) _ φ b := by
  letI := namedStructure (E := E) p
  letI : (constantsOn P).Structure Q := constantsOn.structure p
  letI := reassociate_expansion (E := E) p
  have h := @BoundedFormula.realize_constantsVarsEquiv (Auxiliary E) Q inferInstance
    P R inferInstance inferInstance 0 (reassociate.onBoundedFormula φ) b default
  have hp : (fun a : P => ((Auxiliary E).con a : Q)) = p := rfl
  rw [hp] at h
  simpa only [unname, Formula.Realize, LHom.realize_onBoundedFormula] using h

theorem formula_realize (j : Q → M) (hinj : Function.Injective j)
    (hfun : Compatible (E := E) j) (hrel : RelationsCompatible (E := E) j)
    (hguard : GuardCompatible (E := E) j)
    (p : P → Q) (b : R → Q) (v : B → M)
    (σ : P ⊕ R → (Expanded E).Term B)
    (hσ : ∀ q, (σ q).realize v = j (Sum.elim p b q))
    (φ : (Auxiliary (E.sum (constantsOn P))).Formula R) :
    (formula σ φ).Realize v ↔
      @Formula.Realize _ _ (namedStructure (E := E) p) _ φ b := by
  have h0 : j ∘ (default : Fin 0 → Q) = (default : Fin 0 → M) := by
    funext i
    exact i.elim0
  have h := GuardedLift.formula_realize j hinj hfun hrel hguard σ v
    (Sum.elim p b) hσ (unname φ) (default : Fin 0 → Q)
  rw [h0] at h
  exact h.trans (unname_realize p φ b)

end Semantics
end SpecialTransformations.Section6.AuxiliaryDenaming
