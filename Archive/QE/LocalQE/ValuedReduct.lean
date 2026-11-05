import MarkerBridge
import VFValued

set_option backward.isDefEq.respectTransparency false

/-! The actual valued-field reduct on the VF subtype, with a guarded syntactic
interpretation in LRV. This file proves the saturation transfer rather than
assuming saturation of an interpreted sort. -/

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace ValuedReduct

inductive VFn : ℕ → Type
  | zero : VFn 0
  | one : VFn 0
  | add : VFn 2
  | neg : VFn 1
  | mul : VFn 2
  deriving DecidableEq

inductive VRel : ℕ → Type
  | le : VRel 2
  deriving DecidableEq

/-- Ring language with the comparison `v(x) ≤ v(y)`, in Mathlib's multiplicative
valuation order. -/
@[reducible] def LVal : Language := ⟨VFn, VRel⟩

def fnMap : {k : ℕ} → VFn k → Fn k
  | _, .zero => .vfZero
  | _, .one => .vfOne
  | _, .add => .vfAdd
  | _, .neg => .vfNeg
  | _, .mul => .vfMul

@[instance_reducible] noncomputable def valStructure (M : Type)
    [LRV.Structure M] [M ⊨ Axioms.ACVF] : LVal.Structure (VFType (M := M)) where
  funMap f xs := match f with
    | .zero => 0
    | .one => 1
    | .add => xs 0 + xs 1
    | .neg => -xs 0
    | .mul => xs 0 * xs 1
  RelMap r xs := match r with
    | .le => VFValued.predV (xs 0) (xs 1)

noncomputable instance (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF] :
    LVal.Structure (VFType (M := M)) := valStructure M

private theorem binary_eta {X : Type} (xs : Fin 2 → X) : xs = ![xs 0, xs 1] := by
  funext i; fin_cases i <;> rfl
private theorem unary_eta {X : Type} (xs : Fin 1 → X) : xs = ![xs 0] := by
  funext i; fin_cases i; rfl
private theorem nullary_eta {X : Type} (xs : Fin 0 → X) : xs = fun i => i.elim0 := by
  funext i; exact i.elim0

def translateTerm {α : Type} : LVal.Term α → LRV.Term α
  | .var a => .var a
  | .func f ts => .func (fnMap f) (fun i => translateTerm (ts i))

def rvTerm {α : Type} (t : LRV.Term α) : LRV.Term α := .func Fn.rvMap ![t]

def vfGuard {α : Type} (n : ℕ) : LRV.BoundedFormula α (n + 1) :=
  .rel Rel.memVF ![.var (.inr (Fin.last n))]

/-- Every quantifier ranges over VF, although LRV itself has a single tagged
carrier. The order atom reverses its arguments, as prescribed by predV. -/
def translateFormula {α : Type} : {n : ℕ} → LVal.BoundedFormula α n → LRV.BoundedFormula α n
  | _, .falsum => .falsum
  | _, .equal a b => .equal (translateTerm a) (translateTerm b)
  | _, .rel .le ts => .rel Rel.rvLe ![rvTerm (translateTerm (ts 1)), rvTerm (translateTerm (ts 0))]
  | _, .imp φ ψ => .imp (translateFormula φ) (translateFormula ψ)
  | n, .all φ => .all ((vfGuard n).imp (translateFormula φ))

section Semantics

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem funMap_coe {k : ℕ} (f : VFn k) (xs : Fin k → VFType (M := M)) :
    (Structure.funMap (L := LVal) f xs).1 =
      Structure.funMap (L := LRV) (fnMap f) (fun i => (xs i).1) := by
  cases f with
  | zero => rw [nullary_eta (fun i => (xs i).1)]; rfl
  | one => rw [nullary_eta (fun i => (xs i).1)]; rfl
  | add => rw [binary_eta (fun i => (xs i).1)]; rfl
  | neg => rw [unary_eta (fun i => (xs i).1)]; rfl
  | mul => rw [binary_eta (fun i => (xs i).1)]; rfl

theorem realize_translateTerm {α : Type} (t : LVal.Term α) (v : α → VFType (M := M)) :
    (translateTerm t).realize (fun a => (v a).1) = (t.realize v).1 := by
  induction t with
  | var a => rfl
  | func f ts ih =>
      change Structure.funMap (L := LRV) (fnMap f)
        (fun i => (translateTerm (ts i)).realize (fun a => (v a).1)) =
          (Structure.funMap (L := LVal) f (fun i => (ts i).realize v)).1
      rw [funMap_coe]
      congr 1
      funext i
      exact ih i

theorem realize_rvTerm {α : Type} (t : LRV.Term α) (v : α → M) :
    (rvTerm t).realize v = iRv (t.realize v) := by
  change Structure.funMap (L := LRV) Fn.rvMap (fun i => (![t] i).realize v) = _
  rw [unary_eta (fun i : Fin 1 => (![t] i).realize v)]
  rfl

theorem realize_vfGuard {α : Type} {n : ℕ} (v : α → M) (xs : Fin n → M) (a : M) :
    (vfGuard (α := α) n).Realize v (Fin.snoc xs a) ↔ iVF a := by
  change Structure.RelMap (L := LRV) Rel.memVF
    (fun i => ((![Term.var (.inr (Fin.last n))] i : LRV.Term (α ⊕ Fin (n+1))).realize
      (Sum.elim v (Fin.snoc xs a)))) ↔ _
  rw [unary_eta (fun i : Fin 1 =>
    ((![Term.var (.inr (Fin.last n))] i : LRV.Term (α ⊕ Fin (n+1))).realize
      (Sum.elim v (Fin.snoc xs a))))]
  change iVF ((Fin.snoc xs a : Fin (n+1) → M) (Fin.last n)) ↔ iVF a
  rw [Fin.snoc_last]

theorem coe_sumElim {α β : Type} (v : α → VFType (M := M)) (xs : β → VFType (M := M)) :
    Sum.elim (fun a => (v a).1) (fun i => (xs i).1) =
      fun z => (Sum.elim v xs z).1 := by
  funext z; cases z <;> rfl

theorem coe_snoc {n : ℕ} (xs : Fin n → VFType (M := M)) (a : VFType (M := M)) :
    (fun i : Fin (n+1) => ((Fin.snoc xs a : Fin (n+1) → VFType (M := M)) i).1) =
      (Fin.snoc (fun i => (xs i).1) a.1 : Fin (n+1) → M) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
  · simp only [Fin.snoc_castSucc]

theorem realize_translateFormula {α : Type} :
    ∀ {n : ℕ} (φ : LVal.BoundedFormula α n)
      (v : α → VFType (M := M)) (xs : Fin n → VFType (M := M)),
      (translateFormula φ).Realize (fun a => (v a).1) (fun i => (xs i).1) ↔ φ.Realize v xs
  | _, .falsum, _, _ => Iff.rfl
  | _, .equal a b, v, xs => by
      change (translateTerm a).realize (Sum.elim (fun a => (v a).1) (fun i => (xs i).1)) =
        (translateTerm b).realize (Sum.elim (fun a => (v a).1) (fun i => (xs i).1)) ↔
          a.realize (Sum.elim v xs) = b.realize (Sum.elim v xs)
      rw [coe_sumElim, realize_translateTerm, realize_translateTerm]
      exact Subtype.ext_iff.symm
  | _, .rel .le ts, v, xs => by
      change Structure.RelMap (L := LRV) Rel.rvLe
        (fun i => (![rvTerm (translateTerm (ts 1)), rvTerm (translateTerm (ts 0))] i).realize
          (Sum.elim (fun a => (v a).1) (fun i => (xs i).1))) ↔
        VFValued.predV ((ts 0).realize (Sum.elim v xs)) ((ts 1).realize (Sum.elim v xs))
      rw [binary_eta (fun i : Fin 2 =>
        (![rvTerm (translateTerm (ts 1)), rvTerm (translateTerm (ts 0))] i).realize
          (Sum.elim (fun a => (v a).1) (fun i => (xs i).1)))]
      change iLe ((rvTerm (translateTerm (ts 1))).realize
        (Sum.elim (fun a => (v a).1) (fun i => (xs i).1)))
        ((rvTerm (translateTerm (ts 0))).realize
          (Sum.elim (fun a => (v a).1) (fun i => (xs i).1))) ↔ _
      rw [realize_rvTerm, realize_rvTerm, coe_sumElim,
        realize_translateTerm, realize_translateTerm]
      rfl
  | _, .imp φ ψ, v, xs => by
      change ((translateFormula φ).imp (translateFormula ψ)).Realize _ _ ↔ _
      rw [BoundedFormula.realize_imp, BoundedFormula.realize_imp,
        realize_translateFormula φ, realize_translateFormula ψ]
  | n, .all φ, v, xs => by
      change (BoundedFormula.all ((vfGuard n).imp (translateFormula φ))).Realize _ _ ↔ _
      rw [BoundedFormula.realize_all, BoundedFormula.realize_all]
      simp only [BoundedFormula.realize_imp, realize_vfGuard]
      constructor
      · intro h a
        apply (realize_translateFormula φ v (Fin.snoc xs a)).mp
        rw [coe_snoc]
        exact h a.1 a.2
      · intro h a ha
        have ht := (realize_translateFormula φ v (Fin.snoc xs ⟨a, ha⟩)).mpr (h ⟨a, ha⟩)
        rw [coe_snoc] at ht
        exact ht

theorem realize_translate {α : Type} (φ : LVal.Formula α) (v : α → VFType (M := M)) :
    Formula.Realize (translateFormula φ) (fun a => (v a).1) ↔ φ.Realize v := by
  simp only [Formula.Realize]
  have h := realize_translateFormula φ v (fun i => i.elim0)
  have hleft : (fun i : Fin 0 => (i.elim0 : VFType (M := M)).1) =
      (default : Fin 0 → M) := Subsingleton.elim _ _
  have hright : (fun i : Fin 0 => (i.elim0 : VFType (M := M))) =
      (default : Fin 0 → VFType (M := M)) := Subsingleton.elim _ _
  rw [hleft, hright] at h
  exact h

end Semantics

/-! A type in the valued reduct is translated and augmented by the condition
that its single realization lies in VF. Its parameter index set is unchanged. -/

def variableInVF (A : Type) : LRV.Formula (A ⊕ Unit) :=
  .rel Rel.memVF ![.var (.inl (.inr ()))]

theorem realize_variableInVF {M A : Type} [LRV.Structure M] (g : A → M) (b : M) :
    (variableInVF A).Realize (Sum.elim g (fun _ => b)) ↔ iVF b := by
  change Structure.RelMap (L := LRV) Rel.memVF
    (fun i => ((![Term.var (.inl (.inr ()))] i : LRV.Term ((A ⊕ Unit) ⊕ Fin 0)).realize
      (Sum.elim (Sum.elim g (fun _ => b)) (fun i => i.elim0)))) ↔ _
  rw [unary_eta (fun i : Fin 1 =>
    ((![Term.var (.inl (.inr ()))] i : LRV.Term ((A ⊕ Unit) ⊕ Fin 0)).realize
      (Sum.elim (Sum.elim g (fun _ => b)) (fun i => i.elim0))))]
  rfl

def translatedType {A : Type} (p : MarkerBridge.TypeOver LVal A) : MarkerBridge.TypeOver LRV A :=
  insert (variableInVF A) (translateFormula '' p)

section Saturation

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem translatedType_finSat {A : Type} (g : A → VFType (M := M))
    (p : MarkerBridge.TypeOver LVal A) (hp : MarkerBridge.FinSat g p) :
    MarkerBridge.FinSat (fun a => (g a).1) (translatedType p) := by
  classical
  intro q₀ hfinite hsub
  let choosePreimage : LRV.Formula (A ⊕ Unit) → LVal.Formula (A ⊕ Unit) :=
    fun ψ => if hψ : ψ ∈ translateFormula '' p then Classical.choose hψ else .falsum
  have hchoose (ψ : LRV.Formula (A ⊕ Unit)) (hψ : ψ ∈ translateFormula '' p) :
      choosePreimage ψ ∈ p ∧ translateFormula (choosePreimage ψ) = ψ := by
    simp only [choosePreimage, dif_pos hψ]
    exact Classical.choose_spec hψ
  let p₀ : MarkerBridge.TypeOver LVal A := choosePreimage '' (q₀ ∩ (translateFormula '' p))
  have hpfinite : p₀.Finite :=
    (hfinite.subset (Set.inter_subset_left)).image choosePreimage
  have hpsub : p₀ ⊆ p := by
    rintro φ ⟨ψ, ⟨_, hψ⟩, rfl⟩
    exact (hchoose ψ hψ).1
  obtain ⟨b, hb⟩ := hp p₀ hpfinite hpsub
  refine ⟨b.1, ?_⟩
  intro ψ hψ
  rcases (Set.mem_insert_iff.mp (hsub hψ)) with rfl | hψimage
  · exact (realize_variableInVF _ _).mpr b.2
  · have hpre : choosePreimage ψ ∈ p₀ := ⟨ψ, ⟨hψ, hψimage⟩, rfl⟩
    have ht := (realize_translate (choosePreimage ψ) (Sum.elim g (fun _ => b))).mpr (hb _ hpre)
    rw [(hchoose ψ hψimage).2] at ht
    rw [← coe_sumElim] at ht
    exact ht

/-- Genuine saturation of the tagged structure implies genuine saturation of
its valued-field reduct. No extension property or QE result is used. -/
theorem satAt_valuedReduct {κ : Cardinal} (hSat : MarkerBridge.SatAt LRV M κ) :
    MarkerBridge.SatAt LVal (VFType (M := M)) κ := by
  intro A g hA p hp
  obtain ⟨b, hb⟩ := hSat A (fun a => (g a).1) hA (translatedType p)
    (translatedType_finSat g p hp)
  have hbVF : iVF b := (realize_variableInVF _ _).mp (hb _ (Set.mem_insert _ _))
  refine ⟨⟨b, hbVF⟩, ?_⟩
  intro φ hφ
  have ht := hb (translateFormula φ) (Set.mem_insert_of_mem _ ⟨φ, hφ, rfl⟩)
  apply (realize_translate φ (Sum.elim g (fun _ => (⟨b, hbVF⟩ : VFType (M := M))))).mp
  rw [← coe_sumElim]
  exact ht

end Saturation
end ValuedReduct

#print axioms ValuedReduct.realize_translateTerm
#print axioms ValuedReduct.realize_translateFormula
#print axioms ValuedReduct.translatedType_finSat
#print axioms ValuedReduct.satAt_valuedReduct
