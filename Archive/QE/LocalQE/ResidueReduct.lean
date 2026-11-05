import CanonicalResidueOperations
import MarkerBridge
import Mathlib.ModelTheory.Algebra.Ring.Basic

set_option backward.isDefEq.respectTransparency false

/-! Guarded interpretation of the actual residue field in the tagged model.
The source language is Mathlib's standard ring language. The translation proves
saturation transfer directly from finitely satisfiable one-variable types. -/

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open CanonicalResidue ResidueTranscendentalTransport

namespace ResidueReduct

def fnMap : {k : ℕ} → ringFunc k → Fn k
  | _, .zero => .rvZero
  | _, .one => .rvOne
  | _, .add => .kAdd
  | _, .neg => .kNeg
  | _, .mul => .rvMul

def translateTerm {α : Type} : Language.ring.Term α → LRV.Term α
  | .var a => .var a
  | .func f ts => .func (fnMap f) (fun i => translateTerm (ts i))

def inKFormula {α : Type} {n : ℕ} (t : LRV.Term (α ⊕ Fin n)) :
    LRV.BoundedFormula α n :=
  (BoundedFormula.rel Rel.memUnits ![t]) ⊔
    (BoundedFormula.equal t (.func Fn.rvZero (fun i => i.elim0)))

def residueGuard {α : Type} (n : ℕ) : LRV.BoundedFormula α (n + 1) :=
  inKFormula (.var (.inr (Fin.last n)))

def translateFormula {α : Type} : {n : ℕ} →
    Language.ring.BoundedFormula α n → LRV.BoundedFormula α n
  | _, .falsum => .falsum
  | _, .equal a b => .equal (translateTerm a) (translateTerm b)
  | _, .rel r _ => r.elim
  | _, .imp φ ψ => .imp (translateFormula φ) (translateFormula ψ)
  | n, .all φ => .all ((residueGuard n).imp (translateFormula φ))

private theorem binary_eta {X : Type} (xs : Fin 2 → X) : xs = ![xs 0, xs 1] := by
  funext i; fin_cases i <;> rfl
private theorem unary_eta {X : Type} (xs : Fin 1 → X) : xs = ![xs 0] := by
  funext i; fin_cases i; rfl
private theorem nullary_eta {X : Type} (xs : Fin 0 → X) : xs = fun i => i.elim0 := by
  funext i; exact i.elim0

theorem realize_inKFormula {M α : Type} [LRV.Structure M] {n : ℕ}
    (t : LRV.Term (α ⊕ Fin n)) (g : α → M) (xs : Fin n → M) :
    (inKFormula t).Realize g xs ↔
      iUnits (t.realize (Sum.elim g xs)) ∨ t.realize (Sum.elim g xs) = iRVZero := by
  rw [inKFormula, BoundedFormula.realize_sup]
  change (Structure.RelMap (L := LRV) Rel.memUnits
    (fun i => (![t] i).realize (Sum.elim g xs)) ∨
    t.realize (Sum.elim g xs) = Structure.funMap (L := LRV) Fn.rvZero
      (fun i : Fin 0 => (i.elim0 : LRV.Term (α ⊕ Fin n)).realize (Sum.elim g xs))) ↔ _
  rw [unary_eta (fun i : Fin 1 => (![t] i).realize (Sum.elim g xs)),
    nullary_eta (fun i : Fin 0 =>
      (i.elim0 : LRV.Term (α ⊕ Fin n)).realize (Sum.elim g xs))]
  rfl

theorem realize_residueGuard {M α : Type} [LRV.Structure M] {n : ℕ}
    (g : α → M) (xs : Fin n → M) (a : M) :
    (residueGuard (α := α) n).Realize g (Fin.snoc xs a) ↔
      iUnits a ∨ a = iRVZero := by
  rw [residueGuard, realize_inKFormula]
  simp only [Term.realize_var, Sum.elim_inr, Fin.snoc_last]

section Semantics

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation (VFType (M := M)) Γ)
  (hv : ∀ a b : VFType (M := M), VFValued.predV a b ↔ v a ≤ v b)
variable [FirstOrder.Ring.CompatibleRing (Residue v)]

theorem funMap_encode {k : ℕ} (f : ringFunc k) (xs : Fin k → Residue v) :
    encodeResidue v hv (Structure.funMap (L := Language.ring) f xs) =
      Structure.funMap (L := LRV) (fnMap f) (fun i => encodeResidue v hv (xs i)) := by
  cases f with
  | zero =>
      rw [FirstOrder.Ring.CompatibleRing.funMap_zero,
        nullary_eta (fun i => encodeResidue v hv (xs i))]
      exact encodeResidue_zero v hv
  | one =>
      rw [FirstOrder.Ring.CompatibleRing.funMap_one,
        nullary_eta (fun i => encodeResidue v hv (xs i))]
      exact encodeResidue_one v hv
  | add =>
      rw [FirstOrder.Ring.CompatibleRing.funMap_add,
        binary_eta (fun i => encodeResidue v hv (xs i))]
      exact encodeResidue_add v hv (xs 0) (xs 1)
  | mul =>
      rw [FirstOrder.Ring.CompatibleRing.funMap_mul,
        binary_eta (fun i => encodeResidue v hv (xs i))]
      exact encodeResidue_mul v hv (xs 0) (xs 1)
  | neg =>
      rw [FirstOrder.Ring.CompatibleRing.funMap_neg,
        unary_eta (fun i => encodeResidue v hv (xs i))]
      exact encodeResidue_neg v hv (xs 0)

theorem realize_translateTerm {α : Type} (t : Language.ring.Term α) (g : α → Residue v) :
    (translateTerm t).realize (fun a => encodeResidue v hv (g a)) =
      encodeResidue v hv (t.realize g) := by
  induction t with
  | var a => rfl
  | func f ts ih =>
      change Structure.funMap (L := LRV) (fnMap f)
        (fun i => (translateTerm (ts i)).realize (fun a => encodeResidue v hv (g a))) =
          encodeResidue v hv (Structure.funMap (L := Language.ring) f
            (fun i => (ts i).realize g))
      rw [funMap_encode]
      congr 1
      funext i
      exact ih i

theorem encode_sumElim {α β : Type} (g : α → Residue v) (xs : β → Residue v) :
    Sum.elim (fun a => encodeResidue v hv (g a)) (fun i => encodeResidue v hv (xs i)) =
      fun z => encodeResidue v hv (Sum.elim g xs z) := by
  funext z; cases z <;> rfl

theorem encode_snoc {n : ℕ} (xs : Fin n → Residue v) (a : Residue v) :
    (fun i : Fin (n+1) => encodeResidue v hv ((Fin.snoc xs a : Fin (n+1) → Residue v) i)) =
      (Fin.snoc (fun i => encodeResidue v hv (xs i)) (encodeResidue v hv a) : Fin (n+1) → M) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
  · simp only [Fin.snoc_castSucc]

theorem realize_translateFormula {α : Type} :
    ∀ {n : ℕ} (φ : Language.ring.BoundedFormula α n)
      (g : α → Residue v) (xs : Fin n → Residue v),
      (translateFormula φ).Realize (fun a => encodeResidue v hv (g a))
        (fun i => encodeResidue v hv (xs i)) ↔ φ.Realize g xs
  | _, .falsum, _, _ => Iff.rfl
  | _, .equal a b, g, xs => by
      change (translateTerm a).realize (Sum.elim _ _) =
        (translateTerm b).realize (Sum.elim _ _) ↔
          a.realize (Sum.elim g xs) = b.realize (Sum.elim g xs)
      rw [encode_sumElim, realize_translateTerm, realize_translateTerm]
      exact (encodeResidue_injective v hv).eq_iff
  | _, .rel r _, _, _ => r.elim
  | _, .imp φ ψ, g, xs => by
      change ((translateFormula φ).imp (translateFormula ψ)).Realize _ _ ↔ _
      rw [BoundedFormula.realize_imp, BoundedFormula.realize_imp,
        realize_translateFormula φ, realize_translateFormula ψ]
  | n, .all φ, g, xs => by
      change (BoundedFormula.all ((residueGuard n).imp (translateFormula φ))).Realize _ _ ↔ _
      rw [BoundedFormula.realize_all, BoundedFormula.realize_all]
      simp only [BoundedFormula.realize_imp, realize_residueGuard]
      constructor
      · intro h a
        apply (realize_translateFormula φ g (Fin.snoc xs a)).mp
        rw [encode_snoc]
        exact h (encodeResidue v hv a) (encodeResidue_inK v hv a)
      · intro h a ha
        obtain ⟨b, rfl⟩ := encodeResidue_surjective_inK v hv a ha
        have ht := (realize_translateFormula φ g (Fin.snoc xs b)).mpr (h b)
        rw [encode_snoc] at ht
        exact ht

theorem realize_translate {α : Type} (φ : Language.ring.Formula α) (g : α → Residue v) :
    Formula.Realize (translateFormula φ) (fun a => encodeResidue v hv (g a)) ↔ φ.Realize g := by
  simp only [Formula.Realize]
  have h := realize_translateFormula v hv φ g (fun i => i.elim0)
  have hl : (fun i : Fin 0 => encodeResidue v hv (i.elim0 : Residue v)) =
      (default : Fin 0 → M) := Subsingleton.elim _ _
  have hr : (fun i : Fin 0 => (i.elim0 : Residue v)) =
      (default : Fin 0 → Residue v) := Subsingleton.elim _ _
  rw [hl, hr] at h
  convert h using 2 <;> congr 1 <;> exact Subsingleton.elim _ _

end Semantics

def variableInK (A : Type) : LRV.Formula (A ⊕ Unit) :=
  inKFormula (.var (.inl (.inr ())))

theorem realize_variableInK {M A : Type} [LRV.Structure M] (g : A → M) (b : M) :
    (variableInK A).Realize (Sum.elim g (fun _ => b)) ↔ iUnits b ∨ b = iRVZero := by
  simp only [variableInK, Formula.Realize, realize_inKFormula, Term.realize_var, Sum.elim_inl,
    Sum.elim_inr]

def translatedType {A : Type} (p : MarkerBridge.TypeOver Language.ring A) :
    MarkerBridge.TypeOver LRV A := insert (variableInK A) (translateFormula '' p)

section Saturation

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation (VFType (M := M)) Γ)
  (hv : ∀ a b : VFType (M := M), VFValued.predV a b ↔ v a ≤ v b)
variable [FirstOrder.Ring.CompatibleRing (Residue v)]

include hv

theorem translatedType_finSat {A : Type} (g : A → Residue v)
    (p : MarkerBridge.TypeOver Language.ring A) (hp : MarkerBridge.FinSat g p) :
    MarkerBridge.FinSat (fun a => encodeResidue v hv (g a)) (translatedType p) := by
  intro q₀ hfinite hsub
  let choosePreimage : LRV.Formula (A ⊕ Unit) → Language.ring.Formula (A ⊕ Unit) :=
    fun ψ => if hψ : ψ ∈ translateFormula '' p then Classical.choose hψ else .falsum
  have hchoose (ψ : LRV.Formula (A ⊕ Unit)) (hψ : ψ ∈ translateFormula '' p) :
      choosePreimage ψ ∈ p ∧ translateFormula (choosePreimage ψ) = ψ := by
    simp only [choosePreimage, dif_pos hψ]
    exact Classical.choose_spec hψ
  let p₀ : MarkerBridge.TypeOver Language.ring A := choosePreimage '' (q₀ ∩ (translateFormula '' p))
  have hpfinite : p₀.Finite :=
    (hfinite.subset (Set.inter_subset_left)).image choosePreimage
  have hpsub : p₀ ⊆ p := by
    rintro φ ⟨ψ, ⟨_, hψ⟩, rfl⟩
    exact (hchoose ψ hψ).1
  obtain ⟨b, hb⟩ := hp p₀ hpfinite hpsub
  refine ⟨encodeResidue v hv b, ?_⟩
  intro ψ hψ
  rcases (Set.mem_insert_iff.mp (hsub hψ)) with rfl | hψimage
  · exact (realize_variableInK _ _).mpr (encodeResidue_inK v hv b)
  · have hpre : choosePreimage ψ ∈ p₀ := ⟨ψ, ⟨hψ, hψimage⟩, rfl⟩
    have ht := (realize_translate v hv (choosePreimage ψ) (Sum.elim g (fun _ => b))).mpr
      (hb _ hpre)
    rw [(hchoose ψ hψimage).2] at ht
    rw [← encode_sumElim] at ht
    exact ht

/-- Actual saturation of the tagged model transfers to its actual residue field
in Mathlib's ring language; this uses no QE or model-extension hypothesis. -/
theorem satAt_residue {κ : Cardinal} (hSat : MarkerBridge.SatAt LRV M κ) :
    MarkerBridge.SatAt Language.ring (Residue v) κ := by
  intro A g hA p hp
  obtain ⟨b, hb⟩ := hSat A (fun a => encodeResidue v hv (g a)) hA (translatedType p)
    (translatedType_finSat v hv g p hp)
  have hbK : iUnits b ∨ b = iRVZero :=
    (realize_variableInK _ _).mp (hb _ (Set.mem_insert _ _))
  obtain ⟨c, hc⟩ := encodeResidue_surjective_inK v hv b hbK
  refine ⟨c, ?_⟩
  intro φ hφ
  have ht := hb (translateFormula φ) (Set.mem_insert_of_mem _ ⟨φ, hφ, rfl⟩)
  apply (realize_translate v hv φ (Sum.elim g (fun _ => c))).mp
  rw [← encode_sumElim, hc]
  exact ht

end Saturation
end ResidueReduct

#print axioms ResidueReduct.realize_translateTerm
#print axioms ResidueReduct.realize_translateFormula
#print axioms ResidueReduct.translatedType_finSat
#print axioms ResidueReduct.satAt_residue
