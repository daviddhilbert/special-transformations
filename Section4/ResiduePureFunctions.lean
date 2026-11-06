import Mathlib.ModelTheory.Algebra.Field.Basic
import Mathlib.ModelTheory.Definability
import Mathlib.Tactic.FinCases

open Classical FirstOrder FirstOrder.Language

noncomputable section

namespace SpecialTransformations.Section4.ResiduePurity

variable {K : Type} [Field K]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

abbrev PureDef {ι : Type} (A : Set (ι → K)) : Prop :=
  (Set.univ : Set K).Definable Language.ring A

abbrev PureFun {ι : Type} (f : (ι → K) → K) : Prop :=
  (Set.univ : Set K).DefinableFun Language.ring f

variable {ι : Type} {f g : (ι → K) → K}

theorem pure_const (c : K) : PureFun (fun _ : ι → K => c) :=
  Language.definableFun_const Language.ring ι (Set.mem_univ c)

theorem pure_proj (i : ι) : PureFun (fun x : ι → K => x i) :=
  Set.DefinableFun.proj Language.ring

theorem PureFun.add (hf : PureFun f) (hg : PureFun g) : PureFun (fun x => f x + g x) := by
  have h := (Set.DefinableFun.of_empty
    (Set.DefinableFun.fun_symbol (M := K) (L := Language.ring) ringFunc.add)).comp
      (show (Set.univ : Set K).DefinableMap Language.ring (fun x : ι → K => ![f x, g x]) from
        fun i => by fin_cases i; exact hf; exact hg)
  simpa only [FirstOrder.Ring.CompatibleRing.funMap_add,
    Matrix.cons_val_zero, Matrix.cons_val_one] using h

theorem PureFun.mul (hf : PureFun f) (hg : PureFun g) : PureFun (fun x => f x * g x) := by
  have h := (Set.DefinableFun.of_empty
    (Set.DefinableFun.fun_symbol (M := K) (L := Language.ring) ringFunc.mul)).comp
      (show (Set.univ : Set K).DefinableMap Language.ring (fun x : ι → K => ![f x, g x]) from
        fun i => by fin_cases i; exact hf; exact hg)
  simpa only [FirstOrder.Ring.CompatibleRing.funMap_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one] using h

theorem PureFun.neg (hf : PureFun f) : PureFun (fun x => -f x) := by
  have h := (Set.DefinableFun.of_empty
    (Set.DefinableFun.fun_symbol (M := K) (L := Language.ring) ringFunc.neg)).comp
      (show (Set.univ : Set K).DefinableMap Language.ring (fun x : ι → K => ![f x]) from
        fun i => by fin_cases i; exact hf)
  simpa only [FirstOrder.Ring.CompatibleRing.funMap_neg, Matrix.cons_val_zero] using h

theorem PureFun.eq (hf : PureFun f) (hg : PureFun g) : PureDef {x | f x = g x} :=
  hf.ofPred_eq hg

theorem PureFun.eq_const (hf : PureFun f) (c : K) : PureDef {x | f x = c} :=
  hf.ofPred_eq (pure_const c)

/-- Inversion is definable in the pure ring language, including zero.
No inverse symbol is added to that language. -/
theorem pure_inv : PureFun (fun x : Fin 1 → K => (x 0)⁻¹) := by
  have hx : PureFun (fun z : Option (Fin 1) → K => z (some 0)) := pure_proj _
  have hy : PureFun (fun z : Option (Fin 1) → K => z none) := pure_proj _
  have h := ((hx.mul hy).eq_const 1).union ((hx.eq_const 0).inter (hy.eq_const 0))
  change PureDef _
  convert h using 1
  ext z
  change (z (some 0))⁻¹ = z none ↔
    z (some 0) * z none = 1 ∨ z (some 0) = 0 ∧ z none = 0
  by_cases hz : z (some 0) = 0
  · simp [hz, eq_comm]
  · constructor
    · intro he
      exact Or.inl (by rw [← he, mul_inv_cancel₀ hz])
    · intro he
      rcases he with he | he
      · exact (mul_left_cancel₀ hz
          (he.trans (mul_inv_cancel₀ hz).symm)).symm
      · exact (hz he.1).elim

theorem PureFun.inv (hf : PureFun f) : PureFun (fun x => (f x)⁻¹) := by
  exact pure_inv.comp
    (show (Set.univ : Set K).DefinableMap Language.ring (fun x : ι → K => ![f x]) from
      fun i => by fin_cases i; exact hf)

theorem PureFun.ite {p : (ι → K) → Prop} [DecidablePred p]
    (hp : PureDef {x | p x}) (hf : PureFun f) (hg : PureFun g) :
    PureFun (fun x => if p x then f x else g x) := Set.DefinableFun.ite hp hf hg

theorem pure_proposition (p : Prop) : PureDef {x : ι → K | p} := by
  by_cases hp : p
  · simpa only [hp, Set.ofPred_true] using
      (Set.definable_univ : (Set.univ : Set K).Definable Language.ring (Set.univ : Set (ι → K)))
  · simpa only [hp, Set.ofPred_false] using
      (Set.definable_empty : (Set.univ : Set K).Definable Language.ring (∅ : Set (ι → K)))

end SpecialTransformations.Section4.ResiduePurity

end
