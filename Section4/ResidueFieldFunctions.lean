import Section4.ResiduePureFunctions
import Mathlib.Algebra.Field.Subfield.Basic

open Classical FirstOrder FirstOrder.Language

noncomputable section

namespace SpecialTransformations.Section4.ResiduePurity.Relative

variable {K : Type} [Field K]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

abbrev Def {ι : Type} (E : Subfield K) (A : Set (ι → K)) : Prop :=
  (E : Set K).Definable Language.ring A

abbrev Fun {ι : Type} (E : Subfield K) (f : (ι → K) → K) : Prop :=
  (E : Set K).DefinableFun Language.ring f

variable {ι : Type} {E : Subfield K} {f g : (ι → K) → K}

theorem constant (c : K) (hc : c ∈ E) : Fun E (fun _ : ι → K => c) :=
  Language.definableFun_const Language.ring ι hc

theorem projection (i : ι) : Fun E (fun x : ι → K => x i) :=
  Set.DefinableFun.proj Language.ring

theorem Fun.add (hf : Fun E f) (hg : Fun E g) : Fun E (fun x => f x + g x) := by
  have h := (Set.DefinableFun.of_empty
    (Set.DefinableFun.fun_symbol (M := K) (L := Language.ring) ringFunc.add)).comp
      (show (E : Set K).DefinableMap Language.ring (fun x : ι → K => ![f x, g x]) from
        fun i => by fin_cases i; exact hf; exact hg)
  simpa only [FirstOrder.Ring.CompatibleRing.funMap_add,
    Matrix.cons_val_zero, Matrix.cons_val_one] using h

theorem Fun.mul (hf : Fun E f) (hg : Fun E g) : Fun E (fun x => f x * g x) := by
  have h := (Set.DefinableFun.of_empty
    (Set.DefinableFun.fun_symbol (M := K) (L := Language.ring) ringFunc.mul)).comp
      (show (E : Set K).DefinableMap Language.ring (fun x : ι → K => ![f x, g x]) from
        fun i => by fin_cases i; exact hf; exact hg)
  simpa only [FirstOrder.Ring.CompatibleRing.funMap_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one] using h

theorem Fun.neg (hf : Fun E f) : Fun E (fun x => -f x) := by
  have h := (Set.DefinableFun.of_empty
    (Set.DefinableFun.fun_symbol (M := K) (L := Language.ring) ringFunc.neg)).comp
      (show (E : Set K).DefinableMap Language.ring (fun x : ι → K => ![f x]) from
        fun i => by fin_cases i; exact hf)
  simpa only [FirstOrder.Ring.CompatibleRing.funMap_neg, Matrix.cons_val_zero] using h

theorem Fun.eq (hf : Fun E f) (hg : Fun E g) : Def E {x | f x = g x} := hf.ofPred_eq hg

theorem Fun.eq_const (hf : Fun E f) (c : K) (hc : c ∈ E) : Def E {x | f x = c} :=
  hf.ofPred_eq (constant c hc)

theorem inverse (E : Subfield K) : Fun E (fun x : Fin 1 → K => (x 0)⁻¹) := by
  have hx : Fun E (fun z : Option (Fin 1) → K => z (some 0)) := projection _
  have hy : Fun E (fun z : Option (Fin 1) → K => z none) := projection _
  have h := ((hx.mul hy).eq_const 1 E.one_mem).union
    ((hx.eq_const 0 E.zero_mem).inter (hy.eq_const 0 E.zero_mem))
  change Def E _
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
      · exact (mul_left_cancel₀ hz (he.trans (mul_inv_cancel₀ hz).symm)).symm
      · exact (hz he.1).elim

theorem Fun.inv (hf : Fun E f) : Fun E (fun x => (f x)⁻¹) := by
  exact (inverse E).comp
    (show (E : Set K).DefinableMap Language.ring (fun x : ι → K => ![f x]) from
      fun i => by fin_cases i; exact hf)

theorem Fun.ite {p : (ι → K) → Prop} [DecidablePred p]
    (hp : Def E {x | p x}) (hf : Fun E f) (hg : Fun E g) :
    Fun E (fun x => if p x then f x else g x) := Set.DefinableFun.ite hp hf hg

theorem proposition (E : Subfield K) (p : Prop) : Def E {x : ι → K | p} := by
  by_cases hp : p
  · simpa only [hp, Set.ofPred_true] using
      (Set.definable_univ : (E : Set K).Definable Language.ring (Set.univ : Set (ι → K)))
  · simpa only [hp, Set.ofPred_false] using
      (Set.definable_empty : (E : Set K).Definable Language.ring (∅ : Set (ι → K)))

end SpecialTransformations.Section4.ResiduePurity.Relative

end
