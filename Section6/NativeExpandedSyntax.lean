module

public import Section6.ExpandedLogic
public import CanonicalQF
public import QESaturatedExtension

@[expose] public section

/-! Reuse the released QF sorting normalization when comparing native
algebraic envelopes. This embeds only native QF formulas into the RV-only
expanded language; no earlier field/RV literal reduction is rederived.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.NativeExpandedSyntax
open RVTermSupport

variable {E : Language} {I : Type} {n : ℕ}

theorem term_sort (s : I → SortTag) (sn : Fin n → SortTag)
    (t : LRV.Term (I ⊕ Fin n)) :
    termSort (Sum.elim s sn) ((LHom.sumInl : LRV →ᴸ Expanded E).onTerm t) = TmSort s sn t := by
  induction t with
  | var j => cases j <;> rfl
  | func f ts ih =>
    change (if ∀ i, termSort (Sum.elim s sn)
      ((LHom.sumInl : LRV →ᴸ Expanded E).onTerm (ts i)) = some (Fn.argSort f i)
      then some (Fn.resSort f) else none) = _
    simp only [ih, TmSort]

theorem qf_isVFQF (φ : LRV.BoundedFormula I n) (hφ : φ.IsQF) :
    ExpandedLogic.IsVFQF ((LHom.sumInl : LRV →ᴸ Expanded E).onBoundedFormula φ) := by
  induction hφ with
  | falsum => exact .falsum
  | of_isAtomic h =>
    cases h with
    | equal t u => exact .atomic (.equal _ _)
    | rel r ts => exact .atomic (.rel _ _)
  | imp hφ hψ ihφ ihψ => exact .imp ihφ ihψ

theorem qf_wellSorted (s : I → SortTag) (sn : Fin n → SortTag)
    (φ : LRV.BoundedFormula I n) (hφ : φ.IsQF) (hs : LRV.WellSorted s sn φ) :
    ExpandedLogic.WellSorted s sn
      ((LHom.sumInl : LRV →ᴸ Expanded E).onBoundedFormula φ) := by
  induction hφ with
  | falsum => exact .falsum _
  | of_isAtomic h =>
    cases h with
    | equal t u =>
      cases hs with
      | equal _ ht hu => exact .equal ((term_sort s sn t).trans ht) ((term_sort s sn u).trans hu)
    | rel r ts =>
      cases hs with
      | rel _ r ts hts =>
        apply ExpandedLogic.WellSorted.rel
        intro i
        exact (term_sort s sn (ts i)).trans (hts i)
  | imp hφ hψ ihφ ihψ =>
    cases hs with
    | imp _ hsφ hsψ => exact .imp (ihφ hsφ) (ihψ hsψ)

theorem envelope_qf_type
    {M N U V : Type} [(Expanded E).Structure M] [(Expanded E).Structure N]
    [LRV.Structure M] [LRV.Structure N] [LRV.Structure U] [LRV.Structure V]
    [(LHom.sumInl : LRV →ᴸ Expanded E).IsExpansionOn M]
    [(LHom.sumInl : LRV →ᴸ Expanded E).IsExpansionOn N]
    (hU : U ⊨ Axioms.ACVF) (hV : V ⊨ Axioms.ACVF)
    (hcU : CanonicalStructure.IsCanonical (M := U))
    (hcV : CanonicalStructure.IsCanonical (M := V))
    (j : M ↪[LRV] U) (k : N ↪[LRV] V)
    (s : I → SortTag) (a : I → M) (b : I → N)
    (ha : ∀ i, sortEval (s i) (j (a i))) (hb : ∀ i, sortEval (s i) (k (b i)))
    (htype : ∀ ψ : (Expanded E).Formula I, ExpandedLogic.IsVFQF ψ →
      ExpandedLogic.WellSorted s (fun _ => .rv) ψ → (ψ.Realize a ↔ ψ.Realize b)) :
    ∀ φ : LRV.Formula I, φ.IsQF → (φ.Realize (j ∘ a) ↔ φ.Realize (k ∘ b)) := by
  intro φ hφ
  let θ := CanonicalStructure.sortedQF s (fun _ : Fin 0 => .rv) φ
  have hθ := CanonicalStructure.sortedQF_isQF s (fun _ : Fin 0 => .rv) φ
  have hsθ := CanonicalStructure.sortedQF_wellSorted s (fun _ : Fin 0 => .rv) φ
  have hsame := htype ((LHom.sumInl : LRV →ᴸ Expanded E).onBoundedFormula θ)
    (qf_isVFQF θ hθ) (qf_wellSorted s (fun _ => .rv) θ hθ hsθ)
  have hsame' : Formula.Realize θ a ↔ Formula.Realize θ b := by
    simpa only [Formula.Realize, LHom.realize_onBoundedFormula] using hsame
  have hUθ := CanonicalStructure.sortedQF_realize hU hcU s (fun _ : Fin 0 => .rv)
    (j ∘ a) default ha (fun i => i.elim0) φ hφ
  have hVθ := CanonicalStructure.sortedQF_realize hV hcV s (fun _ : Fin 0 => .rv)
    (k ∘ b) default hb (fun i => i.elim0) φ hφ
  exact hUθ.symm.trans ((QESaturatedExtension.embedding_realize_formula_isQF j hθ a).trans
    (hsame'.trans ((QESaturatedExtension.embedding_realize_formula_isQF k hθ b).symm.trans hVθ)))

end SpecialTransformations.Section6.NativeExpandedSyntax
