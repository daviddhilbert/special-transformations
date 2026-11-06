import Section6.TypedNativeTerms
import Section6.ExpandedLogic
import Mathlib.ModelTheory.Substructures

/-! Every RV parameter in the native term-generated base has a typed
native term in the original parameter context. This justifies denaming
the RV constants introduced after adjoining free VF parameters. The
proof uses Mathlib's actual substructure closure, not definable closure.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.GeneratedParameters
open RVTermSupport

variable {I C : Type} [LRV.Structure C] [hC : C ⊨ Axioms.ACVF]

theorem native_termSort (E : Language) (s : I → SortTag) (t : LRV.Term I) :
    termSort s ((LHom.sumInl : LRV →ᴸ Expanded E).onTerm t) =
      TmSort s (fun _ : Fin 0 => .rv) (t.relabel Sum.inl) := by
  induction t with
  | var i => rfl
  | func f ts ih =>
    change (if ∀ i, termSort s ((LHom.sumInl : LRV →ᴸ Expanded E).onTerm (ts i)) =
        some (Fn.argSort f i) then some (Fn.resSort f) else none) = _
    simp only [ih, Term.relabel, TmSort]

theorem rv_parameter_term (hcan : CanonicalStructure.IsCanonical (M := C))
    (s : I → SortTag) (v : I → C) (hv : ∀ i, sortEval (s i) (v i))
    (a : C) (ha : a ∈ Substructure.closure LRV (Set.range v)) (hRV : iRV a) :
    ∃ t : LRV.Term I,
      TmSort s (fun _ : Fin 0 => .rv) (t.relabel Sum.inl) = some .rv ∧ t.realize v = a := by
  obtain ⟨q, hq⟩ := Substructure.mem_closure_iff_exists_term.mp ha
  let pick : Set.range v → I := fun b => Classical.choose b.property
  have hp (b : Set.range v) : v (pick b) = b.val := Classical.choose_spec b.property
  let t := q.relabel pick
  have ht : t.realize v = a := by
    rw [Term.realize_relabel]
    have he : v ∘ pick = Subtype.val := funext hp
    exact he ▸ hq
  have hn := TypedNativeTerms.term_realize hcan s v hv t
  have hs := TypedNativeTerms.realized_sort s v hv t
  rw [hn, ht] at hs
  have htag : TypedNativeTerms.tag s t = .rv := CanonicalStructure.sort_unique hC hs hRV
  refine ⟨TypedNativeTerms.term s t, ?_, hn.trans ht⟩
  simpa only [htag] using TypedNativeTerms.term_sorted s t

theorem expanded_rv_parameter_term (E : Language)
    (hcan : CanonicalStructure.IsCanonical (M := C))
    (s : I → SortTag) (v : I → C) (hv : ∀ i, sortEval (s i) (v i))
    (a : C) (ha : a ∈ Substructure.closure LRV (Set.range v)) (hRV : iRV a) :
    ∃ t : LRV.Term I, termSort s ((LHom.sumInl : LRV →ᴸ Expanded E).onTerm t) = some .rv ∧
      t.realize v = a := by
  obtain ⟨t, hs, ht⟩ := rv_parameter_term hcan s v hv a ha hRV
  exact ⟨t, (native_termSort E s t).trans hs, ht⟩

end SpecialTransformations.Section6.GeneratedParameters
