import CanonicalQF

/-! Parameter-only adapters for the released native term normalization.
The normalization proof is reused from CanonicalQF; Section 6 only removes
the empty bound-variable context. No earlier term algebra is rederived.
-/

noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.TypedNativeTerms

variable {I : Type}

def collapse : I ⊕ Fin 0 → I := Sum.elim id Fin.elim0

def tag (s : I → SortTag) (t : LRV.Term I) : SortTag :=
  CanonicalStructure.resultSort s (fun _ : Fin 0 => .rv) (t.relabel Sum.inl)

def term (s : I → SortTag) (t : LRV.Term I) : LRV.Term I :=
  (CanonicalStructure.sortedTerm s (fun _ : Fin 0 => .rv) (t.relabel Sum.inl)).relabel collapse

theorem term_sorted (s : I → SortTag) (t : LRV.Term I) :
    TmSort s (fun _ : Fin 0 => .rv) ((term s t).relabel Sum.inl) = some (tag s t) := by
  have he : Sum.inl ∘ (collapse : I ⊕ Fin 0 → I) = id := by
    funext j
    cases j with
    | inl i => rfl
    | inr i => exact i.elim0
  simpa only [term, tag, Term.relabel_relabel, he, Term.relabel_id] using
    CanonicalStructure.sortedTerm_sort s (fun _ : Fin 0 => .rv) (t.relabel Sum.inl)

section Semantics
variable {C : Type} [LRV.Structure C] [hC : C ⊨ Axioms.ACVF]

theorem realized_sort (s : I → SortTag) (v : I → C) (hv : ∀ i, sortEval (s i) (v i))
    (t : LRV.Term I) : sortEval (tag s t) ((term s t).realize v) := by
  have h := CanonicalStructure.term_sort hC s (fun _ : Fin 0 => .rv)
    v default hv (fun i => i.elim0) ((term s t).relabel Sum.inl) (term_sorted s t)
  simpa only [Term.realize_relabel, Sum.elim_comp_inl] using h

theorem term_realize (hcan : CanonicalStructure.IsCanonical (M := C))
    (s : I → SortTag) (v : I → C) (hv : ∀ i, sortEval (s i) (v i)) (t : LRV.Term I) :
    (term s t).realize v = t.realize v := by
  have he : v ∘ (collapse : I ⊕ Fin 0 → I) = Sum.elim v (default : Fin 0 → C) := by
    funext j
    cases j with
    | inl i => rfl
    | inr i => exact i.elim0
  rw [term, Term.realize_relabel, he,
    CanonicalStructure.sortedTerm_realize hC hcan s (fun _ : Fin 0 => .rv)
      v default hv (fun i => i.elim0), Term.realize_relabel, Sum.elim_comp_inl]

end Semantics
end SpecialTransformations.Section6.TypedNativeTerms
