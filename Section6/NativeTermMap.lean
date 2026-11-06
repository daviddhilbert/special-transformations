import Section6.NativeTerms
import Section6.ContractionGraph

/-! Prepare the finite native RV-leaf map directly. Original FV parameters
are retained in S; native FV syntax is not converted to a second copy of
polynomial algebra. Full graph definability uses the given Map.ofCodes.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section5

namespace SpecialTransformations.Section6.NativeTermMap

variable {C : Type} [sC : LRV.Structure C] [hC : C ⊨ Axioms.ACVF]
variable {S : Set C} {r n k : ℕ}

def tokenTerm {V : Type} (q : LRV.Term V) : LRV.Term V := .func Fn.rvMap ![q]

def VFSorted {V : Type} (q : LRV.Term V) : Prop :=
  TmSort (fun _ => .vf) (fun _ : Fin 0 => .vf) (q.relabel Sum.inl) = some .vf

theorem tokenTerm_sorted {V : Type} (q : LRV.Term V) (hq : VFSorted q) :
    TmSort (fun _ => .vf) (fun _ : Fin 0 => .vf)
      ((tokenTerm q).relabel Sum.inl) = some .rv := by
  apply tmSort_func
  intro i
  fin_cases i
  exact hq

def vfValue (c : Fin r → VF (M := C)) (q : LRV.Term (Fin r ⊕ Fin n))
    (hq : VFSorted q) (x : Fin n → VF (M := C)) : VF (M := C) :=
  ⟨q.realize (Sum.elim (fun i => (c i).val) (fun i => (x i).val)), by
    have hh := CanonicalStructure.term_sort hC (fun _ : Fin r ⊕ Fin n => .vf)
      (fun _ : Fin 0 => .vf)
      (Sum.elim (fun i => (c i).val) (fun i => (x i).val))
      (default : Fin 0 → C) (Sum.rec (fun i => (c i).property) (fun i => (x i).property))
      (fun i => i.elim0) (q.relabel Sum.inl) hq
    simpa only [Term.realize_relabel, Sum.elim_comp_inl, sortEval, iVF] using hh⟩

def code (c : Fin r → VF (M := C)) (q : LRV.Term (Fin r ⊕ Fin n))
    (z : Fin n ⊕ Fin 0 → C) : C :=
  @Term.realize LRV C (CanonicalStructure.normalize (M := C)) _
    (Sum.elim (fun i => (c i).val) (fun i => z (.inl i))) (tokenTerm q)

theorem code_eq (c : Fin r → VF (M := C)) (q : LRV.Term (Fin r ⊕ Fin n))
    (hq : VFSorted q) (z : Fin n ⊕ Fin 0 → C) (x : Fin n → VF (M := C))
    (hx : ∀ i, z (.inl i) = (x i).val) :
    code c q z = (rv (vfValue c q hq x)).val := by
  unfold code
  simp_rw [hx]
  have hn := CanonicalStructure.term_normalize hC (fun _ : Fin r ⊕ Fin n => .vf)
    (fun _ : Fin 0 => .vf)
    (Sum.elim (fun i => (c i).val) (fun i => (x i).val)) (default : Fin 0 → C)
    (Sum.rec (fun i => (c i).property) (fun i => (x i).property))
    (fun i => i.elim0) ((tokenTerm q).relabel Sum.inl) (tokenTerm_sorted q hq)
  simp only [Term.realize_relabel, Sum.elim_comp_inl] at hn
  rw [hn]
  change Structure.funMap (L := LRV) Fn.rvMap
      (fun i => ((![q] : Fin 1 → LRV.Term (Fin r ⊕ Fin n)) i).realize _) = _
  have he : (fun i => ((![q] : Fin 1 → LRV.Term (Fin r ⊕ Fin n)) i).realize
      (Sum.elim (fun i => (c i).val) (fun i => (x i).val))) =
      ![q.realize (Sum.elim (fun i => (c i).val) (fun i => (x i).val))] := by
    funext i
    fin_cases i
    rfl
  rw [he]
  rfl

theorem code_definable (c : Fin r → VF (M := C)) (hc : ∀ i, (c i).val ∈ S)
    (q : LRV.Term (Fin r ⊕ Fin n)) : RawFun S (Fin n ⊕ Fin 0) (code c q) := by
  let N := @CanonicalStructure.normalize C sC
  letI := N
  have ht : (∅ : Set C).DefinableFun LRV
      (fun z => @Term.realize LRV C N _ z (tokenTerm q)) :=
    (tokenTerm q).definableFun_realize (M := C)
  have hg : ∀ i : Fin r ⊕ Fin n, @Set.DefinableFun C LRV N (Fin n ⊕ Fin 0) S
      (fun z => Sum.elim (fun j => (c j).val) (fun j => z (.inl j)) i) := by
    intro i
    cases i with
    | inl i => exact LRV.definableFun_const _ (hc i)
    | inr i => exact Set.DefinableFun.proj LRV
  exact @Set.DefinableFun.comp C LRV N (Fin r ⊕ Fin n) (Fin n ⊕ Fin 0) S _
    inferInstance _ hg ht.of_empty

def tupleMap (A : DefSet (M := C) S n 0) (c : Fin r → VF (M := C))
    (hc : ∀ i, (c i).val ∈ S) (qs : Fin k → LRV.Term (Fin r ⊕ Fin n))
    (hs : ∀ i, VFSorted (qs i)) :
    Map A (PresentedSet.univ (pointSpace (M := C) 0 k) S) :=
  Map.ofCodes A (fun a => (Fin.elim0, fun i => rv (vfValue c (qs i) (hs i) (vfAt a))))
    (fun z => Sum.elim Fin.elim0 (fun i => code c (qs i) z))
    (by
      intro i
      cases i with
      | inl i => exact i.elim0
      | inr i => exact code_definable c hc (qs i))
    (by
      intro z
      refine ⟨fun i => i.elim0, ?_⟩
      intro i
      change iRV (code c (qs i) z.val)
      rw [code_eq c (qs i) (hs i) z.val (vfAt (pDecode (pointSpace n 0) z)) (fun _ => rfl)]
      exact (rv (vfValue c (qs i) (hs i) (vfAt (pDecode (pointSpace n 0) z)))).property)
    (by
      intro z
      refine Prod.ext (Subsingleton.elim _ _) ?_
      funext i
      apply Subtype.ext
      exact code_eq c (qs i) (hs i) z.val (vfAt (pDecode (pointSpace n 0) z)) (fun _ => rfl))

theorem tupleMap_values (A : DefSet (M := C) S n 0) (c : Fin r → VF (M := C))
    (hc : ∀ i, (c i).val ∈ S) (qs : Fin k → LRV.Term (Fin r ⊕ Fin n))
    (hs : ∀ i, VFSorted (qs i)) (a : A) :
    (tupleMap A c hc qs hs a).val.2 = fun i => rv (vfValue c (qs i) (hs i) (vfAt a.val)) := rfl

end SpecialTransformations.Section6.NativeTermMap
