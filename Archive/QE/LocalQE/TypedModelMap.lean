import SortedEmbeddings
import VFValued

set_option backward.isDefEq.respectTransparency false

/-! Assemble a typed map from separate VF and RV maps.

The VF component is a field homomorphism. The RV component is an injective
map preserving the named operations and reflecting the named relations.
Compatibility with `rv` is explicit. Preservation of the named RV inverse
follows from multiplicativity, injectivity, and preservation of zero and one.
-/

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.VFValued
open scoped FirstOrder

namespace TypedModelMap

abbrev RVSubtype (M : Type) [LRV.Structure M] := {x : M // iRV x}

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem sort_cover (x : M) : iVF x ∨ iRV x := by
  have h := Transfer.allOne_realize hM
    (φ := pVF &0 ⊔ pRVsort &0)
    (by simp [Axioms.ACVF, Axioms.sortAxioms, Axioms.ofList, Axioms.sdCover]) ![x]
  simpa only [BoundedFormula.realize_sup, Transfer.pVF_realize,
    Transfer.pRVsort_realize, Transfer.realize_tv, Function.comp_apply,
    Term.realize_var, Sum.elim_inr, Matrix.cons_val_zero] using h

theorem not_vf_of_rv {x : M} (hx : iRV x) : ¬ iVF x := by
  intro hv
  have h : SortTag.vf = SortTag.rv := CanonicalStructure.sort_unique hM hv hx
  cases h

theorem not_rv_of_vf {x : M} (hx : iVF x) : ¬ iRV x := by
  intro hr
  exact not_vf_of_rv hr hx

variable (M N : Type) [LRV.Structure M] [LRV.Structure N]
  [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- Concrete algebraic data needed to map the two sorts. The RV equations are
equations in the carrier, avoiding an arbitrary choice of RV algebra instances. -/
structure Components where
  vf : Transfer.VFType (M := M) →+* Transfer.VFType (M := N)
  rv : RVSubtype M ↪ RVSubtype N
  rv_zero : (rv ⟨iRVZero, Transfer.rv_zero_mem hM⟩).1 = iRVZero
  rv_one : (rv ⟨iRVOne, Transfer.rv_one_mem hM⟩).1 = iRVOne
  rv_mul : ∀ x y : RVSubtype M,
    (rv ⟨iRVMul x.1 y.1, Transfer.rv_mul_mem hM x.2 y.2⟩).1 =
      iRVMul (rv x).1 (rv y).1
  k_add : ∀ x y : RVSubtype M,
    (rv ⟨iKAdd x.1 y.1, CanonicalStructure.kAdd_mem hM x.2 y.2⟩).1 =
      iKAdd (rv x).1 (rv y).1
  k_neg : ∀ x : RVSubtype M,
    (rv ⟨TrivCase.iKNeg x.1, CanonicalStructure.kNeg_mem hM x.2⟩).1 =
      TrivCase.iKNeg (rv x).1
  rv_map : ∀ x : Transfer.VFType (M := M),
    (rv ⟨iRv x.1, Transfer.rv_mem hM x.2⟩).1 = iRv (vf x).1
  units_iff : ∀ x : RVSubtype M, iUnits (rv x).1 ↔ iUnits x.1
  order_iff : ∀ x y : RVSubtype M, iLe (rv x).1 (rv y).1 ↔ iLe x.1 y.1

namespace Components

variable {M N} (e : Components M N)

/-- The carrier is exhausted by the two sorts, so the component maps determine
a total map without assigning any meaning to off-sort operations. -/
noncomputable def carrierMap (x : M) : N :=
  if hx : iVF x then (e.vf ⟨x, hx⟩).1
  else (e.rv ⟨x, (sort_cover x).resolve_left hx⟩).1

@[simp] theorem carrierMap_vf {x : M} (hx : iVF x) :
    e.carrierMap x = (e.vf ⟨x, hx⟩).1 := by
  simp only [carrierMap, dif_pos hx]

@[simp] theorem carrierMap_rv {x : M} (hx : iRV x) :
    e.carrierMap x = (e.rv ⟨x, hx⟩).1 := by
  simp only [carrierMap, dif_neg (not_vf_of_rv hx)]

theorem carrierMap_vf_mem {x : M} (hx : iVF x) : iVF (e.carrierMap x) := by
  rw [e.carrierMap_vf hx]
  exact (e.vf ⟨x, hx⟩).2

theorem carrierMap_rv_mem {x : M} (hx : iRV x) : iRV (e.carrierMap x) := by
  rw [e.carrierMap_rv hx]
  exact (e.rv ⟨x, hx⟩).2

theorem carrierMap_sort_iff (s : SortTag) (x : M) :
    sortEval s (e.carrierMap x) ↔ sortEval s x := by
  rcases sort_cover x with hv | hr
  · have hw := e.carrierMap_vf_mem hv
    cases s with
    | vf => exact iff_of_true hw hv
    | rv => exact iff_of_false (not_rv_of_vf hw) (not_rv_of_vf hv)
  · have hw := e.carrierMap_rv_mem hr
    cases s with
    | vf => exact iff_of_false (not_vf_of_rv hw) (not_vf_of_rv hr)
    | rv => exact iff_of_true hw hr

theorem carrierMap_injective : Function.Injective e.carrierMap := by
  intro x y hxy
  rcases sort_cover x with hx | hx
  · have hy : iVF y := (e.carrierMap_sort_iff .vf y).mp
      (hxy ▸ e.carrierMap_vf_mem hx)
    have he : e.vf ⟨x, hx⟩ = e.vf ⟨y, hy⟩ := by
      apply Subtype.ext
      simpa only [e.carrierMap_vf hx, e.carrierMap_vf hy] using hxy
    exact congrArg Subtype.val (e.vf.injective he)
  · have hy : iRV y := (e.carrierMap_sort_iff .rv y).mp
      (hxy ▸ e.carrierMap_rv_mem hx)
    have he : e.rv ⟨x, hx⟩ = e.rv ⟨y, hy⟩ := by
      apply Subtype.ext
      simpa only [e.carrierMap_rv hx, e.carrierMap_rv hy] using hxy
    exact congrArg Subtype.val (e.rv.injective he)

theorem carrierMap_vf_zero :
    e.carrierMap (Transfer.iVFZero : M) = (Transfer.iVFZero : N) := by
  rw [e.carrierMap_vf (Transfer.vf_zero_mem hM)]
  exact congrArg Subtype.val e.vf.map_zero

theorem carrierMap_vf_one :
    e.carrierMap (Transfer.iVFOne : M) = (Transfer.iVFOne : N) := by
  rw [e.carrierMap_vf (Transfer.vf_one_mem hM)]
  exact congrArg Subtype.val e.vf.map_one

theorem carrierMap_vf_add {x y : M} (hx : iVF x) (hy : iVF y) :
    e.carrierMap (iVFAdd x y) = iVFAdd (e.carrierMap x) (e.carrierMap y) := by
  rw [e.carrierMap_vf (Transfer.vf_add_mem hM hx hy),
    e.carrierMap_vf hx, e.carrierMap_vf hy]
  exact congrArg Subtype.val (e.vf.map_add ⟨x, hx⟩ ⟨y, hy⟩)

theorem carrierMap_vf_neg {x : M} (hx : iVF x) :
    e.carrierMap (iVFNeg x) = iVFNeg (e.carrierMap x) := by
  rw [e.carrierMap_vf (Transfer.vf_neg_mem hM hx), e.carrierMap_vf hx]
  exact congrArg Subtype.val (map_neg e.vf ⟨x, hx⟩)

theorem carrierMap_vf_mul {x y : M} (hx : iVF x) (hy : iVF y) :
    e.carrierMap (iVFMul x y) = iVFMul (e.carrierMap x) (e.carrierMap y) := by
  rw [e.carrierMap_vf (Transfer.vf_mul_mem hM hx hy),
    e.carrierMap_vf hx, e.carrierMap_vf hy]
  exact congrArg Subtype.val (e.vf.map_mul ⟨x, hx⟩ ⟨y, hy⟩)

theorem carrierMap_rv_zero : e.carrierMap (iRVZero : M) = (iRVZero : N) := by
  rw [e.carrierMap_rv (Transfer.rv_zero_mem hM)]
  exact e.rv_zero

theorem carrierMap_rv_one : e.carrierMap (iRVOne : M) = (iRVOne : N) := by
  rw [e.carrierMap_rv (Transfer.rv_one_mem hM)]
  exact e.rv_one

theorem carrierMap_rv_mul {x y : M} (hx : iRV x) (hy : iRV y) :
    e.carrierMap (iRVMul x y) = iRVMul (e.carrierMap x) (e.carrierMap y) := by
  rw [e.carrierMap_rv (Transfer.rv_mul_mem hM hx hy),
    e.carrierMap_rv hx, e.carrierMap_rv hy]
  exact e.rv_mul ⟨x, hx⟩ ⟨y, hy⟩

theorem carrierMap_rv_inv {x : M} (hx : iRV x) :
    e.carrierMap (iRVInvFn x) = iRVInvFn (e.carrierMap x) := by
  by_cases hx0 : x = iRVZero
  · subst x
    rw [CanonicalStructure.rvInv_zero hM, e.carrierMap_rv_zero,
      CanonicalStructure.rvInv_zero hN]
  · have hy0 : e.carrierMap x ≠ iRVZero := by
      intro h
      exact hx0 (e.carrierMap_injective (h.trans e.carrierMap_rv_zero.symm))
    apply Transfer.rv_mul_left_cancel_of_model hN
      (e.carrierMap_rv_mem (CanonicalStructure.rvInv_mem hM hx))
      (e.carrierMap_rv_mem hx) hy0
      (CanonicalStructure.rvInv_mem hN (e.carrierMap_rv_mem hx))
    rw [← e.carrierMap_rv_mul (CanonicalStructure.rvInv_mem hM hx) hx,
      CanonicalStructure.rvInv_mul hM hx hx0, e.carrierMap_rv_one,
      CanonicalStructure.rvInv_mul hN (e.carrierMap_rv_mem hx) hy0]

theorem carrierMap_k_add {x y : M} (hx : iRV x) (hy : iRV y) :
    e.carrierMap (iKAdd x y) = iKAdd (e.carrierMap x) (e.carrierMap y) := by
  rw [e.carrierMap_rv (CanonicalStructure.kAdd_mem hM hx hy),
    e.carrierMap_rv hx, e.carrierMap_rv hy]
  exact e.k_add ⟨x, hx⟩ ⟨y, hy⟩

theorem carrierMap_k_neg {x : M} (hx : iRV x) :
    e.carrierMap (TrivCase.iKNeg x) = TrivCase.iKNeg (e.carrierMap x) := by
  rw [e.carrierMap_rv (CanonicalStructure.kNeg_mem hM hx), e.carrierMap_rv hx]
  exact e.k_neg ⟨x, hx⟩

theorem carrierMap_rv_map {x : M} (hx : iVF x) :
    e.carrierMap (iRv x) = iRv (e.carrierMap x) := by
  rw [e.carrierMap_rv (Transfer.rv_mem hM hx), e.carrierMap_vf hx]
  exact e.rv_map ⟨x, hx⟩

private theorem nullary_eta {X : Type} (xs : Fin 0 → X) :
    xs = fun i => i.elim0 := by
  funext i
  exact i.elim0

private theorem unary_eta {X : Type} (xs : Fin 1 → X) : xs = ![xs 0] := by
  funext i
  fin_cases i
  rfl

private theorem binary_eta {X : Type} (xs : Fin 2 → X) : xs = ![xs 0, xs 1] := by
  funext i
  fin_cases i <;> rfl

theorem carrierMap_fun {k : ℕ} (f : Fn k) (xs : Fin k → M)
    (hs : ∀ i, sortEval (Fn.argSort f i) (xs i)) :
    e.carrierMap (Structure.funMap (L := LRV) f xs) =
      Structure.funMap (L := LRV) f (e.carrierMap ∘ xs) := by
  cases f with
  | vfZero =>
      rw [nullary_eta (e.carrierMap ∘ xs), nullary_eta xs]
      exact e.carrierMap_vf_zero
  | vfOne =>
      rw [nullary_eta (e.carrierMap ∘ xs), nullary_eta xs]
      exact e.carrierMap_vf_one
  | rvZero =>
      rw [nullary_eta (e.carrierMap ∘ xs), nullary_eta xs]
      exact e.carrierMap_rv_zero
  | rvOne =>
      rw [nullary_eta (e.carrierMap ∘ xs), nullary_eta xs]
      exact e.carrierMap_rv_one
  | vfAdd =>
      rw [binary_eta (e.carrierMap ∘ xs), binary_eta xs]
      exact e.carrierMap_vf_add (hs 0) (hs 1)
  | vfMul =>
      rw [binary_eta (e.carrierMap ∘ xs), binary_eta xs]
      exact e.carrierMap_vf_mul (hs 0) (hs 1)
  | vfNeg =>
      rw [unary_eta (e.carrierMap ∘ xs), unary_eta xs]
      exact e.carrierMap_vf_neg (hs 0)
  | rvMul =>
      rw [binary_eta (e.carrierMap ∘ xs), binary_eta xs]
      exact e.carrierMap_rv_mul (hs 0) (hs 1)
  | rvInv =>
      rw [unary_eta (e.carrierMap ∘ xs), unary_eta xs]
      exact e.carrierMap_rv_inv (hs 0)
  | kAdd =>
      rw [binary_eta (e.carrierMap ∘ xs), binary_eta xs]
      exact e.carrierMap_k_add (hs 0) (hs 1)
  | kNeg =>
      rw [unary_eta (e.carrierMap ∘ xs), unary_eta xs]
      exact e.carrierMap_k_neg (hs 0)
  | rvMap =>
      rw [unary_eta (e.carrierMap ∘ xs), unary_eta xs]
      exact e.carrierMap_rv_map (hs 0)

theorem carrierMap_rel {k : ℕ} (r : Rel k) (xs : Fin k → M)
    (hs : ∀ i, sortEval (Rel.argSort r i) (xs i)) :
    Structure.RelMap (L := LRV) r (e.carrierMap ∘ xs) ↔
      Structure.RelMap (L := LRV) r xs := by
  cases r with
  | memVF =>
      rw [unary_eta (e.carrierMap ∘ xs), unary_eta xs]
      exact e.carrierMap_sort_iff .vf (xs 0)
  | memRV =>
      rw [unary_eta (e.carrierMap ∘ xs), unary_eta xs]
      exact e.carrierMap_sort_iff .rv (xs 0)
  | memUnits =>
      rw [unary_eta (e.carrierMap ∘ xs), unary_eta xs]
      change iUnits (e.carrierMap (xs 0)) ↔ iUnits (xs 0)
      rw [e.carrierMap_rv (hs 0)]
      exact e.units_iff ⟨xs 0, hs 0⟩
  | rvLe =>
      rw [binary_eta (e.carrierMap ∘ xs), binary_eta xs]
      change iLe (e.carrierMap (xs 0)) (e.carrierMap (xs 1)) ↔ iLe (xs 0) (xs 1)
      rw [e.carrierMap_rv (hs 0), e.carrierMap_rv (hs 1)]
      exact e.order_iff ⟨xs 0, hs 0⟩ ⟨xs 1, hs 1⟩

/-- Typed field/RV data assemble into preservation of every correctly sorted
symbol of the frozen language. -/
noncomputable def toSortedEmbedding : CanonicalStructure.SortedEmbedding M N where
  toFun := e.carrierMap
  injective := e.carrierMap_injective
  sort_iff := e.carrierMap_sort_iff
  map_fun := e.carrierMap_fun
  map_rel := e.carrierMap_rel

@[simp] theorem toSortedEmbedding_apply (x : M) :
    e.toSortedEmbedding.toFun x = e.carrierMap x := rfl

/-- Canonical totalization supplies the off-sort conditions automatically. -/
noncomputable def toCanonicalEmbedding :
    @FirstOrder.Language.Embedding LRV M N
      (CanonicalStructure.normalize (M := M))
      (CanonicalStructure.normalize (M := N)) :=
  e.toSortedEmbedding.toCanonicalEmbedding hM hN

end Components
end TypedModelMap

#print axioms TypedModelMap.Components.carrierMap_injective
#print axioms TypedModelMap.Components.carrierMap_rv_inv
#print axioms TypedModelMap.Components.carrierMap_fun
#print axioms TypedModelMap.Components.carrierMap_rel
#print axioms TypedModelMap.Components.toSortedEmbedding
#print axioms TypedModelMap.Components.toCanonicalEmbedding
