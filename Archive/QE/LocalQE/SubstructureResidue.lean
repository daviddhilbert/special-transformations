import CanonicalResidueOperations
import SubstructureRVGroup

/-! The residue part of an actual language substructure is a subfield once
RV inversion is a named function. A language embedding induces an honest
embedding of these residue fields, without any extension hypothesis. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open CanonicalRV ValuedModelMap ResidueTranscendentalTransport

namespace CanonicalResidue

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation (VFType (M := M)) Γ)
  (hv : ∀ a b : VFType (M := M), VFValued.predV a b ↔ v a ≤ v b)

theorem encodeResidue_mem (x : Residue v) : iRV (encodeResidue v hv x) :=
  (toRV v hv x).property

theorem encodeResidue_ne_zero (x : Residue v) (hx : x ≠ 0) :
    encodeResidue v hv x ≠ iRVZero := by
  intro h
  exact hx (encodeResidue_injective v hv (h.trans (encodeResidue_zero v hv).symm))

theorem encodeResidue_inv (x : Residue v) :
    encodeResidue v hv x⁻¹ = iRVInvFn (encodeResidue v hv x) := by
  by_cases hx : x = 0
  · rw [hx, inv_zero, encodeResidue_zero, CanonicalStructure.rvInv_zero hM]
  · apply rv_mul_left_cancel_of_model hM (encodeResidue_mem v hv x⁻¹)
      (encodeResidue_mem v hv x) (encodeResidue_ne_zero v hv x hx)
      (CanonicalStructure.rvInv_mem hM (encodeResidue_mem v hv x))
    rw [← encodeResidue_mul, inv_mul_cancel₀ hx, encodeResidue_one,
      CanonicalStructure.rvInv_mul hM (encodeResidue_mem v hv x)
        (encodeResidue_ne_zero v hv x hx)]

noncomputable def decodeResidue (a : M) (ha : iUnits a ∨ a = iRVZero) : Residue v :=
  Classical.choose (encodeResidue_surjective_inK v hv a ha)

@[simp] theorem encode_decodeResidue (a : M) (ha : iUnits a ∨ a = iRVZero) :
    encodeResidue v hv (decodeResidue v hv a ha) = a :=
  Classical.choose_spec (encodeResidue_surjective_inK v hv a ha)

end CanonicalResidue

namespace SubstructureResidue

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
  [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

theorem units_map (S : LRV.Substructure M) (f : S ↪[LRV] N)
    (x : S) (hx : iUnits (x : M)) : iUnits (f x) := by
  have hx' : Structure.RelMap (L := LRV) Rel.memUnits (fun _ : Fin 1 => x) := by
    change Structure.RelMap (L := LRV) Rel.memUnits (fun _ : Fin 1 => (x : M))
    have he : (fun _ : Fin 1 => (x : M)) = ![(x : M)] := by
      funext i; fin_cases i; rfl
    rw [he]
    exact hx
  have h := (f.map_rel Rel.memUnits (fun _ : Fin 1 => x)).mpr hx'
  change Structure.RelMap (L := LRV) Rel.memUnits ![f x]
  have he : (fun _ : Fin 1 => f x) = ![f x] := by funext i; fin_cases i; rfl
  rw [← he]
  exact h

theorem inK_map (S : LRV.Substructure M) (f : S ↪[LRV] N)
    (x : S) (hx : iUnits (x : M) ∨ (x : M) = iRVZero) :
    iUnits (f x) ∨ f x = iRVZero := by
  rcases hx with hx | hx
  · exact Or.inl (units_map S f x hx)
  · right
    have he : x = ⟨iRVZero, SubstructureRVGroup.rvZero_mem S⟩ := Subtype.ext hx
    rw [he, SubstructureRVGroup.map_rvZero]

variable {Γ Δ : Type} [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]
  (v : Valuation (VFType (M := M)) Γ) (w : Valuation (VFType (M := N)) Δ)
  (hv : ∀ a b : VFType (M := M), VFValued.predV a b ↔ v a ≤ v b)
  (hw : ∀ a b : VFType (M := N), VFValued.predV a b ↔ w a ≤ w b)

open CanonicalResidue

/-- The actual residue subfield whose encoded points are already in S. -/
noncomputable def field (S : LRV.Substructure M) : Subfield (Residue v) where
  carrier := {x | encodeResidue v hv x ∈ S}
  zero_mem' := by
    change encodeResidue v hv 0 ∈ S
    rw [encodeResidue_zero]
    exact SubstructureRVGroup.rvZero_mem S
  one_mem' := by
    change encodeResidue v hv 1 ∈ S
    rw [encodeResidue_one]
    exact SubstructureRVGroup.rvOne_mem S
  add_mem' := by
    intro x y hx hy
    change encodeResidue v hv (x + y) ∈ S
    rw [encodeResidue_add]
    exact S.fun_mem Fn.kAdd ![encodeResidue v hv x, encodeResidue v hv y]
      (by intro i; fin_cases i; exact hx; exact hy)
  mul_mem' := by
    intro x y hx hy
    change encodeResidue v hv (x * y) ∈ S
    rw [encodeResidue_mul]
    exact S.fun_mem Fn.rvMul ![encodeResidue v hv x, encodeResidue v hv y]
      (by intro i; fin_cases i; exact hx; exact hy)
  neg_mem' := by
    intro x hx
    change encodeResidue v hv (-x) ∈ S
    rw [encodeResidue_neg]
    exact S.fun_mem Fn.kNeg ![encodeResidue v hv x]
      (by intro i; fin_cases i; exact hx)
  inv_mem' := by
    intro x hx
    change encodeResidue v hv x⁻¹ ∈ S
    rw [encodeResidue_inv]
    exact S.fun_mem Fn.rvInv ![encodeResidue v hv x]
      (by intro i; fin_cases i; exact hx)

variable (S : LRV.Substructure M) (f : S ↪[LRV] N)

noncomputable def mapElement (x : field v hv S) : Residue w :=
  decodeResidue w hw (f ⟨encodeResidue v hv x, x.property⟩)
    (inK_map S f _ (encodeResidue_inK v hv x))

@[simp] theorem encode_mapElement (x : field v hv S) :
    encodeResidue w hw (mapElement v w hv hw S f x) =
      f ⟨encodeResidue v hv x, x.property⟩ :=
  encode_decodeResidue w hw _ _

noncomputable def map : field v hv S →+* Residue w where
  toFun := mapElement v w hv hw S f
  map_zero' := by
    apply encodeResidue_injective w hw
    rw [encode_mapElement, encodeResidue_zero]
    have he : (⟨encodeResidue v hv (0 : field v hv S), (0 : field v hv S).property⟩ : S) =
        ⟨iRVZero, SubstructureRVGroup.rvZero_mem S⟩ := Subtype.ext (encodeResidue_zero v hv)
    rw [he, SubstructureRVGroup.map_rvZero]
  map_one' := by
    apply encodeResidue_injective w hw
    rw [encode_mapElement, encodeResidue_one]
    have he : (⟨encodeResidue v hv (1 : field v hv S), (1 : field v hv S).property⟩ : S) =
        ⟨iRVOne, SubstructureRVGroup.rvOne_mem S⟩ := Subtype.ext (encodeResidue_one v hv)
    rw [he, SubstructureRVGroup.map_rvOne]
  map_add' x y := by
    apply encodeResidue_injective w hw
    rw [encode_mapElement, encodeResidue_add, encode_mapElement, encode_mapElement]
    have hm : iKAdd (encodeResidue v hv x) (encodeResidue v hv y) ∈ S :=
      S.fun_mem Fn.kAdd ![encodeResidue v hv x, encodeResidue v hv y]
        (by intro i; fin_cases i; exact x.property; exact y.property)
    have he : (⟨encodeResidue v hv (↑(x + y)), (x + y).property⟩ : S) =
        ⟨iKAdd (encodeResidue v hv x) (encodeResidue v hv y), hm⟩ :=
      Subtype.ext (encodeResidue_add v hv x y)
    rw [he]
    have h := SubstructureField.map_function S f Fn.kAdd
      ![encodeResidue v hv x, encodeResidue v hv y]
      (by intro i; fin_cases i; exact x.property; exact y.property)
    apply h.trans
    change Structure.funMap (L := LRV) Fn.kAdd _ =
      Structure.funMap (L := LRV) Fn.kAdd
        ![f ⟨encodeResidue v hv x, x.property⟩, f ⟨encodeResidue v hv y, y.property⟩]
    congr 1
    funext i
    fin_cases i <;> rfl
  map_mul' x y := by
    apply encodeResidue_injective w hw
    rw [encode_mapElement, encodeResidue_mul, encode_mapElement, encode_mapElement]
    have hm : iRVMul (encodeResidue v hv x) (encodeResidue v hv y) ∈ S :=
      S.fun_mem Fn.rvMul ![encodeResidue v hv x, encodeResidue v hv y]
        (by intro i; fin_cases i; exact x.property; exact y.property)
    have he : (⟨encodeResidue v hv (↑(x * y)), (x * y).property⟩ : S) =
        ⟨iRVMul (encodeResidue v hv x) (encodeResidue v hv y), hm⟩ :=
      Subtype.ext (encodeResidue_mul v hv x y)
    rw [he]
    have h := SubstructureField.map_function S f Fn.rvMul
      ![encodeResidue v hv x, encodeResidue v hv y]
      (by intro i; fin_cases i; exact x.property; exact y.property)
    apply h.trans
    change Structure.funMap (L := LRV) Fn.rvMul _ =
      Structure.funMap (L := LRV) Fn.rvMul
        ![f ⟨encodeResidue v hv x, x.property⟩, f ⟨encodeResidue v hv y, y.property⟩]
    congr 1
    funext i
    fin_cases i <;> rfl

theorem map_agrees (x : field v hv S) :
    encodeResidue w hw (map v w hv hw S f x) =
      f ⟨encodeResidue v hv x, x.property⟩ := encode_mapElement v w hv hw S f x

theorem map_injective : Function.Injective (map v w hv hw S f) :=
  (map v w hv hw S f).injective

end SubstructureResidue

#print axioms CanonicalResidue.encodeResidue_inv
#print axioms SubstructureResidue.field
#print axioms SubstructureResidue.map
#print axioms SubstructureResidue.map_agrees
