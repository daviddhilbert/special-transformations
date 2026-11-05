import CanonicalRVOrder
import SubstructureValuation
import CanonicalStructure

set_option backward.isDefEq.respectTransparency false

/-! Extract the actual nonzero RV group and its map from a language substructure.
The inverse-closure step uses the named RV inverse in the author's language.
-/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace CanonicalRV

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation (VFType (M := M)) Γ)
  (hv : ∀ a b : VFType (M := M), VFValued.predV a b ↔ v a ≤ v b)

noncomputable def encodeUnit (t : _root_.RVCalc.RVUnit v) : M := (equiv v hv (some t)).1

theorem encodeUnit_mem (t : _root_.RVCalc.RVUnit v) : iRV (encodeUnit v hv t) :=
  (equiv v hv (some t)).2

theorem encodeUnit_ne_zero (t : _root_.RVCalc.RVUnit v) : encodeUnit v hv t ≠ iRVZero :=
  (equiv_ne_zero_iff v hv (some t)).mpr (Option.some_ne_none t)

theorem encodeUnit_injective : Function.Injective (encodeUnit v hv) := by
  intro t s h
  exact Option.some.inj ((equiv v hv).injective (Subtype.ext h))

@[simp] theorem encodeUnit_one : encodeUnit v hv 1 = iRVOne := by
  have hrv : _root_.RVCalc.rv v 1 = some 1 := by
    simp [_root_.RVCalc.rv, Units.mk0_one]
  rw [encodeUnit, ← hrv, equiv_one]

theorem encodeUnit_mul (t s : _root_.RVCalc.RVUnit v) :
    encodeUnit v hv (t * s) = iRVMul (encodeUnit v hv t) (encodeUnit v hv s) :=
  equiv_mul v hv (some t) (some s)

theorem exists_encodeUnit (x : M) (hx : iRV x) (hx0 : x ≠ iRVZero) :
    ∃ t : _root_.RVCalc.RVUnit v, encodeUnit v hv t = x := by
  obtain ⟨q, hq⟩ := (equiv v hv).surjective ⟨x, hx⟩
  cases q with
  | none =>
    have he := congrArg Subtype.val hq
    exact False.elim (hx0 (he.symm.trans (equiv_zero v hv)))
  | some t => exact ⟨t, congrArg Subtype.val hq⟩

noncomputable def decodeUnit (x : M) (hx : iRV x) (hx0 : x ≠ iRVZero) :
    _root_.RVCalc.RVUnit v := Classical.choose (exists_encodeUnit v hv x hx hx0)

@[simp] theorem encodeUnit_decodeUnit (x : M) (hx : iRV x) (hx0 : x ≠ iRVZero) :
    encodeUnit v hv (decodeUnit v hv x hx hx0) = x :=
  Classical.choose_spec (exists_encodeUnit v hv x hx hx0)

/-- Canonical quotient inversion agrees with the named inverse operation. -/
theorem encodeUnit_inv (t : _root_.RVCalc.RVUnit v) :
    encodeUnit v hv t⁻¹ = iRVInvFn (encodeUnit v hv t) := by
  apply rv_mul_left_cancel_of_model hM (encodeUnit_mem v hv t⁻¹)
    (encodeUnit_mem v hv t) (encodeUnit_ne_zero v hv t)
    (CanonicalStructure.rvInv_mem hM (encodeUnit_mem v hv t))
  rw [← encodeUnit_mul, inv_mul_cancel, encodeUnit_one,
    CanonicalStructure.rvInv_mul hM (encodeUnit_mem v hv t) (encodeUnit_ne_zero v hv t)]

theorem equiv_inv (t : _root_.RVCalc.RV v) :
    (equiv v hv (ResidueTranscendentalTransport.rvInv v t)).1 =
      iRVInvFn (equiv v hv t).1 := by
  cases t with
  | none =>
    change (equiv v hv none).1 = iRVInvFn (equiv v hv none).1
    rw [equiv_zero, CanonicalStructure.rvInv_zero hM]
  | some t => exact encodeUnit_inv v hv t

end CanonicalRV

namespace SubstructureRVGroup

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
  [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

theorem rvZero_mem (S : LRV.Substructure M) : (iRVZero : M) ∈ S :=
  S.fun_mem Fn.rvZero (fun i : Fin 0 => i.elim0) (fun i => i.elim0)

theorem rvOne_mem (S : LRV.Substructure M) : (iRVOne : M) ∈ S :=
  S.fun_mem Fn.rvOne (fun i : Fin 0 => i.elim0) (fun i => i.elim0)

theorem map_rvZero (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    f ⟨iRVZero, rvZero_mem S⟩ = iRVZero := by
  have h := SubstructureField.map_function S f Fn.rvZero
    (fun i : Fin 0 => i.elim0) (fun i => i.elim0)
  apply h.trans
  change Structure.funMap (L := LRV) Fn.rvZero _ =
    Structure.funMap (L := LRV) Fn.rvZero (fun i => i.elim0)
  congr 1
  funext i
  exact i.elim0

theorem map_rvOne (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    f ⟨iRVOne, rvOne_mem S⟩ = iRVOne := by
  have h := SubstructureField.map_function S f Fn.rvOne
    (fun i : Fin 0 => i.elim0) (fun i => i.elim0)
  apply h.trans
  change Structure.funMap (L := LRV) Fn.rvOne _ =
    Structure.funMap (L := LRV) Fn.rvOne (fun i => i.elim0)
  congr 1
  funext i
  exact i.elim0

theorem rv_map (S : LRV.Substructure M) (f : S ↪[LRV] N)
    (x : S) (hx : iRV (x : M)) : iRV (f x) := by
  have hx' : Structure.RelMap (L := LRV) Rel.memRV (fun _ : Fin 1 => x) := by
    change Structure.RelMap (L := LRV) Rel.memRV (fun _ : Fin 1 => (x : M))
    have he : (fun _ : Fin 1 => (x : M)) = ![(x : M)] := by
      funext i; fin_cases i; rfl
    rw [he]
    exact hx
  have h := (f.map_rel Rel.memRV (fun _ : Fin 1 => x)).mpr hx'
  change Structure.RelMap (L := LRV) Rel.memRV ![f x]
  have he : (fun _ : Fin 1 => f x) = ![f x] := by funext i; fin_cases i; rfl
  rw [← he]
  exact h

theorem map_ne_rvZero (S : LRV.Substructure M) (f : S ↪[LRV] N)
    (x : S) (hx : (x : M) ≠ iRVZero) : f x ≠ iRVZero := by
  intro h
  apply hx
  exact congrArg (fun z : S => (z : M))
    (f.injective (h.trans (map_rvZero S f).symm))

variable {Γ Δ : Type} [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]
  (v : Valuation (VFType (M := M)) Γ) (w : Valuation (VFType (M := N)) Δ)
  (hv : ∀ a b : VFType (M := M), VFValued.predV a b ↔ v a ≤ v b)
  (hw : ∀ a b : VFType (M := N), VFValued.predV a b ↔ w a ≤ w b)

section Map

variable (S : LRV.Substructure M) (f : S ↪[LRV] N)
  (H : Subgroup (_root_.RVCalc.RVUnit v))
  (hH : ∀ t : H, CanonicalRV.encodeUnit v hv (t : _root_.RVCalc.RVUnit v) ∈ S)

noncomputable def mapUnit (t : H) : _root_.RVCalc.RVUnit w :=
  CanonicalRV.decodeUnit w hw
    (f ⟨CanonicalRV.encodeUnit v hv t, hH t⟩)
    (rv_map S f _ (CanonicalRV.encodeUnit_mem v hv t))
    (map_ne_rvZero S f _ (CanonicalRV.encodeUnit_ne_zero v hv t))

@[simp] theorem encode_mapUnit (t : H) :
    CanonicalRV.encodeUnit w hw (mapUnit v w hv hw S f H hH t) =
      f ⟨CanonicalRV.encodeUnit v hv t, hH t⟩ :=
  CanonicalRV.encodeUnit_decodeUnit w hw _ _ _

noncomputable def mapHom : H →* _root_.RVCalc.RVUnit w where
  toFun := mapUnit v w hv hw S f H hH
  map_one' := by
    apply CanonicalRV.encodeUnit_injective w hw
    rw [encode_mapUnit, CanonicalRV.encodeUnit_one]
    have he : (⟨CanonicalRV.encodeUnit v hv (1 : H), hH 1⟩ : S) =
        ⟨iRVOne, rvOne_mem S⟩ := Subtype.ext (CanonicalRV.encodeUnit_one v hv)
    rw [he, map_rvOne]
  map_mul' t s := by
    apply CanonicalRV.encodeUnit_injective w hw
    rw [encode_mapUnit, CanonicalRV.encodeUnit_mul, encode_mapUnit, encode_mapUnit]
    have hm : iRVMul (CanonicalRV.encodeUnit v hv t) (CanonicalRV.encodeUnit v hv s) ∈ S :=
      S.fun_mem Fn.rvMul ![CanonicalRV.encodeUnit v hv t, CanonicalRV.encodeUnit v hv s]
        (by intro i; fin_cases i; exact hH t; exact hH s)
    have he : (⟨CanonicalRV.encodeUnit v hv (↑(t * s)), hH (t * s)⟩ : S) =
        ⟨iRVMul (CanonicalRV.encodeUnit v hv t) (CanonicalRV.encodeUnit v hv s), hm⟩ :=
      Subtype.ext (CanonicalRV.encodeUnit_mul v hv t s)
    rw [he]
    have h := SubstructureField.map_function S f Fn.rvMul
      ![CanonicalRV.encodeUnit v hv t, CanonicalRV.encodeUnit v hv s]
      (by intro i; fin_cases i; exact hH t; exact hH s)
    apply h.trans
    change Structure.funMap (L := LRV) Fn.rvMul _ =
      Structure.funMap (L := LRV) Fn.rvMul
        ![f ⟨CanonicalRV.encodeUnit v hv t, hH t⟩, f ⟨CanonicalRV.encodeUnit v hv s, hH s⟩]
    congr 1
    funext i
    fin_cases i <;> rfl

theorem mapHom_injective : Function.Injective (mapHom v w hv hw S f H hH) := by
  intro t s h
  have hh := congrArg (CanonicalRV.encodeUnit w hw) h
  change CanonicalRV.encodeUnit w hw (mapUnit v w hv hw S f H hH t) =
    CanonicalRV.encodeUnit w hw (mapUnit v w hv hw S f H hH s) at hh
  rw [encode_mapUnit, encode_mapUnit] at hh
  have ht : CanonicalRV.encodeUnit v hv t = CanonicalRV.encodeUnit v hv s :=
    congrArg (fun z : S => (z : M)) (f.injective hh)
  exact Subtype.ext (CanonicalRV.encodeUnit_injective v hv ht)

theorem mapHom_order (t s : H) :
    _root_.RVCalc.vrvUnit v t ≤ _root_.RVCalc.vrvUnit v s ↔
      _root_.RVCalc.vrvUnit w (mapHom v w hv hw S f H hH t) ≤
      _root_.RVCalc.vrvUnit w (mapHom v w hv hw S f H hH s) := by
  have h := SubstructureField.iLe_map S f
    ⟨CanonicalRV.encodeUnit v hv s, hH s⟩ ⟨CanonicalRV.encodeUnit v hv t, hH t⟩
  rw [← encode_mapUnit v w hv hw S f H hH s, ← encode_mapUnit v w hv hw S f H hH t] at h
  have hs := CanonicalRV.le_equiv_iff v hv (some (s : _root_.RVCalc.RVUnit v)) (some (t : _root_.RVCalc.RVUnit v))
  have ht := CanonicalRV.le_equiv_iff w hw (some (mapUnit v w hv hw S f H hH s))
    (some (mapUnit v w hv hw S f H hH t))
  exact hs.symm.trans (h.symm.trans ht)

end Map

/-- Every original RV element is closed under named multiplication and inverse,
so the nonzero part of an arbitrary language substructure is already a group. -/
noncomputable def group (S : LRV.Substructure M) : Subgroup (_root_.RVCalc.RVUnit v) where
  carrier := {t | CanonicalRV.encodeUnit v hv t ∈ S}
  one_mem' := by
    change CanonicalRV.encodeUnit v hv 1 ∈ S
    rw [CanonicalRV.encodeUnit_one]
    exact rvOne_mem S
  mul_mem' := by
    intro t s ht hs
    change CanonicalRV.encodeUnit v hv (t * s) ∈ S
    rw [CanonicalRV.encodeUnit_mul]
    exact S.fun_mem Fn.rvMul ![CanonicalRV.encodeUnit v hv t, CanonicalRV.encodeUnit v hv s]
      (by intro i; fin_cases i; exact ht; exact hs)
  inv_mem' := by
    intro t ht
    change CanonicalRV.encodeUnit v hv t⁻¹ ∈ S
    rw [CanonicalRV.encodeUnit_inv]
    exact S.fun_mem Fn.rvInv ![CanonicalRV.encodeUnit v hv t]
      (by intro i; fin_cases i; exact ht)

noncomputable def map (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    group v hv S →* _root_.RVCalc.RVUnit w :=
  mapHom v w hv hw S f (group v hv S) (fun t => t.2)

theorem map_injective (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    Function.Injective (map v w hv hw S f) :=
  mapHom_injective v w hv hw S f (group v hv S) (fun t => t.2)

theorem map_agrees (S : LRV.Substructure M) (f : S ↪[LRV] N) (t : group v hv S) :
    CanonicalRV.encodeUnit w hw (map v w hv hw S f t) =
      f ⟨CanonicalRV.encodeUnit v hv t, t.2⟩ :=
  encode_mapUnit v w hv hw S f (group v hv S) (fun t => t.2) t

theorem map_order (S : LRV.Substructure M) (f : S ↪[LRV] N) (t s : group v hv S) :
    _root_.RVCalc.vrvUnit v t ≤ _root_.RVCalc.vrvUnit v s ↔
      _root_.RVCalc.vrvUnit w (map v w hv hw S f t) ≤
      _root_.RVCalc.vrvUnit w (map v w hv hw S f s) :=
  mapHom_order v w hv hw S f (group v hv S) (fun t => t.2) t s

/-- The concrete group map agrees with every nonzero old RV element. -/
theorem exists_group_element (S : LRV.Substructure M) (f : S ↪[LRV] N)
    (x : S) (hx : iRV (x : M)) (hx0 : (x : M) ≠ iRVZero) :
    ∃ t : group v hv S, CanonicalRV.encodeUnit v hv t = (x : M) ∧
      CanonicalRV.encodeUnit w hw (map v w hv hw S f t) = f x := by
  obtain ⟨t, ht⟩ := CanonicalRV.exists_encodeUnit v hv (x : M) hx hx0
  have hmem : t ∈ group v hv S := by change CanonicalRV.encodeUnit v hv t ∈ S; rw [ht]; exact x.2
  refine ⟨⟨t, hmem⟩, ht, ?_⟩
  rw [map_agrees]
  congr 1
  exact Subtype.ext ht

end SubstructureRVGroup

#print axioms CanonicalRV.encodeUnit_injective
#print axioms CanonicalRV.encodeUnit_decodeUnit
#print axioms SubstructureRVGroup.mapHom_injective
#print axioms SubstructureRVGroup.mapHom_order
#print axioms CanonicalRV.equiv_inv
#print axioms SubstructureRVGroup.group
#print axioms SubstructureRVGroup.map_injective
#print axioms SubstructureRVGroup.map_order
#print axioms SubstructureRVGroup.exists_group_element
