module

public import Section3.PolynomialRoots

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.PolynomialRoots
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def rootSet (E : Subfield (VFType (M := M))) (p : Polynomial E) : Set M :=
  {x | ∃ hx : iVF x, p.eval₂ E.subtype (⟨x, hx⟩ : VFType (M := M)) = 0}

theorem rootSet_definable (S : Set M) (E : Subfield (VFType (M := M)))
    (hE : ∀ x : E, x.val.val ∈ S) (p : Polynomial E) : DefinableAt S .vf (rootSet E p) := by
  let k := p.natDegree + 1
  let c (i : Fin k) : VFType (M := M) := (p.coeff i.val).val
  let r : Parameters S := ⟨k, fun i => (c i).val, fun _ => .vf,
    fun i => (c i).property, fun i => hE (p.coeff i.val)⟩
  let z : LRV.Term (Fin k ⊕ Fin 1) := .func Fn.vfZero Fin.elim0
  let φ : LRV.BoundedFormula (Fin k) 1 := .equal (term k) z
  have hw : WellSorted r.sorts (fun _ => .vf) φ := by
    apply WellSorted.equal (s := .vf)
    · exact term_sorted k
    · apply tmSort_func
      intro i; exact i.elim0
  have heval (x : VFType (M := M)) : φ.Realize r.values ![x.val] ↔ p.eval₂ E.subtype x = 0 := by
    have hz : z.realize (Sum.elim r.values ![x.val]) = ((0 : VFType (M := M)).val) := by
      change Structure.funMap (L := LRV) Fn.vfZero (fun i => _) =
        Structure.funMap (L := LRV) Fn.vfZero Fin.elim0
      congr 1; funext i; exact i.elim0
    change (term k).realize (Sum.elim (fun i => (c i).val) ![x.val]) =
      z.realize (Sum.elim r.values ![x.val]) ↔ _
    rw [term_realize, hz]
    have he : (∑ i : Fin k, c i * x ^ i.val) = p.eval₂ E.subtype x :=
      (eval₂_eq_sum E p x).symm
    rw [he]
    exact Subtype.val_inj
  refine ⟨⟨r, φ, hw, ?_⟩, ?_⟩
  · ext y
    constructor
    · rintro ⟨hy, hroot⟩
      let x : VFType (M := M) := ⟨y 0, hy⟩
      have he : ![x.val] = y := by funext i; fin_cases i; rfl
      exact ⟨fun i => by fin_cases i; exact hy, he ▸ (heval x).mpr hroot⟩
    · rintro ⟨hy, hφ⟩
      let x : VFType (M := M) := ⟨y 0, hy 0⟩
      have he : ![x.val] = y := by funext i; fin_cases i; rfl
      exact ⟨hy 0, (heval x).mp (he ▸ hφ)⟩
  · rintro x ⟨hx, _⟩
    exact hx

theorem rootSet_finite (E : Subfield (VFType (M := M))) (p : Polynomial E) (hp : p ≠ 0) :
    (rootSet E p).Finite := by
  have hf := Polynomial.finite_setOfPred_isRoot (Polynomial.map_ne_zero (f := E.subtype) hp)
  have hf' : {x : VFType (M := M) | p.eval₂ E.subtype x = 0}.Finite := by
    simpa only [Polynomial.IsRoot, Polynomial.eval_map] using hf
  have he : rootSet E p = Subtype.val '' {x : VFType (M := M) | p.eval₂ E.subtype x = 0} := by
    ext x
    constructor
    · rintro ⟨hx, hroot⟩; exact ⟨⟨x, hx⟩, hroot, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x.property, hx⟩
  rw [he]
  exact hf'.image Subtype.val

theorem algebraicAt_of_isAlgebraic_named (S : Set M) (E : Subfield (VFType (M := M)))
    (hE : ∀ x : E, x.val.val ∈ S) (b : VFType (M := M)) (hb : IsAlgebraic E b) :
    AlgebraicAt S .vf b.val := by
  obtain ⟨p, hp, hpb⟩ := hb
  exact ⟨rootSet E p, rootSet_definable S E hE p, rootSet_finite E p hp, b.property, hpb⟩

end SpecialTransformations.Section3.PolynomialRoots