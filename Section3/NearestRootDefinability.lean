module

public import Section3.ParameterBridge
public import Section3.NearestRoots
public import VFValued

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.NearestRootSyntax
variable {M : Type} [LRV.Structure M]

private def var (i : Fin 3) : LRV.Term (Fin 3 ⊕ Fin 0) := .var (.inl i)
public def difference (i : Fin 3) : LRV.Term (Fin 3 ⊕ Fin 0) :=
  .func Fn.rvMap ![.func Fn.vfAdd ![var i, .func Fn.vfNeg ![var 1] ] ]

def formula : LRV.Formula (Fin 3) := .rel Rel.rvLe ![difference 2, difference 0]

def distanceLe (r a s : M) : Prop := FirstOrder.Language.Formula.Realize formula ![r, a, s]

private theorem func1 {β : Type} (f : Fn 1) (t : LRV.Term β) (v : β → M) :
    (Term.func f ![t]).realize v = Structure.funMap (L := LRV) f ![t.realize v] := by
  change Structure.funMap (L := LRV) f (fun i => _) = _
  congr 1; funext i; fin_cases i; rfl

private theorem func2 {β : Type} (f : Fn 2) (t u : LRV.Term β) (v : β → M) :
    (Term.func f ![t, u]).realize v = Structure.funMap (L := LRV) f ![t.realize v, u.realize v] := by
  change Structure.funMap (L := LRV) f (fun i => _) = _
  congr 1; funext i; fin_cases i <;> rfl

private theorem difference_realize (i : Fin 3) (r a s : M) :
    (difference i).realize (Sum.elim ![r, a, s] Fin.elim0) =
      iRv (iVFAdd (![r, a, s] i) (iVFNeg a)) := by
  rw [difference, func1, func2, func1]
  rfl

theorem distanceLe_realize (r a s : M) : distanceLe r a s ↔
    iLe (iRv (iVFAdd s (iVFNeg a))) (iRv (iVFAdd r (iVFNeg a))) := by
  change Structure.RelMap (L := LRV) Rel.rvLe
    (fun i => (![difference 2, difference 0] i).realize (Sum.elim ![r, a, s] Fin.elim0)) ↔ _
  have he : (fun i => (![difference 2, difference 0] i).realize
      (Sum.elim ![r, a, s] Fin.elim0)) =
      ![iRv (iVFAdd s (iVFNeg a)), iRv (iVFAdd r (iVFNeg a))] := by
    funext i
    fin_cases i
    · exact difference_realize 2 r a s
    · exact difference_realize 0 r a s
  rw [he]
  rfl

theorem distanceLe_definable (S : Set M) :
    S.Definable LRV {z : Fin 3 → M | distanceLe (z 0) (z 1) (z 2)} := by
  have h : (∅ : Set M).Definable LRV {z : Fin 3 → M |
      FirstOrder.Language.Formula.Realize formula z} := Set.empty_definable_iff.mpr ⟨formula, rfl⟩
  convert h.mono (Set.empty_subset S) using 1
  ext z
  have he : ![z 0, z 1, z 2] = z := by funext i; fin_cases i <;> rfl
  exact congrArg (FirstOrder.Language.Formula.Realize formula) he |>.to_iff

variable [hM : M ⊨ Axioms.ACVF]

theorem distanceLe_iff {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (r a s : VFType (M := M)) : distanceLe r.val a.val s.val ↔ v (r - a) ≤ v (s - a) := by
  rw [distanceLe_realize]
  have hr : (r - a).val = iVFAdd r.val (iVFNeg a.val) := by rw [sub_eq_add_neg]; rfl
  have hs : (s - a).val = iVFAdd s.val (iVFNeg a.val) := by rw [sub_eq_add_neg]; rfl
  have he := hv (r - a) (s - a)
  change iLe (iRv (s - a).val) (iRv (r - a).val) ↔ _ at he
  rw [hr, hs] at he
  exact he

end SpecialTransformations.Section3.NearestRootSyntax

set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.NearestRootSyntax
variable {M : Type} [LRV.Structure M]

def nearest (R A : Set M) : Set M :=
  {r | r ∈ R ∧ ∃ a ∈ A, ∀ s ∈ R, distanceLe r a s}

/-- Nearest-root selection names only the original definable sets R and A,
never a containing ball or any chosen member of the finite root set. -/
theorem nearest_definable (S R A : Set M) (hR : S.Definable₁ LRV R)
    (hA : S.Definable₁ LRV A) : S.Definable₁ LRV (nearest R A) := by
  let idx : Fin 3 → Fin 2 ⊕ Fin 1 := ![.inl 0, .inl 1, .inr 0]
  have hp := (distanceLe_definable S).preimage_comp idx
  have hr := hR.preimage_comp (Sum.inr : Fin 1 → Fin 2 ⊕ Fin 1)
  have hall := (hr.himp hp).forall_of_finite
  have hinner : S.Definable LRV {z : Fin 2 → M | ∀ s ∈ R, distanceLe (z 0) (z 1) s} := by
    convert hall using 1
    ext z
    change (∀ s ∈ R, distanceLe (z 0) (z 1) s) ↔
      ∀ u : Fin 1 → M, u 0 ∈ R → distanceLe (z 0) (z 1) (u 0)
    exact ⟨fun h u => h (u 0), fun h s => h ![s]⟩
  let jdx : Fin 2 → Fin 1 ⊕ Fin 1 := ![.inl 0, .inr 0]
  have hi := hinner.preimage_comp jdx
  have ha := hA.preimage_comp (Sum.inr : Fin 1 → Fin 1 ⊕ Fin 1)
  have hex := (ha.inter hi).exists_of_finite
  have houter : S.Definable LRV {z : Fin 1 → M | ∃ a ∈ A, ∀ s ∈ R, distanceLe (z 0) a s} := by
    convert hex using 1
    ext z
    change (∃ a ∈ A, ∀ s ∈ R, distanceLe (z 0) a s) ↔
      ∃ u : Fin 1 → M, u 0 ∈ A ∧ ∀ s ∈ R, distanceLe (z 0) (u 0) s
    exact ⟨fun ⟨a, ha, h⟩ => ⟨![a], ha, h⟩, fun ⟨u, hu, h⟩ => ⟨u 0, hu, h⟩⟩
  exact hR.inter houter

variable [hM : M ⊨ Axioms.ACVF]

theorem nearest_eq_image {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (R : Finset (VFType (M := M))) (A : Set M) (hA : A ⊆ {a | iVF a}) :
    nearest (Subtype.val '' (R : Set (VFType (M := M)))) A =
      Subtype.val '' (Balls.nearestRoots v R {a : VFType (M := M) | a.val ∈ A} :
        Set (VFType (M := M))) := by
  ext z
  change ((∃ r : VFType (M := M), r ∈ R ∧ r.val = z) ∧
    ∃ a ∈ A, ∀ s ∈ Subtype.val '' (R : Set (VFType (M := M))), distanceLe z a s) ↔ _
  constructor
  · rintro ⟨⟨r, hr, rfl⟩, a, ha, hnear⟩
    let a' : VFType (M := M) := ⟨a, hA ha⟩
    refine ⟨r, Finset.mem_filter.mpr ⟨hr, a', ha, ?_⟩, rfl⟩
    intro s hs
    exact (distanceLe_iff v hv r a' s).mp (hnear s.val ⟨s, hs, rfl⟩)
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨hrR, a, ha, hnear⟩ := Finset.mem_filter.mp hr
    refine ⟨⟨r, hrR, rfl⟩, a.val, ha, ?_⟩
    rintro s ⟨s', hs, rfl⟩
    exact (distanceLe_iff v hv r a s').mpr (hnear s' hs)

end SpecialTransformations.Section3.NearestRootSyntax
