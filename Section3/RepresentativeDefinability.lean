import Section3.LiftTerms
import Section3.ValuedDefinability
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.RVRepresentatives
open ValuedDefinability
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ a b : VFType (M := M), VFValued.predV a b ↔ v a ≤ v b)
variable {β : Type}

theorem inResidue_definable {f : (β → VFType (M := M)) → VFType (M := M)}
    (hf : FunDef v f) : SetDef v {x | InResidue v (f x)} := by
  letI := FirstOrder.valStructure v
  exact (ValuedDefinability.val_eq_one v hf).union
    (hf.ofPred_eq (ValuedDefinability.constant v 0))

theorem add_definable {f g : (β → VFType (M := M)) → VFType (M := M)}
    (hf : FunDef v f) (hg : FunDef v g) : FunDef v (fun x => add v (f x) (g x)) := by
  letI := FirstOrder.valStructure v
  have hsum := ValuedDefinability.add v hf hg
  exact Set.DefinableFun.ite
    ((inResidue_definable v hf).inter (inResidue_definable v hg))
    (Set.DefinableFun.ite (hf.ofPred_eq (ValuedDefinability.constant v 0)) hg
      (Set.DefinableFun.ite (hg.ofPred_eq (ValuedDefinability.constant v 0)) hf
        (Set.DefinableFun.ite (ValuedDefinability.val_eq_one v hsum) hsum
          (ValuedDefinability.constant v 0)))) (ValuedDefinability.constant v 0)


theorem neg_definable {f : (β → VFType (M := M)) → VFType (M := M)}
    (hf : FunDef v f) : FunDef v (fun x => neg v (f x)) := by
  letI := FirstOrder.valStructure v
  exact Set.DefinableFun.ite (ValuedDefinability.val_eq_one v hf) (ValuedDefinability.neg v hf)
    (ValuedDefinability.constant v 0)

theorem liftFn_definable {k : ℕ} (f : Fn k)
    (x : (β → VFType (M := M)) → Fin k → VFType (M := M))
    (hx : ∀ i, FunDef v (fun z => x z i)) : FunDef v (fun z => liftFn v f (x z)) := by
  cases f with
  | vfZero => exact ValuedDefinability.constant v 0
  | rvZero => exact ValuedDefinability.constant v 0
  | vfOne => exact ValuedDefinability.constant v 1
  | rvOne => exact ValuedDefinability.constant v 1
  | vfAdd => exact ValuedDefinability.add v (hx 0) (hx 1)
  | vfMul => exact ValuedDefinability.mul v (hx 0) (hx 1)
  | rvMul => exact ValuedDefinability.mul v (hx 0) (hx 1)
  | vfNeg => exact ValuedDefinability.neg v (hx 0)
  | rvInv => exact ValuedDefinability.inv v (hx 0)
  | kAdd => exact add_definable v (hx 0) (hx 1)
  | kNeg => exact neg_definable v (hx 0)
  | rvMap => exact hx 0

theorem liftTerm_definable {α : Type} (w : (β → VFType (M := M)) → α → VFType (M := M))
    (hw : ∀ i, FunDef v (fun z => w z i)) (t : LRV.Term α) :
    FunDef v (fun z => liftTerm v (w z) t) := by
  induction t with
  | var i => exact hw i
  | func f ts ih => exact liftFn_definable v f _ ih

include hv in
theorem rv_eq_iff (a b : VFType (M := M)) :
    iRv a.val = iRv b.val ↔
      (a = 0 ∧ b = 0) ∨ (b ≠ 0 ∧ ¬ v b ≤ v (a - b)) := by
  by_cases hb : b = 0
  · subst b
    rw [show iRv (0 : VFType (M := M)).val = iRVZero from RVCalc.rv_zero_eq hM]
    constructor
    · intro h
      exact Or.inl ⟨(CanonicalRV.encodedRv_zero_iff a).mp h, rfl⟩
    · rintro (⟨ha, _⟩ | ⟨h, _⟩)
      · subst a; exact RVCalc.rv_zero_eq hM
      · exact (h rfl).elim
  · have hb' : b.val ≠ iVFZero := by
      intro h; exact hb (Subtype.ext h)
    rw [CanonicalRV.encoded_eq_iff_close a.property b.property hb']
    have he : iLe (iRv (iVFAdd a.val (iVFNeg b.val))) (iRv b.val) ↔
        v b ≤ v (a - b) := hv b (a - b)
    rw [he]
    simp [hb]

include hv in
theorem rv_eq_definable {f g : (β → VFType (M := M)) → VFType (M := M)}
    (hf : FunDef v f) (hg : FunDef v g) :
    SetDef v {x | iRv (f x).val = iRv (g x).val} := by
  letI := FirstOrder.valStructure v
  have hz := (hf.ofPred_eq (ValuedDefinability.constant v 0)).inter
    (hg.ofPred_eq (ValuedDefinability.constant v 0))
  have hn := (hg.ofPred_eq (ValuedDefinability.constant v 0)).compl
  have hc := (ValuedDefinability.val_le v hg
    (ValuedDefinability.add v hf (ValuedDefinability.neg v hg))).compl
  change (Set.univ : Set (VFType (M := M))).Definable Language.val _
  convert hz.union (hn.inter hc) using 1
  ext x
  simpa only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff,
    Set.mem_ofPred_eq, sub_eq_add_neg] using rv_eq_iff v hv (f x) (g x)

end SpecialTransformations.Section3.RVRepresentatives
