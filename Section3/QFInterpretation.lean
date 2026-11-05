import Section3.RepresentativeDefinability
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.RVRepresentatives
open ValuedDefinability
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ a b : VFType (M := M), VFValued.predV a b ↔ v a ≤ v b)

theorem decode_sorted (s : SortTag) (x : VFType (M := M)) : sortEval s (decode s x) := by
  cases s with
  | vf => exact x.property
  | rv => exact rv_mem hM x.property

omit hM in
private theorem rel1 {α : Type} {n : ℕ} (R : Rel 1)
    (ts : Fin 1 → LRV.Term (α ⊕ Fin n)) (u : α → M) (x : Fin n → M) :
    (BoundedFormula.rel R ts).Realize u x ↔
      Structure.RelMap (L := LRV) R ![(ts 0).realize (Sum.elim u x)] := by
  change Structure.RelMap (L := LRV) R _ ↔ _
  have he : (fun i => (ts i).realize (Sum.elim u x)) =
      (![(ts 0).realize (Sum.elim u x)] : Fin 1 → M) := by
    funext i; fin_cases i; rfl
  rw [he]

omit hM in
private theorem rel2 {α : Type} {n : ℕ} (R : Rel 2)
    (ts : Fin 2 → LRV.Term (α ⊕ Fin n)) (u : α → M) (x : Fin n → M) :
    (BoundedFormula.rel R ts).Realize u x ↔
      Structure.RelMap (L := LRV) R
        ![(ts 0).realize (Sum.elim u x), (ts 1).realize (Sum.elim u x)] := by
  change Structure.RelMap (L := LRV) R _ ↔ _
  have he : (fun i => (ts i).realize (Sum.elim u x)) =
      (![(ts 0).realize (Sum.elim u x), (ts 1).realize (Sum.elim u x)] : Fin 2 → M) := by
    funext i; fin_cases i <;> rfl
  rw [he]

include hv in
theorem qf_definable {α β : Type} {n : ℕ} (sα : α → SortTag) (sn : Fin n → SortTag)
    (u : (β → VFType (M := M)) → α → VFType (M := M))
    (x : (β → VFType (M := M)) → Fin n → VFType (M := M))
    (hu : ∀ i, FunDef v (fun z => u z i)) (hx : ∀ i, FunDef v (fun z => x z i))
    (φ : LRV.BoundedFormula α n) (hq : φ.IsQF) (hw : WellSorted sα sn φ) :
    SetDef v {z | φ.Realize (fun i => decode (sα i) (u z i))
      (fun i => decode (sn i) (x z i))} := by
  letI := FirstOrder.valStructure v
  let T (t : LRV.Term (α ⊕ Fin n)) (z : β → VFType (M := M)) :=
    liftTerm v (Sum.elim (u z) (x z)) t
  have hT (t : LRV.Term (α ⊕ Fin n)) : FunDef v (T t) := by
    apply liftTerm_definable
    intro i
    cases i with
    | inl i => exact hu i
    | inr i => exact hx i
  have hreal (t : LRV.Term (α ⊕ Fin n)) (σ : SortTag)
      (ht : TmSort sα sn t = some σ) (z : β → VFType (M := M)) :
      decode σ (T t z) = t.realize (Sum.elim
        (fun i => decode (sα i) (u z i)) (fun i => decode (sn i) (x z i))) := by
    have hh := liftTerm_correct v hv sα sn (Sum.elim (u z) (x z)) t σ ht
    have he : (fun i => decode (Sum.elim sα sn i) ((Sum.elim (u z) (x z)) i)) =
        Sum.elim (fun i => decode (sα i) (u z i)) (fun i => decode (sn i) (x z i)) := by
      funext i; cases i <;> rfl
    rw [he] at hh
    exact hh
  induction hq with
  | falsum => exact Set.definable_empty
  | of_isAtomic ha =>
    cases ha with
    | equal t t' =>
      cases hw with
      | @equal _ _ _ _ σ ht ht' =>
        cases σ with
        | vf =>
          change (Set.univ : Set (VFType (M := M))).Definable Language.val _
          convert (hT t).ofPred_eq (hT t') using 1
          ext z
          change t.realize _ = t'.realize _ ↔ T t z = T t' z
          rw [← hreal t .vf ht z, ← hreal t' .vf ht' z]
          exact Subtype.val_inj
        | rv =>
          change (Set.univ : Set (VFType (M := M))).Definable Language.val _
          convert rv_eq_definable v hv (hT t) (hT t') using 1
          ext z
          change t.realize _ = t'.realize _ ↔ _
          rw [← hreal t .rv ht z, ← hreal t' .rv ht' z]
          rfl
    | rel R ts =>
      cases hw with
      | rel _ _ _ hts =>
        cases R with
        | memVF =>
          change (Set.univ : Set (VFType (M := M))).Definable Language.val _
          have hd : (Set.univ : Set (VFType (M := M))).Definable Language.val
              (Set.univ : Set (β → VFType (M := M))) := Set.definable_univ
          convert hd using 1
          ext z
          simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
          apply (rel1 .memVF ts _ _).mpr
          change iVF ((ts 0).realize _)
          rw [← hreal (ts 0) .vf (hts 0) z]
          exact (T (ts 0) z).property
        | memRV =>
          change (Set.univ : Set (VFType (M := M))).Definable Language.val _
          have hd : (Set.univ : Set (VFType (M := M))).Definable Language.val
              (Set.univ : Set (β → VFType (M := M))) := Set.definable_univ
          convert hd using 1
          ext z
          simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
          apply (rel1 .memRV ts _ _).mpr
          change iRV ((ts 0).realize _)
          rw [← hreal (ts 0) .rv (hts 0) z]
          exact rv_mem hM (T (ts 0) z).property
        | memUnits =>
          change (Set.univ : Set (VFType (M := M))).Definable Language.val _
          convert ValuedDefinability.val_eq_one v (hT (ts 0)) using 1
          ext z
          simp only [Set.mem_ofPred_eq]
          apply (rel1 .memUnits ts _ _).trans
          change iUnits ((ts 0).realize _) ↔ _
          rw [← hreal (ts 0) .rv (hts 0) z]
          exact CanonicalResidue.units_encodedRv_iff v hv (T (ts 0) z)
        | rvLe =>
          change (Set.univ : Set (VFType (M := M))).Definable Language.val _
          convert ValuedDefinability.val_le v (hT (ts 1)) (hT (ts 0)) using 1
          ext z
          simp only [Set.mem_ofPred_eq]
          apply (rel2 .rvLe ts _ _).trans
          change iLe ((ts 0).realize _) ((ts 1).realize _) ↔ _
          rw [← hreal (ts 0) .rv (hts 0) z, ← hreal (ts 1) .rv (hts 1) z]
          exact hv (T (ts 1) z) (T (ts 0) z)
  | @imp φ ψ hφ hψ ihφ ihψ =>
    cases hw with
    | imp _ hwφ hwψ => exact (ihφ hwφ).himp (ihψ hwψ)

end SpecialTransformations.Section3.RVRepresentatives
