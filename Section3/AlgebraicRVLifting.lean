module

public import QESaturatedExtension
public import Section3.AlgebraicBaseGeometry
public import Section3.AngularPattern
public import Section3.FieldBase
public import Section3.InfiniteValueFibres
public import Section3.QFInterpretation

@[expose] public section

/- Component: CoefficientInterpretation -/
/-!
Coefficient-sensitive form of the checked valued representative interpretation.
Adapted from Section3.ValuedDefinability, RepresentativeDefinability and
QFInterpretation. It keeps the named coefficient subfield in the actual
definability statement instead of enlarging it to the whole ambient VF.
No new language or semantic representative choice is introduced.
-/
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.ValuedOver
variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (F : Subfield K)
variable {α : Type}

abbrev FunDef (f : (α → K) → K) : Prop :=
  letI := FirstOrder.valStructure v
  (F : Set K).DefinableFun Language.val f

abbrev SetDef (s : Set (α → K)) : Prop :=
  letI := FirstOrder.valStructure v
  (F : Set K).Definable Language.val s

abbrev MapDef {β : Type} (f : (α → K) → β → K) : Prop :=
  letI := FirstOrder.valStructure v
  (F : Set K).DefinableMap Language.val f

theorem constant (a : K) (ha : a ∈ F) : FunDef v F
    (fun _ : α → K => a) := by
  letI := FirstOrder.valStructure v
  exact Language.val.definableFun_const α ha

theorem zero : FunDef v F (fun _ : α → K => 0) := constant v F 0 F.zero_mem
theorem one : FunDef v F (fun _ : α → K => 1) := constant v F 1 F.one_mem

theorem add {f g : (α → K) → K}
    (hf : FunDef v F f)
    (hg : FunDef v F g) :
    FunDef v F (fun x => f x + g x) := by
  letI := FirstOrder.valStructure v
  have h := (Set.DefinableFun.fun_symbol (M := K) (L := Language.val) ValFunc.add).of_empty
    (A := (F : Set K))
  exact h.comp (show MapDef v F
    (fun x => ![f x, g x]) from by intro i; fin_cases i; exact hf; exact hg)

theorem mul {f g : (α → K) → K}
    (hf : FunDef v F f)
    (hg : FunDef v F g) :
    FunDef v F (fun x => f x * g x) := by
  letI := FirstOrder.valStructure v
  have h := (Set.DefinableFun.fun_symbol (M := K) (L := Language.val) ValFunc.mul).of_empty
    (A := (F : Set K))
  exact h.comp (show MapDef v F
    (fun x => ![f x, g x]) from by intro i; fin_cases i; exact hf; exact hg)

theorem neg {f : (α → K) → K}
    (hf : FunDef v F f) :
    FunDef v F (fun x => -f x) := by
  letI := FirstOrder.valStructure v
  have h := (Set.DefinableFun.fun_symbol (M := K) (L := Language.val) ValFunc.neg).of_empty
    (A := (F : Set K))
  exact h.comp (show MapDef v F
    (fun x => ![f x]) from by intro i; fin_cases i; exact hf)

theorem val_le {f g : (α → K) → K}
    (hf : FunDef v F f)
    (hg : FunDef v F g) :
    SetDef v F {x | v (f x) ≤ v (g x)} := by
  letI := FirstOrder.valStructure v
  have h : SetDef v F
      {x : Fin 2 → K | v (x 0) ≤ v (x 1)} := by
    change (F : Set K).Definable Language.val _
    rw [Set.definable_iff_exists_formula_sum]
    exact ⟨.rel ValRel.le (fun i => .var (.inl (.inr i))), rfl⟩
  exact h.preimage_map (show MapDef v F
    (fun x => ![f x, g x]) from by intro i; fin_cases i; exact hf; exact hg)

theorem val_eq_one {f : (α → K) → K}
    (hf : FunDef v F f) :
    SetDef v F {x | v (f x) = 1} := by
  letI := FirstOrder.valStructure v
  have h1 := one v F (α := α)
  change (F : Set K).Definable Language.val _
  convert (val_le v F hf h1).inter (val_le v F h1 hf) using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, map_one, le_antisymm_iff]

theorem inv {f : (α → K) → K}
    (hf : FunDef v F f) :
    FunDef v F (fun x => (f x)⁻¹) := by
  letI := FirstOrder.valStructure v
  have hinv : FunDef v F
      (fun x : Fin 1 → K => (x 0)⁻¹) := by
    let a (w : Option (Fin 1) → K) := w (some 0)
    let b (w : Option (Fin 1) → K) := w none
    have ha : FunDef v F a := Set.DefinableFun.proj Language.val
    have hb : FunDef v F b := Set.DefinableFun.proj Language.val
    have h0 := (ha.ofPred_eq (zero v F)).inter (hb.ofPred_eq (zero v F))
    have h1 := (mul v F ha hb).ofPred_eq (one v F)
    have he : Function.tupleGraph (fun x : Fin 1 → K => (x 0)⁻¹) =
        {w | a w = 0 ∧ b w = 0} ∪ {w | a w * b w = 1} := by
      ext w
      change (a w)⁻¹ = b w ↔ (a w = 0 ∧ b w = 0) ∨ a w * b w = 1
      by_cases hz : a w = 0
      · simp [hz, eq_comm]
      · constructor
        · intro hi
          exact Or.inr (by rw [← hi, mul_inv_cancel₀ hz])
        · rintro (⟨h, _⟩ | h)
          · exact (hz h).elim
          · calc
              (a w)⁻¹ = (a w)⁻¹ * (a w * b w) := by rw [h, mul_one]
              _ = b w := by rw [← mul_assoc, inv_mul_cancel₀ hz, one_mul]
    change SetDef v F _
    rw [he]
    exact h0.union h1
  exact hinv.comp (show MapDef v F
    (fun x => ![f x]) from by intro i; fin_cases i; exact hf)

end SpecialTransformations.Section3.ValuedOver

namespace SpecialTransformations.Section3.RVRepresentatives.Over
open ValuedOver
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ) (F : Subfield (VFType (M := M)))
    (hv : ∀ a b : VFType (M := M), VFValued.predV a b ↔ v a ≤ v b)
variable {β : Type}

theorem inResidue_definable {f : (β → VFType (M := M)) → VFType (M := M)}
    (hf : FunDef v F f) : SetDef v F {x | InResidue v (f x)} := by
  letI := FirstOrder.valStructure v
  exact (ValuedOver.val_eq_one v F hf).union
    (hf.ofPred_eq (ValuedOver.zero v F))

theorem add_definable {f g : (β → VFType (M := M)) → VFType (M := M)}
    (hf : FunDef v F f) (hg : FunDef v F g) : FunDef v F (fun x => add v (f x) (g x)) := by
  letI := FirstOrder.valStructure v
  have hsum := ValuedOver.add v F hf hg
  exact Set.DefinableFun.ite
    ((inResidue_definable v F hf).inter (inResidue_definable v F hg))
    (Set.DefinableFun.ite (hf.ofPred_eq (ValuedOver.zero v F)) hg
      (Set.DefinableFun.ite (hg.ofPred_eq (ValuedOver.zero v F)) hf
        (Set.DefinableFun.ite (ValuedOver.val_eq_one v F hsum) hsum
          (ValuedOver.zero v F)))) (ValuedOver.zero v F)


theorem neg_definable {f : (β → VFType (M := M)) → VFType (M := M)}
    (hf : FunDef v F f) : FunDef v F (fun x => neg v (f x)) := by
  letI := FirstOrder.valStructure v
  exact Set.DefinableFun.ite (ValuedOver.val_eq_one v F hf) (ValuedOver.neg v F hf)
    (ValuedOver.zero v F)

theorem liftFn_definable {k : ℕ} (f : Fn k)
    (x : (β → VFType (M := M)) → Fin k → VFType (M := M))
    (hx : ∀ i, FunDef v F (fun z => x z i)) : FunDef v F (fun z => liftFn v f (x z)) := by
  cases f with
  | vfZero => exact ValuedOver.zero v F
  | rvZero => exact ValuedOver.zero v F
  | vfOne => exact ValuedOver.one v F
  | rvOne => exact ValuedOver.one v F
  | vfAdd => exact ValuedOver.add v F (hx 0) (hx 1)
  | vfMul => exact ValuedOver.mul v F (hx 0) (hx 1)
  | rvMul => exact ValuedOver.mul v F (hx 0) (hx 1)
  | vfNeg => exact ValuedOver.neg v F (hx 0)
  | rvInv => exact ValuedOver.inv v F (hx 0)
  | kAdd => exact add_definable v F (hx 0) (hx 1)
  | kNeg => exact neg_definable v F (hx 0)
  | rvMap => exact hx 0

theorem liftTerm_definable {α : Type} (w : (β → VFType (M := M)) → α → VFType (M := M))
    (hw : ∀ i, FunDef v F (fun z => w z i)) (t : LRV.Term α) :
    FunDef v F (fun z => liftTerm v (w z) t) := by
  induction t with
  | var i => exact hw i
  | func f ts ih => exact liftFn_definable v F f _ ih

include hv in
theorem rv_eq_definable {f g : (β → VFType (M := M)) → VFType (M := M)}
    (hf : FunDef v F f) (hg : FunDef v F g) :
    SetDef v F {x | iRv (f x).val = iRv (g x).val} := by
  letI := FirstOrder.valStructure v
  have hz := (hf.ofPred_eq (ValuedOver.zero v F)).inter
    (hg.ofPred_eq (ValuedOver.zero v F))
  have hn := (hg.ofPred_eq (ValuedOver.zero v F)).compl
  have hc := (ValuedOver.val_le v F hg
    (ValuedOver.add v F hf (ValuedOver.neg v F hg))).compl
  change (F : Set (VFType (M := M))).Definable Language.val _
  convert hz.union (hn.inter hc) using 1
  ext x
  simpa only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff,
    Set.mem_ofPred_eq, sub_eq_add_neg] using rv_eq_iff v hv (f x) (g x)

end SpecialTransformations.Section3.RVRepresentatives.Over

namespace SpecialTransformations.Section3.RVRepresentatives.Over
open ValuedOver
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ) (F : Subfield (VFType (M := M)))
    (hv : ∀ a b : VFType (M := M), VFValued.predV a b ↔ v a ≤ v b)

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
    (hu : ∀ i, FunDef v F (fun z => u z i)) (hx : ∀ i, FunDef v F (fun z => x z i))
    (φ : LRV.BoundedFormula α n) (hq : φ.IsQF) (hw : WellSorted sα sn φ) :
    SetDef v F {z | φ.Realize (fun i => decode (sα i) (u z i))
      (fun i => decode (sn i) (x z i))} := by
  letI := FirstOrder.valStructure v
  let T (t : LRV.Term (α ⊕ Fin n)) (z : β → VFType (M := M)) :=
    liftTerm v (Sum.elim (u z) (x z)) t
  have hT (t : LRV.Term (α ⊕ Fin n)) : FunDef v F (T t) := by
    apply liftTerm_definable v F
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
          change (F : Set (VFType (M := M))).Definable Language.val _
          convert (hT t).ofPred_eq (hT t') using 1
          ext z
          change t.realize _ = t'.realize _ ↔ T t z = T t' z
          rw [← hreal t .vf ht z, ← hreal t' .vf ht' z]
          exact Subtype.val_inj
        | rv =>
          change (F : Set (VFType (M := M))).Definable Language.val _
          convert rv_eq_definable v F hv (hT t) (hT t') using 1
          ext z
          change t.realize _ = t'.realize _ ↔ _
          rw [← hreal t .rv ht z, ← hreal t' .rv ht' z]
          rfl
    | rel R ts =>
      cases hw with
      | rel _ _ _ hts =>
        cases R with
        | memVF =>
          change (F : Set (VFType (M := M))).Definable Language.val _
          have hd : (F : Set (VFType (M := M))).Definable Language.val
              (Set.univ : Set (β → VFType (M := M))) := Set.definable_univ
          convert hd using 1
          ext z
          simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
          apply (rel1 .memVF ts _ _).mpr
          change iVF ((ts 0).realize _)
          rw [← hreal (ts 0) .vf (hts 0) z]
          exact (T (ts 0) z).property
        | memRV =>
          change (F : Set (VFType (M := M))).Definable Language.val _
          have hd : (F : Set (VFType (M := M))).Definable Language.val
              (Set.univ : Set (β → VFType (M := M))) := Set.definable_univ
          convert hd using 1
          ext z
          simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
          apply (rel1 .memRV ts _ _).mpr
          change iRV ((ts 0).realize _)
          rw [← hreal (ts 0) .rv (hts 0) z]
          exact rv_mem hM (T (ts 0) z).property
        | memUnits =>
          change (F : Set (VFType (M := M))).Definable Language.val _
          convert ValuedOver.val_eq_one v F (hT (ts 0)) using 1
          ext z
          simp only [Set.mem_ofPred_eq]
          apply (rel1 .memUnits ts _ _).trans
          change iUnits ((ts 0).realize _) ↔ _
          rw [← hreal (ts 0) .rv (hts 0) z]
          exact CanonicalResidue.units_encodedRv_iff v hv (T (ts 0) z)
        | rvLe =>
          change (F : Set (VFType (M := M))).Definable Language.val _
          convert ValuedOver.val_le v F (hT (ts 1)) (hT (ts 0)) using 1
          ext z
          simp only [Set.mem_ofPred_eq]
          apply (rel2 .rvLe ts _ _).trans
          change iLe ((ts 0).realize _) ((ts 1).realize _) ↔ _
          rw [← hreal (ts 0) .rv (hts 0) z, ← hreal (ts 1) .rv (hts 1) z]
          exact hv (T (ts 1) z) (T (ts 0) z)
  | @imp φ ψ hφ hψ ihφ ihψ =>
    cases hw with
    | imp _ hwφ hwψ => exact (ihφ hwφ).himp (ihψ hwψ)

end SpecialTransformations.Section3.RVRepresentatives.Over

/- Component: CoefficientRVGeometry -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.CoefficientRVGeometry
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
include hv

/-- A distinct leading term prevents cancellation at the center's scale. -/
theorem distance_eq_max (x c : VFType (M := M))
    (hxc : CanonicalRV.encodedRv x ≠ CanonicalRV.encodedRv c) :
    v (x-c) = max (v x) (v c) := by
  by_cases hc : c = 0
  · simp only [hc,sub_zero,map_zero,max_eq_left zero_le]
  have hcle : v c ≤ v (x-c) := le_of_not_gt (fun h =>
    hxc (Subtype.ext (Balls.rv_eq_of_sub_lt v hv x c hc h)))
  have hxle : v x ≤ v (x-c) := by
    have he : x = (x-c)+c := by ring
    calc
      v x = v ((x-c)+c) := congrArg v he
      _ ≤ v (x-c) := v.map_add_le le_rfl hcle
  exact le_antisymm (v.map_sub_le (le_max_left _ _) (le_max_right _ _))
    (max_le hxle hcle)

variable {K : Type} [Field K] (f : K →+* VFType (M := M))

/-- Each coefficient-field ball has a coefficient-field center whose RV
class is its only possible angular exception in a fixed value fibre. -/
theorem coefficient_ball_pattern (B : Set (VFType (M := M)))
    (hB : ValOneEC.IsKBall f v B) :
    ∃ c : K, ∀ x y : VFType (M := M), v x = v y →
      CanonicalRV.encodedRv x ≠ CanonicalRV.encodedRv (f c) →
      CanonicalRV.encodedRv y ≠ CanonicalRV.encodedRv (f c) →
      (x ∈ B ↔ y ∈ B) := by
  cases hB with
  | closed a b =>
    refine ⟨a,fun x y hxy hx hy => ?_⟩
    change v (x-f a) ≤ v (f b) ↔ v (y-f a) ≤ v (f b)
    rw [distance_eq_max v hv x (f a) hx,distance_eq_max v hv y (f a) hy,hxy]
  | openball a b =>
    refine ⟨a,fun x y hxy hx hy => ?_⟩
    change v (x-f a) < v (f b) ↔ v (y-f a) < v (f b)
    rw [distance_eq_max v hv x (f a) hx,distance_eq_max v hv y (f a) hy,hxy]
  | univ => exact ⟨0,fun _ _ _ _ _ => Iff.rfl⟩

/-- A Boolean combination over a coefficient field has a finite set of
angular exceptions, and every exceptional RV class has a lift in that field.
The centers are proof data, not additional parameters. -/
theorem finite_exceptions (U : Set (VFType (M := M)))
    (hU : ValOneEC.Good f v U) :
    ∃ T : Set (CanonicalRV.RVSort M), T.Finite ∧
      (∀ t ∈ T, ∃ c : K, CanonicalRV.encodedRv (f c) = t) ∧
      ∀ x y : VFType (M := M), v x = v y →
        CanonicalRV.encodedRv x ∉ T → CanonicalRV.encodedRv y ∉ T →
        (x ∈ U ↔ y ∈ U) := by
  obtain ⟨ι,hι,B,b,hB,hb⟩ := hU
  letI := hι
  choose c hc using fun i => coefficient_ball_pattern v hv f (B i) (hB i)
  let T : Set (CanonicalRV.RVSort M) := Set.range (fun i => CanonicalRV.encodedRv (f (c i)))
  refine ⟨T,Set.finite_range _,?_,?_⟩
  · rintro t ⟨i,rfl⟩
    exact ⟨c i,rfl⟩
  · intro x y hxy hx hy
    have hp : {i | x ∈ B i} = {i | y ∈ B i} := by
      ext i
      exact hc i x y hxy
        (fun he => hx ⟨i,he.symm⟩) (fun he => hy ⟨i,he.symm⟩)
    rw [hb x,hb y,hp]

/-- A finite RV set whose full VF preimage has coefficient-field ball
geometry has lifts in that field. Its restricted valuation may be trivial. -/
theorem finite_rv_set_lifts (h00 : M ⊨ Axioms.ACVF00)
    (A : Set (CanonicalRV.RVSort M)) (hA : A.Finite)
    (hU : ValOneEC.Good f v {x | CanonicalRV.encodedRv x ∈ A}) :
    ∀ t ∈ A, ∃ c : K, CanonicalRV.encodedRv (f c) = t := by
  obtain ⟨T,hT,hTK,hpattern⟩ := finite_exceptions v hv f _ hU
  intro t ht
  by_cases ht0 : t.val = iRVZero
  · refine ⟨0,Subtype.ext ?_⟩
    rw [map_zero]
    exact ((CanonicalRV.encodedRv_zero_iff _).mpr rfl).trans ht0.symm
  by_cases htT : t ∈ T
  · exact hTK t htT
  let γ : Values.Gamma (M := M) := ⟨Values.vrv t,fun h =>
    ht0 ((Values.vrv_eq_infinity_iff t).mp h)⟩
  obtain ⟨u,huγ,hu⟩ := ((Values.infinite_gamma_fibre h00 γ).sdiff (hA.union hT)).nonempty
  obtain ⟨x,hx⟩ := CanonicalRV.encodedRv_surjective t
  obtain ⟨y,hy⟩ := CanonicalRV.encodedRv_surjective u
  have hxy : v x = v y := (Values.vf_value_eq_iff v hv x y).mp (by
    rw [hx,hy]
    exact huγ.symm)
  have hxT : CanonicalRV.encodedRv x ∉ T := by rw [hx]; exact htT
  have hyT : CanonicalRV.encodedRv y ∉ T := by rw [hy]; exact fun h => hu (Or.inr h)
  have hxA : x ∈ {x | CanonicalRV.encodedRv x ∈ A} := by
    change CanonicalRV.encodedRv x ∈ A
    rw [hx]
    exact ht
  have hmem := (hpattern x y hxy hxT hyT).mp hxA
  change CanonicalRV.encodedRv y ∈ A at hmem
  rw [hy] at hmem
  exact (hu (Or.inl hmem)).elim

end SpecialTransformations.Section3.CoefficientRVGeometry

/- Component: AlgebraicRVLifting -/
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3

/-- The valued-language C-minimality wrapper retains the actual coefficient
subfield of a definable set. No nontriviality of that subfield is assumed. -/
theorem c_minimal_valued_definable_subfield {N Γ : Type}
    [Field N] [IsAlgClosed N] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation N Γ) (hnt : ∃ x : N, x ≠ 0 ∧ v x ≠ 1)
    (F : Subfield N) [IsAlgClosed F] (U : Set N)
    (hU : @Set.Definable₁ N (F : Set N) Language.val (FirstOrder.valStructure v) U) :
    ValOneEC.Good F.subtype v U := by
  letI := FirstOrder.valStructure v
  obtain ⟨φ,hφ⟩ := Set.definable_iff_exists_formula_sum.mp hU
  let ψ : Language.val.BoundedFormula F 1 := BoundedFormula.relabel id φ
  have heval (x : N) : ValOneEC.Holds v F.subtype ψ x ↔ x ∈ U := by
    change ψ.Realize F.subtype (fun _ => x) ↔ x ∈ U
    dsimp only [ψ]
    rw [BoundedFormula.realize_relabel]
    have hx : ((fun _ : Fin 1 => x) ∘ Fin.natAdd 1 : Fin 0 → N) = Fin.elim0 := by
      funext i; exact i.elim0
    rw [hx]
    have he : (Sum.elim F.subtype ((fun _ : Fin 1 => x) ∘ Fin.castAdd 0) ∘ id) =
        Sum.elim (fun a : F => (a : N)) (fun _ => x) := by
      funext a; cases a <;> rfl
    rw [he]
    have hmem := congrArg (fun t : Set (Fin 1 → N) => (fun _ => x) ∈ t) hφ
    exact (Iff.of_eq hmem).symm
  have hgood := c_minimal_over_algebraically_closed_base v hnt F.subtype ψ
  have he : {x | ValOneEC.Holds v F.subtype ψ x} = U := by ext x; exact heval x
  rwa [he] at hgood

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)

include hv in
/-- Definability over VF parameters in F translates to valued definability
over F, without adjoining representatives of any external RV parameter. -/
theorem rv_preimage_definable_over_subfield (F : Subfield (VFType (M := M)))
    (S A : Set M) (hS : S ⊆ Subtype.val '' (F : Set (VFType (M := M))))
    (hA : DefinableAt S .rv A) :
    @Set.Definable₁ (VFType (M := M)) (F : Set (VFType (M := M))) Language.val
      (FirstOrder.valStructure v) {x | (CanonicalRV.encodedRv x).val ∈ A} := by
  letI := FirstOrder.valStructure v
  obtain ⟨⟨p,φ,hw,heq⟩,hsort⟩ := hA
  have hp (i : Fin p.length) : ∃ x : F, (x.val : VFType (M := M)).val = p.values i := by
    obtain ⟨x,hx,he⟩ := hS (p.mem_base i)
    exact ⟨⟨x,hx⟩,he⟩
  choose q hq using hp
  have hps (i : Fin p.length) : p.sorts i = .vf := by
    cases hi : p.sorts i with
    | vf => rfl
    | rv =>
      have hr : iRV (p.values i) := by simpa only [hi,sortEval,iRV] using p.sorted i
      have hvf : iVF (p.values i) := (hq i) ▸ (q i).val.property
      exact (TypedModelMap.not_rv_of_vf hvf hr).elim
  obtain ⟨ψ,hψq,hψw,hψ⟩ := theorem_2_3_quantifier_elimination
    (Fin p.length) p.sorts 1 (fun _ => .rv) φ hw
  have hdecode : (fun i => RVRepresentatives.decode (p.sorts i) (q i).val) = p.values := by
    funext i
    rw [hps i]
    exact hq i
  have hd := RVRepresentatives.Over.qf_definable v F hv p.sorts (fun _ : Fin 1 => .rv)
    (fun _ : Fin 1 → VFType (M := M) => fun i => (q i).val) (fun z => z)
    (fun i => ValuedOver.constant v F (q i).val (q i).property)
    (fun _ => Set.DefinableFun.proj Language.val) ψ hψq hψw
  rw [hdecode] at hd
  change (F : Set (VFType (M := M))).Definable Language.val
    {z : Fin 1 → VFType (M := M) | (CanonicalRV.encodedRv (z 0)).val ∈ A}
  convert hd using 1
  ext z
  have he := Set.ext_iff.mp heq ![(CanonicalRV.encodedRv (z 0)).val]
  change (CanonicalRV.encodedRv (z 0)).val ∈ A ↔
    ψ.Realize p.values (fun i => RVRepresentatives.decode .rv (z i))
  have hz : (fun i => RVRepresentatives.decode .rv (z i)) =
      (![(CanonicalRV.encodedRv (z 0)).val] : Fin 1 → M) := by
    funext i; fin_cases i; rfl
  rw [hz]
  exact he.trans (and_iff_right (by
    intro i; fin_cases i; exact (CanonicalRV.encodedRv (z 0)).property)) |>.trans
      (hψ M hM p.values _ p.sorted (by
        intro i; fin_cases i; exact (CanonicalRV.encodedRv (z 0)).property))

/-- RV algebraicity over parameters from an algebraically closed VF
subfield admits a lift in that field. This is independent of saturation
and does not assume its restricted valuation is nontrivial. -/
theorem algebraic_rv_lifts_algebraically_closed_subfield
    (h00 : M ⊨ Axioms.ACVF00) (F : Subfield (VFType (M := M))) [IsAlgClosed F]
    (S : Set M) (hS : S ⊆ Subtype.val '' (F : Set (VFType (M := M))))
    (t : CanonicalRV.RVSort M) (ht : AlgebraicAt S .rv t.val) :
    ∃ x : F, CanonicalRV.encodedRv x.val = t := by
  obtain ⟨A,hA,hfin,htA⟩ := ht
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  obtain ⟨ε,hε0,hε⟩ := ValuedFieldExtension.exists_nontrivial_predV (M := M)
  have hnt : ∃ x : VFType (M := M), x ≠ 0 ∧ v x ≠ 1 := by
    refine ⟨ε,hε0,fun he => hε ((hv 1 ε).mpr (by rw [map_one,he]))⟩
  let A' : Set (CanonicalRV.RVSort M) := {t | t.val ∈ A}
  have hA' : A'.Finite := hfin.preimage Subtype.val_injective.injOn
  have hd := rv_preimage_definable_over_subfield v hv F S A hS hA
  have hg := c_minimal_valued_definable_subfield v hnt F _ hd
  exact CoefficientRVGeometry.finite_rv_set_lifts v hv F.subtype h00 A' hA' hg t htA

end SpecialTransformations.Section3

/- Component: ValuedSubfieldEmbedding -/
open Classical FirstOrder FirstOrder.Language
namespace SpecialTransformations.Section3

/-- The actual valued-language embedding of a subfield with the restricted
valuation. Its function and relation interpretations are definitionally
the inherited field operations and valuation comparisons. -/
def valuedSubfieldEmbedding {N Γ : Type} [Field N] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation N Γ) (F : Subfield N) :
    letI := FirstOrder.valStructure v
    letI := FirstOrder.valStructure (v.comap F.subtype)
    F ↪[Language.val] N := by
  letI := FirstOrder.valStructure v
  letI := FirstOrder.valStructure (v.comap F.subtype)
  exact
    { toFun := fun x => x.val
      inj' := Subtype.val_injective
      map_fun' := by intro n f xs; cases f <;> rfl
      map_rel' := by intro n r xs; cases r; rfl }

/-- Checked valued QE makes a nontrivially valued algebraically closed
subfield elementary in an algebraically closed valued ambient field.
The restricted valuation's nontriviality remains an explicit premise. -/
noncomputable def valuedSubfieldElementary {N Γ : Type} [Field N] [IsAlgClosed N]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation N Γ)
    (F : Subfield N) [IsAlgClosed F]
    (hnt : ∃ x : F, x ≠ 0 ∧ v x.val ≠ 1) :
    letI := FirstOrder.valStructure v
    letI := FirstOrder.valStructure (v.comap F.subtype)
    F ↪ₑ[Language.val] N := by
  let vF := v.comap F.subtype
  letI := FirstOrder.valStructure v
  letI := FirstOrder.valStructure vF
  have hntN : ∃ x : N, x ≠ 0 ∧ v x ≠ 1 := by
    obtain ⟨x,hx,hv⟩ := hnt
    exact ⟨x.val,fun h => hx (Subtype.ext h),hv⟩
  have hntF : ∃ x : F, x ≠ 0 ∧ vF x ≠ 1 := hnt
  have hN : N ⊨ ValPM.ACVF_val := JohnsonValuedBridge.model_ACVF_val v hntN
  have hF : F ⊨ ValPM.ACVF_val := JohnsonValuedBridge.model_ACVF_val vF hntF
  let e := valuedSubfieldEmbedding v F
  refine { toFun := fun x => x.val, map_formula' := ?_ }
  intro n φ x
  obtain ⟨ψ,hq,heq⟩ := JohnsonValuedBridge.fullQE_ACVF_val (Fin n) 0 φ
  have hNφ : φ.Realize (fun i => (x i).val) ↔ Formula.Realize ψ (fun i => (x i).val) :=
    heq N hN (fun i => (x i).val) Fin.elim0
  have hFφ : φ.Realize x ↔ Formula.Realize ψ x := heq F hF x Fin.elim0
  exact hNφ.trans ((QESaturatedExtension.embedding_realize_formula_isQF e hq x).trans hFφ.symm)

end SpecialTransformations.Section3
