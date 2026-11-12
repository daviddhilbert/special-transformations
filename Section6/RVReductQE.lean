module

public import Section6.RVGraphLanguage
public import Section3.QuantifierFree
public import Section3.ParameterBridge
public import Section3.SortedBoolean

@[expose] public section

/-! Stable embeddedness in the form needed here: a definable subset of
RV has a quantifier-free definition using only RV symbols and the RV
parameters already in the original substructure. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section5

namespace SpecialTransformations.Section6.RVGraphLanguage

open RVAbstraction

variable {C : Type} [sC : LRV.Structure C] [hC : C ⊨ Axioms.ACVF]

private theorem vf_term_constant {α : Type} {n : ℕ} {s : α → SortTag}
    (v : α → C) (t : LRV.Term (α ⊕ Fin n))
    (ht : TmSort s (fun _ => .rv) t = some .vf) (x y : Fin n → C) :
    t.realize (Sum.elim v x) = t.realize (Sum.elim v y) := by
  induction t with
  | var i =>
    cases i with
    | inl _ => rfl
    | inr _ => simp [TmSort] at ht
  | func f ts ih =>
    rw [TmSort] at ht
    split at ht <;> rename_i hargs
    · have hs : Fn.resSort f = .vf := Option.some.inj ht
      have ha (i : Fin _) : Fn.argSort f i = .vf := by
        cases f <;> simp_all [Fn.argSort, Fn.resSort] <;> exact i.elim0
      change Structure.funMap (L := LRV) f _ = Structure.funMap (L := LRV) f _
      congr 1
      exact funext (fun i => ih i (by rw [← ha i]; exact hargs i))
    · contradiction

variable (S : LRV.Substructure C)

local notation "RVLang" => (RVBase[[SubRV (S : Set C)]])

private theorem zero_in_base : (iRVZero : C) ∈ S :=
  S.fun_mem Fn.rvZero Fin.elim0 (fun i => i.elim0)

private def frozen {n : ℕ} : Fin n → C := fun _ => iRVZero

private theorem term_in_base {α : Type} {v : α → C} (hv : ∀ i, v i ∈ S)
    (t : LRV.Term α) : t.realize v ∈ S := by
  induction t with
  | var i => exact hv i
  | func f _ ih => exact S.fun_mem f _ ih

private def rvConstant {n : ℕ} (b : SubRV (S : Set C)) : (RVLang).Term (Fin n) :=
  Constants.term (L := RVLang) (Sum.inr b)

private theorem rvConstant_realize {n : ℕ} (b : SubRV (S : Set C)) (u : Fin n → RV (M := C)) :
    @Term.realize RVLang (RV (M := C)) (ambientWithParameters S) (Fin n) u (rvConstant S b) = b.val :=
  rfl

private theorem rv_term_definition (p : Parameters (S : Set C)) {n : ℕ}
    (t : LRV.Term (Fin p.length ⊕ Fin n))
    (ht : TmSort p.sorts (fun _ => .rv) t = some .rv) :
    ∃ e : (RVLang).Term (Fin n), ∀ u : Fin n → RV (M := C),
      (@Term.realize RVLang (RV (M := C)) (ambientWithParameters S) (Fin n) u e).val =
        t.realize (Sum.elim p.values (fun i => (u i).val)) := by
  induction t with
  | var i =>
    cases i with
    | inr i => exact ⟨.var i, fun _ => rfl⟩
    | inl i =>
      have hs : p.sorts i = .rv := Option.some.inj ht
      have hr : iRV (p.values i) := by simpa only [hs, sortEval, iRV] using p.sorted i
      refine ⟨rvConstant S ⟨⟨p.values i, hr⟩, p.mem_base i⟩, ?_⟩
      intro u
      rw [rvConstant_realize]
      rfl
  | func f ts ih =>
    have h := ht
    rw [TmSort] at h
    split at h <;> rename_i hargs
    · have hres : Fn.resSort f = .rv := Option.some.inj h
      have hsame (harg : ∀ i, Fn.argSort f i = .rv) :
          ∃ e : (RVLang).Term (Fin n), ∀ u : Fin n → RV (M := C),
            (@Term.realize RVLang (RV (M := C)) (ambientWithParameters S) (Fin n) u e).val =
              (Term.func f ts : LRV.Term _).realize (Sum.elim p.values (fun i => (u i).val)) := by
        choose e he using fun i => ih i ((harg i) ▸ hargs i)
        refine ⟨.func (.inl ⟨f, hres, harg⟩) e, ?_⟩
        intro u
        change Structure.funMap (L := LRV) f _ = Structure.funMap (L := LRV) f _
        exact congrArg (Structure.funMap (L := LRV) f) (funext (fun i => he i u))
      cases f with
      | rvMap =>
        let w : Fin n → C := frozen
        let b := (Term.func Fn.rvMap ts : LRV.Term _).realize (Sum.elim p.values w)
        have hb : b ∈ S := term_in_base S (by
          rintro (i | i)
          · exact p.mem_base i
          · exact zero_in_base S) _
        have hz : iRV (iRVZero : C) :=
          CanonicalStructure.function_sort hC Fn.rvZero Fin.elim0 (fun i => i.elim0)
        have hr : iRV b := CanonicalStructure.term_sort hC p.sorts (fun _ => .rv)
          p.values w p.sorted (fun _ => hz) _ ht
        refine ⟨rvConstant S ⟨⟨b, hr⟩, hb⟩, ?_⟩
        intro u
        rw [rvConstant_realize]
        change Structure.funMap (L := LRV) Fn.rvMap _ =
          Structure.funMap (L := LRV) Fn.rvMap _
        apply congrArg (Structure.funMap (L := LRV) Fn.rvMap)
        funext i
        exact vf_term_constant p.values (ts i) (by simpa only [Fn.argSort] using hargs i) _ _
      | rvZero => exact hsame (fun i => i.elim0)
      | rvOne => exact hsame (fun i => i.elim0)
      | rvMul => exact hsame (fun _ => rfl)
      | rvInv => exact hsame (fun _ => rfl)
      | kAdd => exact hsame (fun _ => rfl)
      | kNeg => exact hsame (fun _ => rfl)
      | vfZero | vfOne | vfAdd | vfNeg | vfMul => simp [Fn.resSort] at hres
    · contradiction

private theorem rv_formula_definition (p : Parameters (S : Set C)) {n : ℕ}
    (φ : LRV.BoundedFormula (Fin p.length) n) (hq : φ.IsQF)
    (hw : WellSorted p.sorts (fun _ => .rv) φ) :
    ∃ χ : (RVLang).Formula (Fin n), χ.IsQF ∧
      ∀ u : Fin n → RV (M := C),
        @Formula.Realize RVLang (RV (M := C)) (ambientWithParameters S) _ χ u ↔
          φ.Realize p.values (fun i => (u i).val) := by
  letI := ambientWithParameters S
  induction hq with
  | falsum => exact ⟨⊥, .falsum, fun _ => Iff.rfl⟩
  | of_isAtomic h =>
    cases h with
    | equal t u =>
      cases hw with
      | @equal _ _ _ _ σ ht hu =>
        cases σ with
        | vf =>
          let v : Fin n → C := frozen
          by_cases he : t.realize (Sum.elim p.values v) = u.realize (Sum.elim p.values v)
          · refine ⟨⊤, BoundedFormula.IsQF.top, ?_⟩
            intro a
            simp [BoundedFormula.realize_bdEqual, vf_term_constant p.values t ht _ v,
              vf_term_constant p.values u hu _ v, he]
          · refine ⟨⊥, .falsum, ?_⟩
            intro a
            simp [BoundedFormula.realize_bdEqual, vf_term_constant p.values t ht _ v,
              vf_term_constant p.values u hu _ v, he]
        | rv =>
          obtain ⟨e, he⟩ := rv_term_definition S p t ht
          obtain ⟨f, hf⟩ := rv_term_definition S p u hu
          refine ⟨e.equal f, .of_isAtomic (.equal _ _), ?_⟩
          intro a
          rw [Formula.realize_equal, BoundedFormula.realize_bdEqual, ← Subtype.val_inj, he, hf]
    | rel r ts =>
      cases hw with
      | rel _ _ _ hs =>
        cases r with
        | memVF =>
          refine ⟨⊤, BoundedFormula.IsQF.top, ?_⟩
          intro u
          have he := CanonicalStructure.term_sort hC p.sorts (fun _ => .rv) p.values
            (fun i => (u i).val) p.sorted (fun i => (u i).property) (ts 0) (hs 0)
          have hts : ts = ![ts 0] := by funext i; fin_cases i; rfl
          simp only [Formula.realize_top, true_iff]
          rw [hts]
          change (Relations.boundedFormula₁ (L := LRV) Rel.memVF (ts 0)).Realize
            p.values (fun i => (u i).val)
          exact BoundedFormula.realize_rel₁.mpr he
        | memRV =>
          refine ⟨⊤, BoundedFormula.IsQF.top, ?_⟩
          intro u
          have he := CanonicalStructure.term_sort hC p.sorts (fun _ => .rv) p.values
            (fun i => (u i).val) p.sorted (fun i => (u i).property) (ts 0) (hs 0)
          have hts : ts = ![ts 0] := by funext i; fin_cases i; rfl
          simp only [Formula.realize_top, true_iff]
          rw [hts]
          change (Relations.boundedFormula₁ (L := LRV) Rel.memRV (ts 0)).Realize
            p.values (fun i => (u i).val)
          exact BoundedFormula.realize_rel₁.mpr he
        | memUnits =>
          choose e he using fun i => rv_term_definition S p (ts i) (hs i)
          let ρ : (RVLang).Relations 1 := .inl ⟨.memUnits, fun _ => rfl⟩
          refine ⟨ρ.formula e, .of_isAtomic (.rel _ _), ?_⟩
          intro u
          rw [Formula.realize_rel, BoundedFormula.realize_rel]
          change Structure.RelMap (L := LRV) Rel.memUnits
            (fun i => ((e i).realize u).val) ↔ _
          rw [show (fun i => ((e i).realize u).val) =
            (fun i => (ts i).realize (Sum.elim p.values (fun j => (u j).val))) from funext (fun i => he i u)]
        | rvLe =>
          choose e he using fun i => rv_term_definition S p (ts i) (hs i)
          let ρ : (RVLang).Relations 2 := .inl ⟨.rvLe, fun _ => rfl⟩
          refine ⟨ρ.formula e, .of_isAtomic (.rel _ _), ?_⟩
          intro u
          rw [Formula.realize_rel, BoundedFormula.realize_rel]
          change Structure.RelMap (L := LRV) Rel.rvLe
            (fun i => ((e i).realize u).val) ↔ _
          rw [show (fun i => ((e i).realize u).val) =
            (fun i => (ts i).realize (Sum.elim p.values (fun j => (u j).val))) from funext (fun i => he i u)]
  | imp _ _ ihφ ihψ =>
    cases hw with
    | imp _ hφ hψ =>
      obtain ⟨χ, hχ, he⟩ := ihφ hφ
      obtain ⟨ρ, hρ, hf⟩ := ihψ hψ
      exact ⟨χ.imp ρ, hχ.imp hρ, fun u => imp_congr (he u) (hf u)⟩

theorem rvQFDefinitions_of_acvf : RVQFDefinitions S := by
  intro q U hU
  have hs (z) (hz : z ∈ RawRVSet U) : ∀ i, sortEval .rv (z i) := by
    obtain ⟨u, _, rfl⟩ := hz
    exact fun i => (u i).property
  have hr := (definableOver_iff_normalized_raw (S : Set C) (fun _ => .rv) (RawRVSet U)).mpr
    ⟨hU, hs⟩
  obtain ⟨p, ψ, hq, hw, he⟩ := hr.quantifier_free hC
  obtain ⟨χ, hχ, hh⟩ := rv_formula_definition S p ψ hq hw
  refine ⟨χ, hχ, ?_⟩
  intro u
  have hm : (fun i => (u i).val) ∈ RawRVSet U ↔ u ∈ U := by
    constructor
    · rintro ⟨z, hz, heq⟩
      have hzu : z = u := funext (fun i => Subtype.ext (congrFun heq i))
      exact hzu ▸ hz
    · exact fun hu => ⟨u, hu, rfl⟩
  rw [← hm, he]
  exact ⟨fun h => (hh u).mpr h.2, fun h => ⟨fun i => (u i).property, (hh u).mp h⟩⟩

end SpecialTransformations.Section6.RVGraphLanguage
