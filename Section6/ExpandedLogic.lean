module

public import Section6.RVTermSupport
public import Section6.RVAbstraction

@[expose] public section

/-! The logical induction of RelativeSyntax in an arbitrary RV-only
expansion. Formulas are the actual Mathlib formulas in LRV.sum E, using
the canonical guarded encoding of sorted binders. This generic reduction
does not assume that its one-step hypothesis is a henselian theorem.
The native-language proof in RelativeSyntax is the proof reference.
-/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section6.ExpandedLogic
open RVTermSupport

def sortRelation {E : Language} (s : SortTag) : (Expanded E).Relations 1 :=
  .inl (match s with | .vf => .memVF | .rv => .memRV)

def relationSort {E : Language} {k : ℕ} : (Expanded E).Relations k → Fin k → SortTag
  | .inl r => Rel.argSort r
  | .inr _ => fun _ => .rv

def tagEval {E : Language} {M : Type} [(Expanded E).Structure M] (s : SortTag) (a : M) : Prop :=
  Structure.RelMap (L := Expanded E) (sortRelation s) ![a]

def guardAtom {E : Language} {α : Type} {n : ℕ} (s : SortTag) (i : Fin n) :
    (Expanded E).BoundedFormula α n := .rel (sortRelation s) ![.var (.inr i)]

def allSorted {E : Language} {α : Type} {n : ℕ} (s : SortTag)
    (φ : (Expanded E).BoundedFormula α (n + 1)) : (Expanded E).BoundedFormula α n :=
  (guardAtom s (Fin.last n) ⟹ φ).all

def exSorted {E : Language} {α : Type} {n : ℕ} (s : SortTag)
    (φ : (Expanded E).BoundedFormula α (n + 1)) : (Expanded E).BoundedFormula α n :=
  (allSorted s φ.not).not

inductive WellSorted {E : Language} {α : Type} (sα : α → SortTag) :
    {n : ℕ} → (Fin n → SortTag) → (Expanded E).BoundedFormula α n → Prop
  | falsum {n} (sn : Fin n → SortTag) : WellSorted sα sn ⊥
  | equal {n} {sn : Fin n → SortTag} {s : SortTag} {t u : (Expanded E).Term (α ⊕ Fin n)}
      (ht : termSort (Sum.elim sα sn) t = some s)
      (hu : termSort (Sum.elim sα sn) u = some s) : WellSorted sα sn (.equal t u)
  | rel {n k} {sn : Fin n → SortTag} (r : (Expanded E).Relations k)
      (ts : Fin k → (Expanded E).Term (α ⊕ Fin n))
      (hs : ∀ i, termSort (Sum.elim sα sn) (ts i) = some (relationSort r i)) :
      WellSorted sα sn (.rel r ts)
  | imp {n} {sn : Fin n → SortTag} {φ ψ : (Expanded E).BoundedFormula α n}
      (hφ : WellSorted sα sn φ) (hψ : WellSorted sα sn ψ) : WellSorted sα sn (φ.imp ψ)
  | all {n} {sn : Fin n → SortTag} {s : SortTag}
      {φ : (Expanded E).BoundedFormula α (n + 1)}
      (hφ : WellSorted sα (Fin.snoc sn s) φ) : WellSorted sα sn (allSorted s φ)

inductive IsVFQF {E : Language} {α : Type} :
    {n : ℕ} → (Expanded E).BoundedFormula α n → Prop
  | falsum {n} : IsVFQF (⊥ : (Expanded E).BoundedFormula α n)
  | atomic {n} {φ : (Expanded E).BoundedFormula α n} (hφ : φ.IsAtomic) : IsVFQF φ
  | imp {n} {φ ψ : (Expanded E).BoundedFormula α n}
      (hφ : IsVFQF φ) (hψ : IsVFQF ψ) : IsVFQF (φ.imp ψ)
  | all_rv {n} {φ : (Expanded E).BoundedFormula α (n + 1)}
      (hφ : IsVFQF φ) : IsVFQF (allSorted .rv φ)

theorem WellSorted.not {E : Language} {α : Type} {sα : α → SortTag} {n : ℕ}
    {sn : Fin n → SortTag} {φ : (Expanded E).BoundedFormula α n} (hφ : WellSorted sα sn φ) :
    WellSorted sα sn φ.not := .imp hφ (.falsum sn)

theorem IsVFQF.not {E : Language} {α : Type} {n : ℕ}
    {φ : (Expanded E).BoundedFormula α n} (hφ : IsVFQF φ) : IsVFQF φ.not :=
  .imp hφ .falsum

section Semantics
variable {E : Language} {α M : Type} [(Expanded E).Structure M]

theorem guardAtom_realize {n : ℕ} (s : SortTag) (i : Fin n) (v : α → M) (x : Fin n → M) :
    (guardAtom s i : (Expanded E).BoundedFormula α n).Realize v x ↔ tagEval (E := E) s (x i) := by
  have he : (fun j : Fin 1 => Term.realize (Sum.elim v x)
      ((![.var (.inr i)] : Fin 1 → (Expanded E).Term (α ⊕ Fin n)) j)) = ![x i] := by
    funext j
    fin_cases j
    rfl
  change Structure.RelMap (L := Expanded E) (sortRelation s) _ ↔ _
  rw [he]
  rfl

theorem allSorted_realize {n : ℕ} (s : SortTag)
    (φ : (Expanded E).BoundedFormula α (n + 1)) (v : α → M) (x : Fin n → M) :
    (allSorted s φ).Realize v x ↔
      ∀ a : M, tagEval (E := E) s a → φ.Realize v (Fin.snoc x a) := by
  rw [allSorted, BoundedFormula.realize_all]
  apply forall_congr'
  intro a
  rw [BoundedFormula.realize_imp, guardAtom_realize, Fin.snoc_last]

theorem exSorted_realize {n : ℕ} (s : SortTag)
    (φ : (Expanded E).BoundedFormula α (n + 1)) (v : α → M) (x : Fin n → M) :
    (exSorted s φ).Realize v x ↔
      ∃ a : M, tagEval (E := E) s a ∧ φ.Realize v (Fin.snoc x a) := by
  classical
  simp only [exSorted, BoundedFormula.realize_not, allSorted_realize,
    not_forall, not_not, exists_prop]

theorem sorted_snoc {n : ℕ} {sn : Fin n → SortTag} {s : SortTag}
    {x : Fin n → M} {a : M} (hx : ∀ i, tagEval (E := E) (sn i) (x i))
    (ha : tagEval (E := E) s a) :
    ∀ i, tagEval (E := E) (Fin.snoc (α := fun _ => SortTag) sn s i)
      (Fin.snoc (α := fun _ => M) x a i) := by
  intro i
  cases i using Fin.lastCases with
  | last => simpa only [Fin.snoc_last] using ha
  | cast i => simpa only [Fin.snoc_castSucc] using hx i

end Semantics

def OneStep {E : Language} (T : (Expanded E).Theory) : Prop :=
  ∀ (α : Type) (sα : α → SortTag) (n : ℕ) (sn : Fin n → SortTag)
    (φ : (Expanded E).BoundedFormula α (n + 1)),
    WellSorted sα (Fin.snoc sn .vf) φ → IsVFQF φ →
    ∃ ψ : (Expanded E).BoundedFormula α n, IsVFQF ψ ∧ WellSorted sα sn ψ ∧
      ∀ (M : Type) [(Expanded E).Structure M], M ⊨ T →
        ∀ (v : α → M) (x : Fin n → M),
          (∀ a, tagEval (E := E) (sα a) (v a)) → (∀ i, tagEval (E := E) (sn i) (x i)) →
          ((∃ a : M, tagEval (E := E) .vf a ∧ φ.Realize v (Fin.snoc x a)) ↔ ψ.Realize v x)

def HasVFQE {E : Language} (T : (Expanded E).Theory) : Prop :=
  ∀ (α : Type) (sα : α → SortTag) (n : ℕ) (sn : Fin n → SortTag)
    (φ : (Expanded E).BoundedFormula α n), WellSorted sα sn φ →
    ∃ ψ : (Expanded E).BoundedFormula α n, IsVFQF ψ ∧ WellSorted sα sn ψ ∧
      ∀ (M : Type) [(Expanded E).Structure M], M ⊨ T →
        ∀ (v : α → M) (x : Fin n → M),
          (∀ a, tagEval (E := E) (sα a) (v a)) → (∀ i, tagEval (E := E) (sn i) (x i)) →
          (φ.Realize v x ↔ ψ.Realize v x)

/-- The logical part of Proposition 6.4 for arbitrary RV-only expansions.
The henselian application must supply, rather than assume, OneStep. -/
theorem hasVFQE_of_oneStep {E : Language} (T : (Expanded E).Theory)
    (hstep : OneStep T) : HasVFQE T := by
  intro α sα n sn φ hφ
  induction hφ with
  | falsum sn => exact ⟨⊥, .falsum, .falsum sn, fun _ _ _ _ _ _ _ => Iff.rfl⟩
  | equal ht hu => exact ⟨_, .atomic (.equal _ _), .equal ht hu,
      fun _ _ _ _ _ _ _ => Iff.rfl⟩
  | rel rel ts hs => exact ⟨_, .atomic (.rel _ _), .rel rel ts hs,
      fun _ _ _ _ _ _ _ => Iff.rfl⟩
  | imp hφ hψ ihφ ihψ =>
    obtain ⟨φ', hqφ, hsφ, heφ⟩ := ihφ
    obtain ⟨ψ', hqψ, hsψ, heψ⟩ := ihψ
    refine ⟨φ'.imp ψ', .imp hqφ hqψ, .imp hsφ hsψ, ?_⟩
    intro M _ hM v x hv hx
    exact imp_congr (heφ M hM v x hv hx) (heψ M hM v x hv hx)
  | @all n sn s φ hφ ih =>
    obtain ⟨ψ, hqψ, hsψ, heψ⟩ := ih
    cases s with
    | rv =>
      refine ⟨allSorted .rv ψ, .all_rv hqψ, .all hsψ, ?_⟩
      intro M _ hM v x hv hx
      rw [allSorted_realize, allSorted_realize]
      constructor
      · intro hall a ha
        exact (heψ M hM v (Fin.snoc x a) hv (sorted_snoc hx ha)).mp (hall a ha)
      · intro hall a ha
        exact (heψ M hM v (Fin.snoc x a) hv (sorted_snoc hx ha)).mpr (hall a ha)
    | vf =>
      obtain ⟨θ, hqθ, hsθ, heθ⟩ := hstep α sα n sn ψ.not hsψ.not hqψ.not
      refine ⟨θ.not, hqθ.not, hsθ.not, ?_⟩
      intro M _ hM v x hv hx
      rw [allSorted_realize, BoundedFormula.realize_not, ← heθ M hM v x hv hx]
      constructor
      · rintro hall ⟨a, ha, hna⟩
        exact hna ((heψ M hM v (Fin.snoc x a) hv (sorted_snoc hx ha)).mp (hall a ha))
      · intro hno a ha
        by_contra hna
        apply hno
        refine ⟨a, ha, ?_⟩
        intro hψ
        exact hna ((heψ M hM v (Fin.snoc x a) hv (sorted_snoc hx ha)).mpr hψ)

end SpecialTransformations.Section6.ExpandedLogic


/-! Lift an auxiliary RV formula back into the actual expanded language.
Every auxiliary binder becomes a guarded RV binder. Free coefficient
variables may be replaced by RV terms in the original VF/RV parameters.
This is the reverse syntactic interpretation needed after graph assembly.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.GuardedLift
open RVTermSupport RVAbstraction

def functionMap {E : Language} {k : ℕ} :
    (Auxiliary E).Functions k → (Expanded E).Functions k
  | .inl f => .inl f.val
  | .inr f => .inr f

def term {E : Language} {A B : Type} (σ : A → (Expanded E).Term B) {n : ℕ} :
    (Auxiliary E).Term (A ⊕ Fin n) → (Expanded E).Term (B ⊕ Fin n)
  | .var (.inl a) => (σ a).relabel Sum.inl
  | .var (.inr i) => .var (.inr i)
  | .func f ts => .func (functionMap f) (fun i => term σ (ts i))

def formula {E : Language} {A B : Type} (σ : A → (Expanded E).Term B) : {n : ℕ} →
    (Auxiliary E).BoundedFormula A n → (Expanded E).BoundedFormula B n
  | _, .falsum => .falsum
  | _, .equal t u => .equal (term σ t) (term σ u)
  | _, .rel r ts => .rel (sourceRelation r) (fun i => term σ (ts i))
  | _, .imp φ ψ => (formula σ φ).imp (formula σ ψ)
  | _, .all φ => ExpandedLogic.allSorted .rv (formula σ φ)

theorem termSort_relabel {E : Language} {I J : Type}
    (sI : I → SortTag) (sJ : J → SortTag) (f : I → J) (hf : ∀ i, sJ (f i) = sI i)
    (t : (Expanded E).Term I) : termSort sJ (t.relabel f) = termSort sI t := by
  induction t with
  | var i => simp only [Term.relabel, termSort, hf]
  | func g ts ih => simp only [Term.relabel, termSort, ih]

theorem term_sorted {E : Language} {A B : Type} (sB : B → SortTag)
    (σ : A → (Expanded E).Term B) (hσ : ∀ a, termSort sB (σ a) = some .rv)
    {n : ℕ} (t : (Auxiliary E).Term (A ⊕ Fin n)) :
    termSort (Sum.elim sB (fun _ => .rv)) (term σ t) = some .rv := by
  induction t with
  | var i =>
    cases i with
    | inl a =>
      rw [term, termSort_relabel sB (Sum.elim sB (fun _ => .rv)) Sum.inl (fun _ => rfl)]
      exact hσ a
    | inr i => rfl
  | func f ts ih =>
    apply (termSort_func _ (functionMap f) _).mpr
    cases f with
    | inl f =>
      exact ⟨fun i => by simpa only [functionMap, argumentSort, f.property.2 i] using ih i,
        f.property.1⟩
    | inr f => exact ⟨ih, rfl⟩

theorem formula_isVFQF {E : Language} {A B : Type}
    (σ : A → (Expanded E).Term B) {n : ℕ} (φ : (Auxiliary E).BoundedFormula A n) :
    ExpandedLogic.IsVFQF (formula σ φ) := by
  induction φ with
  | falsum => exact .falsum
  | equal => exact .atomic (.equal _ _)
  | rel => exact .atomic (.rel _ _)
  | imp φ ψ ihφ ihψ => exact .imp ihφ ihψ
  | all φ ih => exact .all_rv ih

theorem formula_wellSorted {E : Language} {A B : Type} (sB : B → SortTag)
    (σ : A → (Expanded E).Term B) (hσ : ∀ a, termSort sB (σ a) = some .rv)
    {n : ℕ} (φ : (Auxiliary E).BoundedFormula A n) :
    ExpandedLogic.WellSorted sB (fun _ => .rv) (formula σ φ) := by
  induction φ with
  | falsum => exact .falsum _
  | equal t u => exact .equal (term_sorted sB σ hσ t) (term_sorted sB σ hσ u)
  | rel r ts =>
    apply ExpandedLogic.WellSorted.rel
    intro i
    cases r with
    | inl r =>
      simpa only [sourceRelation, ExpandedLogic.relationSort, r.property i]
        using term_sorted sB σ hσ (ts i)
    | inr r => exact term_sorted sB σ hσ (ts i)
  | imp φ ψ ihφ ihψ => exact .imp ihφ ihψ
  | @all n φ ih =>
    have he : Fin.snoc (fun _ : Fin n => SortTag.rv) .rv = (fun _ => SortTag.rv) := by
      funext i
      cases i using Fin.lastCases <;> simp
    apply ExpandedLogic.WellSorted.all
    rw [he]
    exact ih

section Semantics
variable {E : Language} {A B C Q : Type}
variable [(Expanded E).Structure C] [(Auxiliary E).Structure Q]

theorem term_realize (j : Q → C) (hfun : Compatible (E := E) j)
    (σ : A → (Expanded E).Term B) (vC : B → C) (vQ : A → Q)
    (hσ : ∀ a, (σ a).realize vC = j (vQ a))
    {n : ℕ} (t : (Auxiliary E).Term (A ⊕ Fin n)) (x : Fin n → Q) :
    (term σ t).realize (Sum.elim vC (j ∘ x)) = j (t.realize (Sum.elim vQ x)) := by
  induction t with
  | var i =>
    cases i with
    | inl a =>
      simpa only [term, Term.realize_relabel, Sum.elim_comp_inl, Term.realize,
        Sum.elim_inl] using hσ a
    | inr i => rfl
  | func f ts ih =>
    change Structure.funMap (L := Expanded E) (functionMap f) _ =
      j (Structure.funMap (L := Auxiliary E) f _)
    have he : (fun i => (term σ (ts i)).realize (Sum.elim vC (j ∘ x))) =
        j ∘ (fun i => (ts i).realize (Sum.elim vQ x)) := funext ih
    rw [he]
    cases f with
    | inl f => exact (hfun.1 f _).symm
    | inr f => exact (hfun.2 f _).symm

private theorem snoc_comp {n : ℕ} (j : Q → C) (x : Fin n → Q) (q : Q) :
    j ∘ Fin.snoc x q = Fin.snoc (j ∘ x) (j q) := by
  funext i
  cases i using Fin.lastCases <;> simp

theorem formula_realize (j : Q → C) (hinj : Function.Injective j)
    (hfun : Compatible (E := E) j) (hrel : RelationsCompatible (E := E) j)
    (hguard : GuardCompatible (E := E) j)
    (σ : A → (Expanded E).Term B) (vC : B → C) (vQ : A → Q)
    (hσ : ∀ a, (σ a).realize vC = j (vQ a))
    {n : ℕ} (φ : (Auxiliary E).BoundedFormula A n) (x : Fin n → Q) :
    (formula σ φ).Realize vC (j ∘ x) ↔ φ.Realize vQ x := by
  induction φ with
  | falsum => rfl
  | equal t u =>
    change (term σ t).realize _ = (term σ u).realize _ ↔ t.realize _ = u.realize _
    rw [term_realize j hfun σ vC vQ hσ t x, term_realize j hfun σ vC vQ hσ u x, hinj.eq_iff]
  | rel r ts =>
    change Structure.RelMap (L := Expanded E) (sourceRelation r) _ ↔
      Structure.RelMap (L := Auxiliary E) r _
    have he : (fun i => (term σ (ts i)).realize (Sum.elim vC (j ∘ x))) =
        j ∘ (fun i => (ts i).realize (Sum.elim vQ x)) :=
      funext (fun i => term_realize j hfun σ vC vQ hσ (ts i) x)
    rw [he]
    exact (hrel r _).symm
  | imp φ ψ ihφ ihψ => exact imp_congr (ihφ x) (ihψ x)
  | all φ ih =>
    rw [formula, ExpandedLogic.allSorted_realize, BoundedFormula.realize_all]
    have hb (q : Q) := ih (Fin.snoc x q)
    simp only [snoc_comp] at hb
    constructor
    · intro hall q
      apply (hb q).mp
      apply hall (j q)
      exact (hguard (j q)).mpr ⟨q, rfl⟩
    · intro hall a ha
      obtain ⟨q, rfl⟩ := (hguard a).mp ha
      exact (hb q).mpr (hall q)

end Semantics
end SpecialTransformations.Section6.GuardedLift
