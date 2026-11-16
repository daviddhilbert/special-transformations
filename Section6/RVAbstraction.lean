module

public import Section6.RVTermSupport
public import Section6.RVFormula

@[expose] public section

/-!
The auxiliary reduct of an RV-only expansion, and abstraction of the VF
polynomial leaves. Its symbols are restrictions of published LRV symbols
and the extra RV signature. No VF inverse or extra absorbing point occurs.
The source variable context has arbitrary VF and RV free variables and
only RV bound variables, as in the VF-quantifier-free input to Lemma 6.3.
-/

noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.RVAbstraction

open RVTermSupport

def RVFunction (k : ℕ) := {f : Fn k // Fn.resSort f = .rv ∧ ∀ i, Fn.argSort f i = .rv}
def RVRelation (k : ℕ) := {r : Rel k // ∀ i, Rel.argSort r i = .rv}

def Auxiliary (E : Language) : Language :=
  ⟨fun k => RVFunction k ⊕ E.Functions k, fun k => RVRelation k ⊕ E.Relations k⟩

def sourceSort {V R : Type} {n : ℕ} : (V ⊕ R) ⊕ Fin n → SortTag :=
  Sum.elim (Sum.elim (fun _ => .vf) (fun _ => .rv)) (fun _ => .rv)

/-- Bound RV variables cannot occur in a well-sorted VF polynomial. The
dummy zero branches below are unreachable under a VF sorting proof. -/
def polynomial {E : Language} {V R : Type} {n : ℕ} :
    (Expanded E).Term ((V ⊕ R) ⊕ Fin n) → (Expanded E).Term V
  | .var (.inl (.inl v)) => .var v
  | .var _ => .func (.inl .vfZero) Fin.elim0
  | .func f ts => .func f (fun i => polynomial (ts i))

theorem polynomial_sort {E : Language} {V R : Type} {n : ℕ}
    (t : (Expanded E).Term ((V ⊕ R) ⊕ Fin n))
    (ht : termSort sourceSort t = some .vf) :
    termSort (fun _ => .vf) (polynomial t) = some .vf := by
  induction t with
  | var i =>
    cases i with
    | inl i => cases i with
      | inl v => rfl
      | inr r => cases ht
    | inr i => cases ht
  | func f ts ih =>
    obtain ⟨harg, hres⟩ := (termSort_func sourceSort f ts).mp ht
    apply (termSort_func (fun _ => .vf) f _).mpr
    refine ⟨?_, hres⟩
    cases f with
    | inr f => cases hres
    | inl f =>
      cases f <;> try cases hres
      all_goals intro i; first | exact i.elim0 | exact ih i (harg i)

theorem polynomial_realize {E : Language} {V R M : Type} {n : ℕ}
    [(Expanded E).Structure M]
    (t : (Expanded E).Term ((V ⊕ R) ⊕ Fin n))
    (ht : termSort sourceSort t = some .vf)
    (v : V → M) (r : R → M) (x : Fin n → M) :
    (polynomial t).realize v = t.realize (Sum.elim (Sum.elim v r) x) := by
  induction t with
  | var i =>
    cases i with
    | inl i => cases i with
      | inl v => rfl
      | inr r => cases ht
    | inr i => cases ht
  | func f ts ih =>
    obtain ⟨harg, hres⟩ := (termSort_func sourceSort f ts).mp ht
    have hargs : ∀ i, argumentSort f i = .vf := by
      cases f with
      | inr f => cases hres
      | inl f => cases f <;> try cases hres
                 all_goals intro i; first | exact i.elim0 | rfl
    change Structure.funMap (L := Expanded E) f _ = Structure.funMap (L := Expanded E) f _
    congr 1
    funext i
    exact ih i (by rw [← hargs i]; exact harg i)

def oldFunction {E : Language} {k : ℕ} (f : Fn k)
    (h : Fn.resSort f = .rv ∧ ∀ i, Fn.argSort f i = .rv) : (Auxiliary E).Functions k :=
  .inl ⟨f, h⟩

def zeroTerm {E : Language} {I : Type} : (Auxiliary E).Term I :=
  .func (oldFunction .rvZero ⟨rfl, fun i => i.elim0⟩) Fin.elim0

/-- Replace every rv-polynomial by a free auxiliary variable. Inversion
remains a native RV operation, so denominator leaves are retained. -/
def term {E : Language} {V R : Type} {n : ℕ} :
    (Expanded E).Term ((V ⊕ R) ⊕ Fin n) →
      (Auxiliary E).Term (((Expanded E).Term V ⊕ R) ⊕ Fin n)
  | .var (.inl (.inl _)) => zeroTerm
  | .var (.inl (.inr r)) => .var (.inl (.inr r))
  | .var (.inr i) => .var (.inr i)
  | .func f ts => match f with
    | .inr f => .func (.inr f) (fun i => term (ts i))
    | .inl .rvMap => .var (.inl (.inl (polynomial (ts 0))))
    | .inl .rvZero => zeroTerm
    | .inl .rvOne => .func (oldFunction .rvOne ⟨rfl, fun i => i.elim0⟩) Fin.elim0
    | .inl .rvMul => .func (oldFunction .rvMul ⟨rfl, fun _ => rfl⟩) (fun i => term (ts i))
    | .inl .rvInv => .func (oldFunction .rvInv ⟨rfl, fun _ => rfl⟩) (fun i => term (ts i))
    | .inl .kAdd => .func (oldFunction .kAdd ⟨rfl, fun _ => rfl⟩) (fun i => term (ts i))
    | .inl .kNeg => .func (oldFunction .kNeg ⟨rfl, fun _ => rfl⟩) (fun i => term (ts i))
    | .inl _ => zeroTerm

section Semantics

private theorem emptyTuple_eq {D : Type} (z : Fin 0 → D) : z = Fin.elim0 := by
  funext i
  exact i.elim0

variable {E : Language} {V R C Q : Type} {n : ℕ}
variable [(Expanded E).Structure C] [(Auxiliary E).Structure Q]

/-- Interpretation compatibility for the genuine RV reduct and an
arbitrary extra RV structure. It imposes no QE or closure conclusion. -/
def Compatible (j : Q → C) : Prop :=
  (∀ {k} (f : RVFunction k) (z : Fin k → Q),
    j (Structure.funMap (L := Auxiliary E) (.inl f) z) =
      Structure.funMap (L := Expanded E) (.inl f.val) (j ∘ z)) ∧
  (∀ {k} (f : E.Functions k) (z : Fin k → Q),
    j (Structure.funMap (L := Auxiliary E) (.inr f) z) =
      Structure.funMap (L := Expanded E) (.inr f) (j ∘ z))

theorem term_realize (j : Q → C) (hj : Compatible (E := E) j)
    (v : V → C) (r : R → Q) (x : Fin n → Q)
    (c : (Expanded E).Term V → Q)
    (hc : ∀ p, termSort (fun _ => .vf) p = some .vf →
      j (c p) = (rvTerm p).realize v)
    (t : (Expanded E).Term ((V ⊕ R) ⊕ Fin n))
    (ht : termSort sourceSort t = some .rv) :
    j ((term t).realize (Sum.elim (Sum.elim c r) x)) =
      t.realize (Sum.elim (Sum.elim v (j ∘ r)) (j ∘ x)) := by
  induction t with
  | var i =>
    cases i with
    | inl i => cases i with
      | inl v => cases ht
      | inr r => rfl
    | inr i => rfl
  | @func k f ts ih =>
    obtain ⟨harg, hres⟩ := (termSort_func sourceSort f ts).mp ht
    have step (f' : (Auxiliary E).Functions k)
        (he : term (.func f ts) = .func f' (fun i => term (ts i)))
        (hcompat : ∀ z, j (Structure.funMap (L := Auxiliary E) f' z) =
          Structure.funMap (L := Expanded E) f (j ∘ z))
        (hs : ∀ i, argumentSort f i = .rv) :
        j ((term (.func f ts)).realize (Sum.elim (Sum.elim c r) x)) =
          (Term.func f ts).realize (Sum.elim (Sum.elim v (j ∘ r)) (j ∘ x)) := by
      rw [he]
      change j (Structure.funMap (L := Auxiliary E) f' _) = _
      rw [hcompat]
      change Structure.funMap (L := Expanded E) f _ = Structure.funMap (L := Expanded E) f _
      congr 1
      funext i
      exact ih i (by rw [← hs i]; exact harg i)
    cases f with
    | inr f => exact step (.inr f) rfl (hj.2 f) (fun _ => rfl)
    | inl f =>
      cases f with
      | vfZero => cases hres
      | vfOne => cases hres
      | vfAdd => cases hres
      | vfNeg => cases hres
      | vfMul => cases hres
      | rvMap =>
        change j (c (polynomial (ts 0))) = _
        rw [hc _ (polynomial_sort _ (harg 0))]
        have hp := polynomial_realize (ts 0) (harg 0) v (j ∘ r) (j ∘ x)
        have eta : ts = ![ts 0] := by funext i; fin_cases i; rfl
        rw [eta]
        change Structure.funMap (L := Expanded E) (.inl .rvMap) _ =
          Structure.funMap (L := Expanded E) (.inl .rvMap) _
        congr 1
        funext i
        fin_cases i
        exact hp
      | rvZero =>
        have he := hj.1 (⟨.rvZero, rfl, fun i => i.elim0⟩ : RVFunction 0) Fin.elim0
        simpa only [term, zeroTerm, Term.realize, oldFunction, emptyTuple_eq] using he
      | rvOne =>
        have he := hj.1 (⟨.rvOne, rfl, fun i => i.elim0⟩ : RVFunction 0) Fin.elim0
        simpa only [term, Term.realize, oldFunction, emptyTuple_eq] using he
      | rvMul => exact step _ rfl (hj.1 ⟨.rvMul, rfl, fun _ => rfl⟩) (fun _ => rfl)
      | rvInv => exact step _ rfl (hj.1 ⟨.rvInv, rfl, fun _ => rfl⟩) (fun _ => rfl)
      | kAdd => exact step _ rfl (hj.1 ⟨.kAdd, rfl, fun _ => rfl⟩) (fun _ => rfl)
      | kNeg => exact step _ rfl (hj.1 ⟨.kNeg, rfl, fun _ => rfl⟩) (fun _ => rfl)

end Semantics
end SpecialTransformations.Section6.RVAbstraction


/-! Abstraction under guarded RV quantifiers in the actual expanded
language. VF literals are first replaced using the accepted earlier
normal form. Rational-factor pole and residue-domain guards remain part
of the input formula and are translated by the same recursion. -/

noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.RVAbstraction
open RVTermSupport

def sourceRelation {E : Language} {k : ℕ} :
    (Auxiliary E).Relations k → (Expanded E).Relations k
  | .inl r => .inl r.val
  | .inr r => .inr r

def guard {E : Language} {I : Type} (n : ℕ) : (Expanded E).BoundedFormula I (n + 1) :=
  .rel (.inl .memRV) ![.var (.inr (Fin.last n))]

/-- The RV-literal fragment after the earlier removal of VF literals.
Quantifiers use the usual tagged sort guards. All tuple arities and both
kinds of free variable are arbitrary. -/
inductive Fragment {E : Language} {V R : Type} :
    {n : ℕ} → (Expanded E).BoundedFormula (V ⊕ R) n → Prop
  | falsum {n} : Fragment (⊥ : (Expanded E).BoundedFormula (V ⊕ R) n)
  | equal {n} (t u : (Expanded E).Term ((V ⊕ R) ⊕ Fin n))
      (ht : termSort sourceSort t = some .rv) (hu : termSort sourceSort u = some .rv) :
      Fragment (.equal t u)
  | rel {n k} (r : (Auxiliary E).Relations k)
      (ts : Fin k → (Expanded E).Term ((V ⊕ R) ⊕ Fin n))
      (hs : ∀ i, termSort sourceSort (ts i) = some .rv) :
      Fragment (.rel (sourceRelation r) ts)
  | imp {n} {φ ψ : (Expanded E).BoundedFormula (V ⊕ R) n}
      (hφ : Fragment φ) (hψ : Fragment ψ) : Fragment (φ.imp ψ)
  | all {n} {φ : (Expanded E).BoundedFormula (V ⊕ R) (n + 1)}
      (hφ : Fragment φ) : Fragment ((guard n ⟹ φ).all)

def formula {E : Language} {V R : Type} : {n : ℕ} →
    (Expanded E).BoundedFormula (V ⊕ R) n →
      (Auxiliary E).BoundedFormula ((Expanded E).Term V ⊕ R) n
  | _, .falsum => .falsum
  | _, .equal t u => .equal (term t) (term u)
  | _, .rel rel ts => match rel with
    | .inr rel => .rel (.inr rel) (fun i => term (ts i))
    | .inl rel => match rel with
      | .memVF => ⊥
      | .memRV => .rel (.inl ⟨.memRV, fun _ => rfl⟩) (fun i => term (ts i))
      | .memUnits => .rel (.inl ⟨.memUnits, fun _ => rfl⟩) (fun i => term (ts i))
      | .rvLe => .rel (.inl ⟨.rvLe, fun _ => rfl⟩) (fun i => term (ts i))
  | _, .imp φ ψ => (formula φ).imp (formula ψ)
  | _, .all φ => (formula φ).all

section Semantics
variable {E : Language} {V R C Q : Type}
variable [(Expanded E).Structure C] [(Auxiliary E).Structure Q]

def RelationsCompatible (j : Q → C) : Prop :=
  ∀ {k} (r : (Auxiliary E).Relations k) (z : Fin k → Q),
    Structure.RelMap (L := Auxiliary E) r z ↔
      Structure.RelMap (L := Expanded E) (sourceRelation r) (j ∘ z)

def GuardCompatible (j : Q → C) : Prop :=
  ∀ a : C, Structure.RelMap (L := Expanded E) (.inl .memRV) ![a] ↔ ∃ q, j q = a

private theorem guard_realize {I : Type} {n : ℕ} (v : I → C) (x : Fin (n + 1) → C) :
    (guard n : (Expanded E).BoundedFormula I (n + 1)).Realize v x ↔
      Structure.RelMap (L := Expanded E) (.inl .memRV) ![x (Fin.last n)] := by
  change Structure.RelMap (L := Expanded E) (.inl .memRV) _ ↔ _
  have he : (fun i : Fin 1 => Term.realize (Sum.elim v x)
      ((![.var (.inr (Fin.last n))] : Fin 1 → (Expanded E).Term (I ⊕ Fin (n + 1))) i)) =
      ![x (Fin.last n)] := by
    funext i
    fin_cases i
    rfl
  rw [he]

private theorem snoc_comp {n : ℕ} (j : Q → C) (x : Fin n → Q) (q : Q) :
    j ∘ Fin.snoc x q = Fin.snoc (j ∘ x) (j q) := by
  funext i
  cases i using Fin.lastCases <;> simp

/-- Replacement is valid inside all RV quantifiers in the original
structure. The auxiliary quantifiers range over Q, never over its ACVF
envelope. Coefficients are exactly the RV images of VF polynomial terms. -/
theorem formula_realize (j : Q → C) (hinj : Function.Injective j)
    (hfun : Compatible (E := E) j) (hrel : RelationsCompatible (E := E) j)
    (hguard : GuardCompatible (E := E) j)
    (v : V → C) (r : R → Q) (c : (Expanded E).Term V → Q)
    (hc : ∀ p, termSort (fun _ => .vf) p = some .vf →
      j (c p) = (rvTerm p).realize v)
    {n : ℕ} (φ : (Expanded E).BoundedFormula (V ⊕ R) n) (hφ : Fragment φ)
    (x : Fin n → Q) :
    (formula φ).Realize (Sum.elim c r) x ↔
      φ.Realize (Sum.elim v (j ∘ r)) (j ∘ x) := by
  induction hφ with
  | falsum => rfl
  | equal t u ht hu =>
    change (term t).realize _ = (term u).realize _ ↔ t.realize _ = u.realize _
    rw [← term_realize j hfun v r x c hc t ht,
      ← term_realize j hfun v r x c hc u hu, hinj.eq_iff]
  | @rel n k rel ts hs =>
    have he : (fun i => (ts i).realize (Sum.elim (Sum.elim v (j ∘ r)) (j ∘ x))) =
        j ∘ (fun i => (term (ts i)).realize (Sum.elim (Sum.elim c r) x)) := by
      funext i
      exact (term_realize j hfun v r x c hc (ts i) (hs i)).symm
    cases rel with
    | inr rel =>
      change Structure.RelMap (L := Auxiliary E) (.inr rel) _ ↔
        Structure.RelMap (L := Expanded E) (.inr rel) _
      rw [he]
      exact hrel (.inr rel) _
    | inl rel =>
      rcases rel with ⟨rel, hRV⟩
      cases rel with
      | memVF => have h := hRV 0; cases h
      | memRV =>
        change Structure.RelMap (L := Auxiliary E) (.inl ⟨.memRV, _⟩) _ ↔
          Structure.RelMap (L := Expanded E) (.inl .memRV) _
        rw [he]
        exact hrel (.inl ⟨.memRV, hRV⟩) _
      | memUnits =>
        change Structure.RelMap (L := Auxiliary E) (.inl ⟨.memUnits, _⟩) _ ↔
          Structure.RelMap (L := Expanded E) (.inl .memUnits) _
        rw [he]
        exact hrel (.inl ⟨.memUnits, hRV⟩) _
      | rvLe =>
        change Structure.RelMap (L := Auxiliary E) (.inl ⟨.rvLe, _⟩) _ ↔
          Structure.RelMap (L := Expanded E) (.inl .rvLe) _
        rw [he]
        exact hrel (.inl ⟨.rvLe, hRV⟩) _
  | imp hφ hψ ihφ ihψ =>
    exact imp_congr (ihφ x) (ihψ x)
  | @all n φ hφ ih =>
    have hQ (q : Q) : Structure.RelMap (L := Auxiliary E)
        (.inl (⟨.memRV, fun _ => rfl⟩ : RVRelation 1)) ![q] := by
      apply (hrel (.inl ⟨.memRV, fun _ => rfl⟩) ![q]).mpr
      have he : j ∘ ![q] = ![j q] := by funext i; fin_cases i; rfl
      rw [he]
      exact (hguard (j q)).mpr ⟨q, rfl⟩
    have hbody (q : Q) :
        (formula φ).Realize (Sum.elim c r) (Fin.snoc x q) ↔
        φ.Realize (Sum.elim v (j ∘ r)) (Fin.snoc (j ∘ x) (j q)) := by
      simpa only [snoc_comp] using ih (Fin.snoc x q)
    change (∀ q : Q, _ → (formula φ).Realize _ (Fin.snoc x q)) ↔
      ∀ a : C, (guard n : (Expanded E).BoundedFormula (V ⊕ R) (n + 1)).Realize
        (Sum.elim v (j ∘ r)) (Fin.snoc (j ∘ x) a) →
          φ.Realize (Sum.elim v (j ∘ r)) (Fin.snoc (j ∘ x) a)
    constructor
    · intro hall a ha
      have harv := (guard_realize _ _).mp ha
      rw [Fin.snoc_last] at harv
      obtain ⟨q, rfl⟩ := (hguard a).mp harv
      apply (hbody q).mp
      apply hall q
      change Structure.RelMap (L := Auxiliary E) (.inl ⟨.memRV, _⟩) _
      convert hQ q using 1
      funext i
      fin_cases i
      simp [term, Term.realize]
    · intro hall q _
      apply (hbody q).mpr
      apply hall (j q)
      apply (guard_realize _ _).mpr
      rw [Fin.snoc_last]
      exact (hguard (j q)).mpr ⟨q, rfl⟩

end Semantics
end SpecialTransformations.Section6.RVAbstraction
