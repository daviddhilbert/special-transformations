import CanonicalStructure

/-! Quantifier-free formulas over canonical totalizations can be made well sorted
at any fixed assignment of sorts to their variables. -/

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace CanonicalStructure

variable {α : Type} {n : ℕ}

def zeroTerm (s : SortTag) : LRV.Term (α ⊕ Fin n) :=
  match s with
  | .vf => .func Fn.vfZero (fun i => i.elim0)
  | .rv => .func Fn.rvZero (fun i => i.elim0)

def resultSort (sα : α → SortTag) (sn : Fin n → SortTag) :
    LRV.Term (α ⊕ Fin n) → SortTag
  | .var (.inl a) => sα a
  | .var (.inr i) => sn i
  | .func f _ => Fn.resSort f

noncomputable def sortedTerm (sα : α → SortTag) (sn : Fin n → SortTag) :
    LRV.Term (α ⊕ Fin n) → LRV.Term (α ⊕ Fin n)
  | .var a => .var a
  | .func f ts =>
      if ∀ i, resultSort sα sn (ts i) = Fn.argSort f i then
        .func f (fun i => sortedTerm sα sn (ts i))
      else zeroTerm (Fn.resSort f)

theorem zeroTerm_sort (sα : α → SortTag) (sn : Fin n → SortTag) (s : SortTag) :
    TmSort sα sn (zeroTerm s) = some s := by
  cases s
  · exact tmSort_vfZero sα sn
  · exact tmSort_rvZero sα sn

theorem sortedTerm_sort (sα : α → SortTag) (sn : Fin n → SortTag)
    (t : LRV.Term (α ⊕ Fin n)) :
    TmSort sα sn (sortedTerm sα sn t) = some (resultSort sα sn t) := by
  induction t with
  | var a => cases a <;> rfl
  | func f ts ih =>
      change TmSort sα sn (if ∀ i, resultSort sα sn (ts i) = Fn.argSort f i
        then .func f (fun i => sortedTerm sα sn (ts i)) else zeroTerm (Fn.resSort f)) =
        some (Fn.resSort f)
      by_cases h : ∀ i, resultSort sα sn (ts i) = Fn.argSort f i
      · rw [if_pos h]
        apply tmSort_func
        intro i
        simpa only [h i] using ih i
      · rw [if_neg h]
        exact zeroTerm_sort sα sn _

section Semantics

variable {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF)
include hM

theorem sort_unique {s t : SortTag} {x : M}
    (hs : sortEval s x) (ht : sortEval t x) : s = t := by
  have hd := Transfer.allOne_realize hM (φ := ∼(pVF &0 ⊓ pRVsort &0))
    (by simp [Axioms.ACVF, Axioms.sortAxioms, Axioms.ofList, Axioms.sdDisjoint]) ![x]
  have hvec : (fun _ : Fin 1 => x) = ![x] := by
    funext i
    fin_cases i
    rfl
  have hd' : ¬ (iVF x ∧ iRV x) := by
    simpa [pVF, pRVsort, iVF, iRV, Relations.boundedFormula₁,
      Relations.boundedFormula, BoundedFormula.Realize, Term.realize, hvec] using hd
  cases s <;> cases t
  · rfl
  · exact False.elim (hd' ⟨hs, ht⟩)
  · exact False.elim (hd' ⟨ht, hs⟩)
  · rfl

theorem relation_sorted (hcan : IsCanonical (M := M)) {k : ℕ}
    (r : Rel k) (xs : Fin k → M) (h : Structure.RelMap (L := LRV) r xs) :
    ∀ i, sortEval (Rel.argSort r i) (xs i) := by
  cases r with
  | memVF =>
      have he : xs = ![xs 0] := by funext i; fin_cases i; rfl
      rw [he] at h
      intro i; fin_cases i
      exact h
  | memRV =>
      have he : xs = ![xs 0] := by funext i; fin_cases i; rfl
      rw [he] at h
      intro i; fin_cases i
      exact h
  | memUnits =>
      have he : xs = ![xs 0] := by funext i; fin_cases i; rfl
      rw [he] at h
      intro i; fin_cases i
      exact Transfer.iRV_of_inK hM (Or.inl h)
  | rvLe =>
      by_contra hn
      exact hcan.2 xs hn h

omit hM in
@[simp] theorem zeroTerm_realize (s : SortTag) (v : α ⊕ Fin n → M) :
    (zeroTerm s).realize v = sortZero s := by
  cases s <;> simp only [zeroTerm, sortZero, Term.realize, Transfer.iVFZero, iRVZero]
  all_goals
    congr 1
    funext i
    exact i.elim0

theorem sortedTerm_realize (hcan : IsCanonical (M := M))
    (sα : α → SortTag) (sn : Fin n → SortTag) (v : α → M) (xs : Fin n → M)
    (hv : ∀ a, sortEval (sα a) (v a)) (hx : ∀ i, sortEval (sn i) (xs i))
    (t : LRV.Term (α ⊕ Fin n)) :
    (sortedTerm sα sn t).realize (Sum.elim v xs) = t.realize (Sum.elim v xs) := by
  induction t with
  | var a => rfl
  | func f ts ih =>
      simp only [sortedTerm]
      split_ifs with h
      · change Structure.funMap (L := LRV) f
          (fun i => (sortedTerm sα sn (ts i)).realize (Sum.elim v xs)) = _
        have he := funext ih
        rw [he]
        rfl
      · rw [zeroTerm_realize]
        symm
        apply hcan.1 f _
        intro hall
        apply h
        intro i
        have hi := term_sort hM sα sn v xs hv hx (sortedTerm sα sn (ts i))
          (sortedTerm_sort sα sn (ts i))
        rw [ih i] at hi
        exact sort_unique hM hi (hall i)

end Semantics

/-- Sort checking for atomic formulas after totalizing their terms. A mismatched
atom is false in every canonical model of the theory. -/
noncomputable def sortedQF (sα : α → SortTag) (sn : Fin n → SortTag) :
    LRV.BoundedFormula α n → LRV.BoundedFormula α n
  | .falsum => .falsum
  | .equal t u =>
      if resultSort sα sn t = resultSort sα sn u then
        .equal (sortedTerm sα sn t) (sortedTerm sα sn u)
      else .falsum
  | .rel r ts =>
      if ∀ i, resultSort sα sn (ts i) = Rel.argSort r i then
        .rel r (fun i => sortedTerm sα sn (ts i))
      else .falsum
  | .imp φ ψ => .imp (sortedQF sα sn φ) (sortedQF sα sn ψ)
  | .all _ => .falsum

theorem sortedQF_isQF (sα : α → SortTag) (sn : Fin n → SortTag)
    (φ : LRV.BoundedFormula α n) : (sortedQF sα sn φ).IsQF := by
  induction φ with
  | falsum => exact .falsum
  | equal t u =>
      simp only [sortedQF]
      split_ifs
      · exact BoundedFormula.IsAtomic.isQF (.equal _ _)
      · exact .falsum
  | rel r ts =>
      simp only [sortedQF]
      split_ifs
      · exact BoundedFormula.IsAtomic.isQF (.rel _ _)
      · exact .falsum
  | imp φ ψ ihφ ihψ => exact .imp (ihφ sn) (ihψ sn)
  | all φ ih => exact .falsum

theorem sortedQF_wellSorted (sα : α → SortTag) (sn : Fin n → SortTag)
    (φ : LRV.BoundedFormula α n) : WellSorted sα sn (sortedQF sα sn φ) := by
  induction φ with
  | falsum => exact .falsum _
  | equal t u =>
      simp only [sortedQF]
      split_ifs with h
      · exact .equal sn (sortedTerm_sort sα sn t)
          (by simpa only [h] using sortedTerm_sort sα sn u)
      · exact .falsum _
  | rel r ts =>
      simp only [sortedQF]
      split_ifs with h
      · apply WellSorted.rel
        intro i
        simpa only [h i] using sortedTerm_sort sα sn (ts i)
      · exact .falsum _
  | imp φ ψ ihφ ihψ => exact .imp sn (ihφ sn) (ihψ sn)
  | all φ ih => exact .falsum _

theorem sortedQF_realize {M : Type} [LRV.Structure M]
    (hM : M ⊨ Axioms.ACVF) (hcan : IsCanonical (M := M))
    (sα : α → SortTag) (sn : Fin n → SortTag) (v : α → M) (xs : Fin n → M)
    (hv : ∀ a, sortEval (sα a) (v a)) (hx : ∀ i, sortEval (sn i) (xs i))
    (φ : LRV.BoundedFormula α n) (hq : φ.IsQF) :
    (sortedQF sα sn φ).Realize v xs ↔ φ.Realize v xs := by
  induction φ with
  | falsum => rfl
  | equal t u =>
      simp only [sortedQF]
      split_ifs with h
      · change ((sortedTerm sα sn t).realize (Sum.elim v xs) =
          (sortedTerm sα sn u).realize (Sum.elim v xs)) ↔ _
        rw [sortedTerm_realize hM hcan sα sn v xs hv hx t,
          sortedTerm_realize hM hcan sα sn v xs hv hx u]
        rfl
      · change False ↔ t.realize (Sum.elim v xs) = u.realize (Sum.elim v xs)
        refine ⟨False.elim, ?_⟩
        intro he
        apply h
        have ht := term_sort hM sα sn v xs hv hx (sortedTerm sα sn t)
          (sortedTerm_sort sα sn t)
        have hu := term_sort hM sα sn v xs hv hx (sortedTerm sα sn u)
          (sortedTerm_sort sα sn u)
        rw [sortedTerm_realize hM hcan sα sn v xs hv hx t, he] at ht
        rw [sortedTerm_realize hM hcan sα sn v xs hv hx u] at hu
        exact sort_unique hM ht hu
  | rel r ts =>
      simp only [sortedQF]
      split_ifs with h
      · change Structure.RelMap (L := LRV) r
          (fun i => (sortedTerm sα sn (ts i)).realize (Sum.elim v xs)) ↔ _
        have he := funext fun i => sortedTerm_realize hM hcan sα sn v xs hv hx (ts i)
        rw [he]
        rfl
      · change False ↔ Structure.RelMap (L := LRV) r
          (fun i => (ts i).realize (Sum.elim v xs))
        refine ⟨False.elim, ?_⟩
        intro hrel
        apply h
        intro i
        have hi := term_sort hM sα sn v xs hv hx (sortedTerm sα sn (ts i))
          (sortedTerm_sort sα sn (ts i))
        rw [sortedTerm_realize hM hcan sα sn v xs hv hx (ts i)] at hi
        exact sort_unique hM hi (relation_sorted hM hcan r _ hrel i)
  | imp φ ψ ihφ ihψ =>
      cases hq with
      | of_isAtomic ha => cases ha
      | imp hφ hψ =>
          exact imp_congr (ihφ sn xs hx hφ) (ihψ sn xs hx hψ)
  | all φ ih => exact False.elim (BoundedFormula.not_all_isQF φ hq)

/-- Canonical-model QE allowing an arbitrary quantifier-free output. This is the
output shape delivered by a full-language model-theoretic QE criterion. -/
def HasRawQEOnCanonical (T : LRV.Theory) : Prop :=
  ∀ (α : Type) (sα : α → SortTag) (n : ℕ) (sn : Fin n → SortTag)
    (φ : LRV.BoundedFormula α n), WellSorted sα sn φ →
    ∃ ψ : LRV.BoundedFormula α n, ψ.IsQF ∧
      ∀ (M : Type) [LRV.Structure M], M ⊨ T → IsCanonical (M := M) →
        ∀ (v : α → M) (xs : Fin n → M),
          (∀ a, sortEval (sα a) (v a)) → (∀ i, sortEval (sn i) (xs i)) →
          (φ.Realize v xs ↔ ψ.Realize v xs)

theorem canonicalQE_of_rawQE (h : HasRawQEOnCanonical Axioms.ACVF) :
    HasQEOnCanonical Axioms.ACVF := by
  intro α sα n sn φ hφ
  obtain ⟨ψ, hq, heq⟩ := h α sα n sn φ hφ
  refine ⟨sortedQF sα sn ψ, sortedQF_isQF sα sn ψ, sortedQF_wellSorted sα sn ψ, ?_⟩
  intro M sM hM hc v xs hv hx
  exact (heq M hM hc v xs hv hx).trans (sortedQF_realize hM hc sα sn v xs hv hx ψ hq).symm

/-- Full-language canonical QE yields the well-sorted target for the same
author-corrected language, including named RV inversion. -/
theorem hasQE_of_raw_canonical (h : HasRawQEOnCanonical Axioms.ACVF) : HasQE Axioms.ACVF :=
  hasQE_of_canonical (canonicalQE_of_rawQE h)

end CanonicalStructure

#print axioms CanonicalStructure.sortedTerm_sort
#print axioms CanonicalStructure.sort_unique
#print axioms CanonicalStructure.relation_sorted
#print axioms CanonicalStructure.sortedTerm_realize
#print axioms CanonicalStructure.sortedQF_realize
#print axioms CanonicalStructure.canonicalQE_of_rawQE
#print axioms CanonicalStructure.hasQE_of_raw_canonical
