module

public import Enc
public import Mathlib.ModelTheory.Semantics

@[expose] public section

/-!
The occurrence support for the corrected language, also in arbitrary
RV-only expansions. The language is the sum of the published LRV and the
extra RV signature. Numerators and denominators are both collected: an
inverse does not stop the recursion. VF inversion remains unnamed.
-/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.RVTermSupport

abbrev Expanded (E : Language) := LRV.sum E

def resultSort {E : Language} {k : ℕ} : (Expanded E).Functions k → SortTag
  | .inl f => Fn.resSort f
  | .inr _ => .rv

def argumentSort {E : Language} {k : ℕ} : (Expanded E).Functions k → Fin k → SortTag
  | .inl f => Fn.argSort f
  | .inr _ => fun _ => .rv

def termSort {E : Language} {I : Type} (σ : I → SortTag) :
    (Expanded E).Term I → Option SortTag
  | .var i => some (σ i)
  | .func f ts =>
      if ∀ i, termSort σ (ts i) = some (argumentSort f i)
      then some (resultSort f) else none

theorem termSort_func {E : Language} {I : Type} (σ : I → SortTag) {k : ℕ}
    (f : (Expanded E).Functions k) (ts : Fin k → (Expanded E).Term I) {s : SortTag} :
    termSort σ (.func f ts) = some s ↔
      (∀ i, termSort σ (ts i) = some (argumentSort f i)) ∧ resultSort f = s := by
  classical
  simp only [termSort]
  split_ifs with h
  · simp [h]
  · simp [h]

/-- VF polynomial expressions occurring below rv, at any depth, including
below inverses and in expressions used as domain guards. -/
def leaves {E : Language} {I : Type} : (Expanded E).Term I → List ((Expanded E).Term I)
  | .var _ => []
  | .func f ts => match f with
    | .inl .rvMap => [ts 0]
    | .inl _ => (List.finRange _).flatMap (fun i => leaves (ts i))
    | .inr _ => (List.finRange _).flatMap (fun i => leaves (ts i))

def rvTerm {E : Language} {I : Type} (t : (Expanded E).Term I) : (Expanded E).Term I :=
  .func (.inl .rvMap) ![t]

def inverseTerm {E : Language} {I : Type} (t : (Expanded E).Term I) :
    (Expanded E).Term I := .func (.inl .rvInv) ![t]

def quotientTerm {E : Language} {I : Type} (p q : (Expanded E).Term I) :
    (Expanded E).Term I := .func (.inl .rvMul) ![rvTerm p, inverseTerm (rvTerm q)]

/-- The numerator and denominator are both occurring polynomials. This is
the totalized RV expression; the rational-function pole guard is separate. -/
theorem leaves_quotient {E : Language} {I : Type} (p q : (Expanded E).Term I) :
    leaves (quotientTerm p q) = [p, q] := by
  rfl

theorem leaves_inverse {E : Language} {I : Type} (t : (Expanded E).Term I) :
    leaves (inverseTerm t) = leaves t := by
  simp [inverseTerm, leaves, List.finRange_succ]

variable {E : Language} {I M : Type} [(Expanded E).Structure M]

/-- Equality of all collected rv-polynomial values controls the whole RV
term. No nonzero premise is needed for this congruence: inversion is an
actual total function, including at the single absorbing point. -/
theorem realize_eq_of_leaves (σ : I → SortTag) (t : (Expanded E).Term I)
    (ht : termSort σ t = some .rv) (a b : I → M)
    (hvars : ∀ i, σ i = .rv → a i = b i)
    (hleaves : ∀ p ∈ leaves t, (rvTerm p).realize a = (rvTerm p).realize b) :
    t.realize a = t.realize b := by
  induction t with
  | var i => exact hvars i (Option.some.inj ht)
  | @func k f ts ih =>
    obtain ⟨harg, hres⟩ := (termSort_func σ f ts).mp ht
    have step (hf : ∀ i, argumentSort f i = .rv)
        (hdef : leaves (.func f ts) = (List.finRange k).flatMap (fun i => leaves (ts i))) :
        (Term.func f ts).realize a = (Term.func f ts).realize b := by
      change Structure.funMap (L := Expanded E) f _ = Structure.funMap (L := Expanded E) f _
      congr 1
      funext i
      apply ih i (by rw [← hf i]; exact harg i)
      intro p hp
      apply hleaves p
      rw [hdef]
      exact List.mem_flatMap.mpr ⟨i, List.mem_finRange i, hp⟩
    cases f with
    | inr f => exact step (fun _ => rfl) rfl
    | inl f =>
      cases f with
      | vfZero => cases hres
      | vfOne => cases hres
      | vfAdd => cases hres
      | vfNeg => cases hres
      | vfMul => cases hres
      | rvOne => exact step (fun i => i.elim0) rfl
      | rvZero => exact step (fun i => i.elim0) rfl
      | rvMul => exact step (fun _ => rfl) rfl
      | rvInv => exact step (fun _ => rfl) rfl
      | kAdd => exact step (fun _ => rfl) rfl
      | kNeg => exact step (fun _ => rfl) rfl
      | rvMap =>
        have he := hleaves (ts 0) (by exact List.mem_cons_self)
        have eta : ts = ![ts 0] := by funext i; fin_cases i; rfl
        rw [eta]
        exact he

end SpecialTransformations.Section6.RVTermSupport
