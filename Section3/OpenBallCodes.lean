import Section3.ClosedBallQuotient
import Section3.OpenBallHullGeometry

/- Component: OpenBallCodes -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.OpenBallCodes
variable {M : Type} [sM : LRV.Structure M]

private def variableTerm (i : Fin 3) : LRV.Term (Fin 0 ⊕ Fin 3) := .var (.inr i)

/-- A strict disc is the negation of the reverse weak valuation comparison.
The first two VF coordinates are its center and actual radius representative. -/
def body : LRV.BoundedFormula (Fin 0) 3 :=
  (.rel Rel.rvLe ![.func Fn.rvMap ![.func Fn.vfAdd ![variableTerm 2,
    .func Fn.vfNeg ![variableTerm 0] ] ],.func Fn.rvMap ![variableTerm 1] ] :
      LRV.BoundedFormula (Fin 0) 3).not

theorem body_sorted : WellSorted (fun _ : Fin 0 => .vf) (fun _ => .vf) body := by
  apply wellSorted_not
  apply WellSorted.rel
  intro i
  fin_cases i <;> decide

def tuple (q : Fin 2 → M) (x : M) : Fin 3 → M := ![q 0,q 1,x]

def Proper (q : Fin 2 → M) : Prop := (∀ i, iVF (q i)) ∧ q 1 ≠ iVFZero

def rawBall (q : Fin 2 → M) : Set M :=
  {x | Proper q ∧ iVF x ∧ body.Realize Fin.elim0 (tuple q x)}

def ball (q : Fin 2 → M) : Set (VFType (M := M)) := {x | x.val ∈ rawBall q}

/- The two evaluation helpers follow the existing internal
ClosedBallCodes.body_realize proof, retaining its generic symbol interface. -/
private theorem realize_func1 {β : Type} (f : Fn 1) (t : LRV.Term β) (v : β → M) :
    (Term.func f ![t] : LRV.Term β).realize v = Structure.funMap (L := LRV) f ![t.realize v] := by
  change Structure.funMap (L := LRV) f (fun i => _) = _
  congr 1
  funext i
  fin_cases i
  rfl

private theorem realize_func2 {β : Type} (f : Fn 2) (t u : LRV.Term β) (v : β → M) :
    (Term.func f ![t,u] : LRV.Term β).realize v = Structure.funMap (L := LRV) f ![t.realize v,u.realize v] := by
  change Structure.funMap (L := LRV) f (fun i => _) = _
  congr 1
  funext i
  fin_cases i <;> rfl

theorem body_realize (q : Fin 2 → M) (x : M) :
    body.Realize Fin.elim0 (tuple q x) ↔
      ¬ iLe (iRv (iVFAdd x (iVFNeg (q 0)))) (iRv (q 1)) := by
  rw [body,BoundedFormula.realize_not]
  apply not_congr
  change Structure.RelMap (L := LRV) Rel.rvLe (fun i =>
    (![Term.func Fn.rvMap ![Term.func Fn.vfAdd ![variableTerm 2,
      Term.func Fn.vfNeg ![variableTerm 0] ] ],Term.func Fn.rvMap ![variableTerm 1] ] i).realize _) ↔ _
  have he : (fun i =>
      (![Term.func Fn.rvMap ![Term.func Fn.vfAdd ![variableTerm 2,
        Term.func Fn.vfNeg ![variableTerm 0] ] ],Term.func Fn.rvMap ![variableTerm 1] ] i).realize
        (Sum.elim (Fin.elim0 : Fin 0 → M) (tuple q x))) =
      ![iRv (iVFAdd x (iVFNeg (q 0))),iRv (q 1)] := by
    funext i
    fin_cases i
    · change (Term.func Fn.rvMap ![Term.func Fn.vfAdd ![variableTerm 2,
        Term.func Fn.vfNeg ![variableTerm 0] ] ]).realize _ = _
      rw [realize_func1,realize_func2,realize_func1]
      rfl
    · change (Term.func Fn.rvMap ![variableTerm 1]).realize _ = _
      rw [realize_func1]
      rfl
  rw [he]
  rfl

variable [hM : M ⊨ Axioms.ACVF]

theorem ball_eq_open {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (q : Fin 2 → M) (hq : Proper q) :
    ball q = ValOneEC.openBall v (⟨q 0,hq.1 0⟩ : VFType (M := M))
      (v (⟨q 1,hq.1 1⟩ : VFType (M := M))) := by
  ext x
  change x.val ∈ rawBall q ↔ _
  rw [rawBall,Set.mem_setOf_eq,body_realize,and_iff_right hq,and_iff_right x.property]
  let a : VFType (M := M) := ⟨q 0,hq.1 0⟩
  let r : VFType (M := M) := ⟨q 1,hq.1 1⟩
  have hd : (x-a).val = iVFAdd x.val (iVFNeg (q 0)) := by rw [sub_eq_add_neg]; rfl
  have hc : iLe (iRv (iVFAdd x.val (iVFNeg (q 0)))) (iRv (q 1)) ↔
      VFValued.predV r (x-a) := by
    change _ ↔ iLe (iRv (x-a).val) (iRv (q 1))
    rw [hd]
  exact (not_congr (hc.trans (hv r (x-a)))).trans not_le

def Code (M : Type) [LRV.Structure M] := {q : Fin 2 → M // Proper q}

def codeSetoid : Setoid (Code M) where
  r q u := rawBall q.val = rawBall u.val
  iseqv := ⟨fun _ => rfl,Eq.symm,Eq.trans⟩

abbrev OpenBall (M : Type) [LRV.Structure M] := Quotient (codeSetoid (M := M))

def underlying : OpenBall M → Set M :=
  Quotient.lift (fun q : Code M => rawBall q.val) (fun _ _ h => h)

theorem underlying_injective : Function.Injective (underlying (M := M)) := by
  intro B B'
  induction B using Quotient.inductionOn with
  | h q =>
    induction B' using Quotient.inductionOn with
    | h u => exact fun he => Quotient.sound he

def pullback (A : Set (OpenBall M)) : Set (Fin 2 → M) :=
  {q | ∃ hq : Proper q, Quotient.mk _ (⟨q,hq⟩ : Code M) ∈ A}

end SpecialTransformations.Section3.OpenBallCodes

/- Component: OpenBallHulls -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.OpenBallCodes
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def hullCode (q : Fin 2 → M) : Fin 3 → M := ![q 0,q 1,iVFOne]

theorem hullCode_sorted (q : Fin 2 → M) (hq : Proper q) :
    ∀ i, iVF (hullCode q i) := by
  intro i
  fin_cases i
  · exact hq.1 0
  · exact hq.1 1
  · exact (1 : VFType (M := M)).property

theorem hullCode_flag_ne_zero (q : Fin 2 → M) : hullCode q 2 ≠ iVFZero := by
  intro he
  exact (one_ne_zero : (1 : VFType (M := M)) ≠ 0) (Subtype.ext he)

theorem radius_ne_zero (q : Fin 2 → M) (hq : Proper q) :
    (⟨q 1,hq.1 1⟩ : VFType (M := M)) ≠ (0 : VFType (M := M)) := by
  intro he
  exact hq.2 (congrArg Subtype.val he)

/-- Passing from a proper open disc to its same-radius closed hull
respects actual balls, regardless of which real code represents them. -/
theorem hull_raw_eq_of_raw_eq (q u : Fin 2 → M) (hq : Proper q) (hu : Proper u)
    (he : rawBall q = rawBall u) :
    ClosedBallCodes.rawBall (hullCode q) = ClosedBallCodes.rawBall (hullCode u) := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  have ho : ball q = ball u := congrArg
    (fun U : Set M => {x : VFType (M := M) | x.val ∈ U}) he
  rw [ball_eq_open v hv q hq,ball_eq_open v hv u hu] at ho
  have hc := Balls.closedHull_eq_of_strictDisc_eq v
    (⟨q 0,hq.1 0⟩ : VFType (M := M)) (⟨u 0,hu.1 0⟩ : VFType (M := M))
    (⟨q 1,hq.1 1⟩ : VFType (M := M)) (⟨u 1,hu.1 1⟩ : VFType (M := M))
    (radius_ne_zero q hq) (radius_ne_zero u hu) ho
  have hqC := ClosedBallCodes.ball_eq_closed v hv (hullCode q)
    (hullCode_sorted q hq) (hullCode_flag_ne_zero q)
  have huC := ClosedBallCodes.ball_eq_closed v hv (hullCode u)
    (hullCode_sorted u hu) (hullCode_flag_ne_zero u)
  have hC : ClosedBallCodes.ball (hullCode q) = ClosedBallCodes.ball (hullCode u) := by
    rw [hqC,huC]
    exact hc
  ext x
  by_cases hx : iVF x
  · exact Set.ext_iff.mp hC (⟨x,hx⟩ : VFType (M := M))
  · exact iff_of_false (fun h => hx h.2.1) (fun h => hx h.2.1)

def hull : OpenBall M → ClosedBallCodes.ClosedBall M :=
  Quotient.map (fun q : Code M =>
    (⟨hullCode q.val,hullCode_sorted q.val q.property⟩ : ClosedBallCodes.Code M))
    (fun q u h => hull_raw_eq_of_raw_eq q.val u.val q.property u.property h)

theorem hull_mk (q : Code M) :
    hull (Quotient.mk _ q) = Quotient.mk _
      (⟨hullCode q.val,hullCode_sorted q.val q.property⟩ : ClosedBallCodes.Code M) := rfl

theorem raw_subset_hull (q : Fin 2 → M) (hq : Proper q) :
    rawBall q ⊆ ClosedBallCodes.rawBall (hullCode q) := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  have ho := ball_eq_open v hv q hq
  have hc := ClosedBallCodes.ball_eq_closed v hv (hullCode q)
    (hullCode_sorted q hq) (hullCode_flag_ne_zero q)
  intro x hx
  let y : VFType (M := M) := ⟨x,hx.2.1⟩
  have hy : y ∈ ball q := hx
  have hylt := Set.ext_iff.mp ho y |>.mp hy
  exact (Set.ext_iff.mp hc y).mpr hylt.le

theorem underlying_subset_hull (B : OpenBall M) :
    underlying B ⊆ ClosedBallCodes.underlying (hull B) := by
  induction B using Quotient.inductionOn with
  | h q => exact raw_subset_hull q.val q.property

end SpecialTransformations.Section3.OpenBallCodes
