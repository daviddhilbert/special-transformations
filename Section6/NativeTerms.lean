module

public import Section6.RVTermSupport

@[expose] public section

/-! A well-sorted FV term in an RV-only expansion is literally the image
of a native LRV FV term. This is syntax, before any model or assignment.
It lets Section 6 prepare the actual finite native term map with the
given general Section 5 theorem, without rebuilding polynomial algebra.
-/

noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.NativeTerms
open RVTermSupport

theorem exists_native_vf {E : Language} {V : Type} (t : (Expanded E).Term V)
    (ht : termSort (fun _ => .vf) t = some .vf) :
    ∃ q : LRV.Term V,
      (LHom.sumInl : LRV →ᴸ Expanded E).onTerm q = t ∧
      TmSort (fun _ => .vf) (fun _ : Fin 0 => .vf) (q.relabel Sum.inl) = some .vf := by
  induction t with
  | var v => exact ⟨.var v, rfl, rfl⟩
  | func f ts ih =>
    obtain ⟨harg, hres⟩ := (termSort_func (fun _ => .vf) f ts).mp ht
    cases f with
    | inr f => cases hres
    | inl f =>
      change Fn.resSort f = .vf at hres
      have hs : ∀ i, Fn.argSort f i = .vf := by
        cases f <;> try cases hres
        all_goals intro i; first | exact i.elim0 | rfl
      have hargs : ∀ i, ∃ q : LRV.Term V,
          (LHom.sumInl : LRV →ᴸ Expanded E).onTerm q = ts i ∧
          TmSort (fun _ => .vf) (fun _ : Fin 0 => .vf) (q.relabel Sum.inl) = some .vf := by
        intro i
        exact ih i (by simpa only [argumentSort, hs i] using harg i)
      choose qs he hq using hargs
      refine ⟨.func f qs, ?_, ?_⟩
      · change Term.func (L := Expanded E) (Sum.inl f)
          (fun i => (LHom.sumInl : LRV →ᴸ Expanded E).onTerm (qs i)) =
          Term.func (L := Expanded E) (Sum.inl f) ts
        congr 1
        exact funext he
      · change TmSort (fun _ => .vf) (fun _ : Fin 0 => .vf)
          (.func f (fun i => (qs i).relabel Sum.inl)) = some .vf
        have hn : TmSort (fun _ => .vf) (fun _ : Fin 0 => .vf)
            (.func f (fun i => (qs i).relabel Sum.inl)) = some (Fn.resSort f) := by
          apply tmSort_func
          intro i
          simpa only [hs i] using hq i
        exact hn.trans (congrArg some hres)

theorem realize_native {E : Language} {V M : Type}
    [LRV.Structure M] [E.Structure M] (q : LRV.Term V) (v : V → M) :
    ((LHom.sumInl : LRV →ᴸ Expanded E).onTerm q).realize v = q.realize v :=
  LHom.realize_onTerm _ _ _

end SpecialTransformations.Section6.NativeTerms
