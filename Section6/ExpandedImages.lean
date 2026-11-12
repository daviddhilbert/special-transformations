module

public import Section6.ExtraSortSemantics
public import Section6.CommonEnvelopeComparison

@[expose] public section

/-! An actual native embedding carries the arbitrary RV expansion to
its image. The source added-symbol laws are derived from the henselian
theory in ExtraSortSemantics. The resulting full expanded isomorphism is
proved here, so an algebraic-envelope input need supply only native data.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Milestone0.LRV FirstOrder.Language.sum
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.ExpandedImages
open RVTermSupport ExpandedLogic

variable {E : _root_.FirstOrder.Language.{0, 0}} {M C : Type}
variable [(Expanded E).Structure M] [sC : LRV.Structure C] [hC : C ⊨ Axioms.ACVF]
variable [sM : LRV.Structure M] [(LHom.sumInl : LRV →ᴸ Expanded E).IsExpansionOn M]

abbrev Native (M : Type) [(Expanded E).Structure M] :=
  (LHom.sumInl : LRV →ᴸ Expanded E).reduct M

abbrev Part := {m : M // tagEval (E := E) .rv m}

abbrev Image (f : Embedding LRV M C) := f.toHom.range

theorem rv_preserved (f : Embedding LRV M C) (m : M) :
    iRV (f m) ↔ tagEval (E := E) .rv m := by
  have h := f.map_rel Rel.memRV ![m]
  have he : f ∘ ![m] = ![f m] := by funext i; fin_cases i; rfl
  rw [he] at h
  exact h.trans (Iff.of_eq ((LHom.sumInl : LRV →ᴸ Expanded E).map_onRelation Rel.memRV ![m]).symm)

def rvImage (f : Embedding LRV M C) (q : Part (E := E) (M := M)) :
    SubRV ((Image f) : Set C) :=
  ⟨⟨f q.val, (rv_preserved (E := E) f q.val).mpr q.property⟩, ⟨q.val, rfl⟩⟩

theorem rvImage_bijective (f : Embedding LRV M C) :
    Function.Bijective (rvImage (E := E) f) := by
  constructor
  · intro q r he
    exact Subtype.ext (f.injective (congrArg (fun t => t.val.val) he))
  · intro q
    obtain ⟨m, hm⟩ := q.property
    have hr : tagEval (E := E) .rv m := (rv_preserved (E := E) f m).mp (hm.symm ▸ q.val.property)
    exact ⟨⟨m, hr⟩, Subtype.ext (Subtype.ext hm)⟩

def rvEquiv (f : Embedding LRV M C) :
    Part (E := E) (M := M) ≃ SubRV ((Image f) : Set C) :=
  Equiv.ofBijective (rvImage (E := E) f) (rvImage_bijective (E := E) f)

@[instance_reducible] def partStructure (h : ExtraSortSemantics.Laws (E := E) (M := M)) :
    E.Structure (Part (E := E) (M := M)) where
  funMap f z := ⟨Structure.funMap (L := Expanded E) (.inr f) (fun i => (z i).val),
    h.functions f _ (fun i => (z i).property)⟩
  RelMap r z := Structure.RelMap (L := Expanded E) (.inr r) (fun i => (z i).val)

@[instance_reducible] def extraStructure
    (f : Embedding LRV M C)
    (h : ExtraSortSemantics.Laws (E := E) (M := M)) :
    E.Structure (SubRV ((Image f) : Set C)) where
  funMap g z := rvEquiv (E := E) f
    ⟨Structure.funMap (L := Expanded E) (.inr g) (fun i => ((rvEquiv (E := E) f).symm (z i)).val),
      h.functions g _ (fun i => ((rvEquiv (E := E) f).symm (z i)).property)⟩
  RelMap r z := Structure.RelMap (L := Expanded E) (.inr r)
    (fun i => ((rvEquiv (E := E) f).symm (z i)).val)

private theorem inverse_arguments
    (f : Embedding LRV M C) {k : ℕ} (z : Fin k → M)
    (hz : ∀ i, tagEval (E := E) .rv (z i)) (hx : ∀ i, iRV (f (z i))) :
    (fun i => (rvEquiv (E := E) f).symm
      (⟨⟨f (z i), hx i⟩, ⟨z i, rfl⟩⟩ : SubRV ((Image f) : Set C))) =
      (fun i => (⟨z i, hz i⟩ : Part (E := E) (M := M))) := by
  funext i
  apply (rvEquiv (E := E) f).injective
  rw [Equiv.apply_symm_apply]
  rfl

private theorem image_zero (f : Embedding LRV M C) :
    f.equivRange (ExtraSortSemantics.zero (E := E) (M := M)) =
      RVSubstructure.inclusion (Image f) (RVSubstructure.zero (Image f)) := by
  apply Subtype.ext
  have h := f.map_fun Fn.rvZero (Fin.elim0 : Fin 0 → M)
  have h0 : f ∘ (Fin.elim0 : Fin 0 → M) = Fin.elim0 := Subsingleton.elim _ _
  rw [h0] at h
  have hs : ExtraSortSemantics.zero (E := E) (M := M) =
      Structure.funMap (L := LRV) Fn.rvZero (Fin.elim0 : Fin 0 → M) :=
    (LHom.sumInl : LRV →ᴸ Expanded E).map_onFunction Fn.rvZero Fin.elim0
  change f (ExtraSortSemantics.zero (E := E) (M := M)) = _
  rw [hs]
  convert h using 1 <;> congr 1 <;> funext i <;> exact i.elim0

private theorem inverse_values (f : Embedding LRV M C) {k : ℕ} (z : Fin k → M)
    (hz : ∀ i, tagEval (E := E) .rv (z i)) (hx : ∀ i, iRV (f (z i))) :
    (fun i => ((rvEquiv (E := E) f).symm
      (⟨⟨f (z i), hx i⟩, ⟨z i, rfl⟩⟩ : SubRV ((Image f) : Set C))).val) = z := by
  funext i
  exact congrArg Subtype.val (congrFun (inverse_arguments f z hz hx) i)

def expandedEquiv (f : Embedding LRV M C)
    (h : ExtraSortSemantics.Laws (E := E) (M := M)) :
    letI := extraStructure f h
    @FirstOrder.Language.Equiv (Expanded E) M (Image f) inferInstance
      (CommonEnvelopeComparison.expandedStructure (E := E) (Image f)) := by
  letI := extraStructure f h
  letI := RVSubstructure.extraStructure (E := E) (Image f)
  letI : (Expanded E).Structure (Image f) :=
    CommonEnvelopeComparison.expandedStructure (E := E) (Image f)
  let base : M ≃ Image f := f.equivRange.toEquiv
  refine { toEquiv := base, map_fun' := ?_, map_rel' := ?_ }
  · intro k g z
    cases g with
    | inl g =>
      apply Subtype.ext
      change f (Structure.funMap (L := Expanded E) (.inl g) z) =
        Structure.funMap (L := LRV) g (f ∘ z)
      exact (congrArg f ((LHom.sumInl : LRV →ᴸ Expanded E).map_onFunction g z)).trans
        (f.map_fun g z)
    | inr g =>
      change f.equivRange (Structure.funMap (L := Expanded E) (.inr g) z) =
        (if hx : ∀ i, iRV (f (z i)) then
          RVSubstructure.inclusion (Image f) (rvEquiv (E := E) f
            ⟨Structure.funMap (L := Expanded E) (.inr g)
              (fun i => ((rvEquiv (E := E) f).symm
                (⟨⟨f (z i), hx i⟩, ⟨z i, rfl⟩⟩ : SubRV ((Image f) : Set C))).val), _⟩)
          else RVSubstructure.inclusion (Image f) (RVSubstructure.zero (Image f)))
      by_cases hz : ∀ i, tagEval (E := E) .rv (z i)
      · have hx : ∀ i, iRV (f (z i)) := fun i => (rv_preserved (E := E) f _).mpr (hz i)
        rw [dif_pos hx]
        apply Subtype.ext
        change f (Structure.funMap (L := Expanded E) (.inr g) z) =
          f (Structure.funMap (L := Expanded E) (.inr g)
            (fun i => ((rvEquiv (E := E) f).symm
              (⟨⟨f (z i), hx i⟩, ⟨z i, rfl⟩⟩ : SubRV ((Image f) : Set C))).val))
        rw [inverse_values f z hz hx]
      · have hx : ¬ ∀ i, iRV (f (z i)) := by
          intro hx
          exact hz (fun i => (rv_preserved (E := E) f _).mp (hx i))
        rw [dif_neg hx, h.junk g z hz]
        exact image_zero f
  · intro k r z
    cases r with
    | inl r =>
      exact (f.map_rel r z).trans
        (Iff.of_eq ((LHom.sumInl : LRV →ᴸ Expanded E).map_onRelation r z).symm)
    | inr r =>
      change (if hx : ∀ i, iRV (f (z i)) then
        Structure.RelMap (L := Expanded E) (.inr r)
          (fun i => ((rvEquiv (E := E) f).symm
            (⟨⟨f (z i), hx i⟩, ⟨z i, rfl⟩⟩ : SubRV ((Image f) : Set C))).val) else False) ↔
        Structure.RelMap (L := Expanded E) (.inr r) z
      by_cases hz : ∀ i, tagEval (E := E) .rv (z i)
      · have hx : ∀ i, iRV (f (z i)) := fun i => (rv_preserved (E := E) f _).mpr (hz i)
        rw [dif_pos hx, inverse_values f z hz hx]
      · have hx : ¬ ∀ i, iRV (f (z i)) := by
          intro hx
          exact hz (fun i => (rv_preserved (E := E) f _).mp (hx i))
        rw [dif_neg hx]
        exact ⟨False.elim, fun hr => hz (h.relations r z hr)⟩

end SpecialTransformations.Section6.ExpandedImages


