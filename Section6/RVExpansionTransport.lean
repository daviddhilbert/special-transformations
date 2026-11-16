module

public import Section6.RVSubstructure

@[expose] public section

/-! Transport an arbitrary RV expansion along an actual native
isomorphism of substructures. Its interpretation is transported only on
RV; it is never extended to the ambient algebraically closed field.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section6.RVExpansionTransport
open RVTermSupport RVAbstraction

variable {C D : Type} [LRV.Structure C] [LRV.Structure D]
variable [C ⊨ Axioms.ACVF] [D ⊨ Axioms.ACVF]
variable {E : Language} {Y : LRV.Substructure C} {X : LRV.Substructure D}

theorem rv_preserved (e : Y ≃[LRV] X) (y : Y) : iRV (e y).val ↔ iRV y.val := by
  have h := e.map_rel Rel.memRV ![y]
  have he : e ∘ ![y] = ![e y] := by funext i; fin_cases i; rfl
  rw [he] at h
  change Structure.RelMap (L := LRV) Rel.memRV (fun i => (![e y] i).val) ↔
    Structure.RelMap (L := LRV) Rel.memRV (fun i => (![y] i).val) at h
  have hX : (fun i : Fin 1 => (![e y] i).val) = ![(e y).val] := by
    funext i
    fin_cases i
    rfl
  have hY : (fun i : Fin 1 => (![y] i).val) = ![y.val] := by
    funext i
    fin_cases i
    rfl
  rw [hX, hY] at h
  exact h

def rvEquiv (e : Y ≃[LRV] X) : SubRV (Y : Set C) ≃ SubRV (X : Set D) where
  toFun q := ⟨⟨(e (RVSubstructure.inclusion Y q)).val,
    (rv_preserved e _).mpr q.val.property⟩, (e (RVSubstructure.inclusion Y q)).property⟩
  invFun q := ⟨⟨(e.symm (RVSubstructure.inclusion X q)).val,
    (rv_preserved e.symm _).mpr q.val.property⟩, (e.symm (RVSubstructure.inclusion X q)).property⟩
  left_inv q := by
    apply RVSubstructure.inclusion_injective Y
    exact e.symm_apply_apply (RVSubstructure.inclusion Y q)
  right_inv q := by
    apply RVSubstructure.inclusion_injective X
    exact e.apply_symm_apply (RVSubstructure.inclusion X q)

theorem inclusion_rvEquiv (e : Y ≃[LRV] X) (q : SubRV (Y : Set C)) :
    RVSubstructure.inclusion X (rvEquiv e q) = e (RVSubstructure.inclusion Y q) := rfl

@[instance_reducible] def extraStructure (e : Y ≃[LRV] X)
    [E.Structure (SubRV (Y : Set C))] : E.Structure (SubRV (X : Set D)) where
  funMap f z := rvEquiv e (Structure.funMap f ((rvEquiv e).symm ∘ z))
  RelMap r z := Structure.RelMap r ((rvEquiv e).symm ∘ z)

def auxiliaryEquiv (e : Y ≃[LRV] X) [E.Structure (SubRV (Y : Set C))] :
    letI := extraStructure (E := E) e
    letI := RVSubstructure.auxiliaryStructure (E := E) Y
    letI := RVSubstructure.auxiliaryStructure (E := E) X
    SubRV (Y : Set C) ≃[Auxiliary E] SubRV (X : Set D) := by
  letI := extraStructure (E := E) e
  letI := RVSubstructure.auxiliaryStructure (E := E) Y
  letI := RVSubstructure.auxiliaryStructure (E := E) X
  refine { toEquiv := rvEquiv e, map_fun' := ?_, map_rel' := ?_ }
  · intro k f z
    cases f with
    | inr f =>
      change rvEquiv e (Structure.funMap f z) =
        rvEquiv e (Structure.funMap f ((rvEquiv e).symm ∘ rvEquiv e ∘ z))
      have he : (rvEquiv e).symm ∘ rvEquiv e ∘ z = z := by
        funext i
        exact (rvEquiv e).symm_apply_apply (z i)
      rw [he]
    | inl f =>
      apply RVSubstructure.inclusion_injective X
      have h := e.map_fun f.val (RVSubstructure.inclusion Y ∘ z)
      exact h
  · intro k r z
    cases r with
    | inr r =>
      change Structure.RelMap r ((rvEquiv e).symm ∘ rvEquiv e ∘ z) ↔ Structure.RelMap r z
      have he : (rvEquiv e).symm ∘ rvEquiv e ∘ z = z := by
        funext i
        exact (rvEquiv e).symm_apply_apply (z i)
      rw [he]
    | inl r =>
      exact e.map_rel r.val (RVSubstructure.inclusion Y ∘ z)

private theorem inverse_arguments (e : Y ≃[LRV] X) {k : ℕ} (z : Fin k → Y)
    (h : ∀ i, iRV (z i).val) (hx : ∀ i, iRV (e (z i)).val) :
    (rvEquiv e).symm ∘
      (fun i => (⟨⟨(e (z i)).val, hx i⟩, (e (z i)).property⟩ : SubRV (X : Set D))) =
      (fun i => (⟨⟨(z i).val, h i⟩, (z i).property⟩ : SubRV (Y : Set C))) := by
  funext i
  apply (rvEquiv e).injective
  simp only [Function.comp_apply, Equiv.apply_symm_apply]
  rfl

private theorem native_zero (Z : LRV.Substructure C) :
    Structure.funMap (L := LRV) Fn.rvZero (Fin.elim0 : Fin 0 → Z) =
      RVSubstructure.inclusion Z (RVSubstructure.zero Z) := by
  apply Subtype.ext
  change Structure.funMap (L := LRV) Fn.rvZero _ = Structure.funMap (L := LRV) Fn.rvZero _
  congr 1
  funext i
  exact i.elim0

def expandedEquiv (e : Y ≃[LRV] X) [sEY : E.Structure (SubRV (Y : Set C))] :
    letI := extraStructure (E := E) e
    letI := RVSubstructure.extraStructure (E := E) Y
    letI := RVSubstructure.extraStructure (E := E) X
    Y ≃[Expanded E] X := by
  letI := extraStructure (E := E) e
  letI := RVSubstructure.extraStructure (E := E) Y
  letI := RVSubstructure.extraStructure (E := E) X
  refine { toEquiv := e.toEquiv, map_fun' := ?_, map_rel' := ?_ }
  · intro k f z
    cases f with
    | inl f => exact e.map_fun f z
    | inr f =>
      change e (if h : ∀ i, iRV (z i).val then
        RVSubstructure.inclusion Y (@Structure.funMap E (SubRV (Y : Set C)) sEY k f
          (fun i => ⟨⟨(z i).val, h i⟩, (z i).property⟩)) else RVSubstructure.inclusion Y (RVSubstructure.zero Y)) =
        (if h : ∀ i, iRV (e (z i)).val then
          RVSubstructure.inclusion X (rvEquiv e
            (@Structure.funMap E (SubRV (Y : Set C)) sEY k f
              ((rvEquiv e).symm ∘ fun i => ⟨⟨(e (z i)).val, h i⟩, (e (z i)).property⟩)))
          else RVSubstructure.inclusion X (RVSubstructure.zero X))
      by_cases h : ∀ i, iRV (z i).val
      · have hx : ∀ i, iRV (e (z i)).val := fun i => (rv_preserved e _).mpr (h i)
        rw [dif_pos h, dif_pos hx]
        rw [inverse_arguments e z h hx, inclusion_rvEquiv]
      · have hx : ¬ ∀ i, iRV (e (z i)).val := by
          intro hx
          exact h (fun i => (rv_preserved e _).mp (hx i))
        rw [dif_neg h, dif_neg hx]
        have hz := e.map_fun Fn.rvZero (Fin.elim0 : Fin 0 → Y)
        have h0 : e ∘ (Fin.elim0 : Fin 0 → Y) = Fin.elim0 := Subsingleton.elim _ _
        rw [h0] at hz
        rw [native_zero Y, native_zero X] at hz
        exact hz
  · intro k r z
    cases r with
    | inl r => exact e.map_rel r z
    | inr r =>
      change (if h : ∀ i, iRV (e (z i)).val then
        @Structure.RelMap E (SubRV (Y : Set C)) sEY k r
          ((rvEquiv e).symm ∘ fun i => ⟨⟨(e (z i)).val, h i⟩, (e (z i)).property⟩) else False) ↔
        (if h : ∀ i, iRV (z i).val then @Structure.RelMap E (SubRV (Y : Set C)) sEY k r
          (fun i => ⟨⟨(z i).val, h i⟩, (z i).property⟩) else False)
      by_cases h : ∀ i, iRV (z i).val
      · have hx : ∀ i, iRV (e (z i)).val := fun i => (rv_preserved e _).mpr (h i)
        rw [dif_pos h, dif_pos hx]
        rw [inverse_arguments e z h hx]
      · have hx : ¬ ∀ i, iRV (e (z i)).val := by
          intro hx
          exact h (fun i => (rv_preserved e _).mp (hx i))
        rw [dif_neg h, dif_neg hx]

end SpecialTransformations.Section6.RVExpansionTransport
