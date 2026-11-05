import CanonicalStructure
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3
variable {M : Type} [sM : LRV.Structure M]

/-- Normalization preserves the carrier of every original substructure. -/
noncomputable def normalizeSubstructure (S : LRV.Substructure M) :
    @Language.Substructure LRV M (CanonicalStructure.normalize (M := M)) := by
  classical
  have hclosed {k : ℕ} (f : Fn k) (xs : Fin k → M) (hxs : ∀ i, xs i ∈ S) :
      @Structure.funMap LRV M sM k f xs ∈ S := S.fun_mem f xs hxs
  have hz : Transfer.iVFZero ∈ S := S.fun_mem Fn.vfZero Fin.elim0 (fun i => i.elim0)
  have hrz : iRVZero ∈ S := S.fun_mem Fn.rvZero Fin.elim0 (fun i => i.elim0)
  let N := @CanonicalStructure.normalize M sM
  letI := N
  refine { carrier := (S : Set M), fun_mem := ?_ }
  intro k f xs hxs
  change (if ∀ i, @sortEval M sM (Fn.argSort f i) (xs i) then
    @Structure.funMap LRV M sM k f xs else @CanonicalStructure.sortZero M sM (Fn.resSort f)) ∈ S
  split_ifs
  · exact hclosed f xs hxs
  · cases hs : Fn.resSort f with
    | vf => exact hz
    | rv => exact hrz

@[simp] theorem mem_normalizeSubstructure (S : LRV.Substructure M) (x : M) :
    x ∈ normalizeSubstructure S ↔ x ∈ S := Iff.rfl

variable [hM : M ⊨ Axioms.ACVF]

/-- The standing pure-characteristic-zero context transfers as well as ACVF. -/
theorem normalized_model00 (h00 : M ⊨ Axioms.ACVF00) :
    @Theory.Model LRV M (CanonicalStructure.normalize (M := M)) Axioms.ACVF00 := by
  apply (@Theory.model_iff LRV M (CanonicalStructure.normalize (M := M)) Axioms.ACVF00).mpr
  intro φ hφ
  have hr := h00.realize_of_mem φ hφ
  rcases hφ with (hφ | ⟨k, rfl⟩) | ⟨p, _, rfl⟩
  · exact ((@Theory.model_iff LRV M (CanonicalStructure.normalize (M := M)) Axioms.ACVF).mp
      (CanonicalStructure.normalized_model hM)) φ hφ
  · exact (CanonicalStructure.sentence_normalize hM _ (Audit.wss_charZeroVF k)).mpr hr
  · exact (CanonicalStructure.sentence_normalize hM _ (Audit.wss_residueCharZero p)).mpr hr

end SpecialTransformations.Section3
