import Section3.SortedBoolean
import Section3.EncodedBallGeometry
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.DefinableCosets
variable {M : Type} [sM : LRV.Structure M]

def relation (A : Set M) : Set (Fin 2 → M) :=
  {z | iVF (z 0) ∧ iVF (z 1) ∧ iVFAdd (z 0) (iVFNeg (z 1)) ∈ A}

theorem relation_raw_definable (S A : Set M) (hA : S.Definable₁ LRV A) :
    S.Definable LRV (relation A) := by
  have hn : S.DefinableFun LRV (fun z : Fin 2 → M => iVFNeg (z 1)) := by
    have hf : S.DefinableFun LRV (Structure.funMap (L := LRV) Fn.vfNeg) :=
      Set.DefinableFun.of_empty (@Set.DefinableFun.fun_symbol M LRV sM 1 Fn.vfNeg)
    have hg : S.DefinableMap LRV (fun z : Fin 2 → M => ![z 1]) := by
      intro i; fin_cases i; exact Set.DefinableFun.proj LRV
    exact hf.comp hg
  have hd : S.DefinableFun LRV (fun z : Fin 2 → M => iVFAdd (z 0) (iVFNeg (z 1))) := by
    have hf : S.DefinableFun LRV (Structure.funMap (L := LRV) Fn.vfAdd) :=
      Set.DefinableFun.of_empty (@Set.DefinableFun.fun_symbol M LRV sM 2 Fn.vfAdd)
    have hg : S.DefinableMap LRV (fun z : Fin 2 → M => ![z 0, iVFNeg (z 1)]) := by
      intro i; fin_cases i
      · exact Set.DefinableFun.proj LRV
      · exact hn
    exact hf.comp hg
  have hh := hA.preimage_map (fun _ : Fin 1 => hd)
  have h0 := (definableAt_sort S .vf).raw_definable.preimage_comp (fun _ : Fin 1 => (0 : Fin 2))
  have h1 := (definableAt_sort S .vf).raw_definable.preimage_comp (fun _ : Fin 1 => (1 : Fin 2))
  convert (h0.inter h1).inter hh using 1
  ext z
  change (iVF (z 0) ∧ iVF (z 1) ∧ _) ↔ (iVF (z 0) ∧ iVF (z 1)) ∧ _
  tauto

variable [hM : M ⊨ Axioms.ACVF]

theorem difference_normalize (x a : M) (hx : iVF x) (ha : iVF a) :
    @iVFAdd M (CanonicalStructure.normalize (M := M)) x
      (@iVFNeg M (CanonicalStructure.normalize (M := M)) a) = iVFAdd x (iVFNeg a) := by
  let N := CanonicalStructure.normalize (M := M)
  letI := sM
  have hn : @iVFNeg M N a = iVFNeg a := CanonicalStructure.normalize_fun Fn.vfNeg ![a]
    (by intro i; fin_cases i; exact ha)
  have hadd : @iVFAdd M N x (iVFNeg a) = iVFAdd x (iVFNeg a) :=
    CanonicalStructure.normalize_fun Fn.vfAdd ![x, iVFNeg a]
      (by intro i; fin_cases i; exact hx; exact vf_neg_mem hM ha)
  exact (congrArg (@iVFAdd M N x) hn).trans hadd

theorem relation_normalize (A : Set M) :
    @relation M (CanonicalStructure.normalize (M := M)) A = relation A := by
  ext z
  change (iVF (z 0) ∧ iVF (z 1) ∧ @iVFAdd M (CanonicalStructure.normalize (M := M)) (z 0) (@iVFNeg M (CanonicalStructure.normalize (M := M)) (z 1)) ∈ A) ↔
    (iVF (z 0) ∧ iVF (z 1) ∧ iVFAdd (z 0) (iVFNeg (z 1)) ∈ A)
  by_cases hx : iVF (z 0)
  · by_cases hy : iVF (z 1)
    · simp only [relation, Set.mem_ofPred_eq, hx, hy, true_and]
      rw [difference_normalize (z 0) (z 1) hx hy]
    · simp only [relation, Set.mem_ofPred_eq, hy, false_and, and_false]
  · simp only [relation, Set.mem_ofPred_eq, hx, false_and]

theorem relation_definable (S A : Set M) (hA : DefinableAt S .vf A) :
    DefinableOver S (fun _ => .vf) (relation A) := by
  let N := CanonicalStructure.normalize (M := M)
  letI := sM
  have hAN := (definableAt_normalize_iff S .vf A).mpr hA
  apply (definableOver_iff_normalized_raw S (fun _ => .vf) _).mpr
  constructor
  · have hh := @relation_raw_definable M N S A (@DefinableAt.raw_definable M N S .vf A hAN)
    exact relation_normalize A ▸ hh
  · intro z hz i
    fin_cases i
    · exact hz.1
    · exact hz.2.1

theorem mem_relation (H : AddSubgroup (VFType (M := M))) (x y : VFType (M := M)) :
    ![x.val,y.val] ∈ relation (Subtype.val '' (H : Set (VFType (M := M)))) ↔
      QuotientAddGroup.mk' H x = QuotientAddGroup.mk' H y := by
  rw [relation, Set.mem_ofPred_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, x.property, y.property, true_and]
  have hd : (x - y).val = iVFAdd x.val (iVFNeg y.val) := by rw [sub_eq_add_neg]; rfl
  rw [← hd]
  change (∃ z : VFType (M := M), z ∈ H ∧ z.val = (x - y).val) ↔
    (x : VFType (M := M) ⧸ H) = y
  rw [QuotientAddGroup.eq_iff_sub_mem]
  exact ⟨fun ⟨z,hz,he⟩ => (Subtype.ext he : z = x-y) ▸ hz, fun h => ⟨x-y,h,rfl⟩⟩

end SpecialTransformations.Section3.DefinableCosets
