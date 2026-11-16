module

public import Section4.GammaPredicates
public import Section3.GammaOperations

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section3.GammaParameters.EndpointLogic

noncomputable section

namespace SpecialTransformations.Section4.GammaSyntax

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {ι : Type} [Finite ι]

private theorem rv_product_nonzero (a b : M) (ha : NonzeroRV a) (hb : NonzeroRV b) :
    NonzeroRV (iRVMul a b) := by
  refine ⟨rv_mul_mem hM ha.1 hb.1, ?_⟩
  intro hz
  have hp := Values.vrv_mul (⟨a, ha.1⟩ : CanonicalRV.RVSort M) ⟨b, hb.1⟩
  have hi := (Values.vrv_eq_infinity_iff
    (⟨iRVMul a b, rv_mul_mem hM ha.1 hb.1⟩ : CanonicalRV.RVSort M)).mpr hz
  have he : (Values.gammaOf ⟨a, ha.1⟩ ha.2 * Values.gammaOf ⟨b, hb.1⟩ hb.2).val =
      Values.infinity := hp.symm.trans hi
  exact (Values.gammaOf ⟨a, ha.1⟩ ha.2 * Values.gammaOf ⟨b, hb.1⟩ hb.2).property he

private theorem codeValue_product (a b : M) (ha : NonzeroRV a) (hb : NonzeroRV b) :
    codeValue (iRVMul a b) = codeValue a * codeValue b := by
  simp only [codeValue, dif_pos ha, dif_pos hb, dif_pos (rv_product_nonzero a b ha hb), value]
  apply Subtype.ext
  exact Values.vrv_mul (M := M) (⟨a, ha.1⟩ : CanonicalRV.RVSort M) ⟨b, hb.1⟩

private def mulCode (a b : M) : M := @iRVMul M (CanonicalStructure.normalize (M := M)) a b

private theorem mulCode_eq (a b : M) (ha : NonzeroRV a) (hb : NonzeroRV b) :
    mulCode a b = iRVMul a b :=
  CanonicalStructure.normalize_fun Fn.rvMul ![a,b]
    (by intro i; fin_cases i; exact ha.1; exact hb.1)

/-- Multiplication on the actual Gamma quotient is definable using all
proper RV representatives and the named RV multiplication symbol. -/
theorem mul_definable (S : Set M) (i j k : ι) :
    Definable S (fun a : ι → Values.Gamma (M := M) => a i * a j = a k) := by
  let N := CanonicalStructure.normalize (M := M)
  letI := sM
  let f (z : ι → M) := mulCode (z i) (z j)
  have hf : @Set.DefinableFun M LRV N ι S f := by
    letI := N
    exact (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMul)).comp
      (show S.DefinableMap LRV (fun z : ι → M => ![z i,z j]) from
        fun r => by fin_cases r <;> exact Set.DefinableFun.proj LRV)
  let F (z : ι → M) : Fin 2 → M := ![f z,z k]
  let G (z : ι → M) : Fin 2 → M := ![z k,f z]
  have hF : @Set.DefinableMap M LRV N ι (Fin 2) S F := by
    intro r
    fin_cases r
    · exact hf
    · exact @Set.DefinableFun.proj M LRV N ι S k
  have hG : @Set.DefinableMap M LRV N ι (Fin 2) S G := by
    intro r
    fin_cases r
    · exact @Set.DefinableFun.proj M LRV N ι S k
    · exact hf
  have hl := codeLe_definable (M := M) S
  have hle : @Set.Definable M S LRV N ι (F ⁻¹' {z : Fin 2 → M | codeLe (z 0) (z 1)}) := by
    letI := N
    exact hl.preimage_map hF
  have hge : @Set.Definable M S LRV N ι (G ⁻¹' {z : Fin 2 → M | codeLe (z 0) (z 1)}) := by
    letI := N
    exact hl.preimage_map hG
  have hg := proper_definable (M := M) (ι := ι) S
  have h := @Set.Definable.inter M S LRV N ι _ _ hg
    (@Set.Definable.inter M S LRV N ι _ _ hle hge)
  change @Set.Definable M S LRV N ι _
  convert h using 1
  ext a
  change (Proper a ∧ codeValue (a i) * codeValue (a j) = codeValue (a k)) ↔
    (Proper a ∧ codeLe (f a) (a k) ∧ codeLe (a k) (f a))
  apply and_congr_right
  intro ha
  have he : f a = iRVMul (a i) (a j) := mulCode_eq _ _ (ha i) (ha j)
  have hp : NonzeroRV (f a) := he.symm ▸ rv_product_nonzero _ _ (ha i) (ha j)
  rw [codeLe_iff _ _ hp (ha k), codeLe_iff _ _ (ha k) hp,
    he, codeValue_product _ _ (ha i) (ha j)]
  exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩

theorem one_definable (S : Set M) : Values.GammaDefinable S {1} := by
  apply (scalar_definable_iff {1}).mp
  exact (mul_definable (M := M) S (0 : Fin 1) 0 0).congr (fun a => by
    change a 0 * a 0 = a 0 ↔ a 0 = 1
    constructor
    · intro h
      exact mul_left_cancel (h.trans (mul_one (a 0)).symm)
    · intro h
      rw [h, one_mul])

end SpecialTransformations.Section4.GammaSyntax

end
