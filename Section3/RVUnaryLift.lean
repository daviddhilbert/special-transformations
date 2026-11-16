module

public import Section3.SortedBoolean
public import Section3.CMinimal

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- RV preimages are sorted-definable over exactly the original base. -/
theorem DefinableAt.rv_preimage {S A : Set M} (hA : DefinableAt S .rv A) :
    DefinableAt S .vf {x | iVF x ∧ iRv x ∈ A} := by
  let N := CanonicalStructure.normalize (M := M)
  letI := sM
  have hAN : @DefinableAt M N S .rv A := (definableAt_normalize_iff S .rv A).mpr hA
  have hfun (z : Fin 1 → M) (hz : @iVF M sM (z 0)) :
      @Structure.funMap LRV M N 1 Fn.rvMap z = @iRv M sM (z 0) := by
    have hn := CanonicalStructure.normalize_fun Fn.rvMap z (by
      intro i; fin_cases i; exact hz)
    have he : z = ![z 0] := by funext i; fin_cases i; rfl
    exact hn.trans (congrArg (@Structure.funMap LRV M sM 1 Fn.rvMap) he)
  apply (definableAt_iff_normalized_raw S .vf _).mpr
  constructor
  · letI := N
    have hraw : S.Definable₁ LRV A := hAN.raw_definable
    have hF : S.DefinableMap LRV (fun z : Fin 1 → M =>
        (fun _ : Fin 1 => Structure.funMap (L := LRV) Fn.rvMap z)) := by
      intro i
      change S.DefinableFun LRV (Structure.funMap (L := LRV) Fn.rvMap)
      exact Set.DefinableFun.of_empty (@Set.DefinableFun.fun_symbol M LRV N 1 Fn.rvMap)
    have hcomp := hraw.preimage_map hF
    have hVF := (definableAt_sort S .vf).raw_definable
    change S.Definable LRV _
    convert hVF.inter hcomp using 1
    ext z
    change (@iVF M sM (z 0) ∧ @iRv M sM (z 0) ∈ A) ↔
      (@iVF M N (z 0) ∧ @Structure.funMap LRV M N 1 Fn.rvMap z ∈ A)
    exact and_congr_right (fun hz => by rw [hfun z hz])
  · exact fun _ hx => hx.1

/-- The completed C-minimality theorem applies to every sorted definable
unary VF set over the original arbitrary parameter set. -/
theorem DefinableAt.isBoolComb_balls {S A : Set M} (hA : DefinableAt S .vf A) :
    IsBoolComb {B : Set M | IsBall B} A := by
  obtain ⟨⟨p, φ, hw, heq⟩, hsort⟩ := hA
  have hset : A = {x | iVF x ∧ φ.Realize p.values ![x]} := by
    ext x
    change (x ∈ A ↔ iVF x ∧ φ.Realize p.values ![x])
    have he := Set.ext_iff.mp heq ![x]
    change (x ∈ A ↔ (∀ i : Fin 1, iVF (![x] i)) ∧ φ.Realize p.values ![x]) at he
    simpa only [Fin.forall_fin_one, Matrix.cons_val_zero] using he
  rw [hset]
  exact theorem_2_8_c_minimal (Fin p.length) p.sorts φ hw p.values p.sorted

end SpecialTransformations.Section3
