/-
**Proposition 3.9 from two ingredients: `VFGenCaseP` is redundant on this route.**

`QE/Assembly_frozen.lean` reduces the frozen Theorem 2.3 to Shoenfield's test plus `Prop39FS`,
and `Assembly.prop39P` derives Proposition 3.9 (`lrv:mono:lift`) from three lemma-props:

    PrepStepP    (Lemma 3.3 + henselization)
    OneStepVFP   (Lemmas 3.4-3.8)
    VFGenCaseP   (Remark 3.1 + Weispfenning's QE for `L_v`)

This file proves the third is **not exercised at all**: `prop39P` replaces the domain with the
substructure produced by `exists_vf_allP`, which contains every `VF` element of `M`, and such a
substructure *is* the whole model — `eq_top_of_vf_all`, from

* `QE/SortCover.lean`'s `iVF_or_iRV` (the encoding axiom `Axioms.sdCover`: every element of a
  model is `VF` or `RV`),
* `Assembly.RVeqRvVF_of_model` (the encoding axiom `Axioms.rvSurj`: every `RV` element is `rv` of
  a `VF` element or is `rv 0`), and
* substructure closure under `Fn.rvMap` and the constants.

So after the `VF` exhaustion there is nothing left to extend, and Weispfenning's theorem is
*unused*.  (This is a property of the tagged one-carrier encoding: `rv` is a function of the
language and the sort cover forces every element into a sort, so `VF`-exhaustion is exhaustive.
The paper reaches the same place via Remark 3.1 because its substructures' `RV` parts are free.)

Headline theorems, everything else intermediate:

* `Prop39FS_of_two      -- Prop39FS from PrepStepP + OneStepVFP alone`
* `theorem_2_3_of_two   -- HasQE ACVF from ShoenfieldTestFS + PrepStepP + OneStepVFP`

(Merged from swarm `smw1rx5g2` member m7, `.ultramath/smw1rx5g2/m7/M7_vfgen.lean`, which was
verified green and axiom-clean by the judge before merging; nothing here changes its content.)
-/
import Assembly_frozen
import SortCover

open FirstOrder FirstOrder.Language
open scoped FirstOrder
open SpecialTransformations.Milestone0.Axioms

namespace SpecialTransformations
namespace Milestone0
namespace Assembly

variable {M : Type} [LRV.Structure M]

/-- **A substructure containing every `VF` element is the whole model.**  Every element is `VF` or
`RV` (`iVF_or_iRV`), and every `RV` element is `rv` of a `VF` element or is `rv 0`
(`Assembly.RVeqRvVF_of_model`), which the substructure has by closure under `rvMap` and the
constants. -/
theorem eq_top_of_vf_all [M ⊨ Axioms.ACVF] (T : LRV.Substructure M)
    (hT : ∀ y : M, iVF y → y ∈ T) : T = ⊤ := by
  refine Substructure.ext (fun x => ⟨fun _ => trivial, fun _ => ?_⟩)
  rcases SortCover.iVF_or_iRV (M := M) x with h | h
  · exact hT x h
  · rcases Assembly.RVeqRvVF_of_model (M := M) x h with ⟨y, hyVF, hyx⟩ | h0
    · rw [← hyx]
      show Structure.funMap (L := LRV) Fn.rvMap ![y] ∈ T
      exact T.fun_mem Fn.rvMap ![y] (fun i => by
        have : i = 0 := by fin_cases i; rfl
        subst this
        simpa using hT y hyVF)
    · rw [h0]
      show Structure.funMap (L := LRV) Fn.rvZero (fun i : Fin 0 => i.elim0) ∈ T
      exact T.fun_mem Fn.rvZero (fun i => i.elim0) (fun i => i.elim0)

/-- **The only instance of the third ingredient that Proposition 3.9 uses**, proved outright:
a monomorphism out of a substructure that contains every `VF` element extends to the whole model.
No saturation, no `VF`-generatedness and no Weispfenning input is needed for it — the substructure
*is* the model. -/
theorem VFGenCaseP_top {N : Type} [LRV.Structure N]
    [M ⊨ Axioms.ACVF] (S : LRV.Substructure M) (hS : ∀ y : M, iVF y → y ∈ S)
    (f : S ↪[LRV] N) :
    ∃ g : M ↪[LRV] N, ∀ x : S, g (x : M) = f x := by
  have hT : S = ⊤ := eq_top_of_vf_all S hS
  subst hT
  refine ⟨f.comp (Substructure.topEquiv (L := LRV) (M := M)).symm.toEmbedding, fun x => ?_⟩
  show f ((Substructure.topEquiv (L := LRV) (M := M)).symm ((x : M))) = f x
  have h1 : (Substructure.topEquiv (L := LRV) (M := M)).symm ((x : M)) = ⟨(x : M), trivial⟩ :=
    rfl
  have h2 : (x : ↥(⊤ : LRV.Substructure M)) = ⟨(x : M), trivial⟩ := Subtype.ext rfl
  exact congrArg f (h1.trans h2.symm)

/-- **Proposition 3.9 (`lrv:mono:lift`), saturation-free, with the third ingredient removed.**
`Assembly.prop39P` with the `VFGenCaseP` hypothesis deleted; only `T = ⊤` (`eq_top_of_vf_all`)
replaces it.  `RVeqRvVF` is not needed either, since it is only used to prove `VF`-generatedness
of `T`, which is now beside the point. -/
theorem prop39P_noVFGen {M N : Type} [LRV.Structure M] [LRV.Structure N]
    [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF]
    (hPrep : PrepStepP (M := M) (N := N))
    (hOne : OneStepVFP (M := M) (N := N))
    (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    ∃ g : M ↪[LRV] N, ∀ x : S, g (x : M) = f x := by
  obtain ⟨T, g, hST, hagree, hall⟩ := exists_vf_allP hPrep hOne S f
  have hT : T = ⊤ := eq_top_of_vf_all T hall
  subst hT
  refine ⟨g.comp (Substructure.topEquiv (L := LRV) (M := M)).symm.toEmbedding, fun x => ?_⟩
  have h1 : (Substructure.topEquiv (L := LRV) (M := M)).symm ((x : M)) = ⟨(x : M), trivial⟩ :=
    rfl
  simp only [Embedding.comp_apply, h1]
  exact hagree x

/-- **Proposition 3.9 in the saturated formulation of `QE/Assembly_frozen.lean`, without the
third ingredient.**  Same conclusion as `Assembly.prop39`, with `hVFGen` and `hRv` deleted. -/
theorem prop39_noVFGen {M N : Type} [LRV.Structure M] [LRV.Structure N]
    [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF] (hSat : Saturated N)
    (hPrep : PrepStep (M := M) (N := N) hSat)
    (hOne : OneStepVF (M := M) (N := N) hSat)
    (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    ∃ g : M ↪[LRV] N, ∀ x : S, g (x : M) = f x :=
  prop39P_noVFGen hPrep hOne S f

/-- **`Prop39FS` from two ingredients.**  Compare `Assembly.Prop39FS_of_P`, which needs a third. -/
theorem Prop39FS_of_two
    (hPrep : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF], PrepStepP (M := M) (N := N))
    (hOne : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF], OneStepVFP (M := M) (N := N)) :
    Prop39FS := by
  intro M N _ _ hM hN hSat S f
  exact prop39P_noVFGen (hPrep M N) (hOne M N) S f

/-- **The frozen Theorem 2.3 modulo two ingredients** (instead of the three of
`theorem_2_3_quantifier_elimination_of_ingredients`): Shoenfield's test, Lemma 3.3 + henselization,
and Lemmas 3.4-3.8.  Remark 3.1 + Weispfenning is not needed on this route. -/
theorem theorem_2_3_of_two (hShoen : ShoenfieldTestFS)
    (hPrep : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF], PrepStepP (M := M) (N := N))
    (hOne : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF], OneStepVFP (M := M) (N := N)) :
    HasQE Axioms.ACVF :=
  Assembly.theorem_2_3_of_fs hShoen (Prop39FS_of_two hPrep hOne)

end Assembly
end Milestone0
end SpecialTransformations
