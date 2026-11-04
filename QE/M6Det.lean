/-
m6, swarm `smw1sd59b`, direction 2 (amalgamation for the frozen tagged `L_RV`).

**What this file proves, and why the amalgamation route needs it.**

`JohnsonCriterion.HasAmalgamation Axioms.ACVF` asks: for models `A`, `B`, `C` of the frozen
`ACVF` and embeddings `i : A ↪ B`, `j : A ↪ C`, produce a model `D` with embeddings
`i' : B ↪ D`, `j' : C ↪ D` agreeing on `A`.  Any construction of `D` has to rebuild the `RV`
sort of the amalgam, and the question this file settles is the *well-posedness* half of that
rebuild:

* in a model of `ACVF` the carrier is the disjoint union of the two sorts (`cover`,
  `not_vf_and_rv`, `vf_xor_rv`), and **every `RV`-element is `rv` of a `VF`-element**
  (`rv_factor`, the `rvSurj` axiom read off a model);
* consequently **an `L_RV`-embedding of models is determined by its values on the `VF` sort**
  (`emb_ext_of_factor`, `emb_ext_of_model`).  So the `RV` part of an embedding carries no
  freedom: what an amalgam must get right is the valued-field embedding of the `VF` parts, and
  the `RV` sort of the amalgam is a *function* of it;
* the restriction of an `L_RV`-embedding to the `VF` sort preserves the valuation ring
  (`iUnits ∘ iRv`) and the value order (`iLe` on `rv`-values), i.e. it *is* a valued-field
  embedding in Johnson's `L_val` sense (`emb_units_iff`, `emb_le_iff`, `emb_inO_iff`).

Together: the frozen amalgamation property is exactly the statement that a valued-field
amalgam of the two `VF` parts -- which the tree already produces
(`QE/Amalgamation_reduced.lean`, `Johnson22.star` and
`Johnson22.amalgamation_of_ring_amalgamation`) -- can be *equipped* with an `RV` sort.  This
file supplies the uniqueness half of that equipment; the existence half is the port of
`Milestone0/accepted/ACVF_general_model.lean`'s general model `C v` recorded in `NOTES.md`.

Everything is read off `Axioms.ACVF` through the frozen encoding (`import Enc`, via
`Assembly_frozen` and `RVCalc`); nothing is assumed.
-/
import Assembly_frozen
import RVCalc

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

set_option linter.style.haveILetI false

namespace SpecialTransformations.Milestone0.M6

variable {M : Type} [LRV.Structure M] {N : Type} [LRV.Structure N]

/-! ## 1. The sort discipline of a model: the carrier is the disjoint union of the two sorts -/

theorem mem_ACVF_sdCover : Axioms.sdCover ∈ Axioms.ACVF := by
  simp [Axioms.ACVF, Axioms.ACVFpaper, Axioms.sortAxioms, Axioms.sortClosure, Axioms.ofList]

theorem mem_ACVF_sdDisjoint : Axioms.sdDisjoint ∈ Axioms.ACVF := by
  simp [Axioms.ACVF, Axioms.ACVFpaper, Axioms.sortAxioms, Axioms.sortClosure, Axioms.ofList]

/-- **The carrier of a model is covered by the two sorts** (`Axioms.sdCover` read off). -/
theorem cover (hM : M ⊨ Axioms.ACVF) (x : M) : iVF x ∨ iRV x := by
  have h := allOne_realize hM (T := Axioms.ACVF)
    (φ := (pVF (n := 1) &0 ⊔ pRVsort (n := 1) &0)) mem_ACVF_sdCover ![x]
  simpa [BoundedFormula.realize_sup, pVF_realize, pRVsort_realize, RVCalc.realize_var_inr,
    Matrix.cons_val_zero] using h

/-- **The two sorts are disjoint in a model** (`Axioms.sdDisjoint` read off). -/
theorem not_vf_and_rv (hM : M ⊨ Axioms.ACVF) (x : M) : ¬ (iVF x ∧ iRV x) := by
  have h := allOne_realize hM (T := Axioms.ACVF)
    (φ := ∼(pVF (n := 1) &0 ⊓ pRVsort (n := 1) &0)) mem_ACVF_sdDisjoint ![x]
  simpa [BoundedFormula.realize_not, BoundedFormula.realize_inf, pVF_realize, pRVsort_realize,
    RVCalc.realize_var_inr, Matrix.cons_val_zero] using h

/-- Every element of a model is in exactly one of the two sorts. -/
theorem vf_xor_rv (hM : M ⊨ Axioms.ACVF) (x : M) : iVF x ↔ ¬ iRV x := by
  constructor
  · intro h hrv
    exact not_vf_and_rv hM x ⟨h, hrv⟩
  · intro h
    rcases cover hM x with h' | h'
    · exact h'
    · exact absurd h' h

/-! ## 2. Every `RV`-element of a model is `rv` of a `VF`-element

This is `Axioms.rvSurj` (the paper's surjectivity of `rv : VF^× → RV^×`) read off a model; the
`0 = ∞ = rv 0` case is `Axioms.rvZeroEq`. -/

/-- **`RV = rv(VF)` in a model of `ACVF`**, the absorbing element included: every `RV`-element
has a `VF` preimage under `rv`. -/
theorem rv_factor (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iRV x) :
    ∃ y : M, iVF y ∧ iRv y = x := by
  haveI : M ⊨ Axioms.ACVF := hM
  rcases Assembly.RVeqRvVF_of_model (M := M) x hx with ⟨y, hy, hxy⟩ | h0
  · exact ⟨y, hy, hxy⟩
  · exact ⟨iVFZero, vf_zero_mem (M := M) hM, by rw [RVCalc.rv_zero_eq hM, h0]⟩

/-! ## 3. Embeddings of models are determined by the `VF` sort -/

/-- `iRv` commutes with every `L_RV`-embedding, at every argument:
`f (rv x) = rv (f x)`. -/
theorem emb_rv (f : M ↪[LRV] N) (x : M) : f (iRv x) = iRv (f x) := by
  have h := FirstOrder.Language.Embedding.map_fun (L := LRV) f Fn.rvMap (![x])
  have e2 : (f ∘ ![x]) = ![f x] := by funext i; fin_cases i; rfl
  rw [e2] at h
  simpa [iRv] using h

/-- **The determination theorem, in factored form.**  If every element of `S` is either in the
`VF` sort or is `rv` of a `VF`-element of `S`, then two `L_RV`-embeddings of `S` agreeing on the
`VF` sort are equal. -/
theorem emb_ext_of_factor {S : Type} [LRV.Structure S]
    (hfac : ∀ x : S, iVF x ∨ ∃ y : S, iVF y ∧ iRv y = x)
    (f g : S ↪[LRV] N) (h : ∀ x : S, iVF x → f x = g x) : f = g := by
  refine FirstOrder.Language.Embedding.ext (fun x => ?_)
  rcases hfac x with hx | ⟨y, hy, hxy⟩
  · exact h x hx
  · rw [← hxy, emb_rv, emb_rv, h y hy]

/-- **An `L_RV`-embedding of models of `ACVF` is determined by its values on the `VF` sort.**

This is what makes the `RV` sort of an amalgam a function of the valued-field amalgam of the
`VF` parts: two amalgams of the same two models over the same base whose `VF` embeddings agree,
and whose `RV` parts are built by any `rv`-compatible rule, agree on `RV` too. -/
theorem emb_ext_of_model (hM : M ⊨ Axioms.ACVF) (f g : M ↪[LRV] N)
    (h : ∀ x : M, iVF x → f x = g x) : f = g :=
  emb_ext_of_factor (S := M) (fun x => by
    rcases cover hM x with hx | hx
    · exact Or.inl hx
    · exact Or.inr (rv_factor hM hx)) f g h

/-! ## 4. The `VF`-reduct of an `L_RV`-embedding is a valued-field embedding

An `L_RV`-embedding of models *induces* the data of a valued-field (Johnson `L_val`) embedding:
the field homomorphism on the `VF` part, the valuation ring, and the value order.  These are
the lemmas which make a `VF`-amalgam (produced by `Johnson22.star`) the right input to the
reconstruction of an `L_RV`-amalgam. -/

/-- the valuation ring of a model, as a predicate on the carrier: `{x ∈ VF : v x ≥ 0}`, i.e.
`x = 0` or `rv x` is a unit (`Kˣ` is the class of `1`). -/
def inO (x : M) : Prop := iVF x ∧ (iUnits (iRv x) ∨ iRv x = iRVZero)

/-- An `L_RV`-embedding sends `0 = ∞` of `RV` to `0 = ∞`. -/
theorem emb_rvZero (f : M ↪[LRV] N) : f (iRVZero (M := M)) = iRVZero (M := N) := by
  have h := FirstOrder.Language.Embedding.map_fun (L := LRV) f Fn.rvZero
    (fun i : Fin 0 => i.elim0)
  have e : (f ∘ fun i : Fin 0 => i.elim0) = fun i : Fin 0 => i.elim0 := by
    funext i; exact i.elim0
  rw [e] at h
  simpa [iRVZero] using h

/-- `rv`-equality is preserved and reflected by an `L_RV`-embedding. -/
theorem emb_rv_eq_iff (f : M ↪[LRV] N) (x y : M) :
    iRv x = iRv y ↔ iRv (f x) = iRv (f y) := by
  rw [← emb_rv f x, ← emb_rv f y]
  exact ⟨fun h => congrArg (fun z => f z) h, fun h => f.injective h⟩

/-- **An `L_RV`-embedding preserves the valuation ring.** -/
theorem emb_units_iff (f : M ↪[LRV] N) (x : M) :
    iUnits (iRv x) ↔ iUnits (iRv (f x)) := by
  have h := FirstOrder.Language.Embedding.map_rel (L := LRV) f Rel.memUnits (![iRv x])
  have hcomp : (f ∘ ![iRv x]) = ![iRv (f x)] := by
    funext i
    fin_cases i
    simp [Function.comp_apply, emb_rv]
  rw [hcomp] at h
  simpa [iUnits] using h.symm

/-- **An `L_RV`-embedding preserves the value order** on `VF`-elements. -/
theorem emb_le_iff (f : M ↪[LRV] N) (x y : M) :
    iLe (iRv x) (iRv y) ↔ iLe (iRv (f x)) (iRv (f y)) := by
  have h := FirstOrder.Language.Embedding.map_rel (L := LRV) f Rel.rvLe (![iRv x, iRv y])
  have hcomp : (f ∘ ![iRv x, iRv y]) = ![iRv (f x), iRv (f y)] := by
    funext i
    fin_cases i
    · simp [Function.comp_apply, emb_rv]
    · simp [Function.comp_apply, emb_rv]
  rw [hcomp] at h
  simpa [iLe] using h.symm

/-- An `L_RV`-embedding preserves and reflects the `VF` sort. -/
theorem emb_vf_iff (f : M ↪[LRV] N) (x : M) : iVF (f x) ↔ iVF x := by
  have h := FirstOrder.Language.Embedding.map_rel (L := LRV) f Rel.memVF (![x])
  have hcomp : (f ∘ ![x]) = ![f x] := by funext i; fin_cases i; rfl
  rw [hcomp] at h
  simpa [iVF] using h

/-- **The induced valued-field embedding of the `VF` parts**: an `L_RV`-embedding of models is,
on the `VF` sort, a field embedding (it is a hom of the ambient language) which preserves the
valuation ring at every `VF`-element. -/
theorem emb_inO_iff (f : M ↪[LRV] N) (x : M) : inO x ↔ inO (f x) := by
  have hv : iVF (f x) ↔ iVF x := emb_vf_iff f x
  have hu : (iUnits (iRv x) ↔ iUnits (iRv (f x))) := emb_units_iff f x
  have hz : (iRv x = iRVZero (M := M)) ↔ (iRv (f x) = iRVZero (M := N)) := by
    rw [← emb_rv f x, ← emb_rvZero f]
    exact ⟨fun h => congrArg (fun z => f z) h, fun h => f.injective h⟩
  constructor
  · rintro ⟨hx, hu' | h0⟩
    · exact ⟨hv.mpr hx, Or.inl (hu.mp hu')⟩
    · exact ⟨hv.mpr hx, Or.inr (hz.mp h0)⟩
  · rintro ⟨hx, hu' | h0⟩
    · exact ⟨hv.mp hx, Or.inl (hu.mpr hu')⟩
    · exact ⟨hv.mp hx, Or.inr (hz.mpr h0)⟩

end SpecialTransformations.Milestone0.M6

#print axioms SpecialTransformations.Milestone0.M6.cover
#print axioms SpecialTransformations.Milestone0.M6.rv_factor
#print axioms SpecialTransformations.Milestone0.M6.emb_ext_of_model
#print axioms SpecialTransformations.Milestone0.M6.emb_units_iff
#print axioms SpecialTransformations.Milestone0.M6.emb_le_iff
#print axioms SpecialTransformations.Milestone0.M6.emb_inO_iff
