/-
# m3 / p6 — Interface closure for the frozen separated slot

Member `m3`, swarm `smw2mluv7`, direction `d7`.  Read `QE/OneStepCases.lean` (the ledger and the
two candidate antecedents `caseSeparated_of_RVControl` / `caseSeparated_of_ResidualClasses`) and
`QE/M5L34_36.lean` (Claim (⋆) in `Γ`-class form`) before this file.

**Attribution note.**  `QE/OneStepCases.lean` assigns the separated slot to Lemmas 3.4/3.6.  m1's
`.ultramath/smw2mluv7/m1/Case34Slot.lean` (board d3, findings f1/f8) machine-checks that this is
rotated: 3.4 and 3.6 have `e ∈ U(M)`, hence are `¬ M5L.Separated`, and the frozen `CaseSeparated`
is exactly the `e:transc` (3.7) hypothesis.  Everything below is about the frozen slot **as
stated** — the extension `(T, g)`, `Standing T`, at `Standing S`, `iVF m`, `iRv m ∈ S`,
`M5L.Separated S m` — so the attribution does not affect any statement here.  It does explain §4:
over a `VF`-generated `S` the frozen hypotheses are empty, so the frozen separated branch can only be
the `RV`-junk part of `S` (which is what the `e:transc` case has to be about once `iRv e ∈ S` is
assumed).

## What this file decides

At `M4Cases.CaseSeparated`'s own hypotheses (`S` `Standing`, `f : S ↪[LRV] N`, `m : M` with
`iVF m`, `iRv m ∈ S`, `M5L.Separated S m`) the tree owes the extension `(T, g)` with
`M5L.ResidualClasses S T`.  This file:

* **§1** adds `PolyExpansions S T e`, the *polynomial* form of the paper's field-theoretic input
  (`VF(⟨Ŝ,e⟩) = K(Ŝ)(e)`) that matches the tagged encoding (no inverse symbol on the `VF` sort),
  and proves `ResidualClasses_of_poly`: **Claim (⋆) in class form with `VFInvClosedOn S` removed**
  from the tree's `ResidualClasses_of_VFGen`.  `PolyExpansions ⟹ QuotExpansions` is proved, so the
  new interface is a comparable refinement, not a weakening in disguise.
* **§2** states the exact residual at the slot — realization of the atomic type of `m` over `S`
  (model theory: saturation + finite satisfiability) together with the two field-theoretic facts
  about the generated substructure — and proves
  `caseSeparated_of_slotRealization_and_fieldData`, with `m ∈ S` and `m = 0` handled (the slot has
  no `m ≠ 0` side condition, unlike `M5L.OneStepSeparatedP`).
* **§3** identifies the merged tree's own sufficient interface at the slot: `M5L.OneStepSeparatedP`
  plus the one bridge `∀ S, Standing S → VFInvClosedOn S`, and proves that the two candidate
  antecedents (`RV`-control vs `Γ`-class-control) are **equivalent** at the slot's hypotheses
  (`Standing S` supplies `KEqTop S`, which is exactly what `RVControl_of_Residual` consumes).
* **§4** is the **obstruction**: the slot's hypotheses plus `Assembly.IsVFGen S` are
  *contradictory*.  `iRv m ∈ S` and `Separated S m` cannot coexist over a `VF`-generated `S`:
  `IsVFGen S` turns `iRv m ∈ S` into `iRv m = iRv y` for some `y ∈ S ∩ VF`, and `Separated` at
  `k = 1`, `x = 1` forbids exactly that class.  Consequence: no slot statement that carries
  `IsVFGen S` (the paper's `Ŝ` is `VF`-generated!) can use this hypothesis combination, and the
  separated branch bites only on substructures whose `RV`-part is not `rv` of their `VF`-part.
* **§5** stress-tests: the `⊤`-instances of every hypothesis of the merged interface, the reflexive
  instance `PolyExpansions S S e`, `Separated S 0` for every `S` (so the slot's `m = 0` branch is
  non-vacuous and trivial), the junk probe (the generated substructure contains the ill-sorted value
  `vfAdd rvZero rvZero`, so `ResidualClasses S (closure …)` demands class control of an element no
  axiom constrains), and the ledger combination with the other two slots.

No `sorry`, no `axiom`, no `native_decide`; the axiom audit is at the end.
-/
import OneStepCases
import Assembly_frozen
import Prop39Decomp

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Milestone0.Transc

namespace SpecialTransformations.Milestone0
namespace M3Slot

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-! ## 0. Two membership facts for the constants -/

/-- The `VF`-zero is a constant symbol, so it lies in every substructure. -/
theorem vfZero_mem_sub (S : LRV.Substructure M) : iVFZero (M := M) ∈ S :=
  S.fun_mem Fn.vfZero (fun i => i.elim0) (fun i => i.elim0)

/-- The `VF`-one is a constant symbol, so it lies in every substructure. -/
theorem vfOne_mem_sub (S : LRV.Substructure M) : iVFOne (M := M) ∈ S :=
  S.fun_mem Fn.vfOne (fun i => i.elim0) (fun i => i.elim0)

/-- `(rv e)^1 = rv e`, the normalization the `Separated`-at-`k = 1` step needs. -/
theorem rvpow_one (hM : M ⊨ Axioms.ACVF) {ε : M} (hε : iRV ε) : rvpow ε 1 = ε := by
  show iRVMul (rvpow ε 0) ε = ε
  show iRVMul iRVOne ε = ε
  rw [rv_mul_comm_of_model hM (rv_one_mem hM) hε, rv_mul_one_any_right hM hε]

/-! ## 1. The polynomial form of Claim (⋆), without `VFInvClosedOn`

`M5L.ResidualClasses_of_VFGen` consumes `VFInvClosedOn S`: the paper's `Ŝ = ⟨VF(S)⟩` is a **field**,
so a quotient `p(e)/q(e)` has its class in `Γ(S)`.  In the tagged encoding the `VF` sort has no
inverse symbol, so `M5L.VFInvClosedOn S` has to be *assumed* and is not a consequence of `Standing`
(`QE/M5L34_36.lean`'s docstring records this, and `OneStepSeparatedP_of_hypotheses` keeps it as a
hypothesis).  The representation that matches the encoding is *polynomial*: every `VF`-element of
the extension is `Σ_{i≤n} b_i e^i` with `b_i ∈ S`.  Then the tree's own `rvPoly_mem_of_separated`
gives `rv` of every `VF`-element of `T` *in* `S`, with no quotient step at all. -/

/-- **The polynomial representation of the `VF`-part of the extension** (the paper's
`VF(⟨Ŝ,e⟩) = K(Ŝ)(e)`, in the encoding's vocabulary).  `x ∈ T ∩ VF`, `x ≠ 0` is a polynomial in `e`
with coefficients in `S ∩ VF`, all nonzero (support indexing, as in `M5L.rvPoly_mem_of_separated`). -/
def PolyExpansions (S T : LRV.Substructure M) (e : M) : Prop :=
  ∀ x : M, x ∈ T → iVF x → x ≠ iVFZero →
    ∃ (b : ℕ → M) (m : ℕ),
      (∀ i, iVF (b i)) ∧ (∀ i, b i ∈ S) ∧ (∀ i, b i ≠ iVFZero) ∧
        x = vsum (fun i => iVFMul (b i) (vpow e i)) (m + 1)

/-- `PolyExpansions` is stronger than the tree's `QuotExpansions` (take denominator `1`), so §1's
interface is not a weakening of the merged one in the `VF`-representation row. -/
theorem polyExpansions_quot {S T : LRV.Substructure M} {e : M}
    (h : PolyExpansions (M := M) S T e) : M5L.QuotExpansions S T e := by
  intro x hxT hxVF hx0
  obtain ⟨b, m, hb, hbS, hb0, hxeq⟩ := h x hxT hxVF hx0
  refine ⟨b, fun _ => iVFOne, m, 0, hb, hbS, hb0, fun _ => vf_one_mem hM,
    fun _ => vfOne_mem_sub S, fun _ => (RVCalc.vf_zero_ne_one hM).symm, ?_, ?_⟩
  · -- the denominator `Σ_{i≤0} 1 · e^i = 1` is nonzero
    show iVFAdd (vsum (fun i => iVFMul iVFOne (vpow e i)) 0)
      (iVFMul iVFOne (vpow e 0)) ≠ iVFZero
    show iVFAdd iVFZero (iVFMul iVFOne iVFOne) ≠ iVFZero
    rw [RVCalc.vf_zero_add hM (vf_mul_mem hM (vf_one_mem hM) (vf_one_mem hM)),
      RVCalc.vf_mul_one hM (vf_one_mem hM)]
    exact fun h => RVCalc.vf_zero_ne_one hM h.symm
  · show iVFMul x (iVFAdd (vsum (fun i => iVFMul iVFOne (vpow e i)) 0)
      (iVFMul iVFOne (vpow e 0))) = vsum (fun i => iVFMul (b i) (vpow e i)) (m + 1)
    show iVFMul x (iVFAdd iVFZero (iVFMul iVFOne iVFOne))
      = vsum (fun i => iVFMul (b i) (vpow e i)) (m + 1)
    rw [RVCalc.vf_zero_add hM (vf_mul_mem hM (vf_one_mem hM) (vf_one_mem hM)),
      RVCalc.vf_mul_one hM (vf_one_mem hM), RVCalc.vf_mul_one hM hxVF]
    exact hxeq

/-- **The `VF`-part of Claim (⋆).**  From the paper's hypotheses plus the polynomial representation,
every `VF`-element of `T` has its `rv` **in** `S`: this is `M5L.rvPoly_mem_of_separated` applied to
the representation.  No `VFInvClosedOn`, no quotient. -/
theorem rv_mem_of_polyExpansions (hM : M ⊨ Axioms.ACVF) {S T : LRV.Substructure M}
    (hK : Assembly.KEqTop S) {e : M} (he : iVF e) (he0 : e ≠ iVFZero) (heS : iRv e ∈ S)
    (hsep : M5L.Separated S e) (hpoly : PolyExpansions S T e) :
    ∀ x : M, x ∈ T → iVF x → iRv x ∈ S := by
  intro x hxT hxVF
  by_cases hx0 : x = iVFZero
  · rw [hx0, RVCalc.rv_zero_eq hM]
    exact M5L.rvZero_mem_sub S
  · obtain ⟨b, m, hb, hbS, hb0, hxeq⟩ := hpoly x hxT hxVF hx0
    rw [hxeq]
    exact M5L.rvPoly_mem_of_separated hM hK he he0 heS hb hbS hb0 hsep m

/-- **Claim (⋆) in `Γ`-class form, `VFInvClosedOn`-free.**  `IsVFGen T` reduces the class control of
`T` to `rv` of `VF`-elements of `T`, and `rv_mem_of_polyExpansions` disposes of those.  Compare
`M5L.ResidualClasses_of_VFGen`, which needs `M5L.VFInvClosedOn S` in addition to `QuotExpansions`. -/
theorem ResidualClasses_of_poly (hM : M ⊨ Axioms.ACVF) {S T : LRV.Substructure M}
    (hK : Assembly.KEqTop S) {e : M} (he : iVF e) (he0 : e ≠ iVFZero) (heS : iRv e ∈ S)
    (hsep : M5L.Separated S e) (hVFGen : Assembly.IsVFGen T)
    (hpoly : PolyExpansions S T e) : M5L.ResidualClasses S T := by
  intro y hyT hyRV
  rcases hVFGen y hyT hyRV with ⟨x, hxT, hxVF, hxr⟩ | hz
  · refine ⟨iRv x, rv_mem_of_polyExpansions hM hK he he0 heS hsep hpoly x hxT hxVF,
      rv_mem hM hxVF, ?_⟩
    rw [← hxr]
    exact cls_refl hM (rv_mem hM hxVF)
  · refine ⟨iRVZero, M5L.rvZero_mem_sub S, rv_zero_mem hM, ?_⟩
    rw [hz]
    exact cls_refl hM (rv_zero_mem hM)

/-- The same `Standing`-output form as `M5L.standing_of_paper_hypotheses`, with the inverse-closure
row replaced by the polynomial representation. -/
theorem standing_of_poly_hypotheses (hM : M ⊨ Axioms.ACVF) {S T : LRV.Substructure M}
    (hST : S ≤ T) (hS : Assembly.Standing S) {e : M} (he : iVF e) (he0 : e ≠ iVFZero)
    (heS : iRv e ∈ S) (hsep : M5L.Separated S e) (hVFGen : Assembly.IsVFGen T)
    (hpoly : PolyExpansions S T e) : Assembly.Standing T :=
  M5L.standing_of_ClassControl hST hS
    (ResidualClasses_of_poly hM hS.1 he he0 heS hsep hVFGen hpoly)

/-! ## 2. The exact residual at the slot, and the chain to `CaseSeparated` -/

/-- The model-theoretic half of the slot: the pushed atomic type of a **new** element is realized. -/
def SlotRealization : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m → m ∉ S →
    ∃ b : N, Realize.RealizesAtomic S f m b

/-- The field-theoretic half of the slot, at the canonical extension `closure (S ∪ {m})`. -/
def SlotFieldData (S : LRV.Substructure M) (m : M) : Prop :=
  Assembly.IsVFGen (Substructure.closure LRV ((S : Set M) ∪ {m})) ∧
    PolyExpansions S (Substructure.closure LRV ((S : Set M) ∪ {m})) m

/-- `Realize.exists_oneStep` with the generated substructure named: the witness `T` is
`closure (S ∪ {m})` and the embedding is `Realize.gEmb`.  (The tree's `exists_oneStep` states the
same conclusion existentially, so its witness cannot be unfolded; this version is the one the
slot's field data is stated at.) -/
theorem exists_oneStep_closure {S : LRV.Substructure M} {f : S ↪[LRV] N} {m : M} {b : N}
    (hb : Realize.RealizesAtomic S f m b) (hm : m ∉ S) :
    ∃ (g : (Substructure.closure LRV ((S : Set M) ∪ {m})) ↪[LRV] N)
      (hST : S ≤ Substructure.closure LRV ((S : Set M) ∪ {m})),
      m ∈ Substructure.closure LRV ((S : Set M) ∪ {m}) ∧
        (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) := by
  refine ⟨Realize.gEmb hb hm, fun x hx => Substructure.subset_closure (Set.mem_union_left _ hx),
    Substructure.subset_closure (Set.mem_union_right _ (Set.mem_singleton m)), ?_⟩
  intro x
  have hxT : (x : M) ∈ Substructure.closure LRV ((S : Set M) ∪ {m}) :=
    Substructure.subset_closure (Set.mem_union_left {m} x.2)
  have hk : Realize.kappa S m hm (⟨(x : M), Set.mem_union_left {m} x.2⟩ : ↥((S : Set M) ∪ {m}))
      = Sum.inl (⟨(x : M), x.2⟩ : S) := by
    simp only [Realize.kappa]
    exact (dif_pos x.2).trans (congrArg Sum.inl (Subtype.ext rfl))
  show Realize.gfun f b hm (x : M) hxT = f x
  rw [Realize.gfun_eq hb hm
    (Term.var (⟨(x : M), Set.mem_union_left {m} x.2⟩ : ↥((S : Set M) ∪ {m}))) (x : M) hxT rfl]
  show Realize.toN S f b m hm ⟨(x : M), Set.mem_union_left {m} x.2⟩ = f x
  show Realize.wv f b (Realize.kappa S m hm ⟨(x : M), Set.mem_union_left {m} x.2⟩) = f x
  rw [hk]
  rfl

/-- **The slot is closed modulo its exact residual.**  At `CaseSeparated`'s hypotheses: if `m ∈ S`,
`T = S`; otherwise the realization gives `T = closure (S ∪ {m})` and its embedding `g`, and the
field data plus `ResidualClasses_of_poly` gives `Standing T` through `standing_of_ClassControl`. -/
theorem caseSeparated_of_slotRealization_and_fieldData
    (hreal : SlotRealization (M := M) (N := N))
    (hfield : ∀ (S : LRV.Substructure M) (_f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M,
      iVF m → iRv m ∈ S → M5L.Separated S m → SlotFieldData (M := M) S m) :
    M4Cases.CaseSeparated (M := M) (N := N) := by
  intro S f hS m hmVF hmrv hsep
  by_cases hm : m ∈ S
  · exact ⟨S, f, le_rfl, fun _ => rfl, hm, hS⟩
  · have hm0 : m ≠ iVFZero := fun h => hm (h ▸ vfZero_mem_sub S)
    obtain ⟨b, hb⟩ := hreal S f hS m hmVF hm
    obtain ⟨g, hST, hmT, hagree⟩ := exists_oneStep_closure (M := M) (N := N) hb hm
    obtain ⟨hgen, hpoly⟩ := hfield S f hS m hmVF hmrv hsep
    exact ⟨Substructure.closure LRV ((S : Set M) ∪ {m}), g, hST, hagree, hmT,
      M5L.standing_of_ClassControl hST hS
        (ResidualClasses_of_poly hM hS.1 hmVF hm0 hmrv hsep hgen hpoly)⟩

/-- The residual in the form the assembler can discharge case by case: the realization row is
exactly `Assembly.realizesAtomic_of_saturatedFS`'s hypothesis (finite satisfiability of the pushed
type at a `SaturatedFS` target), so the two rows are the model-theoretic and the field-theoretic
content of Lemmas 3.4/3.6. -/
theorem slotRealization_of_saturatedFS_and_individual
    (hSat : Assembly.SaturatedFS N)
    (hreal : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N) (m : M) (φ : LRV.Formula (S ⊕ Unit)),
      φ.Realize (Realize.mv S m) → ∃ b : N, φ.Realize (Realize.wv f b)) :
    SlotRealization (M := M) (N := N) :=
  fun S f _ m _ _ => Assembly.realizesAtomic_of_saturatedFS hSat S f m (hreal S f m)

/-- **The ledger combination**: `M4Cases.Cases` from the two halves of the separated slot and the
other two branch hypotheses of `M4Cases`.  So `SlotRealization ∧ SlotFieldData` is *the* separated
row of `M4Cases.Cases` at a fixed pair. -/
theorem cases_of_slotResidual_and_rest
    (hreal : SlotRealization (M := M) (N := N))
    (hfield : ∀ (S : LRV.Substructure M) (_f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M,
      iVF m → iRv m ∈ S → M5L.Separated S m → SlotFieldData (M := M) S m)
    (hnotsep : M4Cases.CaseNotSeparated (M := M) (N := N))
    (hnew : M4Cases.CaseNewRV (M := M) (N := N)) : M4Cases.Cases (M := M) (N := N) where
  separated := caseSeparated_of_slotRealization_and_fieldData hreal hfield
  notSeparated := hnotsep
  newRV := hnew

/-- **The piecewise closure of the slot in `Γ`-class form**: from the extension data plus
`IsVFGen T` and the polynomial representation, `M4Cases.CaseSeparated` follows *directly*, without
detouring through `M5L.OneStepSeparatedP` and without `VFInvClosedOn S`. -/
theorem caseSeparated_of_extension_and_poly
    (h : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m →
      iRv m ∈ S → M5L.Separated S m →
      ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
        (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧
          Assembly.IsVFGen T ∧ PolyExpansions S T m) :
    M4Cases.CaseSeparated (M := M) (N := N) := by
  intro S f hS m hmVF hmrv hsep
  by_cases hm : m ∈ S
  · exact ⟨S, f, le_rfl, fun _ => rfl, hm, hS⟩
  · obtain ⟨T, g, hST, hagree, hmT, hgen, hpoly⟩ := h S f hS m hmVF hmrv hsep
    exact ⟨T, g, hST, hagree, hmT,
      M5L.standing_of_ClassControl hST hS
        (ResidualClasses_of_poly hM hS.1 hmVF (fun h0 => hm (h0 ▸ vfZero_mem_sub S)) hmrv hsep
          hgen hpoly)⟩

/-- **Wire-up to the frozen frontier**: at a fixed pair, Proposition 3.9 (`G3.ExtendsHere`, the
pair-level form of the frozen target's input 5) follows from the hull step together with the paper's
case split *with the separated row supplied by §2*.  So `SlotRealization ∧ SlotFieldData` is exactly
the separated content that `QE/Prop39Decomp.lean`'s `extendsHere_iff_hullExtension_and_cases` still
owes at the pair. -/
theorem extendsHere_of_hullExtension_and_slotResidual
    (hHull : G3.HullExtension (M := M) (N := N))
    (hreal : SlotRealization (M := M) (N := N))
    (hfield : ∀ (S : LRV.Substructure M) (_f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M,
      iVF m → iRv m ∈ S → M5L.Separated S m → SlotFieldData (M := M) S m)
    (hnotsep : M4Cases.CaseNotSeparated (M := M) (N := N))
    (hnew : M4Cases.CaseNewRV (M := M) (N := N)) :
    G3.ExtendsHere M N :=
  G3.extendsHere_of_hullExtension_of_oneStep hHull
    (M4Cases.oneStepVFP_of_cases (cases_of_slotResidual_and_rest hreal hfield hnotsep hnew))

/-! ## 3. The merged tree's sufficient interface, and the equivalence of the two antecedents -/

/-- The slot's conclusion in `RV`-control form. -/
def SlotRVControl : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m → iRv m ∈ S →
    M5L.Separated S m →
      ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
        (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ (∀ y : M, y ∈ T → iRV y → y ∈ S)

/-- The slot's conclusion in `Γ`-class form. -/
def SlotClassControl : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m → iRv m ∈ S →
    M5L.Separated S m →
      ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
        (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ M5L.ResidualClasses S T

/-- **The two candidate antecedents are equivalent at the slot.**  `RV`-control gives class control
by reflexivity of `Cls`; the converse is the merged `M5L.RVControl_of_Residual`, whose `KEqTop S`
hypothesis is the first conjunct of `Assembly.Standing S`.  So "which antecedent is provable" is a
question about *content*, not about strength: the class form is not a weakening. -/
theorem slotRVControl_iff_slotClassControl :
    SlotRVControl (M := M) (N := N) ↔ SlotClassControl (M := M) (N := N) := by
  constructor
  · intro h S f hS m hmVF hmrv hsep
    obtain ⟨T, g, hST, hagree, hmT, hRV⟩ := h S f hS m hmVF hmrv hsep
    exact ⟨T, g, hST, hagree, hmT,
      fun y hyT hyRV => ⟨y, hRV y hyT hyRV, hyRV, cls_refl hM hyRV⟩⟩
  · intro h S f hS m hmVF hmrv hsep
    obtain ⟨T, g, hST, hagree, hmT, hcc⟩ := h S f hS m hmVF hmrv hsep
    exact ⟨T, g, hST, hagree, hmT, M5L.RVControl_of_Residual hST hS.1 hcc⟩

/-- `QE/OneStepCases.lean`'s `RV`-control antecedent is exactly `SlotRVControl`. -/
theorem caseSeparated_of_slotRVControl (h : SlotRVControl (M := M) (N := N)) :
    M4Cases.CaseSeparated (M := M) (N := N) :=
  M4Cases.caseSeparated_of_RVControl h

/-- `QE/OneStepCases.lean`'s `Γ`-class antecedent is exactly `SlotClassControl`. -/
theorem caseSeparated_of_slotClassControl (h : SlotClassControl (M := M) (N := N)) :
    M4Cases.CaseSeparated (M := M) (N := N) :=
  M4Cases.caseSeparated_of_ResidualClasses h

/-- **The merged tree's own separated interface closes the slot** once the single bridge
`Standing S → VFInvClosedOn S` is available: `M5L.OneStepSeparatedP` differs from the slot only by
that row and by the `m ≠ 0` side condition, which the slot's `m ∉ S` case supplies because `0` is a
constant of every substructure. -/
theorem caseSeparated_of_oneStepSeparatedP (h : M5L.OneStepSeparatedP (M := M) (N := N))
    (hfinv : ∀ S : LRV.Substructure M, Assembly.Standing S → M5L.VFInvClosedOn S) :
    M4Cases.CaseSeparated (M := M) (N := N) := by
  intro S f hS m hmVF hmrv hsep
  by_cases hm : m ∈ S
  · exact ⟨S, f, le_rfl, fun _ => rfl, hm, hS⟩
  · exact h S f hS (hfinv S hS) m hmVF (fun h0 => hm (h0 ▸ vfZero_mem_sub S)) hmrv hsep

/-! ## 4. The obstruction: the slot's hypotheses exclude `IsVFGen S`

`M5L.Separated S m` at `k = 1`, `x = 1` says that no class of an element of `S ∩ VF` equals the
class of `m`; `Assembly.IsVFGen S` at the `RV`-element `iRv m ∈ S` produces exactly such an
element.  So the hypothesis combination of the frozen separated slot is **empty over `VF`-generated
`S`**: `IsVFGen` may only be demanded of the *extension* `T` (`SlotFieldData`), never of the base
`S`.  The branch bites only on substructures whose `RV`-part contains elements that are not `rv` of
their `VF`-part — the `kAdd`/junk part that §5's junk probe isolates. -/
theorem not_isVFGen_of_slot {S : LRV.Substructure M} {m : M}
    (hmVF : iVF m) (hmrv : iRv m ∈ S) (hm0 : m ≠ iVFZero)
    (hsep : M5L.Separated S m) : ¬ Assembly.IsVFGen S := by
  intro hgen
  have hmR : iRV (iRv m) := rv_mem hM hmVF
  have hmR0 : iRv m ≠ iRVZero := fun h => hm0 (RVCalc.vf_eq_zero_of_rv_eq_zero hM hmVF h)
  rcases hgen (iRv m) hmrv hmR with ⟨y, hyS, hyVF, hyeq⟩ | hz
  · have hy0 : y ≠ iVFZero := by
      intro hy
      rw [hy, RVCalc.rv_zero_eq hM] at hyeq
      exact hmR0 hyeq.symm
    have h1 : iVFOne ≠ iVFZero := (RVCalc.vf_zero_ne_one hM).symm
    have hne := hsep 1 (by norm_num) iVFOne y (vf_one_mem hM) hyVF (vfOne_mem_sub S) hyS h1 hy0
    rw [rvpow_one hM hmR, RVCalc.rv_one hM, rv_mul_one_any_right hM hmR] at hne
    rw [hyeq] at hne
    exact hne (cls_refl hM hmR)
  · exact hmR0 hz

/-- **The core of the obstruction.**  If `Separated S m` holds and `m ≠ 0`, then the `RV`-element
`iRv m ∈ S` has **no `VF`-witness in `S`**: there is no `y ∈ S ∩ VF` with `iRv y = iRv m`.  (Take
`k = 1`, `x = 1` in `Separated` — the class of `rv y` would then be the class of `rv m`.) -/
theorem no_vf_witness_of_separated {S : LRV.Substructure M} {m : M} (hmVF : iVF m)
    (hm0 : m ≠ iVFZero) (hsep : M5L.Separated S m) :
    ¬ ∃ y : M, y ∈ S ∧ iVF y ∧ iRv y = iRv m := by
  rintro ⟨y, hyS, hyVF, hyeq⟩
  have hmR : iRV (iRv m) := rv_mem hM hmVF
  have hy0 : y ≠ iVFZero := by
    intro hy
    rw [hy, RVCalc.rv_zero_eq hM] at hyeq
    exact hm0 (RVCalc.vf_eq_zero_of_rv_eq_zero hM hmVF hyeq.symm)
  have h1 : iVFOne ≠ iVFZero := (RVCalc.vf_zero_ne_one hM).symm
  have hne := hsep 1 (by norm_num) iVFOne y (vf_one_mem hM) hyVF (vfOne_mem_sub S) hyS h1 hy0
  rw [rvpow_one hM hmR, RVCalc.rv_one hM, rv_mul_one_any_right hM hmR] at hne
  rw [hyeq] at hne
  exact hne (cls_refl hM hmR)

/-- The same obstruction in the contrapositive, in the form a slot proof can consume directly: over
a `VF`-generated `S`, no nonzero `VF`-element `m` with `iRv m ∈ S` is separated from `S`. -/
theorem not_separated_of_isVFGen_mem {S : LRV.Substructure M} {m : M}
    (hgen : Assembly.IsVFGen S) (hmVF : iVF m) (hmrv : iRv m ∈ S) (hm0 : m ≠ iVFZero) :
    ¬ M5L.Separated S m :=
  fun hsep => not_isVFGen_of_slot hmVF hmrv hm0 hsep hgen

/-- **`S = ⊤` cross-check** (independent of m1's `not_separated_top`): `⊤` is `VF`-generated and
contains `iRv m`, so no nonzero `VF`-element is separated from `⊤`. -/
theorem not_separated_top {m : M} (hmVF : iVF m) (hm0 : m ≠ iVFZero) :
    ¬ M5L.Separated (⊤ : LRV.Substructure M) m :=
  fun hsep => no_vf_witness_of_separated (S := ⊤) hmVF hm0 hsep ⟨m, trivial, hmVF, rfl⟩

/-- **Corollary (the sharp form of §4).**  Over a `VF`-generated base `S`, the separated slot's
hypotheses force `m = 0` — the point at which the slot is trivial (`T = S`).  So adding `IsVFGen S`
to the slot's hypotheses would make the separated branch vacuous, and `IsVFGen` can only be demanded
of the *extension* `T` (`SlotFieldData`). -/
theorem eq_zero_of_slot_of_isVFGen {S : LRV.Substructure M} {m : M}
    (hgen : Assembly.IsVFGen S) (hmVF : iVF m) (hmrv : iRv m ∈ S)
    (hsep : M5L.Separated S m) : m = iVFZero := by
  by_contra hm0
  exact not_isVFGen_of_slot hmVF hmrv hm0 hsep hgen

/-- **The `VF`-generated half of the slot is a theorem.**  At `IsVFGen S` the hypotheses force
`m = 0` (§4), and there the conclusion holds with `T = S`.  So the whole content of
`M4Cases.CaseSeparated` sits in its `¬ IsVFGen S` restriction — stated as
`caseSeparated_iff_nonVFGen` below — and no residual is owed on the `VF`-generated bases. -/
theorem caseSeparated_at_isVFGen :
    ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → Assembly.IsVFGen S →
      ∀ m : M, iVF m → iRv m ∈ S → M5L.Separated S m →
        ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
          (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T := by
  intro S f hS hgen m hmVF hmrv hsep
  have hm0 : m = iVFZero := eq_zero_of_slot_of_isVFGen hgen hmVF hmrv hsep
  exact ⟨S, f, le_rfl, fun _ => rfl, hm0 ▸ vfZero_mem_sub S, hS⟩

/-- The separated slot restricted to bases that are **not** `VF`-generated. -/
def CaseSeparatedNonVFGen : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ¬ Assembly.IsVFGen S →
    ∀ m : M, iVF m → iRv m ∈ S → M5L.Separated S m →
      ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
        (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T

/-- **The slot is exactly its `¬ IsVFGen S` restriction** (by §4): the `VF`-generated bases are
vacuous, and the non-`VF`-generated ones are all that is left.  Together with §4 this says: the
separated branch of the paper's case split, as frozen in `M4Cases.CaseSeparated`, is *only* about
the `RV`-elements of `S` that are not `rv` of its `VF`-part — the `kAdd`/junk part isolated by
`residual_demands_junk_class` below. -/
theorem caseSeparated_iff_nonVFGen :
    M4Cases.CaseSeparated (M := M) (N := N) ↔ CaseSeparatedNonVFGen (M := M) (N := N) := by
  constructor
  · intro h S f hS _ m hmVF hmrv hsep
    exact h S f hS m hmVF hmrv hsep
  · intro h S f hS m hmVF hmrv hsep
    by_cases hgen : Assembly.IsVFGen S
    · have hm0 : m = iVFZero := eq_zero_of_slot_of_isVFGen hgen hmVF hmrv hsep
      exact ⟨S, f, le_rfl, fun _ => rfl, hm0 ▸ vfZero_mem_sub S, hS⟩
    · exact h S f hS hgen m hmVF hmrv hsep

/-! ## 5. Stress tests -/

section Stress

/-- `Standing ⊤`: the slot's own hypothesis is satisfiable. -/
theorem standing_top : Assembly.Standing (⊤ : LRV.Substructure M) := StandingTree.standing_top

/-- `IsVFGen ⊤` (via `RV = rv(VF^×) ∪ {0}`, `Assembly.RVeqRvVF_of_model`): the field-data row is
satisfiable. -/
theorem isVFGen_top : Assembly.IsVFGen (⊤ : LRV.Substructure M) := by
  intro x _ hx
  rcases Assembly.RVeqRvVF_of_model (M := M) x hx with ⟨y, hyVF, hyx⟩ | hz
  · exact Or.inl ⟨y, trivial, hyVF, hyx⟩
  · exact Or.inr hz

/-- `VFInvClosedOn ⊤`: the merged interface's inverse-closure row is satisfiable — it is a
hypothesis about *classes*, so `⊤` has it, and no `Standing`-level argument supplies it at a general
`S` (that is the row §1 removes). -/
theorem vfInvClosedOn_top : M5L.VFInvClosedOn (⊤ : LRV.Substructure M) := by
  intro x hxVF _ hx0
  rcases vf_mul_inv_or_zero hM hxVF with h | ⟨y, hyVF, hy⟩
  · exact absurd h hx0
  · exact ⟨y, hyVF, trivial, hy⟩

/-- `PolyExpansions` at the trivial extension `T = S` (constant coefficients): the representation
row is not an empty condition, and it is reflexive. -/
theorem polyExpansions_self (S : LRV.Substructure M) (e : M) :
    PolyExpansions (M := M) S S e := by
  intro x hxS hxVF hx0
  refine ⟨fun _ => x, 0, fun _ => hxVF, fun _ => hxS, fun _ => hx0, ?_⟩
  show x = iVFAdd (vsum (fun i => iVFMul x (vpow e i)) 0) (iVFMul x (vpow e 0))
  show x = iVFAdd iVFZero (iVFMul x iVFOne)
  rw [RVCalc.vf_zero_add hM (vf_mul_mem hM hxVF (vf_one_mem hM)), RVCalc.vf_mul_one hM hxVF]

/-- `0 ^ n = 0` in the `RV` sort for `n > 0`. -/
theorem rvpow_zero (hM : M ⊨ Axioms.ACVF) {n : ℕ} (hn : 0 < n) :
    rvpow (iRVZero : M) n = iRVZero := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
  show iRVMul (rvpow iRVZero j) iRVZero = iRVZero
  exact rv_mul_zero_right_of_model hM (iRV_rvpow hM (rv_zero_mem hM) j)

/-- `Separated S 0` holds for **every** `S`: the slot's `m = 0` branch has satisfiable hypotheses
(and its conclusion is trivial by §2), so the `m ≠ 0` side condition of `M5L.OneStepSeparatedP` is a
genuine restriction of that interface, not a consequence of the slot's hypotheses. -/
theorem separated_zero (S : LRV.Substructure M) : M5L.Separated S iVFZero := by
  intro k hk x y hxVF hyVF _ _ hx0 hy0
  show ¬ Cls (iRVMul (rvpow (iRv (iVFZero : M)) k) (iRv x)) (iRv y)
  rw [RVCalc.rv_zero_eq hM, rvpow_zero hM hk, rv_mul_zero_left_of_model hM (rv_mem hM hxVF)]
  intro hcls
  have hy_rv : iRV (iRv y) := rv_mem hM hyVF
  exact hy0 (RVCalc.vf_eq_zero_of_rv_eq_zero hM hyVF (RVCalc.le_infty_eq hM hy_rv hcls.1))

/-- The generated substructure contains the ill-sorted value `vfAdd rvZero rvZero`: the encoding's
closure is closed under *every* function symbol, so the extension `T` of the slot cannot avoid
`kAdd`/junk-generated elements. -/
theorem junk_mem_closure (S : LRV.Substructure M) (m : M) :
    iVFAdd iRVZero iRVZero ∈ Substructure.closure LRV ((S : Set M) ∪ {m}) := by
  refine (Substructure.closure LRV ((S : Set M) ∪ {m})).fun_mem Fn.vfAdd
    ![iRVZero, iRVZero] ?_
  intro i
  fin_cases i <;>
    exact Substructure.subset_closure
      (Set.mem_union_left {m} (M5L.rvZero_mem_sub (M := M) S))

/-- **The junk probe.**  `ResidualClasses S T` at the canonical extension demands, for the ill-sorted
value `z = vfAdd rvZero rvZero ∈ T` that no axiom constrains, that *if* `rv z` happens to be an
`RV`-element then its class is the class of an element of `S`.  This is the row of the residual that
`IsVFGen T` and `PolyExpansions S T m` do **not** reach: it is the `kAdd`/junk content of the
encoding, and it is why the slot's residual is stated with the class computation as its conclusion
rather than derived from `Axioms.ACVF` alone. -/
theorem residual_demands_junk_class {S : LRV.Substructure M} {m : M}
    (hres : M5L.ResidualClasses S (Substructure.closure LRV ((S : Set M) ∪ {m})))
    (hj : iRV (iRv (iVFAdd (M := M) iRVZero iRVZero))) :
    ∃ s : M, s ∈ S ∧ iRV s ∧ Cls (iRv (iVFAdd (M := M) iRVZero iRVZero)) s :=
  hres (iRv (iVFAdd (M := M) iRVZero iRVZero))
    ((Substructure.closure LRV ((S : Set M) ∪ {m})).fun_mem Fn.rvMap
      ![iVFAdd (M := M) iRVZero iRVZero]
      (by intro i; fin_cases i; exact junk_mem_closure S m))
    hj

end Stress

end M3Slot
end SpecialTransformations.Milestone0

/-! ## Axiom audit -/

#print axioms SpecialTransformations.Milestone0.M3Slot.rvpow_one
#print axioms SpecialTransformations.Milestone0.M3Slot.polyExpansions_quot
#print axioms SpecialTransformations.Milestone0.M3Slot.rv_mem_of_polyExpansions
#print axioms SpecialTransformations.Milestone0.M3Slot.ResidualClasses_of_poly
#print axioms SpecialTransformations.Milestone0.M3Slot.standing_of_poly_hypotheses
#print axioms SpecialTransformations.Milestone0.M3Slot.caseSeparated_of_slotRealization_and_fieldData
#print axioms SpecialTransformations.Milestone0.M3Slot.slotRealization_of_saturatedFS_and_individual
#print axioms SpecialTransformations.Milestone0.M3Slot.cases_of_slotResidual_and_rest
#print axioms SpecialTransformations.Milestone0.M3Slot.extendsHere_of_hullExtension_and_slotResidual
#print axioms SpecialTransformations.Milestone0.M3Slot.caseSeparated_of_extension_and_poly
#print axioms SpecialTransformations.Milestone0.M3Slot.slotRVControl_iff_slotClassControl
#print axioms SpecialTransformations.Milestone0.M3Slot.caseSeparated_of_slotRVControl
#print axioms SpecialTransformations.Milestone0.M3Slot.caseSeparated_of_slotClassControl
#print axioms SpecialTransformations.Milestone0.M3Slot.caseSeparated_of_oneStepSeparatedP
#print axioms SpecialTransformations.Milestone0.M3Slot.no_vf_witness_of_separated
#print axioms SpecialTransformations.Milestone0.M3Slot.not_isVFGen_of_slot
#print axioms SpecialTransformations.Milestone0.M3Slot.not_separated_of_isVFGen_mem
#print axioms SpecialTransformations.Milestone0.M3Slot.not_separated_top
#print axioms SpecialTransformations.Milestone0.M3Slot.eq_zero_of_slot_of_isVFGen
#print axioms SpecialTransformations.Milestone0.M3Slot.caseSeparated_at_isVFGen
#print axioms SpecialTransformations.Milestone0.M3Slot.caseSeparated_iff_nonVFGen
#print axioms SpecialTransformations.Milestone0.M3Slot.standing_top
#print axioms SpecialTransformations.Milestone0.M3Slot.isVFGen_top
#print axioms SpecialTransformations.Milestone0.M3Slot.vfInvClosedOn_top
#print axioms SpecialTransformations.Milestone0.M3Slot.polyExpansions_self
#print axioms SpecialTransformations.Milestone0.M3Slot.rvpow_zero
#print axioms SpecialTransformations.Milestone0.M3Slot.separated_zero
#print axioms SpecialTransformations.Milestone0.M3Slot.junk_mem_closure
#print axioms SpecialTransformations.Milestone0.M3Slot.residual_demands_junk_class
