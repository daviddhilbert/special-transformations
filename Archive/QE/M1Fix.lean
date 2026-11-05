/-
# The Shoenfield step for the frozen `HasQE`: obstruction, relative saturation, and the correct
  residual

Swarm `smw1tqlqv`, member m1 (direction 6: `Assembly.ShoenfieldTestFS`).

This file does three things, all machine-checked.

## 1. `Assembly.Prop39FS` is not the paper's Proposition 3.9 (cardinality)

`Assembly.Prop39FS` concludes `∃ g : M ↪[LRV] N`, an *injective* map on all of `M`, under the
hypothesis `Assembly.SaturatedFS N` which is a property of `N` alone and is quantified over *all*
models `M`.  So the statement forces `#M ≤ #N` for every pair of models for which some partial
embedding into `N` exists (`card_le_of_prop39FS`).  The paper's Proposition 3.9 fixes the pair and
assumes `N` is `‖M‖⁺`-saturated; the frozen statement drops that, and `M` can be larger than `N`.
Hence `ShoenfieldTestFS` is *vacuous* if `Props39FS` is refutable (see `not_prop39FS_of_data` and
`shoenfieldTestFS_of_cardObstruction`).

## 2. The frozen saturation notion is the wrong quantification (`SatRel`)

`Assembly.SaturatedFS N` says: for **all** models `M ⊨ ACVF`, all substructures `S ≤ M`, all
`f : S ↪ N`, all `m : M`, every *finitely satisfiable* pushed type of `m` is realised in `N`.
What `‖M‖⁺`-saturation of `N` gives is the *relative* statement `SatRel M N` for the single pair at
hand — a model of cardinality `κ` cannot be `κ⁺`-saturated, so `SatRel N N` is the false instance
that makes the "for all `M`" version unusable.  `saturatedFS_iff` records that the frozen notion is
exactly the `∀ M`-version of `SatRel`, and `Prop39Rel` is the paper's per-pair statement, which
implies the frozen `Prop39FS` (`prop39FS_of_prop39Rel`): the relative version is the one to prove
and it is *not* weaker in any usable sense.

## 3. The correct Shoenfield step: elementary amalgamation (`QFEAmalg`)

Even with the cardinality repaired, an embedding is not an elementary map, and quantifier-free
types only determine quantifier-free truth along embeddings.  The classical Shoenfield test (as
used e.g. for separably closed fields, Messmer) extends the isomorphism to an *elementary*
embedding; at the frozen interface the equivalent formulation is `QFEAmalg`: two models whose
sorted tuples have the same quantifier-free well-sorted type sit elementarily in a common model with
the tuples identified.  `qfTypeDetWS_of_qfEAmalg` proves that `QFEAmalg` gives well-sorted
quantifier-free type determination `M1Shoenfield.QFTypeDetWS`, and `hasQE_of_qfEAmalg` composes
with the (already green) criterion `M1Shoenfield.hasQE_ACVF_of_qfTypeDet` to give the frozen target
`HasQE Axioms.ACVF`.  This is the honest residual for the saturation route: it is satisfiable, it
has no cardinality obstruction, and its classical proof is "put both models elementarily inside a
saturated model and use strong homogeneity".

No `sorry`, no `axiom`, no `native_decide`.
-/
import Assembly_frozen
import ShoenfieldWS

open FirstOrder FirstOrder.Language
open scoped FirstOrder
open SpecialTransformations.Milestone0

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace M1Fix

/-! ## 1. `Prop39FS` forces `#M ≤ #N` -/

/-- **The cardinality obstruction.**  The conclusion of `Assembly.Prop39FS` is an injective map on
all of `M`, so any instantiation of it bounds `#M` by `#N`.  Nothing in `Assembly.SaturatedFS N`
bounds `M` (it is a property of `N` alone), so the frozen statement cannot be the paper's
Proposition 3.9, whose pair `(M, N)` satisfies `|N| ≥ ‖M‖⁺`. -/
theorem card_le_of_prop39FS (h39 : Assembly.Prop39FS)
    {M N : Type} [LRV.Structure M] [LRV.Structure N] [hM : M ⊨ Axioms.ACVF]
    [hN : N ⊨ Axioms.ACVF] (hSat : Assembly.SaturatedFS N) (S : LRV.Substructure M)
    (f : S ↪[LRV] N) : Cardinal.mk M ≤ Cardinal.mk N := by
  obtain ⟨g, _⟩ := h39 M N hSat S f
  exact Cardinal.mk_le_of_injective g.toEmbedding.injective

/-- **`Prop39FS` is refuted by any pair of models with `#N < #M` and a partial embedding into `N`.**
Such a pair exists as soon as one has a model of `ACVF` of cardinality `κ`, a `SaturatedFS` model
`N` of cardinality `≤ κ`, and any partial embedding `S ↪ N` (`S = ⊥`, or `S` an image of `N` inside
the larger model).  No such pair can be *produced* in Lean without a saturated model, which is why
the refutation is stated with the data as arguments. -/
theorem not_prop39FS_of_data {M N : Type} [LRV.Structure M] [LRV.Structure N]
    [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF] (hSat : Assembly.SaturatedFS N)
    (S : LRV.Substructure M) (f : S ↪[LRV] N) (hcard : Cardinal.mk N < Cardinal.mk M) :
    ¬ Assembly.Prop39FS :=
  fun h39 => absurd (card_le_of_prop39FS h39 hSat S f) (not_le_of_gt hcard)

/-- **`Assembly.ShoenfieldTestFS` holds vacuously** when a `SaturatedFS` model and a strictly larger
model with a partial embedding into it exist.  This is the exact sense in which the third
hypothesis of `Assembly.theorem_2_3_of_two` is discharged for free by the frozen statements: it is
not the model-theoretic content of Shoenfield's test. -/
theorem shoenfieldTestFS_of_cardObstruction {M N : Type} [LRV.Structure M] [LRV.Structure N]
    [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF] (hSat : Assembly.SaturatedFS N)
    (S : LRV.Substructure M) (f : S ↪[LRV] N) (hcard : Cardinal.mk N < Cardinal.mk M) :
    Assembly.ShoenfieldTestFS :=
  fun h39 => (not_prop39FS_of_data hSat S f hcard h39).elim

/-! ## 2. Relative saturation: the frozen notion is the `∀ M`-version of the paper's

`‖M‖⁺`-saturation of `N` is a statement about the pair `(M, N)`: `N` realises every finitely
satisfiable type pushed from a substructure of *this* `M`.  `Assembly.SaturatedFS N` quantifies the
same clause over all models `M`, and the instance `M = N` is the one that a model cannot satisfy.
The relative version is therefore the one to prove; and it implies the frozen one, so nothing is
lost by switching. -/

/-- **Relative saturation**: the per-pair form of `Assembly.SaturatedFS`. -/
def SatRel (M N : Type) [LRV.Structure M] [LRV.Structure N] : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N) (m : M),
    (∀ (φ : LRV.Formula (S ⊕ Unit)),
        φ.Realize (Realize.mv S m) → ∃ b : N, φ.Realize (Realize.wv f b)) →
      ∃ b : N, ∀ (φ : LRV.Formula (S ⊕ Unit)),
        φ.Realize (Realize.mv S m) → φ.Realize (Realize.wv f b)

/-- The frozen `Assembly.SaturatedFS N` is exactly "`SatRel M N` for every model `M`". -/
theorem saturatedFS_iff {N : Type} [LRV.Structure N] :
    Assembly.SaturatedFS N ↔ ∀ (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF], SatRel M N :=
  Iff.rfl

/-- **The paper's Proposition 3.9, with the saturation attached to the pair.**  This is the
statement the three Section 3.1 ingredients can actually prove; the frozen `Assembly.Prop39FS`
asks for the same conclusion from `∀ M, SatRel M N`, which is strictly stronger. -/
def Prop39Rel : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    SatRel M N → ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), ∃ g : M ↪[LRV] N, ∀ x : S, g x = f x

/-- The relative statement implies the frozen one, so proving `Prop39Rel` remains sufficient for the
assembly as it stands. -/
theorem prop39FS_of_prop39Rel (h : Prop39Rel) : Assembly.Prop39FS := by
  intro M N _ _ hM hN hSat S f
  exact h M N (hSat M) S f

/-! ## 3. The correct Shoenfield step: elementary amalgamation

An `L_RV`-embedding of models of `ACVF` need not be elementary (the prime model inside a model with
a nontrivial value group is the standard witness), so a quantifier-free type comparison can never
reach a formula of higher complexity through an embedding alone.  What the classical argument
produces is a *common elementary extension* in which the two tuples coincide, and that is what
`QFEAmalg` states.  It has no cardinality obstruction and it is not a restatement of QE: it is the
statement that a saturated model with strong homogeneity gives. -/

/-- **Same quantifier-free well-sorted type** on sorted tuples (both parameter and variable parts). -/
def SameQFWS {M N : Type} [LRV.Structure M] [LRV.Structure N] {α : Type} {n : ℕ}
    (sα : α → SortTag) (sn : Fin n → SortTag) (v : α → M) (x : Fin n → M)
    (w : α → N) (y : Fin n → N) : Prop :=
  ∀ ψ : LRV.BoundedFormula α n, ψ.IsQF → LRV.WellSorted sα sn ψ →
    (ψ.Realize v x ↔ ψ.Realize w y)

/-- **The elementary-amalgamation form of Shoenfield's test, at the frozen interface.**  Two models
of `ACVF` whose sorted tuples have the same quantifier-free well-sorted type sit elementarily in a
common structure with the tuples identified.  (`K` is then a model of `ACVF` automatically: see
`qfEAmalg_model`.) -/
def QFEAmalg : Prop :=
  ∀ (α : Type) (sα : α → SortTag) (n : ℕ) (sn : Fin n → SortTag)
    (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF]
    (N : Type) [LRV.Structure N] [N ⊨ Axioms.ACVF]
    (v : α → M) (x : Fin n → M) (w : α → N) (y : Fin n → N),
    M1Shoenfield.SortedVec sα v → M1Shoenfield.SortedTup sn x →
    M1Shoenfield.SortedVec sα w → M1Shoenfield.SortedTup sn y →
    SameQFWS sα sn v x w y →
    ∃ (K : Type) (_ : LRV.Structure K) (e : M ↪ₑ[LRV] K) (e' : N ↪ₑ[LRV] K),
      (∀ a, e (v a) = e' (w a)) ∧ (∀ i, e (x i) = e' (y i))

/-- The amalgamating structure of `QFEAmalg` is itself a model of `ACVF`. -/
theorem qfEAmalg_model {α : Type} {sα : α → SortTag} {n : ℕ} {sn : Fin n → SortTag}
    {M N K : Type} [LRV.Structure M] [LRV.Structure N] [LRV.Structure K]
    [hM : M ⊨ Axioms.ACVF] (e : M ↪ₑ[LRV] K) : K ⊨ Axioms.ACVF :=
  (e.theory_model_iff Axioms.ACVF).mp hM

/-- **`QFEAmalg` gives well-sorted quantifier-free type determination.**  Transfer the truth value
of `φ` along the two elementary embeddings and use that the tuples coincide in `K`. -/
theorem qfTypeDetWS_of_qfEAmalg (h : QFEAmalg) : M1Shoenfield.QFTypeDetWS Axioms.ACVF := by
  intro α sα n sn φ hws M sM hM N sN hN v x w y hv hx hw hy hsame
  obtain ⟨K, sK, e, e', hag, hax⟩ := h α sα n sn M N v x w y hv hx hw hy hsame
  letI : LRV.Structure K := sK
  have h1 : φ.Realize v x ↔ φ.Realize (fun a => e (v a)) (fun i => e (x i)) :=
    (e.map_boundedFormula φ v x).symm
  have h2 : φ.Realize w y ↔ φ.Realize (fun a => e' (w a)) (fun i => e' (y i)) :=
    (e'.map_boundedFormula φ w y).symm
  have h3 : (fun a => e (v a)) = (fun a => e' (w a)) := funext hag
  have h4 : (fun i => e (x i)) = (fun i => e' (y i)) := funext hax
  rw [h1, h2, h3, h4]

/-- **The frozen Theorem 2.3 from the corrected Shoenfield step**: well-sorted quantifier
elimination for `ACVF` follows from `QFEAmalg` alone — no extension property, no cardinality
hypothesis, and no `Prop39FS`. -/
theorem hasQE_of_qfEAmalg (h : QFEAmalg) : HasQE Axioms.ACVF :=
  M1Shoenfield.hasQE_ACVF_of_qfTypeDet (qfTypeDetWS_of_qfEAmalg h)

/-- Restatement for the assembly: `QFEAmalg` alone yields the frozen target. -/
theorem theorem_2_3_of_qfEAmalg (h : QFEAmalg) : HasQE Axioms.ACVF := hasQE_of_qfEAmalg h

/-! ## 4. Exactly what an embedding transfers: quantifier-free truth

`Assembly.Prop39FS` supplies an `L_RV`-monomorphism.  An embedding preserves and reflects
quantifier-free formulas (`FirstOrder.Language.IsQF.realize_embedding`) and nothing more, so it
transfers the *hypothesis* of `M1Shoenfield.QFTypeDetWS` and not its conclusion.  This is the
mechanism the elementary amalgamation replaces: there the transfer is
`ElementaryEmbedding.map_boundedFormula`. -/

/-- An `L_RV`-embedding transfers quantifier-free truth (in both directions). -/
theorem qf_realize_embedding {M N : Type} [LRV.Structure M] [LRV.Structure N] (g : M ↪[LRV] N)
    {α : Type} {n : ℕ} {φ : LRV.BoundedFormula α n} (hQF : φ.IsQF) (v : α → M) (xs : Fin n → M) :
    φ.Realize (g ∘ v) (g ∘ xs) ↔ φ.Realize v xs :=
  hQF.realize_embedding g

/-- The same, in the shape in which the frozen `Prop39FS` hands it over: a monomorphism `M ↪ N`
matching the tuples carries the quantifier-free well-sorted type from `M` to `N`.  This is the
*hypothesis* of `QFTypeDetWS`, which is why the extension property alone cannot close it. -/
theorem sameQFWS_of_embedding {M N : Type} [LRV.Structure M] [LRV.Structure N] (g : M ↪[LRV] N)
    {α : Type} {n : ℕ} {sα : α → SortTag} {sn : Fin n → SortTag}
    (v : α → M) (x : Fin n → M) :
    SameQFWS sα sn (g ∘ v) (g ∘ x) v x :=
  fun _ hQF _ => qf_realize_embedding g hQF v x

/-- **Robinson's model completeness of `ACVF` at the frozen interface.**  An `L_RV`-embedding is
*well-sorted elementary* when it preserves and reflects every well-sorted formula at sorted tuples. -/
def WellSortedElem {M N : Type} [LRV.Structure M] [LRV.Structure N] (e : M ↪[LRV] N) : Prop :=
  ∀ (α : Type) (sα : α → SortTag) (n : ℕ) (sn : Fin n → SortTag) (φ : LRV.BoundedFormula α n),
    LRV.WellSorted sα sn φ → ∀ (v : α → M) (x : Fin n → M),
      M1Shoenfield.SortedVec sα v → M1Shoenfield.SortedTup sn x →
      (φ.Realize v x ↔ φ.Realize (e ∘ v) (e ∘ x))

/-- **Model completeness of `ACVF` in `L_RV`**: every `L_RV`-embedding between models of `ACVF` is
well-sorted elementary.  This is classical — A. Robinson (1956) proved `ACVF` model complete in the
language of valued fields (see e.g. Haskell–Macpherson, *Definable sets in algebraically closed
valued fields*, §2.1), and the `RV`-sort is interpretable from the valuation ring, so elementarity
transfers to `L_RV`.  It is strictly weaker than `HasQE` (model completeness says nothing about
quantifier-free witnesses) and it is not in Mathlib or in this repo. -/
def ModelCompleteRV : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF]
    (e : M ↪[LRV] N), WellSortedElem e

/-- **The paper's Proposition 3.9 in amalgamation form.**  Models of `ACVF` whose sorted tuples have
the same quantifier-free well-sorted type embed in a *common* model of `ACVF` with the tuples
identified.  This is what the Section 3.1 ingredients produce: a monomorphism into a saturated model,
taken once for each model with the same image tuple, so that the two images coincide.  Unlike
`QFEAmalg` the embeddings here are not required to be elementary, and this is exactly the form the
frozen `Prop39FS`/`PrepStepP`/`OneStepVFP` chain aims at. -/
def MonoAmalg : Prop :=
  ∀ (α : Type) (sα : α → SortTag) (n : ℕ) (sn : Fin n → SortTag)
    (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF]
    (N : Type) [LRV.Structure N] [N ⊨ Axioms.ACVF]
    (v : α → M) (x : Fin n → M) (w : α → N) (y : Fin n → N),
    M1Shoenfield.SortedVec sα v → M1Shoenfield.SortedTup sn x →
    M1Shoenfield.SortedVec sα w → M1Shoenfield.SortedTup sn y →
    SameQFWS sα sn v x w y →
    ∃ (K : Type) (_ : LRV.Structure K) (_ : K ⊨ Axioms.ACVF)
      (g : M ↪[LRV] K) (h : N ↪[LRV] K),
      (∀ a, g (v a) = h (w a)) ∧ (∀ i, g (x i) = h (y i))

/-- Elementary amalgamation is a special case of embedding amalgamation, and the amalgamating
structure is a model of `ACVF` there too. -/
theorem monoAmalg_of_qfEAmalg (h : QFEAmalg) : MonoAmalg := by
  intro α sα n sn M sM hM N sN hN v x w y hv hx hw hy hsame
  obtain ⟨K, sK, e, e', hag, hax⟩ := h α sα n sn M N v x w y hv hx hw hy hsame
  letI : LRV.Structure K := sK
  haveI : K ⊨ Axioms.ACVF := (e.theory_model_iff Axioms.ACVF).mp hM
  exact ⟨K, sK, ‹K ⊨ Axioms.ACVF›, e.toEmbedding, e'.toEmbedding, hag, hax⟩

/-- **The Shoenfield step for `ACVF`, from the two classical inputs.**  Quantifier-free well-sorted
types determine well-sorted types: transfer along the two embeddings using model completeness, then
use that the tuples coincide in the common model. -/
theorem qfTypeDetWS_of_modelComplete_monoAmalg (hmc : ModelCompleteRV) (ham : MonoAmalg) :
    M1Shoenfield.QFTypeDetWS Axioms.ACVF := by
  intro α sα n sn φ hws M sM hM N sN hN v x w y hv hx hw hy hsame
  obtain ⟨K, sK, hK, g, h, hag, hax⟩ := ham α sα n sn M N v x w y hv hx hw hy hsame
  letI : LRV.Structure K := sK
  haveI : K ⊨ Axioms.ACVF := hK
  have h1 : φ.Realize v x ↔ φ.Realize (g ∘ v) (g ∘ x) := hmc M K g α sα n sn φ hws v x hv hx
  have h2 : φ.Realize w y ↔ φ.Realize (h ∘ w) (h ∘ y) := hmc N K h α sα n sn φ hws w y hw hy
  have h3 : (g ∘ v) = (h ∘ w) := funext hag
  have h4 : (g ∘ x) = (h ∘ y) := funext hax
  rw [h1, h2, h3, h4]

/-- **The frozen Theorem 2.3 from model completeness and embedding amalgamation.**  Neither
hypothesis is a restatement of QE: `ModelCompleteRV` is Robinson's theorem, and `MonoAmalg` is what
Proposition 3.9 supplies. -/
theorem hasQE_of_modelComplete_monoAmalg (hmc : ModelCompleteRV) (ham : MonoAmalg) :
    HasQE Axioms.ACVF :=
  M1Shoenfield.hasQE_ACVF_of_qfTypeDet (qfTypeDetWS_of_modelComplete_monoAmalg hmc ham)

/-! ## 5. `QFEAmalg` is satisfiable in its diagonal instance

The `∃`-shape of `QFEAmalg` is not vacuous: for a single model the identity works.  This is a
sanity check on the statement, not a proof of it. -/

/-- The diagonal instance of `QFEAmalg`: with `N = M` the identity amalgamates. -/
theorem qfEAmalg_diagonal (M : Type) [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
    {α : Type} {sα : α → SortTag} {n : ℕ} {sn : Fin n → SortTag}
    (v : α → M) (x : Fin n → M) :
    ∃ (K : Type) (_ : LRV.Structure K) (e : M ↪ₑ[LRV] K) (e' : M ↪ₑ[LRV] K),
      (∀ a, e (v a) = e' (v a)) ∧ (∀ i, e (x i) = e' (x i)) :=
  ⟨M, inferInstance, ElementaryEmbedding.refl LRV M, ElementaryEmbedding.refl LRV M,
    fun _ => rfl, fun _ => rfl⟩

end M1Fix

#print axioms M1Fix.card_le_of_prop39FS
#print axioms M1Fix.not_prop39FS_of_data
#print axioms M1Fix.shoenfieldTestFS_of_cardObstruction
#print axioms M1Fix.saturatedFS_iff
#print axioms M1Fix.prop39FS_of_prop39Rel
#print axioms M1Fix.qfEAmalg_model
#print axioms M1Fix.qfTypeDetWS_of_qfEAmalg
#print axioms M1Fix.hasQE_of_qfEAmalg
#print axioms M1Fix.qf_realize_embedding
#print axioms M1Fix.sameQFWS_of_embedding
#print axioms M1Fix.monoAmalg_of_qfEAmalg
#print axioms M1Fix.qfTypeDetWS_of_modelComplete_monoAmalg
#print axioms M1Fix.hasQE_of_modelComplete_monoAmalg
#print axioms M1Fix.qfEAmalg_diagonal
