/-
# D7 — `HullExtension`, Lemma 3.3's *map* half, factored into its stage steps

Swarm `smw2ox51x`, member m5, direction d7.  Companion notes: `NOTES.md`.

`G3.HullExtension M N` (`QE/Prop39Decomp.lean`) is Lemma 3.3 in hull form: every monomorphism
`S ↪ N` extends to the fixed hull `standingHull S`; it is equivalent to the frozen
`Assembly.PrepStepP` and is one conjunct of Proposition 3.9.  The substructure half of Lemma 3.3
(the hull exists, is `Standing`, is least) is `QE/StandingHull.lean`.  This file settles what the
**map** half is made of.

* §1–§3  `ExtendsTo`, `HullExtensionAt`, the stagewise form `Stagewise`, and restriction.
* §4     the `ω`-iteration: `HullBaseStep` (the units), `HullRootStep` (the roots), the compatible
         chain `chainOf`, agreement `chainOf_agree`, and the union `unionEmb`;
         `hullExtension_of_base_root`, `prepStepP_of_base_root`.
* §5, §9 where the content is: every hull stage of a `Standing` domain *is* the domain
         (`hullSeq_eq_of_standing`), so both steps are trivial there; the base step has content
         exactly at `¬ KEqTop` (`hullBaseStep_iff_nonKEqTop`) and the root step exactly at
         `KEqTop ∧ ¬ Standing` (`rootStepResidual_iff`).  The case lemmas 3.4–3.8 have `Standing`
         domains (`Assembly.OneStepVFP`), i.e. the complementary class.
* §6, §8 the named residual `RootStepResidual`, and the stress tests: the base step alone forces
         `#K(M)ˣ ≤ #N` (`hullBaseStep_forces_units_size`, `not_hullBaseStep_of_cardinality`), the
         hull form follows from `Assembly.VFGenCaseP` at `VF`-generated domains, and it is trivial at
         `⊤`/`Standing` domains (non-vacuity).
* §7     the factorization is exact:
         `Assembly.PrepStepP ⟺ HullBaseStep ∧ HullRootStep`,
         `G3.ExtendsHere ⟺ HullBaseStep ∧ HullRootStep ∧ Assembly.OneStepVFP`.

Verification: `cd $R && LEAN_PATH=$R/.scratch2/sec3:$LEAN_PATH lean
.ultramath/smw2ox51x/m5/D7Hull.lean` — exit 0, 0 `error` lines, no `sorry`/`admit`/`native_decide`,
no new `axiom`; every `#print axioms` below is `[propext, Classical.choice, Quot.sound]`.
-/
import Prop39Decomp
import StandingHull

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations
namespace Milestone0
namespace D7

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
  [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

/-- `f : S ↪ N` extends to `g : T ↪ N` along `S ≤ T`.  Stated with the ambient element exposed, so
that no membership proof ever has to be transported. -/
def ExtendsTo {S T : LRV.Substructure M} (hST : S ≤ T) (f : S ↪[LRV] N) (g : T ↪[LRV] N) : Prop :=
  ∀ (y : M) (hy : y ∈ S), g ⟨y, hST hy⟩ = f ⟨y, hy⟩

/-! ## 1. The hull half at a fixed domain -/

/-- **Lemma 3.3, map half, at a fixed `S`**: every monomorphism out of `S` extends to the *fixed*
hull `standingHull S`. -/
def HullExtensionAt (S : LRV.Substructure M) : Prop :=
  ∀ f : S ↪[LRV] N, ∃ g : M8Hull.standingHull S ↪[LRV] N,
    ExtendsTo (M8Hull.le_standingHull S) f g

/-- `G3.HullExtension` is the conjunction of its fixed-domain forms. -/
theorem hullExtension_iff_forall_hullExtensionAt :
    G3.HullExtension M N ↔ ∀ S : LRV.Substructure M, HullExtensionAt (N := N) S := by
  constructor
  · rintro h S f
    obtain ⟨g, hg⟩ := h S f
    exact ⟨g, fun y hy => hg ⟨y, hy⟩⟩
  · rintro h S f
    obtain ⟨g, hg⟩ := h S f
    exact ⟨g, fun x => hg x.1 x.2⟩

/-! ## 2. The hull half is trivial at `Standing` domains -/

/-- **`standingHull S = S` when `S` is `Standing`, so the hull half costs nothing there.** -/
theorem hullExtensionAt_of_standing (S : LRV.Substructure M) (h : Assembly.Standing S) :
    HullExtensionAt (N := N) S := by
  intro f
  refine ⟨f.comp (Substructure.inclusion (le_of_eq (M8Hull.standingHull_eq_self_iff.mpr h))), ?_⟩
  intro y hy
  exact congrArg f (Subtype.ext rfl)

/-- The `⊤`-witness: the hull of `⊤` is `⊤`, so at the top domain the hull half is the trivial
statement that a total embedding extends itself. -/
theorem hullExtensionAt_top : HullExtensionAt (M := M) (N := N) (⊤ : LRV.Substructure M) :=
  hullExtensionAt_of_standing _ StandingTree.standing_top

/-! ## 3. The stagewise form: extending to every stage of the canonical hull -/

/-- Every element of `S` lies in every stage of the hull of `S`. -/
theorem le_hullSeq (S : LRV.Substructure M) (k : ℕ) : S ≤ M8Hull.hullSeq S k :=
  (M8Hull.le_baseClosure S).trans (M8Hull.monotone_hullSeq S (Nat.zero_le k))

/-- Membership in a later stage, at the ambient element. -/
theorem mem_hullSeq_mono (S : LRV.Substructure M) {k j : ℕ} (h : k ≤ j) {y : M}
    (hy : y ∈ M8Hull.hullSeq S k) : y ∈ M8Hull.hullSeq S j :=
  M8Hull.monotone_hullSeq S h hy

/-- **The stagewise form of Lemma 3.3's map half**: every monomorphism extends to *every* stage of
the canonical hull of its domain.  No existential over superstructures appears. -/
def Stagewise (M N : Type) [LRV.Structure M] [LRV.Structure N]
    [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF] : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N) (k : ℕ),
    ∃ g : M8Hull.hullSeq S k ↪[LRV] N, ExtendsTo (le_hullSeq S k) f g

/-- The hull half of Lemma 3.3 implies its stagewise form (restrict the extension). -/
theorem stagewise_of_hullExtension (h : G3.HullExtension M N) : Stagewise M N := by
  intro S f k
  obtain ⟨g, hg⟩ := h S f
  refine ⟨g.comp (Substructure.inclusion (M8Hull.hullSeq_le_standingHull S k)), ?_⟩
  intro y hy
  refine (congrArg g (Subtype.ext rfl)).trans ?_
  exact hg ⟨y, hy⟩

/-! ## 4. The two steps of Lemma 3.3, and the `ω`-iteration -/

/-- The base step: every monomorphism extends to `hullSeq S 0 = closure (S ∪ K(M)ˣ)`. -/
def HullBaseStep (M N : Type) [LRV.Structure M] [LRV.Structure N]
    [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF] : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N),
    ∃ g : M8Hull.hullSeq S 0 ↪[LRV] N, ExtendsTo (M8Hull.le_baseClosure S) f g

/-- The root step: every monomorphism out of a stage extends to the next stage. -/
def HullRootStep (M N : Type) [LRV.Structure M] [LRV.Structure N]
    [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF] : Prop :=
  ∀ (S : LRV.Substructure M) (k : ℕ) (f : M8Hull.hullSeq S k ↪[LRV] N),
    ∃ g : M8Hull.hullSeq S (k + 1) ↪[LRV] N, ExtendsTo (M8Hull.hullSeq_le_succ S k) f g

/-- The stagewise hypothesis already gives the base step. -/
theorem hullBaseStep_of_stagewise (h : Stagewise M N) : HullBaseStep M N := by
  intro S f
  obtain ⟨g, hg⟩ := h S f 0
  exact ⟨g, hg⟩

section Iteration

variable (hb : HullBaseStep M N) (hr : HullRootStep M N)

/-- **The compatible chain of extensions of the hull stages.** -/
noncomputable def chainOf (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    ∀ k : ℕ, M8Hull.hullSeq S k ↪[LRV] N
  | 0 => Classical.choose (hb S f)
  | (k + 1) => Classical.choose (hr S k (chainOf S f k))

/-- The base of the chain extends `f`. -/
theorem chainOf_zero_extends (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    ExtendsTo (M8Hull.le_baseClosure S) f (chainOf hb hr S f 0) :=
  Classical.choose_spec (hb S f)

/-- Consecutive stages of the chain agree. -/
theorem chainOf_succ_extends (S : LRV.Substructure M) (f : S ↪[LRV] N) (k : ℕ) :
    ExtendsTo (M8Hull.hullSeq_le_succ S k) (chainOf hb hr S f k)
      (chainOf hb hr S f (k + 1)) :=
  Classical.choose_spec (hr S k (chainOf hb hr S f k))

/-- **Agreement of the chain at any two comparable stages**, at the ambient element. -/
theorem chainOf_agree (S : LRV.Substructure M) (f : S ↪[LRV] N) {k j : ℕ} (h : k ≤ j) :
    ∀ (y : M) (hy : y ∈ M8Hull.hullSeq S k),
      chainOf hb hr S f j ⟨y, mem_hullSeq_mono S h hy⟩ = chainOf hb hr S f k ⟨y, hy⟩ := by
  induction j, h using Nat.le_induction with
  | base =>
    intro y hy
    exact congrArg (chainOf hb hr S f k) (Subtype.ext rfl)
  | succ n hn ih =>
    intro y hy
    have hstep := chainOf_succ_extends hb hr S f n y (mem_hullSeq_mono S hn hy)
    have heq : (⟨y, mem_hullSeq_mono S (Nat.le_succ_of_le hn) hy⟩ :
        ↥(M8Hull.hullSeq S (n + 1)))
        = ⟨y, M8Hull.hullSeq_le_succ S n (mem_hullSeq_mono S hn hy)⟩ := Subtype.ext rfl
    rw [heq, hstep]
    exact ih y hy

/-! ### The union map -/

/-- Every element of the hull lies in some stage. -/
theorem exists_stage (S : LRV.Substructure M) {x : M} (hx : x ∈ M8Hull.standingHull S) :
    ∃ k : ℕ, x ∈ M8Hull.hullSeq S k :=
  (Substructure.mem_iSup_of_directed (M8Hull.directed_hullSeq S)).mp hx

/-- The underlying function of the union of the chain. -/
noncomputable def unionFun (S : LRV.Substructure M) (f : S ↪[LRV] N)
    (x : M8Hull.standingHull S) : N :=
  chainOf hb hr S f (Classical.choose (exists_stage S x.2))
    ⟨x.1, Classical.choose_spec (exists_stage S x.2)⟩

/-- The union does not depend on which stage realises the element. -/
theorem unionFun_spec (S : LRV.Substructure M) (f : S ↪[LRV] N)
    (x : M8Hull.standingHull S) (k : ℕ) (hx : x.1 ∈ M8Hull.hullSeq S k) :
    unionFun hb hr S f x = chainOf hb hr S f k ⟨x.1, hx⟩ := by
  have hk₀' : x.1 ∈ M8Hull.hullSeq S (Classical.choose (exists_stage S x.2)) :=
    Classical.choose_spec (exists_stage S x.2)
  have e1 : chainOf hb hr S f (Classical.choose (exists_stage S x.2))
        ⟨x.1, hk₀'⟩
      = chainOf hb hr S f (max (Classical.choose (exists_stage S x.2)) k)
        ⟨x.1, mem_hullSeq_mono S (le_max_left _ _) hk₀'⟩ :=
    (chainOf_agree hb hr S f (le_max_left _ _) x.1 hk₀').symm
  have e2 : chainOf hb hr S f k ⟨x.1, hx⟩
      = chainOf hb hr S f (max (Classical.choose (exists_stage S x.2)) k)
        ⟨x.1, mem_hullSeq_mono S (le_max_right _ _) hx⟩ :=
    (chainOf_agree hb hr S f (le_max_right _ _) x.1 hx).symm
  show chainOf hb hr S f (Classical.choose (exists_stage S x.2)) ⟨x.1, hk₀'⟩
      = chainOf hb hr S f k ⟨x.1, hx⟩
  rw [e1, e2]

/-- The union map is injective. -/
theorem unionFun_inj (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    Function.Injective (unionFun hb hr S f) := by
  intro x y hxy
  obtain ⟨kx, hx⟩ := exists_stage S x.2
  obtain ⟨ky, hy⟩ := exists_stage S y.2
  have hxm : x.1 ∈ M8Hull.hullSeq S (max kx ky) := mem_hullSeq_mono S (le_max_left kx ky) hx
  have hym : y.1 ∈ M8Hull.hullSeq S (max kx ky) := mem_hullSeq_mono S (le_max_right kx ky) hy
  have h1 : chainOf hb hr S f (max kx ky) ⟨x.1, hxm⟩
      = chainOf hb hr S f (max kx ky) ⟨y.1, hym⟩ := by
    rw [← unionFun_spec hb hr S f x (max kx ky) hxm,
      ← unionFun_spec hb hr S f y (max kx ky) hym]
    exact hxy
  have h2 := (chainOf hb hr S f (max kx ky)).injective h1
  exact Subtype.ext (by simpa using congrArg Subtype.val h2)

/-- Finitely many elements of the hull lie in a common stage. -/
theorem exists_stage_finset (S : LRV.Substructure M) {n : ℕ}
    (x : Fin n → M8Hull.standingHull S) :
    ∃ k : ℕ, ∀ i, (x i).1 ∈ M8Hull.hullSeq S k := by
  choose K hK using fun i => exists_stage S (x i).2
  exact ⟨Finset.univ.sup K,
    fun i => mem_hullSeq_mono S (Finset.le_sup (Finset.mem_univ i)) (hK i)⟩

/-- **The union of the chain is an `LRV`-embedding of the hull.** -/
noncomputable def unionEmb (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    M8Hull.standingHull S ↪[LRV] N :=
  Language.Embedding.mk ⟨unionFun hb hr S f, unionFun_inj hb hr S f⟩
    (fun {n} F x => by
      obtain ⟨k, hk⟩ := exists_stage_finset S x
      show unionFun hb hr S f (Structure.funMap F x)
        = Structure.funMap F (fun i => unionFun hb hr S f (x i))
      have hmem : Structure.funMap F (fun i => (x i).1) ∈ M8Hull.hullSeq S k :=
        (M8Hull.hullSeq S k).fun_mem F (fun i => (x i).1) hk
      have hlhs : unionFun hb hr S f (Structure.funMap F x)
          = Structure.funMap F
              (fun i => chainOf hb hr S f k ⟨(x i).1, hk i⟩) := by
        refine (unionFun_spec hb hr S f (Structure.funMap F x) k hmem).trans ?_
        exact (chainOf hb hr S f k).map_fun' F
          (fun i => (⟨(x i).1, hk i⟩ : ↥(M8Hull.hullSeq S k)))
      have hrhs : Structure.funMap F (fun i => unionFun hb hr S f (x i))
          = Structure.funMap F
              (fun i => chainOf hb hr S f k ⟨(x i).1, hk i⟩) := by
        refine congrArg (Structure.funMap F) ?_
        funext i
        exact unionFun_spec hb hr S f (x i) k (hk i)
      rw [hlhs, hrhs])
    (fun {n} r x => by
      obtain ⟨k, hk⟩ := exists_stage_finset S x
      show Structure.RelMap r (fun i => unionFun hb hr S f (x i)) ↔ Structure.RelMap r x
      have he : (fun i => unionFun hb hr S f (x i))
          = (fun i => chainOf hb hr S f k ⟨(x i).1, hk i⟩) := by
        funext i
        exact unionFun_spec hb hr S f (x i) k (hk i)
      have hbasis : Structure.RelMap r (fun i => chainOf hb hr S f k ⟨(x i).1, hk i⟩)
          ↔ Structure.RelMap r (fun i => ((x i) : M8Hull.standingHull S).1) :=
        (chainOf hb hr S f k).map_rel' r
          (fun i => (⟨(x i).1, hk i⟩ : ↥(M8Hull.hullSeq S k)))
      rw [he]
      exact hbasis)

/-- The union of the chain extends `f`. -/
theorem unionEmb_extends (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    ExtendsTo (M8Hull.le_standingHull S) f (unionEmb hb hr S f) := by
  intro y hy
  show unionFun hb hr S f ⟨y, M8Hull.le_standingHull S hy⟩ = f ⟨y, hy⟩
  refine (unionFun_spec hb hr S f ⟨y, M8Hull.le_standingHull S hy⟩ 0
    (le_hullSeq S 0 hy)).trans ?_
  exact (congrArg (chainOf hb hr S f 0) (Subtype.ext rfl)).trans
    (chainOf_zero_extends hb hr S f y hy)

end Iteration

/-- **§4 main: the two steps of Lemma 3.3 give its map half.** -/
theorem hullExtensionAt_of_base_root (hb : HullBaseStep M N) (hr : HullRootStep M N)
    (S : LRV.Substructure M) : HullExtensionAt (N := N) S :=
  fun f => ⟨unionEmb hb hr S f, unionEmb_extends hb hr S f⟩

/-- **The two steps of Lemma 3.3 give the hull form of Lemma 3.3.** -/
theorem hullExtension_of_base_root (hb : HullBaseStep M N) (hr : HullRootStep M N) :
    G3.HullExtension M N := by
  rw [hullExtension_iff_forall_hullExtensionAt]
  exact fun S => hullExtensionAt_of_base_root hb hr S

/-- **The two steps of Lemma 3.3 give the frozen `Assembly.PrepStepP`.** -/
theorem prepStepP_of_base_root (hb : HullBaseStep M N) (hr : HullRootStep M N) :
    Assembly.PrepStepP (M := M) (N := N) :=
  G3.prepStepP_iff_hullExtension.mpr (hullExtension_of_base_root hb hr)

/-! ## 5. At `Standing` domains every stage is the domain itself -/

/-- The base closure of a `KEqTop` substructure is itself. -/
theorem baseClosure_le_of_KEqTop {T : LRV.Substructure M} (h : Assembly.KEqTop T) :
    M8Hull.baseClosure T ≤ T := by
  show Substructure.closure LRV ((T : Set M) ∪ {x : M | iUnits x}) ≤ T
  rw [Substructure.closure_le]
  rintro x (hxT | hxU)
  · exact hxT
  · exact h x hxU

theorem baseClosure_eq_of_KEqTop {T : LRV.Substructure M} (h : Assembly.KEqTop T) :
    M8Hull.baseClosure T = T :=
  le_antisymm (baseClosure_le_of_KEqTop h) (M8Hull.le_baseClosure T)

/-- The root closure of a `Standing` substructure is itself. -/
theorem rootClosure_le_of_standing {T : LRV.Substructure M} (h : Assembly.Standing T) :
    M8Hull.rootClosure T ≤ T := by
  show Substructure.closure LRV ((T : Set M) ∪ M8Hull.rootSet T) ≤ T
  rw [Substructure.closure_le]
  rintro x (hxT | hxr)
  · exact hxT
  · exact M8Hull.rootSet_subset_of_standing le_rfl h hxr

/-- **At a `Standing` domain the hull never grows.** -/
theorem hullSeq_eq_of_standing {T : LRV.Substructure M} (h : Assembly.Standing T) :
    ∀ k : ℕ, M8Hull.hullSeq T k = T
  | 0 => baseClosure_eq_of_KEqTop h.1
  | (k + 1) => by
    show M8Hull.rootClosure (M8Hull.hullSeq T k) = T
    rw [hullSeq_eq_of_standing h k]
    exact le_antisymm (rootClosure_le_of_standing h) (M8Hull.le_rootClosure T)

/-- **The base step is trivial at a `Standing` domain.** -/
theorem hullBaseStep_standing_trivial (T : LRV.Substructure M) (h : Assembly.Standing T)
    (f : T ↪[LRV] N) :
    ∃ g : M8Hull.hullSeq T 0 ↪[LRV] N, ExtendsTo (M8Hull.le_baseClosure T) f g := by
  refine ⟨f.comp (Substructure.inclusion (le_of_eq (baseClosure_eq_of_KEqTop h.1))), ?_⟩
  intro y hy
  exact congrArg f (Subtype.ext rfl)

/-- **The root step is trivial at a `Standing` domain**: the stage does not grow. -/
theorem hullRootStep_standing_trivial (T : LRV.Substructure M) (h : Assembly.Standing T)
    (k : ℕ) (f : M8Hull.hullSeq T k ↪[LRV] N) :
    ∃ g : M8Hull.hullSeq T (k + 1) ↪[LRV] N, ExtendsTo (M8Hull.hullSeq_le_succ T k) f g := by
  have hle : M8Hull.hullSeq T (k + 1) ≤ M8Hull.hullSeq T k := by
    rw [hullSeq_eq_of_standing h (k + 1), hullSeq_eq_of_standing h k]
  refine ⟨f.comp (Substructure.inclusion hle), ?_⟩
  intro y hy
  exact congrArg f (Subtype.ext rfl)

/-! ## 6. Demand table and stress tests -/

/-- The size content of the hull half (from `QE/Prop39Decomp.lean`), restated: it forces
`#K(M)ˣ ≤ #N`, never `#M ≤ #N`. -/
theorem hullExtension_forces_units_size_restated (h : G3.HullExtension M N)
    (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    Cardinal.mk {x : M // iUnits x} ≤ Cardinal.mk N :=
  G3.hullExtension_forces_units_size h S f

/-- **Stress test (cardinality): the hull half is not a theorem of ACVF.** -/
theorem not_hullExtension_of_cardinality (S : LRV.Substructure M) (f : S ↪[LRV] N)
    (h : Cardinal.mk N < Cardinal.mk {x : M // iUnits x}) : ¬ G3.HullExtension M N :=
  fun hh => absurd (hullExtension_forces_units_size_restated hh S f) (not_le.mpr h)

/-- **The hull half costs nothing at `VF`-generated domains**. -/
theorem hullExtensionAt_of_vfGenCase (h : Assembly.VFGenCaseP (M := M) (N := N))
    (S : LRV.Substructure M) (hgen : Assembly.IsVFGen S) : HullExtensionAt (N := N) S := by
  intro f
  obtain ⟨g, hg⟩ := h S f hgen
  refine ⟨g.domRestrict (M8Hull.standingHull S), ?_⟩
  intro y hy
  exact hg ⟨y, hy⟩

/-- The total extension property implies the hull form, so the hull half is weaker than
Proposition 3.9's conclusion. -/
theorem hullExtension_of_extensHere (h : G3.ExtendsHere M N) : G3.HullExtension M N :=
  G3.hullExtension_of_extendsHere h


/-! ## 7. The converse: every stage is reached from the two steps

So the factorization of §4 is exact, and the frozen `Assembly.PrepStepP` is *equivalent* to the two
single-step statements.  This is the ledger form of Lemma 3.3. -/

/-- The first root stage of the hull of a hull stage is the next stage of the hull. -/
theorem hullSeq_succ_of_KEqTop (S : LRV.Substructure M) (k : ℕ) :
    M8Hull.hullSeq (M8Hull.hullSeq S k) 1 = M8Hull.hullSeq S (k + 1) := by
  show M8Hull.rootClosure (M8Hull.hullSeq (M8Hull.hullSeq S k) 0)
      = M8Hull.rootClosure (M8Hull.hullSeq S k)
  rw [show M8Hull.hullSeq (M8Hull.hullSeq S k) 0
      = M8Hull.baseClosure (M8Hull.hullSeq S k) from rfl,
    baseClosure_eq_of_KEqTop (M8Hull.KEqTop_hullSeq S k)]

/-- The stagewise hypothesis gives the root step: apply it at the stage as a *new* base. -/
theorem hullRootStep_of_stagewise (h : Stagewise M N) : HullRootStep M N := by
  intro S k f
  obtain ⟨g, hg⟩ := h (M8Hull.hullSeq S k) f 1
  refine ⟨g.comp (Substructure.inclusion (le_of_eq (hullSeq_succ_of_KEqTop S k).symm)), ?_⟩
  intro y hy
  exact hg y hy

/-- **The stagewise form is exactly the two steps.** -/
theorem stagewise_iff_base_root : Stagewise M N ↔ HullBaseStep M N ∧ HullRootStep M N :=
  ⟨fun h => ⟨hullBaseStep_of_stagewise h, hullRootStep_of_stagewise h⟩,
   fun h => stagewise_of_hullExtension (hullExtension_of_base_root h.1 h.2)⟩

/-- **Lemma 3.3 (hull form) is exactly its two steps.** -/
theorem hullExtension_iff_base_root :
    G3.HullExtension M N ↔ HullBaseStep M N ∧ HullRootStep M N :=
  ⟨fun h => stagewise_iff_base_root.mp (stagewise_of_hullExtension h),
   fun h => hullExtension_of_base_root h.1 h.2⟩

/-- **The frozen `Assembly.PrepStepP` (Lemma 3.3) is exactly its two steps**: the unit adjoinment
and the `ω`-iteration of root adjoinments. -/
theorem prepStepP_iff_base_root :
    Assembly.PrepStepP (M := M) (N := N) ↔ HullBaseStep M N ∧ HullRootStep M N :=
  ⟨fun h => stagewise_iff_base_root.mp (stagewise_of_hullExtension
      (G3.prepStepP_iff_hullExtension.mp h)),
   fun h => prepStepP_of_base_root h.1 h.2⟩

/-- The stagewise form and the hull form are the same statement. -/
theorem stagewise_iff_hullExtension : Stagewise M N ↔ G3.HullExtension M N :=
  ⟨fun h => hullExtension_of_base_root (hullBaseStep_of_stagewise h)
      (hullRootStep_of_stagewise h),
   stagewise_of_hullExtension⟩

/-! ## 8. The named residual, and the size obstruction of the *base* step -/

/-- **The residual of Lemma 3.3, single-step form**: extend a monomorphism along one root
adjoinment, at a `KEqTop` domain — which is exactly what every hull stage is.  This is the
obligation that the case lemmas 3.4–3.8 do *not* supply, because their domains are `Standing`
(§5). -/
def RootStepResidual (M N : Type) [LRV.Structure M] [LRV.Structure N]
    [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF] : Prop :=
  ∀ (T : LRV.Substructure M) (f : T ↪[LRV] N), Assembly.KEqTop T →
    ∃ g : M8Hull.rootClosure T ↪[LRV] N, ExtendsTo (M8Hull.le_rootClosure T) f g

/-- `RootStepResidual` gives the root step of Lemma 3.3. -/
theorem hullRootStep_of_rootStepResidual (h : RootStepResidual M N) : HullRootStep M N :=
  fun S k f => h (M8Hull.hullSeq S k) f (M8Hull.KEqTop_hullSeq S k)

/-- **The base step alone already forces `#K(M)ˣ ≤ #N`**: every unit of `K(M)` is adjoined at stage
`0`, hence must be injected into `N`. -/
theorem hullBaseStep_forces_units_size (hb : HullBaseStep M N) (S : LRV.Substructure M)
    (f : S ↪[LRV] N) :
    Cardinal.mk {x : M // iUnits x} ≤ Cardinal.mk N := by
  obtain ⟨g, -⟩ := hb S f
  refine Cardinal.mk_le_of_injective (f := fun x : {x : M // iUnits x} =>
    g ⟨x.1, M8Hull.units_mem_baseClosure S x.2⟩) ?_
  intro x y hxy
  have h := g.injective hxy
  exact Subtype.ext (congrArg (fun z : ↥(M8Hull.hullSeq S 0) => (z : M)) h)

/-- **Stress test (cardinality, base step only)**: the unit adjoinment is not a theorem of ACVF
either — it needs `#K(M)ˣ ≤ #N`. -/
theorem not_hullBaseStep_of_cardinality (S : LRV.Substructure M) (f : S ↪[LRV] N)
    (h : Cardinal.mk N < Cardinal.mk {x : M // iUnits x}) : ¬ HullBaseStep M N :=
  fun hb => absurd (hullBaseStep_forces_units_size hb S f) (not_le.mpr h)


/-! ## 9. Where the two steps really have content

Machine-checked confinement: the base step is trivial at every `KEqTop` domain, and the root step is
trivial at every `Standing` domain.  So

* `HullBaseStep` has content exactly at the domains with `¬ KEqTop S` (the residue field has to be
  adjoined), and
* `HullRootStep` — whose domains are the hull stages, all `KEqTop` — has content exactly at the
  `KEqTop` domains that are *not* `Standing`.

The case lemmas 3.4–3.8 have `Standing` domains (`Assembly.OneStepVFP`), so they live in the
complement of the region where the hull half is open. -/

/-- The base step is trivial at every `KEqTop` domain. -/
theorem hullBaseStep_KEqTop_trivial (T : LRV.Substructure M) (h : Assembly.KEqTop T)
    (f : T ↪[LRV] N) :
    ∃ g : M8Hull.hullSeq T 0 ↪[LRV] N, ExtendsTo (M8Hull.le_baseClosure T) f g := by
  refine ⟨f.comp (Substructure.inclusion (le_of_eq (baseClosure_eq_of_KEqTop h))), ?_⟩
  intro y hy
  exact congrArg f (Subtype.ext rfl)

/-- The root step is trivial at every `Standing` domain (in the `RootStepResidual` shape). -/
theorem rootStepResidual_standing_trivial (T : LRV.Substructure M) (h : Assembly.Standing T)
    (f : T ↪[LRV] N) :
    ∃ g : M8Hull.rootClosure T ↪[LRV] N, ExtendsTo (M8Hull.le_rootClosure T) f g :=
  ⟨f.comp (Substructure.inclusion (rootClosure_le_of_standing h)), fun y hy =>
    congrArg f (Subtype.ext rfl)⟩

/-- **`HullBaseStep` has content exactly at `¬ KEqTop` domains.** -/
theorem hullBaseStep_iff_nonKEqTop :
    HullBaseStep M N ↔ ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N),
      ¬ Assembly.KEqTop S →
      ∃ g : M8Hull.hullSeq S 0 ↪[LRV] N, ExtendsTo (M8Hull.le_baseClosure S) f g := by
  constructor
  · intro h S f _
    exact h S f
  · intro h S f
    by_cases hK : Assembly.KEqTop S
    · have hle : M8Hull.hullSeq S 0 ≤ S := le_of_eq (baseClosure_eq_of_KEqTop hK)
      exact ⟨f.comp (Substructure.inclusion hle), fun y hy => congrArg f (Subtype.ext rfl)⟩
    · exact h S f hK

/-- **`RootStepResidual` has content exactly at `KEqTop` domains that are not `Standing`.** -/
theorem rootStepResidual_iff :
    RootStepResidual M N ↔ ∀ (T : LRV.Substructure M) (f : T ↪[LRV] N),
      Assembly.KEqTop T → ¬ Assembly.Standing T →
      ∃ g : M8Hull.rootClosure T ↪[LRV] N, ExtendsTo (M8Hull.le_rootClosure T) f g := by
  constructor
  · intro h T f hK _
    exact h T f hK
  · intro h T f hK
    by_cases hS : Assembly.Standing T
    · exact rootStepResidual_standing_trivial T hS f
    · exact h T f hK hS


/-- **The ledger line for Proposition 3.9**: at a fixed pair, the extension property is the unit
adjoinment ∧ the root adjoinments ∧ the one-step case lemmas.  (Composition of
`G3.extendsHere_iff_hullExtension_and_oneStep` with `hullExtension_iff_base_root`.) -/
theorem extendsHere_iff_steps_and_oneStep :
    G3.ExtendsHere M N ↔
      HullBaseStep M N ∧ HullRootStep M N ∧ Assembly.OneStepVFP (M := M) (N := N) := by
  rw [G3.extendsHere_iff_hullExtension_and_oneStep, hullExtension_iff_base_root]
  tauto

end D7
end Milestone0
end SpecialTransformations

#print axioms SpecialTransformations.Milestone0.D7.hullExtensionAt_of_standing
#print axioms SpecialTransformations.Milestone0.D7.stagewise_of_hullExtension
#print axioms SpecialTransformations.Milestone0.D7.chainOf_agree
#print axioms SpecialTransformations.Milestone0.D7.unionFun_spec
#print axioms SpecialTransformations.Milestone0.D7.unionEmb
#print axioms SpecialTransformations.Milestone0.D7.hullExtension_of_base_root
#print axioms SpecialTransformations.Milestone0.D7.prepStepP_of_base_root
#print axioms SpecialTransformations.Milestone0.D7.hullSeq_eq_of_standing
#print axioms SpecialTransformations.Milestone0.D7.hullRootStep_standing_trivial
#print axioms SpecialTransformations.Milestone0.D7.not_hullExtension_of_cardinality
#print axioms SpecialTransformations.Milestone0.D7.hullExtensionAt_of_vfGenCase
#print axioms SpecialTransformations.Milestone0.D7.prepStepP_iff_base_root
#print axioms SpecialTransformations.Milestone0.D7.stagewise_iff_hullExtension
#print axioms SpecialTransformations.Milestone0.D7.hullRootStep_of_rootStepResidual
#print axioms SpecialTransformations.Milestone0.D7.hullBaseStep_forces_units_size
#print axioms SpecialTransformations.Milestone0.D7.hullBaseStep_KEqTop_trivial
#print axioms SpecialTransformations.Milestone0.D7.rootStepResidual_standing_trivial
#print axioms SpecialTransformations.Milestone0.D7.hullBaseStep_iff_nonKEqTop
#print axioms SpecialTransformations.Milestone0.D7.rootStepResidual_iff
#print axioms SpecialTransformations.Milestone0.D7.extendsHere_iff_steps_and_oneStep
