/-
# The Hahn-field obstruction to `OneStepVFP`, and the repaired quantifier shape

Direction d5 of swarm `smw2ioy2w` (listed in the task as d8).

## Result

`MILESTONES.md` and `QE/PaperRoute.lean` repair Lemma 3.3 by a size bound `SizeHyp M N` and leave
the one-step obligation (Lemmas 3.4–3.8) universally quantified over all pairs of models, with the
caveat that "`OneStepVFP` appears to fail also at equal cardinality — Hahn fields
`M = ℂ((t^{ℚ²}))`, `N = ℂ((t^ℚ))` — because divisibility at `rv(m)`, `n = 2`, creates
`v(m)/2 ∈ Γ(T)`, i.e. the value group of `N` must have room".  This file machine-checks that
obstruction **in the abstract form** (the direction's fallback: no Hahn series needed) and draws the
consequence:

* `not_oneStepSizeFree` : the frozen `M7Paper.OneStepSizeFree` is **false** at any pair carrying the
  configuration `RoomObstruction M N` whose target satisfies `ArchimedeanRV N`;
* `not_oneStepSizeBounded` : so is the size-bounded repair `∀ M N, SizeHyp M N → OneStepSizeVFP`.
  **The size half of `PaperHyp` does not repair the one-step; only the saturation half can**;
* `paper_theorem_2_3_sat_of_paper` : the repair `OneStepPaper` (same obligation, restricted to the
  paper's pairs `PaperHyp M N = SaturatedFS N ∧ #M ≤ #N`) still yields Theorem 2.3
  (`HasQE Axioms.ACVF`) from `ShoenfieldTestSat` and `PrepStepSize`;
* `oneStepSizeBounded_of_free`, `oneStepPaper_of_sizeBounded`, `oneStepPaper_of_free` : the three
  shapes are nested, so `OneStepPaper` is the weakest of them.

## The mechanism, in three layers

**§1 transport** (`Transport.lean`).  An `L_RV`-embedding commutes with `iRVMul`, `iRv`, `iRVOne`,
`iRVZero`, hence with `Assembly.rvPow`, and preserves *and reflects* `iLe` and the sort predicates.
So the relation `∀ n, iLe (rvPow a n) b` — "the value of `a` is infinitesimal with respect to the
value of `b`" — is an `L_RV`-invariant.  That is the whole mechanism: the one-step embedding can
neither destroy an infinitesimal nor manufacture a commensurability.

**§2–§3 the arithmetic core** (`no_archimedean_infinitesimal`).  In *any* model of `ACVF`: if
`iRV a`, `iRV b`, `a ≠ 0`, `¬ iLe a iRVOne` (i.e. `v a > 0`) and `∀ n, iLe (rvPow a n) b`, then there
is no `n` with `iLe b (rvPow a n)`.  Proof: `b ≤ aⁿ` and `aⁿ⁺¹ ≤ b` give `aⁿ⁺¹ ≤ aⁿ`; cancelling
`aⁿ ≠ 0` (`RVCalc.le_mul_iff`) gives `a ≤ 1`, contradiction.  `ArchimedeanRV M` is the standard
Archimedean property of `Γ(M)` (`¬ iLe a iRVOne` is `v a > 0`, since `iLe` is the value order and
`Kˣ` is the class of `1`); `not_archimedeanRV_of_infinitesimalRoom` shows that an infinitesimal pair
defeats it, so the hypothesis is the Archimedean property and not something stronger.

**§4 the refutation** (`not_oneStepAt_of_infinitesimal`, `not_oneStepVFP_of_infinitesimal`,
`not_archimedeanRV_of_oneStep`).  At a pair `(M, N)` with `ArchimedeanRV N` and the configuration —
`S ⊆ M`, `f : S ↪[LRV] N`, `s ∈ S` of strictly positive value, `m : VF(M)` with `m ∉ S`,
`v(rv m) > 0`, and `∀ n, (rv m)ⁿ ≤ s` — there is **no** one-step extension at `m`.  The `Standing S`
hypothesis of `OneStepVFP` is not used by the refutation (it is kept only in the wrapper, where
`OneStepVFP` supplies it).

## Stress tests (report standard)

* (a) *No hypothesis is the conclusion.*  `ArchimedeanRV N` is a property of `N` alone; the rest is
  a configuration in `M`; the conclusion is about *all* one-step extensions at `m`.
* (b) *`m ∉ S` is not removable*: `oneStepAt_of_mem` shows that for `m ∈ S` the one-step conclusion
  holds trivially (`T = S`, `g = f`).
* (c) *No impossible cardinality is forced*: `roomObstruction_forces_units_size` derives
  `#Kˣ(M) ≤ #N` from the configuration, exactly the bound the paper's `‖M‖⁺`-saturation supplies and
  that `M7Paper.prepStepP_forces_units_size` extracts from `PrepStepP`.  No cardinality hypothesis
  is used in §4 and none is contradicted by it.
* (d) *The repaired shape is size-consistent*: `paperHyp_supplies_standing_size`.
* (e) *Inhabitation of the configuration in the paper's setting*: `NOTES.md` §4 gives the argument
  for `M = ℂ((t^{ℚ²}))`, `N = ℂ((t^ℚ))`, `S = {x : v x ∈ ℚ·(1,0)}` and checks every hypothesis.  It
  is a **citation**, not machine-checked: the tree has no concrete model of `Axioms.ACVF`, and
  building one (Hahn series plus the tagged encoding) is out of scope here.

## Not proved here

`OneStepPaper` itself (the paper's Lemmas 3.4–3.8 at the paper's pairs — the swarm's live frontier);
`SaturatedFS N → ¬ ArchimedeanRV N` (the statement that saturation makes the repaired shape immune;
true by compactness on the type `{x > n·a}`, see `NOTES.md` §5); and the Hahn models themselves.

## Verification

`lean` exit 0, `grep -c error` = 0, no `sorry`/`admit`/`native_decide`/new `axiom`; `#print axioms`
of every head theorem is a subset of `{propext, Classical.choice, Quot.sound}` (output at the end of
the file).
-/
import Enc
import RVCalc
import Assembly_frozen
import PaperRoute
import Transport

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0

namespace SpecialTransformations.Milestone0.Hahn

/-! ## 2. The Archimedean property of the `RV` order

`iLe` is the value order (`RVCalc.units_iff_le_one`: `Kˣ` is the class of `1`), so
`¬ iLe a iRVOne` says "the value of `a` is strictly positive" and
`∀ n, iLe (rvPow a n) b` says "`v a` is infinitesimal with respect to `v b`".  `ArchimedeanRV M`
is the (standard) statement that `Γ(M)` has no infinitesimals: any two elements of strictly
positive value are commensurable.  `Γ(ℂ((t^ℚ))) = ℚ` has it, `Γ(ℂ((t^{ℚ²}))) = ℚ²` (lex) does not;
it is a property of the model `M` alone, and is *not* a consequence of `Axioms.ACVF`. -/

def ArchimedeanRV (M : Type) [LRV.Structure M] : Prop :=
  ∀ a b : M, iRV a → iRV b → b ≠ iRVZero → ¬ iLe a iRVOne → ¬ iLe b iRVOne →
    ∃ n : ℕ, iLe b (Assembly.rvPow a n)

/-- The negation of `ArchimedeanRV`, unpacked: a pair of `RV`-elements of strictly positive value,
one of which is not commensurable with the other.  This is only `¬ ArchimedeanRV` written out —
it is here so that the definition of `ArchimedeanRV` can be checked against the notion it is
supposed to name (see `not_archimedeanRV_of_room`). -/
def NotArchimedeanRV (M : Type) [LRV.Structure M] : Prop :=
  ∃ a b : M, iRV a ∧ iRV b ∧ b ≠ iRVZero ∧ ¬ iLe a iRVOne ∧ ¬ iLe b iRVOne ∧
    ∀ n : ℕ, ¬ iLe b (Assembly.rvPow a n)

theorem notArchimedeanRV_iff (M : Type) [LRV.Structure M] :
    ¬ ArchimedeanRV M ↔ NotArchimedeanRV M := by
  constructor
  · intro h
    simp only [ArchimedeanRV, not_forall] at h
    obtain ⟨a, b, h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨a, b, h1, h2, h3, h4, h5, fun n => not_exists.mp h6 n⟩
  · rintro ⟨a, b, h1, h2, h3, h4, h5, h6⟩ hArch
    obtain ⟨n, hn⟩ := hArch a b h1 h2 h3 h4 h5
    exact h6 n hn

/-! ## 3. The arithmetic core

Nothing here mentions substructures or embeddings: it is the statement that a positive value with
an infinitesimal below it is not Archimedean. -/

section Core

variable {M : Type} [LRV.Structure M]

theorem rvPow_mem (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iRV a) :
    ∀ n : ℕ, iRV (Assembly.rvPow a n)
  | 0 => by rw [Assembly.rvPow.eq_1]; exact Transfer.rv_one_mem hM
  | n + 1 => by
      rw [Assembly.rvPow.eq_2]
      exact Transfer.rv_mul_mem hM (rvPow_mem hM ha n) ha

theorem rvPow_ne_zero (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iRV a) (ha0 : a ≠ iRVZero) :
    ∀ n : ℕ, Assembly.rvPow a n ≠ iRVZero
  | 0 => by rw [Assembly.rvPow.eq_1]; exact RVCalc.rv_one_ne_zero hM
  | n + 1 => by
      rw [Assembly.rvPow.eq_2]
      intro h
      rcases (Transfer.rv_mul_eq_zero_of_model hM (rvPow_mem hM ha n) ha).mp h with h' | h'
      · exact rvPow_ne_zero hM ha ha0 n h'
      · exact ha0 h'

/-- **The core of the obstruction.**  A value `a` of strictly positive value with an infinitesimal
`b` above its powers (`∀ n, aⁿ ≤ b`, i.e. `n·v a ≤ v b` for all `n`) is not Archimedean below `b`.
Any model in which `b` is commensurable with `a` — in particular any model whose value group is
Archimedean, such as `ℂ((t^ℚ))` — therefore cannot realise the pair `(a, b)`. -/
theorem no_archimedean_infinitesimal (hM : M ⊨ Axioms.ACVF) {a b : M} (ha : iRV a) (hb : iRV b)
    (ha0 : a ≠ iRVZero) (hagt : ¬ iLe a iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow a n) b)
    (harch : ∃ n : ℕ, iLe b (Assembly.rvPow a n)) : False := by
  obtain ⟨n, hn⟩ := harch
  have hmem : iRV (Assembly.rvPow a n) := rvPow_mem hM ha n
  have hmem' : iRV (Assembly.rvPow a (n + 1)) := rvPow_mem hM ha (n + 1)
  have h1 : iLe (Assembly.rvPow a (n + 1)) b := hinf (n + 1)
  have h2 : iLe (Assembly.rvPow a (n + 1)) (Assembly.rvPow a n) :=
    RVCalc.le_trans_rv hM hmem' hb hmem h1 hn
  rw [Assembly.rvPow.eq_2] at h2
  have h3 : iLe (iRVMul (Assembly.rvPow a n) a) (iRVMul (Assembly.rvPow a n) iRVOne) := by
    rw [Transfer.rv_mul_one_any_right hM hmem]; exact h2
  have h4 : iLe (iRVMul a (Assembly.rvPow a n)) (iRVMul iRVOne (Assembly.rvPow a n)) := by
    rw [Transfer.rv_mul_comm_of_model hM ha hmem,
      Transfer.rv_mul_comm_of_model hM (Transfer.rv_one_mem hM) hmem]
    exact h3
  exact hagt ((RVCalc.le_mul_iff hM ha (Transfer.rv_one_mem hM) hmem
    (rvPow_ne_zero hM ha ha0 n)).mpr h4)

/-- **`ArchimedeanRV` is the Archimedean property, not something stronger**: if a model has an
element `a` of strictly positive value with an infinitesimal `b` above all its powers, then
`ArchimedeanRV` fails there.  Together with `notArchimedeanRV_iff` this pins the definition: the
hypothesis of §4 is exactly "`Γ` has no infinitesimal pair", which is what `Γ(ℚ) = ℚ` satisfies and
`Γ(ℚ²)` (lex) does not. -/
theorem not_archimedeanRV_of_infinitesimalRoom (hM : M ⊨ Axioms.ACVF) {a b : M}
    (ha : iRV a) (hb : iRV b) (hb0 : b ≠ iRVZero) (ha0 : a ≠ iRVZero)
    (hagt : ¬ iLe a iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow a n) b) : ¬ ArchimedeanRV M := by
  have ha1 : Assembly.rvPow a 1 = a := by
    rw [Assembly.rvPow.eq_2, Assembly.rvPow.eq_1]
    exact Transfer.rv_mul_one_any hM ha
  have hbgt : ¬ iLe b iRVOne := by
    intro h
    have h1 : iLe (Assembly.rvPow a 1) b := hinf 1
    rw [ha1] at h1
    exact hagt (RVCalc.le_trans_rv hM ha hb (Transfer.rv_one_mem hM) h1 h)
  intro hArch
  obtain ⟨n, hn⟩ := hArch a b ha hb hb0 hagt hbgt
  exact no_archimedean_infinitesimal hM ha hb ha0 hagt hinf ⟨n, hn⟩

end Core

/-! ## 4. The refutation of the one-step at a pair with an infinitesimal configuration -/

section Refute

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]

/-- The one-step obligation at a fixed substructure `S`, embedding `f` and new element `m`:
`Assembly.OneStepVFP` is `∀ S f, Standing S → ∀ m, iVF m → OneStepAt S f m`. -/
def OneStepAt (S : LRV.Substructure M) (f : S ↪[LRV] N) (m : M) : Prop :=
  ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
    (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T

/-- No one-step extension at `m` exists, for *any* substructure `S` (the `Standing` hypothesis of
`Assembly.OneStepVFP` is not even needed for the refutation; it is kept in the wrapper below only
because `OneStepVFP` supplies it). -/
theorem not_oneStepAt_of_infinitesimal [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (hArch : ArchimedeanRV N)
    {S : LRV.Substructure M} {f : S ↪[LRV] N}
    {s : M} (hsS : s ∈ S) (hsRV : iRV s) (hsne : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    {m : M} (hmVF : iVF m) (hmS : m ∉ S)
    (hmgt : ¬ iLe (iRv m) iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow (iRv m) n) s) :
    ¬ OneStepAt S f m := by
  rintro ⟨T, g, hST, _hagree, hmT, _hStandT⟩
  -- `0` is a constant, so it lies in every substructure, hence `m ≠ 0` and `rv m ≠ 0`
  have hzeroS : (Transfer.iVFZero (M := M)) ∈ S := by
    have h := S.fun_mem (Fn.vfZero) (fun i : Fin 0 => i.elim0) (fun i => i.elim0)
    simpa [Transfer.iVFZero] using h
  have hm0 : m ≠ Transfer.iVFZero (M := M) := fun h => hmS (h ▸ hzeroS)
  have hmrv : iRv m ≠ iRVZero :=
    fun h => hm0 (RVCalc.vf_eq_zero_of_rv_eq_zero hM hmVF h)
  have hsT : s ∈ T := hST hsS
  -- (a) the infinitesimal relation holds inside `T`
  have hT_le : ∀ n : ℕ, iLe (Assembly.rvPow (iRv (⟨m, hmT⟩ : T)) n) (⟨s, hsT⟩ : T) := by
    intro n
    refine (coe_le_iff T _ _).mp ?_
    have h5 : iLe ((Assembly.rvPow (iRv (⟨m, hmT⟩ : T)) n : T) : M) ((⟨s, hsT⟩ : T) : M) := by
      rw [coe_rvPow T (iRv (⟨m, hmT⟩ : T)) n, coe_rv T (⟨m, hmT⟩ : T)]
      exact hinf n
    exact h5
  -- (b) push the relation forward along the one-step embedding `g`
  have hN_le : ∀ n : ℕ, iLe (Assembly.rvPow (iRv (g ⟨m, hmT⟩)) n) (g ⟨s, hsT⟩) := by
    intro n
    have h := (map_le_iff g (Assembly.rvPow (iRv (⟨m, hmT⟩ : T)) n) (⟨s, hsT⟩ : T)).mpr
      (hT_le n)
    rwa [map_rvPow g (iRv (⟨m, hmT⟩ : T)) n, map_rv g (⟨m, hmT⟩ : T)] at h
  -- the two hypotheses of the Archimedean property, transported to `N`
  have hmVFT : iVF ((⟨m, hmT⟩ : T)) := (coe_vfMem_iff T (⟨m, hmT⟩ : T)).mp hmVF
  have hmVF' : iVF (g (⟨m, hmT⟩ : T)) := (map_vfMem_iff g (⟨m, hmT⟩ : T)).mpr hmVFT
  have haRV : iRV (iRv (g ⟨m, hmT⟩)) := Transfer.rv_mem hN hmVF'
  have hsRVT : iRV ((⟨s, hsT⟩ : T)) := (coe_rvMem_iff T (⟨s, hsT⟩ : T)).mp hsRV
  have hsRV' : iRV (g (⟨s, hsT⟩ : T)) := (map_rvMem_iff g (⟨s, hsT⟩ : T)).mpr hsRVT
  have ha0' : iRv (g ⟨m, hmT⟩) ≠ iRVZero := by
    intro h
    have h1 : g (iRv (⟨m, hmT⟩ : T)) = g (iRVZero : T) := by
      rw [map_rv g (⟨m, hmT⟩ : T), map_rvZero g]; exact h
    have h2 : iRv (⟨m, hmT⟩ : T) = (iRVZero : T) := Embedding.injective g h1
    have h3 : iRv m = iRVZero := by
      have h4 := congrArg (Subtype.val) h2
      rwa [coe_rv T (⟨m, hmT⟩ : T), coe_rvZero T] at h4
    exact hmrv h3
  have hsne' : g ⟨s, hsT⟩ ≠ iRVZero := by
    intro h
    have h1 : g (⟨s, hsT⟩ : T) = g (iRVZero : T) := by rw [map_rvZero g]; exact h
    have h2 : (⟨s, hsT⟩ : T) = iRVZero := Embedding.injective g h1
    have h3 : s = iRVZero := by
      have h4 := congrArg (Subtype.val) h2
      rwa [coe_rvZero T] at h4
    exact hsne h3
  have hmgt' : ¬ iLe (iRv (g ⟨m, hmT⟩)) iRVOne := by
    intro h
    have h1 : iLe (g (iRv (⟨m, hmT⟩ : T))) (g (iRVOne : T)) := by
      rw [map_rv g (⟨m, hmT⟩ : T), map_rvOne g]; exact h
    have h2 : iLe (iRv (⟨m, hmT⟩ : T)) (iRVOne : T) := (map_le_iff g _ _).mp h1
    have h5 := (coe_le_iff T (iRv (⟨m, hmT⟩ : T)) (iRVOne : T)).mpr h2
    rw [coe_rv T (⟨m, hmT⟩ : T), coe_rvOne T] at h5
    exact hmgt h5
  have hsgt' : ¬ iLe (g ⟨s, hsT⟩) iRVOne := by
    intro h
    have h1 : iLe (g ⟨s, hsT⟩) (g (iRVOne : T)) := by rw [map_rvOne g]; exact h
    have h2 : iLe (⟨s, hsT⟩ : T) (iRVOne : T) := (map_le_iff g _ _).mp h1
    have h5 := (coe_le_iff T (⟨s, hsT⟩ : T) (iRVOne : T)).mpr h2
    rw [coe_rvOne T] at h5
    exact hsgt h5
  -- the Archimedean property of `N` contradicts the transported infinitesimal
  obtain ⟨n, hn⟩ := hArch (iRv (g ⟨m, hmT⟩)) (g ⟨s, hsT⟩) haRV hsRV' hsne' hmgt' hsgt'
  exact no_archimedean_infinitesimal hN haRV hsRV' ha0' hmgt' hN_le ⟨n, hn⟩

/-- **The one-step fails at a pair with an infinitesimal configuration.** -/
theorem not_oneStepVFP_of_infinitesimal [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (hArch : ArchimedeanRV N)
    (S : LRV.Substructure M) (f : S ↪[LRV] N) (hStand : Assembly.Standing S)
    (s : M) (hsS : s ∈ S) (hsRV : iRV s) (hsne : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    (m : M) (hmVF : iVF m) (hmS : m ∉ S)
    (hmgt : ¬ iLe (iRv m) iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow (iRv m) n) s) :
    ¬ Assembly.OneStepVFP (M := M) (N := N) :=
  fun hOne => not_oneStepAt_of_infinitesimal hArch hsS hsRV hsne hsgt hmVF hmS hmgt hinf
    (hOne S f hStand m hmVF)

/-- **Contrapositive form — the one-step forces `Γ(N)` to be non-Archimedean.**  Given a
configuration in which `M` has an infinitesimal value above a positive value of `S`, a one-step
extension into `N` forces `Γ(N)` to contain an infinitesimal relative to the image of that value,
i.e. `Γ(N)` cannot be Archimedean.  This is the form in which the obstruction bears on the paper's
route: `‖M‖⁺`-saturation of `N` makes `Γ(N)` *non*-Archimedean (it realises
`{x > n·a : n ∈ ℕ}`), which is exactly what a size bound cannot supply. -/
theorem not_archimedeanRV_of_oneStep [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (hOne : Assembly.OneStepVFP (M := M) (N := N))
    (S : LRV.Substructure M) (f : S ↪[LRV] N) (hStand : Assembly.Standing S)
    (s : M) (hsS : s ∈ S) (hsRV : iRV s) (hsne : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    (m : M) (hmVF : iVF m) (hmS : m ∉ S)
    (hmgt : ¬ iLe (iRv m) iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow (iRv m) n) s) :
    ¬ ArchimedeanRV N :=
  fun hArch => not_oneStepVFP_of_infinitesimal hArch S f hStand s hsS hsRV hsne hsgt m hmVF hmS
    hmgt hinf hOne

/-- The infinitesimal configuration, packaged: the hypotheses of `not_oneStepVFP_of_infinitesimal`
other than `ArchimedeanRV N`, existentially closed up.  (Stress test: this is what the paper's
Hahn-field pair supplies, see the module docstring.) -/
def RoomObstruction (M N : Type) [LRV.Structure M] [LRV.Structure N]
    [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF] : Prop :=
  ∃ (S : LRV.Substructure M) (f : S ↪[LRV] N) (s m : M),
    Assembly.Standing S ∧ s ∈ S ∧ iRV s ∧ s ≠ iRVZero ∧ ¬ iLe s iRVOne ∧
      iVF m ∧ m ∉ S ∧ ¬ iLe (iRv m) iRVOne ∧ ∀ n : ℕ, iLe (Assembly.rvPow (iRv m) n) s

theorem not_oneStepVFP_of_roomObstruction [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (h : RoomObstruction M N) (hArch : ArchimedeanRV N) :
    ¬ Assembly.OneStepVFP (M := M) (N := N) := by
  obtain ⟨S, f, s, m, hStand, hsS, hsRV, hsne, hsgt, hmVF, hmS, hmgt, hinf⟩ := h
  exact not_oneStepVFP_of_infinitesimal hArch S f hStand s hsS hsRV hsne hsgt m hmVF hmS hmgt hinf

/-- **The one-step forces room in the target's value group** — the `Γ`-divisibility form of the
obstruction, i.e. the form in which the failure was first noticed ("divisibility at `rv(m)`, `n = 2`,
creates `v(m)/2 ∈ Γ(T)`, so the value group of `N` must have room").  If a one-step extension at `m`
exists and `S` is `Standing`, then for every `n ≥ 1` the target contains an `n`-th root of the value
of the image of `m`, modulo a unit: `uⁿ = rv(g m) · c` with `c ∈ Kˣ(N)`.  Compare
`not_oneStepVFP_of_infinitesimal`: the room that `u` needs is exactly what `ArchimedeanRV` denies. -/
theorem oneStepAt_gives_root_mod_units [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    {S : LRV.Substructure M} {f : S ↪[LRV] N} {m : M}
    (h : OneStepAt S f m) (hStand : Assembly.Standing S)
    (hmVF : iVF m) (hm0 : m ≠ Transfer.iVFZero (M := M)) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T) (hmT : m ∈ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧
        ∃ u c : N, iRV u ∧ u ≠ iRVZero ∧ iUnits c ∧
          Assembly.rvPow u n = iRVMul (iRv (g ⟨m, hmT⟩)) c := by
  obtain ⟨T, g, hST, hagree, hmT, hStandT⟩ := h
  have hmVF_T : iVF ((⟨m, hmT⟩ : T)) := (coe_vfMem_iff T (⟨m, hmT⟩ : T)).mp hmVF
  have hmRV_M : iRV (iRv m) := Transfer.rv_mem hM hmVF
  have hmRV_T : iRV (iRv (⟨m, hmT⟩ : T)) := by
    refine (coe_rvMem_iff T (iRv (⟨m, hmT⟩ : T))).mp ?_
    rwa [coe_rv T (⟨m, hmT⟩ : T)]
  have hm0M : iRv m ≠ iRVZero := fun hh => hm0 (RVCalc.vf_eq_zero_of_rv_eq_zero hM hmVF hh)
  have hm0T : iRv (⟨m, hmT⟩ : T) ≠ iRVZero := by
    intro hh
    have h2 : iRv m = iRVZero := by
      have h3 := congrArg (Subtype.val) hh
      rwa [coe_rv T (⟨m, hmT⟩ : T), coe_rvZero T] at h3
    exact hm0M h2
  -- `Standing S` gives divisibility in `T` (it is a hypothesis on `T`, and `S ≤ T`)
  obtain ⟨u, c, huT, huRV, hu0, hcT, hcUnits, hpow⟩ :=
    hStandT.2 ((iRv (⟨m, hmT⟩ : T) : T) : M) (iRv (⟨m, hmT⟩ : T)).2
      (by rwa [coe_rv T (⟨m, hmT⟩ : T)]) (by rwa [coe_rv T (⟨m, hmT⟩ : T)]) n hn
  refine ⟨T, g, hST, hmT, hagree, g ⟨u, huT⟩, g ⟨c, hcT⟩,
    (map_rvMem_iff g (⟨u, huT⟩ : T)).mpr ((coe_rvMem_iff T (⟨u, huT⟩ : T)).mp huRV), ?_, ?_, ?_⟩
  · intro hh
    have h1 : g (⟨u, huT⟩ : T) = g (iRVZero : T) := by rw [map_rvZero g]; exact hh
    have h2 : (⟨u, huT⟩ : T) = iRVZero := Embedding.injective g h1
    have h3 := congrArg (Subtype.val) h2
    rw [coe_rvZero T] at h3
    exact hu0 h3
  · exact (map_units_iff g (⟨c, hcT⟩ : T)).mpr ((coe_units_iff T (⟨c, hcT⟩ : T)).mp hcUnits)
  · have hT : Assembly.rvPow (⟨u, huT⟩ : T) n
        = iRVMul (iRv (⟨m, hmT⟩ : T)) (⟨c, hcT⟩ : T) := by
      apply Subtype.ext
      change ((Assembly.rvPow (⟨u, huT⟩ : T) n : T) : M)
        = ((iRVMul (iRv (⟨m, hmT⟩ : T)) (⟨c, hcT⟩ : T) : T) : M)
      rw [coe_rvPow T (⟨u, huT⟩ : T) n, coe_rvMul, coe_rv T (⟨m, hmT⟩ : T), hpow,
        coe_rv T (⟨m, hmT⟩ : T)]
    calc Assembly.rvPow (g ⟨u, huT⟩) n
        = g (Assembly.rvPow (⟨u, huT⟩ : T) n) := (map_rvPow g (⟨u, huT⟩ : T) n).symm
      _ = g (iRVMul (iRv (⟨m, hmT⟩ : T)) (⟨c, hcT⟩ : T)) := by rw [hT]
      _ = iRVMul (g (iRv (⟨m, hmT⟩ : T))) (g ⟨c, hcT⟩) := map_rvMul g _ _
      _ = iRVMul (iRv (g ⟨m, hmT⟩)) (g ⟨c, hcT⟩) := by rw [map_rv g (⟨m, hmT⟩ : T)]

/-! ### 4.1 Stress tests for §4 -/

/-- **`m ∉ S` is not removable**: for an element already in `S` the one-step conclusion holds
trivially, with `T = S` and `g = f`.  So the refutation genuinely needs a *new* element, exactly as
the paper's one-step does. -/
theorem oneStepAt_of_mem {S : LRV.Substructure M} (f : S ↪[LRV] N)
    (hStand : Assembly.Standing S) {m : M} (hm : m ∈ S) : OneStepAt S f m :=
  ⟨S, f, le_rfl, fun _ => rfl, hm, hStand⟩

/-- **The configuration is not excluded by size.**  `Standing S` already puts every unit of `M` in
`S`, and `f : S ↪[LRV] N` is injective, so a `RoomObstruction` at `(M, N)` already forces
`#Kˣ(M) ≤ #N` — the very bound that the paper's `‖M‖⁺`-saturation supplies and that
`M7Paper.prepStepP_forces_units_size` extracts from `PrepStepP`.  In particular no cardinality
hypothesis is used by §4, and none is contradicted by it. -/
theorem roomObstruction_forces_units_size [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (h : RoomObstruction M N) : Cardinal.mk {x : M // iUnits x} ≤ Cardinal.mk N := by
  obtain ⟨S, f, s, m, hStand, _⟩ := h
  exact M7Paper.standing_forces_units_size S f hStand

/-- **The repaired shape is not vacuous, or size-refuted.**  At a `PaperHyp` pair the size content
that `Standing` needs is supplied by the hypothesis itself (`#Kˣ(M) ≤ #M ≤ #N`), which is why the
paper-pair restriction is compatible with the one-step's own hypothesis — unlike the frozen shape,
whose size content had to come from nowhere (`M7Paper.prepStepP_forces_units_size`). -/
theorem paperHyp_supplies_standing_size [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (h : M7Paper.PaperHyp M N) :
    Cardinal.mk {x : M // iUnits x} ≤ Cardinal.mk N :=
  M7Paper.paperHyp_supplies_units_size h

end Refute

/-! ## 5. The repaired quantifier shape

The frozen `M7Paper.OneStepSizeFree` quantifies over all pairs of models; §4 shows that the
size-bounded restriction does not repair it, so the quantifier must be restricted to the pairs on
which the paper's Section 3 argument actually runs: `M7Paper.PaperHyp M N`
(`SaturatedFS N ∧ #M ≤ #N`).  The implications below are the machine-checked content of
"`OneStepPaper` is the weakest of the three shapes, and it still yields Theorem 2.3". -/

/-- **Lemmas 3.4–3.8 restricted to the paper's pairs.** -/
def OneStepPaper : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M7Paper.PaperHyp M N → Assembly.OneStepVFP (M := M) (N := N)

/-- **Lemmas 3.4–3.8 with the size bound only** — the shape that §4 refutes. -/
def OneStepSizeBounded : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF],
    M7Paper.SizeHyp M N → Assembly.OneStepVFP (M := M) (N := N)

/-- The frozen shape implies the size-bounded shape. -/
theorem oneStepSizeBounded_of_free (h : M7Paper.OneStepSizeFree) : OneStepSizeBounded :=
  fun M N _ _ _ _ _ => h M N

/-- The size-bounded shape implies the paper-pair shape (`PaperHyp` contains `SizeHyp`). -/
theorem oneStepPaper_of_sizeBounded (h : OneStepSizeBounded) : OneStepPaper :=
  fun M N _ _ _ _ hP => h M N hP.2

/-- The paper-pair shape is implied by the frozen one, so the repair only ever weakens. -/
theorem oneStepPaper_of_free (h : M7Paper.OneStepSizeFree) : OneStepPaper :=
  oneStepPaper_of_sizeBounded (oneStepSizeBounded_of_free h)

/-- **Proposition 3.9 at the paper's pairs, from the paper-pair one-step.** -/
theorem prop39Sat_of_paper (hPrep : M7Paper.PrepStepSize) (hOne : OneStepPaper) :
    M7Paper.Prop39Sat :=
  fun M N _ _ _ _ hP S f =>
    Assembly.prop39P_noVFGen (hPrep M N hP.2) (hOne M N hP) S f

/-- **Theorem 2.3 at the repaired shape** (`qe:acvf`): Shoenfield's test at the paper's pairs, the
size-bounded Lemma 3.3, and Lemmas 3.4–3.8 restricted to the paper's pairs. -/
theorem paper_theorem_2_3_sat_of_paper (hShoen : M7Paper.ShoenfieldTestSat)
    (hPrep : M7Paper.PrepStepSize) (hOne : OneStepPaper) : HasQE Axioms.ACVF :=
  hShoen (prop39Sat_of_paper hPrep hOne)

/-- The same theorem with the size-bounded shape, for comparison: the hypothesis that §4 refutes. -/
theorem paper_theorem_2_3_sat_of_sizeBounded (hShoen : M7Paper.ShoenfieldTestSat)
    (hPrep : M7Paper.PrepStepSize) (hOne : OneStepSizeBounded) : HasQE Axioms.ACVF :=
  paper_theorem_2_3_sat_of_paper hShoen hPrep (oneStepPaper_of_sizeBounded hOne)

/-! ### 5.1 The refutation of the un-restricted shapes -/

/-- **The frozen `OneStepSizeFree` is false** at any pair carrying a `RoomObstruction` whose target
is Archimedean.  (The paper's pair `ℂ((t^{ℚ²}))`, `ℂ((t^ℚ))` is such a pair; see §6.) -/
theorem not_oneStepSizeFree [LRV.Structure M] [LRV.Structure N]
    [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (h : RoomObstruction M N) (hArch : ArchimedeanRV N) : ¬ M7Paper.OneStepSizeFree :=
  fun hFree => not_oneStepVFP_of_roomObstruction h hArch (hFree M N)

/-- **The size-bounded repair is false too**: the witness pair of `not_oneStepSizeFree` has
`SizeHyp` (both models are of cardinality `𝔠`), so restricting the one-step to size-bounded pairs
does not remove the obstruction. -/
theorem not_oneStepSizeBounded [LRV.Structure M] [LRV.Structure N]
    [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (h : RoomObstruction M N) (hArch : ArchimedeanRV N) (hSize : M7Paper.SizeHyp M N) :
    ¬ OneStepSizeBounded :=
  fun hB => not_oneStepVFP_of_roomObstruction h hArch (hB M N hSize)

/-- Conversely: `OneStepVFP` has no content at a pair over which no `Standing` substructure
`L_RV`-embeds into the target (it is then vacuous), which is why the saturated-pair restriction is
the only place its content can be weakened without changing the statement. -/
theorem oneStepVFP_of_no_standing [LRV.Structure M] [LRV.Structure N]
    [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (h : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), ¬ Assembly.Standing S) :
    Assembly.OneStepVFP (M := M) (N := N) :=
  fun S f hStand => absurd hStand (h S f)

end SpecialTransformations.Milestone0.Hahn

#print axioms SpecialTransformations.Milestone0.Hahn.map_rvPow
#print axioms SpecialTransformations.Milestone0.Hahn.notArchimedeanRV_iff
#print axioms SpecialTransformations.Milestone0.Hahn.no_archimedean_infinitesimal
#print axioms SpecialTransformations.Milestone0.Hahn.not_archimedeanRV_of_infinitesimalRoom
#print axioms SpecialTransformations.Milestone0.Hahn.not_oneStepAt_of_infinitesimal
#print axioms SpecialTransformations.Milestone0.Hahn.not_oneStepVFP_of_infinitesimal
#print axioms SpecialTransformations.Milestone0.Hahn.not_oneStepVFP_of_roomObstruction
#print axioms SpecialTransformations.Milestone0.Hahn.oneStepAt_gives_root_mod_units
#print axioms SpecialTransformations.Milestone0.Hahn.oneStepAt_of_mem
#print axioms SpecialTransformations.Milestone0.Hahn.roomObstruction_forces_units_size
#print axioms SpecialTransformations.Milestone0.Hahn.not_archimedeanRV_of_oneStep
#print axioms SpecialTransformations.Milestone0.Hahn.paperHyp_supplies_standing_size
#print axioms SpecialTransformations.Milestone0.Hahn.prop39Sat_of_paper
#print axioms SpecialTransformations.Milestone0.Hahn.paper_theorem_2_3_sat_of_paper
#print axioms SpecialTransformations.Milestone0.Hahn.paper_theorem_2_3_sat_of_sizeBounded
#print axioms SpecialTransformations.Milestone0.Hahn.not_oneStepSizeFree
#print axioms SpecialTransformations.Milestone0.Hahn.not_oneStepSizeBounded
#print axioms SpecialTransformations.Milestone0.Hahn.oneStepVFP_of_no_standing
