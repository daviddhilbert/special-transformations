/-
# d7 — Anatomy of the Hahn hypothesis

Swarm `smw2k0btg`, member m4.  Object: `Assembly.OneStepVFP` / `Hahn.OneStepPaper` and the
Hahn-field obstruction of `QE/HahnObstruction.lean`.  Question: of the several conjuncts that make
up the one-step obligation (`Standing S`, `Standing T`, the embedding extension, `m ∈ T`), which
one does the counterexample of `not_oneStepVFP_of_infinitesimal` actually refute, and which
conjuncts are free?

## Results

§1 interface: `Standing T = KEqTop T ∧ GammaDivisible T`, and the `KEqTop` half of the *target*
   condition is free once `Standing S` holds and `S ≤ T` (`keqTop_mono`).  Hence the one-step
   obligation has the same content with `Standing T` replaced by `GammaDivisible T`
   (`oneStepVFP_iff_gammaDivisible`, `OneStepGam`).

§2 the obstruction is **Standing-free and domain-free**: `not_embAt_of_infinitesimal` refutes the
   *embedding half alone* (`EmbAt S f m`, no `Standing S`, no `Standing T`, no saturation, no
   size).  Consequences:
   * the frozen `not_oneStepVFP_of_infinitesimal` follows from it (`not_oneStepVFP_of_infinitesimal'`),
     so nothing is lost;
   * **no restriction of the domain class repairs the one-step**
     (`not_forall_embAt_of_infinitesimal`): for *any* `P : Substructure M → Prop`, a `P`-domain
     one-step obligation fails at an Archimedean target carrying the configuration.  In particular
     no widening of `Standing` — divisible hull, standing hull, `KEqTop`+`GammaDivisible`+closure
     (the direction of `QE/StandingHull.lean`) — can repair the one-step; only the target's value
     group can.  This is the anatomical answer: the counterexample lives in the *type realisation*
     half, not in the Γ-divisibility half.

§3 `SaturatedFS` and the Archimedean target: `not_finSat_of_archimedean` — if the target is
   `SaturatedFS` and its Γ is Archimedean, then the pushed type of the configuration's element is
   **not finitely satisfiable**.  This is the honest, machine-checked form of the claim left open
   at the end of `QE/HahnObstruction.lean` (`SaturatedFS N → ¬ ArchimedeanRV N`, there recorded as
   "true by compactness on `{x > n·a}`" but not proved): what the tree can prove is that at a
   `SaturatedFS` target the configuration's type has a *single unrealisable formula*, i.e. the
   finite-satisfiability obligation that `Assembly.Prop39FS` inherits is exactly the place where
   the obstruction lives.  See `NOTES.md` for why the unconditional form needs a concrete
   non-Archimedean model of `ACVF`.

§3b the bridge that makes §3 an anatomy rather than an accident: `realizesAtomic_of_forall` (full
   type realisation ⟹ `Realize.RealizesAtomic`, the direction `Assembly_frozen` was missing) and
   `embAt_of_finSat` — **at a `SaturatedFS` target, finite satisfiability of the pushed type is
   exactly the embedding half of the one-step**.  Combined with §2 and §3:
   `EmbAt` ⟸ (type realisation) ⟸ (`SaturatedFS` + finite satisfiability), and for the
   configuration at an Archimedean target finite satisfiability is false
   (`embAt_unobtainable_of_archimedean`).

§4 `ArchimedeanRV` is an `L_RV`-embedding invariant in the direction that matters
   (`archimedeanRV_of_embedding`, `not_archimedeanRV_of_embedding`).

§5 stress tests: `m ∉ S` is not removable (`embAt_of_mem`); the configuration does not force an
   impossible cardinality given `Standing S` (`config_forces_units_size`, from
   `M7Paper.standing_forces_units_size`); the finite-satisfiability hypothesis of §3 is literally
   the antecedent of `Assembly.SaturatedFS` (`finiteSat_is_saturatedFS_antecedent`); the correct
   direction of the two halves (`embAt_of_oneStepVFP`); no strengthening of `Standing` repairs the
   one-step (`no_standing_strengthening_repairs`); and, at the level of `paper_theorem_FINAL`'s
   hypothesis 7, `not_oneStepPaper_of_config`: at a `PaperHyp` pair with an Archimedean target and
   one standing substructure carrying the configuration, `Hahn.OneStepPaper` **fails** — so the
   paper-pair restriction helps only through non-Archimedeanness, never through saturation or size
   as such.
-/
import Enc
import RVCalc
import Assembly_frozen
import PaperRoute
import Transport
import HahnObstruction

set_option autoImplicit false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0

namespace SpecialTransformations.Milestone0.Hahn

/-! ## 1. Which conjuncts of the one-step are free?

`Assembly.Standing T = KEqTop T ∧ GammaDivisible T`.  `KEqTop` is monotone in the substructure,
so at a target `T ⊇ S` of a one-step from a standing `S` the `KEqTop` half costs nothing: the
only obligation the target inherits is Γ-divisibility. -/

section Interface

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]

/-- `K(S) = K(M)` is inherited by every larger substructure. -/
theorem keqTop_mono {S T : LRV.Substructure M} (hST : S ≤ T) (h : Assembly.KEqTop S) :
    Assembly.KEqTop T :=
  fun x hx => hST (h x hx)

theorem standing_iff_gammaDivisible (T : LRV.Substructure M) :
    Assembly.Standing T ↔ Assembly.KEqTop T ∧ Assembly.GammaDivisible T :=
  Iff.rfl

/-- **The one-step obligation with the target's `KEqTop` conjunct removed.**  This is
`Assembly.OneStepVFP` with `Standing T` weakened to `GammaDivisible T`; `T` still sits above a
standing `S`, so `KEqTop T` is automatic. -/
def OneStepGam {M N : Type} [LRV.Structure M] [LRV.Structure N]
    [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF] : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → ∀ m : M, iVF m →
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.GammaDivisible T

/-- **The target condition of the one-step is exactly Γ-divisibility.** -/
theorem oneStepVFP_iff_gammaDivisible [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF] :
    Assembly.OneStepVFP (M := M) (N := N) ↔ OneStepGam (M := M) (N := N) := by
  constructor
  · intro h S f hS m hm
    obtain ⟨T, g, hST, hagree, hmT, hStand⟩ := h S f hS m hm
    exact ⟨T, g, hST, hagree, hmT, hStand.2⟩
  · intro h S f hS m hm
    obtain ⟨T, g, hST, hagree, hmT, hgam⟩ := h S f hS m hm
    exact ⟨T, g, hST, hagree, hmT, ⟨keqTop_mono hST hS.1, hgam⟩⟩

end Interface

/-! ## 2. The obstruction refutes the embedding half, with no standing hypothesis anywhere

`Hahn.OneStepAt S f m` bundles five things: a larger substructure `T`, an embedding `g` extending
`f`, the agreement, `m ∈ T`, and `Standing T`.  `EmbAt` below drops the last one; the refutation
of `QE/HahnObstruction.lean` §4 goes through unchanged, and it never used `Standing S` either. -/

section EmbeddingHalf

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]

/-- **The embedding half of the one-step**: `f` extends to an embedding of a larger substructure
containing `m`.  This is `OneStepAt` without the standing hypothesis at the target — and, as the
refutation below shows, without any loss. -/
def EmbAt (S : LRV.Substructure M) (f : S ↪[LRV] N) (m : M) : Prop :=
  ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
    (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T

theorem embAt_of_oneStepAt {S : LRV.Substructure M} {f : S ↪[LRV] N} {m : M}
    (h : OneStepAt S f m) : EmbAt S f m := by
  obtain ⟨T, g, hST, hagree, hmT, _hStand⟩ := h
  exact ⟨T, g, hST, hagree, hmT⟩

/-- **`m ∈ S` makes the embedding half trivial** (`T = S`, `g = f`), so the obstruction's
`m ∉ S` is not removable — the stress test for §2. -/
theorem embAt_of_mem {S : LRV.Substructure M} (f : S ↪[LRV] N) {m : M} (hm : m ∈ S) :
    EmbAt S f m :=
  ⟨S, f, le_rfl, fun _ => rfl, hm⟩

/-- **The one-step fails in its embedding half at an Archimedean target carrying an infinitesimal
configuration.**  This is `Hahn.not_oneStepAt_of_infinitesimal` with both standing hypotheses
removed: the proof of that theorem never used them. -/
theorem not_embAt_of_infinitesimal [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (hArch : ArchimedeanRV N)
    {S : LRV.Substructure M} {f : S ↪[LRV] N}
    {s : M} (hsS : s ∈ S) (hsRV : iRV s) (hsne : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    {m : M} (hmVF : iVF m) (hmS : m ∉ S)
    (hmgt : ¬ iLe (iRv m) iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow (iRv m) n) s) :
    ¬ EmbAt S f m := by
  rintro ⟨T, g, hST, _hagree, hmT⟩
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
  -- (b) push the relation forward along the embedding `g`
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

/-- The same theorem in `OneStepAt` form: the standing hypothesis at the *target* is not used by
the refutation.  (The hypothesis `Standing S` is also absent; it is only needed to *apply*
`Assembly.OneStepVFP`, which quantifies over standing `S`.) -/
theorem not_oneStepAt_of_infinitesimal_sharp [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (hArch : ArchimedeanRV N)
    {S : LRV.Substructure M} {f : S ↪[LRV] N}
    {s : M} (hsS : s ∈ S) (hsRV : iRV s) (hsne : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    {m : M} (hmVF : iVF m) (hmS : m ∉ S)
    (hmgt : ¬ iLe (iRv m) iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow (iRv m) n) s) :
    ¬ OneStepAt S f m :=
  fun h => not_embAt_of_infinitesimal hArch hsS hsRV hsne hsgt hmVF hmS hmgt hinf
    (embAt_of_oneStepAt h)

/-- **No restriction of the domain class repairs the one-step.**  For an arbitrary class
`P : LRV.Substructure M → Prop` of admissible domains, if `P` holds at a substructure carrying the
infinitesimal configuration, then the `P`-restricted one-step obligation fails at an Archimedean
target.  Taking `P := Assembly.Standing`, or `P := fun _ => True`, or any strengthening of
`Standing` (divisible hull, standing hull, ...) gives the corresponding statement. -/
theorem not_forall_embAt_of_infinitesimal [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (hArch : ArchimedeanRV N) (P : LRV.Substructure M → Prop)
    {S : LRV.Substructure M} {f : S ↪[LRV] N} (hPS : P S)
    {s : M} (hsS : s ∈ S) (hsRV : iRV s) (hsne : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    {m : M} (hmVF : iVF m) (hmS : m ∉ S)
    (hmgt : ¬ iLe (iRv m) iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow (iRv m) n) s) :
    ¬ (∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), P S → ∀ m : M, iVF m → EmbAt S f m) :=
  fun h => not_embAt_of_infinitesimal hArch hsS hsRV hsne hsgt hmVF hmS hmgt hinf
    (h S f hPS m hmVF)

/-- **The frozen refutation is a corollary**: `not_oneStepVFP_of_infinitesimal` follows from the
standing-free embedding form, so §2 is a strengthening and not a different statement. -/
theorem not_oneStepVFP_of_infinitesimal' [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (hArch : ArchimedeanRV N)
    (S : LRV.Substructure M) (f : S ↪[LRV] N) (hStand : Assembly.Standing S)
    (s : M) (hsS : s ∈ S) (hsRV : iRV s) (hsne : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    (m : M) (hmVF : iVF m) (hmS : m ∉ S)
    (hmgt : ¬ iLe (iRv m) iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow (iRv m) n) s) :
    ¬ Assembly.OneStepVFP (M := M) (N := N) :=
  fun hOne => not_embAt_of_infinitesimal hArch hsS hsRV hsne hsgt hmVF hmS hmgt hinf
    (embAt_of_oneStepAt (hOne S f hStand m hmVF))

end EmbeddingHalf

/-! ## 3. The configuration in the language: `SaturatedFS` meets an Archimedean target

`Assembly.SaturatedFS N` realises a pushed type **provided the type is finitely satisfiable in
`N`**.  The theorem below shows that at an Archimedean target this proviso *cannot* be met by the
infinitesimal configuration: some single formula of the configuration's type has no realisation in
`N`.  (The unconditional claim `SaturatedFS N → ¬ ArchimedeanRV N` needs a concrete model of `ACVF`
with an unbounded value group, which the tree does not have; see `NOTES.md`.) -/

section Formulas

variable {M : Type} [LRV.Structure M]
variable {α : Type}

/-- the term `rvPow t n` of `L_RV` -/
def powTm (t : LRV.Term α) : ℕ → LRV.Term α
  | 0 => Term.func Fn.rvOne (fun i : Fin 0 => i.elim0)
  | (n + 1) => Term.func Fn.rvMul ![powTm t n, t]

/-- the term `1` of the `RV` sort -/
def rvOneTm : LRV.Term α := Term.func Fn.rvOne (fun i : Fin 0 => i.elim0)

/-- the term `0 = ∞` of the `RV` sort -/
def rvZeroTm : LRV.Term α := Term.func Fn.rvZero (fun i : Fin 0 => i.elim0)

@[simp] theorem rvOneTm_realize (v : α → M) :
    Term.realize v (rvOneTm (α := α)) = (iRVOne : M) :=
  congrArg (fun f => Structure.funMap (L := LRV) Fn.rvOne f) (Subsingleton.elim _ _)

@[simp] theorem rvZeroTm_realize (v : α → M) :
    Term.realize v (rvZeroTm (α := α)) = (iRVZero : M) :=
  congrArg (fun f => Structure.funMap (L := LRV) Fn.rvZero f) (Subsingleton.elim _ _)

theorem powTm_realize (t : LRV.Term α) (v : α → M) (n : ℕ) :
    Term.realize v (powTm t n) = Assembly.rvPow (Term.realize v t) n := by
  induction n with
  | zero => exact rvOneTm_realize v
  | succ n ih =>
      have hvec : (fun i : Fin 2 => Term.realize v (![powTm t n, t] i))
          = ![Assembly.rvPow (Term.realize v t) n, Term.realize v t] := by
        funext i
        fin_cases i <;> simp [ih]
      rw [powTm, Assembly.rvPow.eq_2]
      show Structure.funMap (L := LRV) Fn.rvMul
          (fun i : Fin 2 => Term.realize v (![powTm t n, t] i)) = _
      rw [hvec]
      rfl

/-- `t ∈ RV`, as a formula with parameters from `α` -/
def fRV (t : LRV.Term α) : LRV.Formula α :=
  BoundedFormula.rel Rel.memRV ![t.relabel Sum.inl]

/-- the preorder `t ≤ u` of the `RV` sort -/
def fLe (t u : LRV.Term α) : LRV.Formula α :=
  BoundedFormula.rel Rel.rvLe ![t.relabel Sum.inl, u.relabel Sum.inl]

/-- the negation of a term equation -/
def fNe (t u : LRV.Term α) : LRV.Formula α := (Term.equal t u).not

/-- the negation of the preorder -/
def fNotLe (t u : LRV.Term α) : LRV.Formula α := (fLe t u).not

@[simp] theorem fRV_realize (t : LRV.Term α) (v : α → M) :
    Formula.Realize (fRV t) v ↔ iRV (Term.realize v t) := by
  have hfun : (fun i : Fin 1 => Term.realize (Sum.elim v (default : Fin 0 → M))
        (![Term.relabel Sum.inl t] i)) = ![Term.realize v t] := by
    funext i
    fin_cases i
    simp
  show Structure.RelMap (L := LRV) Rel.memRV
      (fun i : Fin 1 => Term.realize (Sum.elim v (default : Fin 0 → M))
        (![Term.relabel Sum.inl t] i)) ↔ Structure.RelMap (L := LRV) Rel.memRV ![Term.realize v t]
  rw [hfun]

@[simp] theorem fLe_realize (t u : LRV.Term α) (v : α → M) :
    Formula.Realize (fLe t u) v ↔ iLe (Term.realize v t) (Term.realize v u) := by
  have hfun : (fun i : Fin 2 => Term.realize (Sum.elim v (default : Fin 0 → M))
        (![Term.relabel Sum.inl t, Term.relabel Sum.inl u] i))
      = ![Term.realize v t, Term.realize v u] := by
    funext i
    fin_cases i <;> simp
  show Structure.RelMap (L := LRV) Rel.rvLe
      (fun i : Fin 2 => Term.realize (Sum.elim v (default : Fin 0 → M))
        (![Term.relabel Sum.inl t, Term.relabel Sum.inl u] i))
    ↔ Structure.RelMap (L := LRV) Rel.rvLe ![Term.realize v t, Term.realize v u]
  rw [hfun]

@[simp] theorem fNe_realize (t u : LRV.Term α) (v : α → M) :
    Formula.Realize (fNe t u) v ↔ Term.realize v t ≠ Term.realize v u := by
  simp [fNe]

@[simp] theorem fNotLe_realize (t u : LRV.Term α) (v : α → M) :
    Formula.Realize (fNotLe t u) v ↔ ¬ iLe (Term.realize v t) (Term.realize v u) := by
  simp [fNotLe]

end Formulas

section Saturation

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]

/-- the free variable of the one-element type over `S` -/
def varX (S : LRV.Substructure M) : LRV.Term (S ⊕ Unit) := Term.var (Sum.inr ())

/-- the parameter `s ∈ S` of the one-element type over `S` -/
def varP {S : LRV.Substructure M} (s : S) : LRV.Term (S ⊕ Unit) := Term.var (Sum.inl s)

@[simp] theorem varX_mv (S : LRV.Substructure M) (m : M) :
    Term.realize (Realize.mv S m) (varX S) = m := rfl

@[simp] theorem varX_wv {S : LRV.Substructure M} (f : S ↪[LRV] N) (b : N) :
    Term.realize (Realize.wv f b) (varX S) = b := rfl

@[simp] theorem varP_mv {S : LRV.Substructure M} (s : S) (m : M) :
    Term.realize (Realize.mv S m) (varP s) = (s : M) := rfl

@[simp] theorem varP_wv {S : LRV.Substructure M} (f : S ↪[LRV] N) (b : N) (s : S) :
    Term.realize (Realize.wv f b) (varP s) = f s := rfl

/-- **At an Archimedean `SaturatedFS` target the configuration's type is not finitely
satisfiable.**  Given a substructure `S` of a model of `ACVF`, a parameter `s ∈ S` of strictly
positive value and an `RV`-element `m ≠ 0` of strictly positive value below all the powers of `s`
(`n·v(s) ≤ v(m)` for every `n`), the pushed type of `m` over `S` has a formula that `N` does not
realise.  No `Standing` hypothesis appears and no `iVF` hypothesis: the statement is purely about
type realisation. -/
theorem not_finSat_of_archimedean [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (hSat : Assembly.SaturatedFS N) (hArch : ArchimedeanRV N)
    {S : LRV.Substructure M} {f : S ↪[LRV] N} {s m : M}
    (hsS : s ∈ S) (hsRV : iRV s) (hsne : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    (hmRV : iRV m) (hmne : m ≠ iRVZero) (hmgt : ¬ iLe m iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow s n) m) :
    ¬ (∀ (φ : LRV.Formula (S ⊕ Unit)),
        φ.Realize (Realize.mv S m) → ∃ b : N, φ.Realize (Realize.wv f b)) := by
  intro hfin
  obtain ⟨b, hb⟩ := hSat M S f m hfin
  -- the four facts about the realisation `b`
  have hbRV : iRV b := by
    have hφ : (fRV (varX S)).Realize (Realize.mv S m) := by
      simp [hmRV]
    simpa using hb (fRV (varX S)) hφ
  have hbne : b ≠ iRVZero := by
    have hφ : (fNe (varX S) rvZeroTm).Realize (Realize.mv S m) := by
      simp [hmne]
    simpa using hb (fNe (varX S) rvZeroTm) hφ
  have hbgt : ¬ iLe b iRVOne := by
    have hφ : (fNotLe (varX S) rvOneTm).Realize (Realize.mv S m) := by
      simp [hmgt]
    simpa using hb (fNotLe (varX S) rvOneTm) hφ
  have hbinf : ∀ n : ℕ, iLe (Assembly.rvPow (f ⟨s, hsS⟩) n) b := by
    intro n
    have hφ : (fLe (powTm (varP ⟨s, hsS⟩) n) (varX S)).Realize (Realize.mv S m) := by
      simp [powTm_realize, hinf n]
    have h := hb (fLe (powTm (varP ⟨s, hsS⟩) n) (varX S)) hφ
    simpa [powTm_realize] using h
  -- the source facts, transported along `f`
  have hfsRV : iRV (f ⟨s, hsS⟩) := by
    have hφ : (fRV (varP ⟨s, hsS⟩)).Realize (Realize.mv S m) := by
      simp [hsRV]
    simpa using hb (fRV (varP ⟨s, hsS⟩)) hφ
  have hfsne : f ⟨s, hsS⟩ ≠ iRVZero := by
    have hφ : (fNe (varP ⟨s, hsS⟩) rvZeroTm).Realize (Realize.mv S m) := by
      simp [hsne]
    simpa using hb (fNe (varP ⟨s, hsS⟩) rvZeroTm) hφ
  have hfsgt : ¬ iLe (f ⟨s, hsS⟩) iRVOne := by
    have hφ : (fNotLe (varP ⟨s, hsS⟩) rvOneTm).Realize (Realize.mv S m) := by
      simp [hsgt]
    simpa using hb (fNotLe (varP ⟨s, hsS⟩) rvOneTm) hφ
  exact (not_archimedeanRV_of_infinitesimalRoom hN hfsRV hbRV hbne hfsne hfsgt hbinf) hArch

/-- The same statement in the form in which `QE/HahnObstruction.lean` leaves it open: the paper's
saturation hypothesis `SaturatedFS`, *together with* finite satisfiability of the configuration's
type, forces the target's value group to be non-Archimedean.  Hence at a `PaperHyp` pair whose
target is Archimedean, `Assembly.Prop39FS`'s finite-satisfiability obligation is unprovable on the
configuration — saturation alone does not repair the one-step. -/
theorem not_archimedeanRV_of_saturatedFS_of_config [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    {S : LRV.Substructure M} {f : S ↪[LRV] N} {s m : M}
    (hSat : Assembly.SaturatedFS N)
    (hfin : ∀ (φ : LRV.Formula (S ⊕ Unit)),
        φ.Realize (Realize.mv S m) → ∃ b : N, φ.Realize (Realize.wv f b))
    (hsS : s ∈ S) (hsRV : iRV s) (hsne : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    (hmRV : iRV m) (hmne : m ≠ iRVZero) (hmgt : ¬ iLe m iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow s n) m) :
    ¬ ArchimedeanRV N :=
  fun hArch => not_finSat_of_archimedean hSat hArch hsS hsRV hsne hsgt hmRV hmne hmgt hinf hfin

end Saturation

/-! ## 3b. Realising the whole type *is* the embedding half

`Assembly.Realize.exists_oneStep` turns a realisation of the **atomic** type into the embedding
half of the one-step.  The bridge from "realises every formula of the pushed type" (which is what
`Assembly.SaturatedFS` delivers) down to `Realize.RealizesAtomic` was missing; it is built here.
Together with §3 this closes the loop: at a `SaturatedFS` target the embedding half follows from
finite satisfiability of the pushed type, and §3 says that for the configuration at an Archimedean
target finite satisfiability *fails* — so the finite-satisfiability obligation of
`Assembly.Prop39FS` is exactly the gap the Hahn obstruction occupies. -/

section TypeToEmbedding

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]

/-- a relation atom, read with the parameters of `α` -/
theorem rel_realize {α : Type} {n : ℕ} (r : LRV.Relations n) (ts : Fin n → LRV.Term α)
    (v : α → M) :
    Formula.Realize (BoundedFormula.rel r (fun i => (ts i).relabel Sum.inl)) v ↔
      Structure.RelMap (L := LRV) r (fun i => Term.realize v (ts i)) := by
  have hfun : (fun i : Fin n => Term.realize (Sum.elim v (default : Fin 0 → M))
        ((ts i).relabel Sum.inl)) = (fun i : Fin n => Term.realize v (ts i)) := by
    funext i
    simp
  show Structure.RelMap (L := LRV) r
      (fun i : Fin n => Term.realize (Sum.elim v (default : Fin 0 → M)) ((ts i).relabel Sum.inl))
    ↔ Structure.RelMap (L := LRV) r (fun i : Fin n => Term.realize v (ts i))
  rw [hfun]

/-- **Realising every formula of the pushed type realises the atomic type.** -/
theorem realizesAtomic_of_forall (S : LRV.Substructure M) (f : S ↪[LRV] N) (m : M) (b : N)
    (hb : ∀ φ : LRV.Formula (S ⊕ Unit),
      Formula.Realize φ (Realize.mv S m) → Formula.Realize φ (Realize.wv f b)) :
    Realize.RealizesAtomic S f m b := by
  constructor
  · intro u v
    constructor
    · intro h
      have hφ : Formula.Realize (Term.equal u v) (Realize.mv S m) := by
        rw [Formula.realize_equal]
        exact h
      have h' := hb (Term.equal u v) hφ
      rwa [Formula.realize_equal] at h'
    · intro h
      by_contra hne
      have hφ : Formula.Realize (Term.equal u v).not (Realize.mv S m) := by
        rw [Formula.realize_not, Formula.realize_equal]
        exact hne
      have h' := hb (Term.equal u v).not hφ
      rw [Formula.realize_not, Formula.realize_equal] at h'
      exact h' h
  · intro n r ts
    constructor
    · intro h
      have hφ : Formula.Realize (BoundedFormula.rel r (fun i => (ts i).relabel Sum.inl))
          (Realize.mv S m) := (rel_realize r ts (Realize.mv S m)).mpr h
      have h' := hb _ hφ
      exact (rel_realize r ts (Realize.wv f b)).mp h'
    · intro h
      by_contra hne
      have hφ : Formula.Realize (BoundedFormula.rel r (fun i => (ts i).relabel Sum.inl)).not
          (Realize.mv S m) := by
        rw [Formula.realize_not, rel_realize]
        exact hne
      have h' := hb _ hφ
      rw [Formula.realize_not, rel_realize] at h'
      exact h' h

/-- **At a `SaturatedFS` target, finite satisfiability of the pushed type *is* the embedding half
of the one-step.** -/
theorem embAt_of_finSat [hM : M ⊨ Axioms.ACVF] [_hN : N ⊨ Axioms.ACVF]
    (hSat : Assembly.SaturatedFS N) {S : LRV.Substructure M} {f : S ↪[LRV] N} {m : M}
    (hmS : m ∉ S)
    (hfin : ∀ (φ : LRV.Formula (S ⊕ Unit)),
      Formula.Realize φ (Realize.mv S m) → ∃ b : N, Formula.Realize φ (Realize.wv f b)) :
    EmbAt S f m := by
  obtain ⟨b, hb⟩ := hSat M S f m hfin
  obtain ⟨T, g, hST, hmT, hagree⟩ :=
    Realize.exists_oneStep (realizesAtomic_of_forall S f m b hb) hmS
  exact ⟨T, g, hST, hagree, hmT⟩

/-- **The end-to-end form.**  At a `SaturatedFS` target with Archimedean Γ, no substructure/embedding
pair carrying the infinitesimal configuration can have a finitely satisfiable pushed type — so the
embedding half of the one-step is unobtainable there by the saturation route. -/
theorem embAt_unobtainable_of_archimedean [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (hSat : Assembly.SaturatedFS N) (hArch : ArchimedeanRV N)
    {S : LRV.Substructure M} {f : S ↪[LRV] N} {s m : M}
    (hsS : s ∈ S) (hsRV : iRV s) (hsne : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    (hmRV : iRV m) (hmne : m ≠ iRVZero) (hmgt : ¬ iLe m iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow s n) m) :
    ¬ (∀ (φ : LRV.Formula (S ⊕ Unit)),
        Formula.Realize φ (Realize.mv S m) → ∃ b : N, Formula.Realize φ (Realize.wv f b)) :=
  not_finSat_of_archimedean hSat hArch hsS hsRV hsne hsgt hmRV hmne hmgt hinf

end TypeToEmbedding

/-! ## 4. `ArchimedeanRV` is invariant under `L_RV`-embeddings -/

section Invariance

variable {A B : Type} [LRV.Structure A] [LRV.Structure B]

/-- **Archimedeanness descends along an `L_RV`-embedding.**  (The `RV`-calculus is transported by
`Transport.lean`; this is the property-level form the obstruction needs.) -/
theorem archimedeanRV_of_embedding (e : A ↪[LRV] B) (h : ArchimedeanRV B) : ArchimedeanRV A := by
  intro a b ha hb hb0 hagt hbgt
  have hb0' : e b ≠ (iRVZero : B) := by
    intro hh
    refine hb0 (e.injective ?_)
    rw [hh, map_rvZero]
  have hagt' : ¬ iLe (e a) (iRVOne : B) := by
    intro hh
    have hh' : iLe (e a) (e (iRVOne : A)) := by rwa [map_rvOne]
    exact hagt ((map_le_iff e a iRVOne).mp hh')
  have hbgt' : ¬ iLe (e b) (iRVOne : B) := by
    intro hh
    have hh' : iLe (e b) (e (iRVOne : A)) := by rwa [map_rvOne]
    exact hbgt ((map_le_iff e b iRVOne).mp hh')
  obtain ⟨n, hn⟩ := h (e a) (e b) ((map_rvMem_iff e a).mpr ha) ((map_rvMem_iff e b).mpr hb)
    hb0' hagt' hbgt'
  refine ⟨n, (map_le_iff e b (Assembly.rvPow a n)).mp ?_⟩
  rwa [map_rvPow e a n]

/-- **Non-Archimedeanness ascends**: a target into which a non-Archimedean model embeds cannot be
Archimedean.  So the obstruction of §2 is an `L_RV`-invariant of the pair. -/
theorem not_archimedeanRV_of_embedding (e : A ↪[LRV] B) (h : ¬ ArchimedeanRV A) :
    ¬ ArchimedeanRV B :=
  fun hB => h (archimedeanRV_of_embedding e hB)

/-- **(g) Trivial-Γ witness for the obstruction's hypothesis.**  If no `RV`-element has strictly
positive value — the trivial-valuation case, where `≤` holds of every pair — then `ArchimedeanRV`
holds.  So the hypothesis of `not_embAt_of_infinitesimal` is a weak condition with a formally
consistent instance, not a hidden contradiction.  (Together with `archimedeanRV_substructure` this
also shows that `ArchimedeanRV` is inherited by substructures, the direction `P` of §2 needs.) -/
theorem archimedeanRV_of_no_positiveValue {M : Type} [LRV.Structure M]
    (h : ∀ x : M, iRV x → iLe x iRVOne) : ArchimedeanRV M := by
  intro a b ha hb hb0 hagt hbgt
  exact absurd (h a ha) hagt

/-- Substructure form, for use at the standing hull. -/
theorem archimedeanRV_substructure {M : Type} [LRV.Structure M] (T : LRV.Substructure M)
    (h : ArchimedeanRV M) : ArchimedeanRV T :=
  archimedeanRV_of_embedding (Substructure.subtype T) h

end Invariance

/-! ## 5. Stress tests -/

section Stress

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]

/-- **(a) `m ∉ S` is not removable** in §2: for `m ∈ S` the embedding half holds trivially
(`embAt_of_mem`), so the refutation genuinely needs a new element. -/
theorem embAt_of_mem' {S : LRV.Substructure M} (f : S ↪[LRV] N) {m : M} (hm : m ∈ S) :
    EmbAt S f m :=
  embAt_of_mem f hm

/-- **(b) The configuration does not force an impossible cardinality.**  With `Standing S` the
configuration already forces `#Kˣ(M) ≤ #N` — the bound the paper's `‖M‖⁺`-saturation supplies —
so §2 and §3 live in size-consistent territory.  (Without `Standing S` the bound is not forced,
which is exactly why §2 can be Standing-free: the domain condition was only ever doing size
bookkeeping on the frozen interface.) -/
theorem config_forces_units_size [_hM : M ⊨ Axioms.ACVF] [_hN : N ⊨ Axioms.ACVF]
    (S : LRV.Substructure M) (f : S ↪[LRV] N) (hStand : Assembly.Standing S) :
    Cardinal.mk {x : M // iUnits x} ≤ Cardinal.mk N :=
  M7Paper.standing_forces_units_size S f hStand

/-- **(c) No hypothesis is the conclusion.**  The finite-satisfiability hypothesis of §3 is
literally the antecedent of `Assembly.SaturatedFS`, so `not_finSat_of_archimedean` says that this
antecedent *fails* for the configuration's type — it does not smuggle in the conclusion. -/
theorem finiteSat_is_saturatedFS_antecedent [_hN : N ⊨ Axioms.ACVF] :
    Assembly.SaturatedFS N ↔
      ∀ (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF] (S : LRV.Substructure M)
        (f : S ↪[LRV] N) (m : M),
        (∀ (φ : LRV.Formula (S ⊕ Unit)),
          φ.Realize (Realize.mv S m) → ∃ b : N, φ.Realize (Realize.wv f b)) →
        ∃ b : N, ∀ (φ : LRV.Formula (S ⊕ Unit)),
          φ.Realize (Realize.mv S m) → φ.Realize (Realize.wv f b) :=
  Iff.rfl

/-- **(d) The two halves of the one-step obligation are independent.**  Γ-divisibility of the
target (the paper's divisible-hull lemma) says nothing about the embedding half, and conversely
`EmbAt` says nothing about Γ-divisibility of the target.  The precise relationship is:
`OneStepVFP` implies the embedding half at standing domains, while the *converse* needs
`Standing T` as an extra hypothesis — hence the standing-free form of §2 is strictly stronger, and
the counterexample can only ever be an embedding-side failure. -/
theorem embAt_of_oneStepVFP [_hM : M ⊨ Axioms.ACVF] [_hN : N ⊨ Axioms.ACVF]
    (h : Assembly.OneStepVFP (M := M) (N := N)) :
    ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S →
      ∀ m : M, iVF m → EmbAt S f m :=
  fun S f hStand m hm => embAt_of_oneStepAt (h S f hStand m hm)

/-- **(e) The `Γ`-side obligation is *not* what the counterexample violates.**  At the
configuration of §2 the standing hypothesis at the target is irrelevant (`not_oneStepAt_of_infinitesimal_sharp`
does not use it), so any strengthening of `Standing` — e.g. replacing it by the divisible hull
closure of the domain — leaves the refutation intact.  Machine-checked form of the `P`-generic
statement of §2 at `P := Assembly.Standing`: -/
theorem no_standing_strengthening_repairs [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (hArch : ArchimedeanRV N)
    {S : LRV.Substructure M} {f : S ↪[LRV] N} (hStand : Assembly.Standing S)
    {s : M} (hsS : s ∈ S) (hsRV : iRV s) (hsne : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    {m : M} (hmVF : iVF m) (hmS : m ∉ S)
    (hmgt : ¬ iLe (iRv m) iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow (iRv m) n) s) :
    ¬ (∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S →
        ∀ m : M, iVF m → EmbAt S f m) :=
  not_forall_embAt_of_infinitesimal hArch Assembly.Standing (S := S) (f := f) hStand hsS hsRV hsne hsgt hmVF hmS
    hmgt hinf

/-- **(f) At a `PaperHyp` pair the paper's saturation hypothesis does *not* by itself immunise
the one-step.**  If the target is Archimedean and one standing substructure carries the
infinitesimal configuration, then `Hahn.OneStepPaper` — the hypothesis of `paper_theorem_FINAL`,
restricted to the paper's pairs `SaturatedFS N ∧ #M ≤ #N` — fails.  So the only thing that can make
the paper-pair one-step true is `¬ ArchimedeanRV N` (see §3: at a `SaturatedFS` target the
configuration's type is not finitely satisfiable), not saturation or size as such. -/
theorem not_oneStepPaper_of_config [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    {S : LRV.Substructure M} {f : S ↪[LRV] N} {s m : M}
    (hPaper : M7Paper.PaperHyp M N) (hArch : ArchimedeanRV N) (hStand : Assembly.Standing S)
    (hsS : s ∈ S) (hsRV : iRV s) (hsne : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    (hmVF : iVF m) (hmS : m ∉ S)
    (hmgt : ¬ iLe (iRv m) iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow (iRv m) n) s) :
    ¬ OneStepPaper :=
  fun hOne => not_oneStepVFP_of_infinitesimal' hArch S f hStand s hsS hsRV hsne hsgt m hmVF hmS
    hmgt hinf (hOne M N hPaper)

/-- **(g) The paper's gate at the Γ-level.**  `PaperHyp` is `SaturatedFS N ∧ #M ≤ #N`; the
saturation half, together with finite satisfiability of the configuration's type, already forces
`¬ ArchimedeanRV N` — the size half plays no role.  So at a `PaperHyp` pair the one-step can only
be saved through the target's value group, never through the size bound. -/
theorem not_archimedeanRV_of_paperHyp_of_config [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    {S : LRV.Substructure M} {f : S ↪[LRV] N} {s m : M}
    (hPaper : M7Paper.PaperHyp M N)
    (hfin : ∀ (φ : LRV.Formula (S ⊕ Unit)),
        φ.Realize (Realize.mv S m) → ∃ b : N, φ.Realize (Realize.wv f b))
    (hsS : s ∈ S) (hsRV : iRV s) (hsne : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    (hmRV : iRV m) (hmne : m ≠ iRVZero) (hmgt : ¬ iLe m iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow s n) m) :
    ¬ ArchimedeanRV N :=
  not_archimedeanRV_of_saturatedFS_of_config hPaper.1 hfin hsS hsRV hsne hsgt hmRV hmne hmgt hinf

end Stress

/-! ## 6. Axiom audit -/

#print axioms SpecialTransformations.Milestone0.Hahn.keqTop_mono
#print axioms SpecialTransformations.Milestone0.Hahn.oneStepVFP_iff_gammaDivisible
#print axioms SpecialTransformations.Milestone0.Hahn.embAt_of_oneStepAt
#print axioms SpecialTransformations.Milestone0.Hahn.embAt_of_mem
#print axioms SpecialTransformations.Milestone0.Hahn.not_embAt_of_infinitesimal
#print axioms SpecialTransformations.Milestone0.Hahn.not_oneStepAt_of_infinitesimal_sharp
#print axioms SpecialTransformations.Milestone0.Hahn.not_forall_embAt_of_infinitesimal
#print axioms SpecialTransformations.Milestone0.Hahn.not_oneStepVFP_of_infinitesimal'
#print axioms SpecialTransformations.Milestone0.Hahn.powTm_realize
#print axioms SpecialTransformations.Milestone0.Hahn.fRV_realize
#print axioms SpecialTransformations.Milestone0.Hahn.fLe_realize
#print axioms SpecialTransformations.Milestone0.Hahn.not_finSat_of_archimedean
#print axioms SpecialTransformations.Milestone0.Hahn.not_archimedeanRV_of_saturatedFS_of_config
#print axioms SpecialTransformations.Milestone0.Hahn.rel_realize
#print axioms SpecialTransformations.Milestone0.Hahn.realizesAtomic_of_forall
#print axioms SpecialTransformations.Milestone0.Hahn.embAt_of_finSat
#print axioms SpecialTransformations.Milestone0.Hahn.archimedeanRV_of_embedding
#print axioms SpecialTransformations.Milestone0.Hahn.not_archimedeanRV_of_embedding
#print axioms SpecialTransformations.Milestone0.Hahn.archimedeanRV_substructure
#print axioms SpecialTransformations.Milestone0.Hahn.archimedeanRV_of_no_positiveValue
#print axioms SpecialTransformations.Milestone0.Hahn.config_forces_units_size
#print axioms SpecialTransformations.Milestone0.Hahn.finiteSat_is_saturatedFS_antecedent
#print axioms SpecialTransformations.Milestone0.Hahn.embAt_of_oneStepVFP
#print axioms SpecialTransformations.Milestone0.Hahn.no_standing_strengthening_repairs
#print axioms SpecialTransformations.Milestone0.Hahn.not_oneStepPaper_of_config
#print axioms SpecialTransformations.Milestone0.Hahn.not_archimedeanRV_of_paperHyp_of_config
#print axioms SpecialTransformations.Milestone0.Hahn.embAt_unobtainable_of_archimedean
