/-
# m8 / r8 — The Archimedean configuration: non-vacuity, finite satisfiability, and what a
  counterexample needs

Swarm `smw2ox51x`, member m8, direction r8.  This file continues `QE/NonVacuity.lean`
(m7, swarm `smw2mluv7`), whose §1–§2 state the gate / Archimedean-configuration analysis and whose
§3 records the verdict as prose.  Nothing here proves anything about `ACVF` itself: there is no
concrete model of `Axioms.ACVF` with an unbounded value group in the tree, so the model-existence
question the ledger in §4 reduces to cannot be settled internally.

## What is machine-checked here

§1  **The configurations are self-refuting.**  `ConfigHuge` and `ConfigTiny`
    (`QE/NonVacuity.lean` §2) each contradict `Hahn.ArchimedeanRV` *of their own model*
    (`not_archimedean_of_configHuge`, `not_archimedean_of_configTiny`).  Hence any pair at which the
    tree's Archimedean refutations fire has a **non-Archimedean source** and an **Archimedean
    target** — the exact shape of the non-vacuity question.  `configTiny_rv_ne_zero` closes the
    apparent gap in `ConfigTiny` (`¬ iLe (iRv m) iRVOne` alone does not exclude `iRv m = 0`, but
    `m ∉ S` plus `0` a closed term does).

§2  **The ordinal core of the configurations' pushed types is finitely satisfiable at *every*
    target**, Archimedean or not: `huge_ordinal_core_in_target`, `tiny_ordinal_core_in_target` at the
    level of elements, and `huge_ordinal_atoms_realizable` at the level of the pushed type's
    *formulas* (all ordinal atoms `rv s ^ n ≤ x` for `n ≤ N₀`, together with `iRV x`, `x ≠ 0`,
    `¬ x ≤ 1`, are realised by one `b` in the target).  So no finite conjunction of the
    configuration's ordinal atoms can be the failing formula produced by
    `M7NonVac.not_finSatAt_iff`; the witness of `¬ QFFinSat` has to come from the residue-field /
    quantifier part of the type.

§1 also records the structural asymmetry the ledger turns on: `ConfigHuge` does not depend on the
    substructure (`configHuge_top_iff`, so it sits at `⊤`), while `ConfigTiny` cannot
    (`not_configTiny_top`), so only the tiny refutations need a proper substructure and an embedding.

§3  **The finite-satisfiability input and the vacuity ledger.**  `FinSatAtArchimedean` is the missing
    input as a named `Prop`; `RefutingConfig` is the data at which the tree refutes `Input5R`.
    Machine-checked: (`i`) `RefutingConfig → ¬ Input5R`; (`ii`) `RefutingConfig → ¬ QFFinSat` *from
    the tiny configuration*, which the tree only does for the huge one
    (`not_finSat_of_satRel_of_archimedean_tiny`); (`iii`) `RefutingConfig → ¬ ArchimedeanRV` of the
    source; (`iv`) `FinSatAtArchimedean → ¬ RefutingConfig`, so under the expected answer the whole
    Archimedean family of refutations is **vacuous** and `Input5R` is *not* refuted by it; (`v`) the
    transfer form `archimedean_of_finSatInput_of_embedding`; (`vi`) `input5R_of_finSat_split`: the
    `QFFinSat`-at-`relGate` input of `G3.input5R_of_relGate_finSat` splits into
    `FinSatAtArchimedean` plus a non-Archimedean half, so granting the expected answer removes the
    Archimedean family from the final route entirely.

No `sorry`, no `admit`, no `native_decide`, no new `axiom`; axiom audit at the end.
-/
import NonVacuity
import BallSec3

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Milestone0.M8NV

/-! ## §0. A term constructor, and what an embedding of a substructure preserves -/

/-- the term `rv t` of `L_RV` -/
def rvTm {α : Type} (t : LRV.Term α) : LRV.Term α := Term.func Fn.rvMap ![t]

@[simp] theorem rvTm_realize {A : Type} [LRV.Structure A] {α : Type} (t : LRV.Term α)
    (v : α → A) : Term.realize v (rvTm t) = iRv (Term.realize v t) := by
  have hvec : (fun i : Fin 1 => Term.realize v (![t] i)) = ![Term.realize v t] := by
    funext i
    fin_cases i
    rfl
  show Structure.funMap (L := LRV) Fn.rvMap (fun i : Fin 1 => Term.realize v (![t] i)) = _
  rw [hvec]
  simp [iRv]

section Embedding

variable {A B : Type} [LRV.Structure A] [LRV.Structure B]

/-- An embedding reflects membership in the `RV` sort. -/
theorem iRV_map {S : LRV.Substructure A} (f : S ↪[LRV] B) (x : S) :
    iRV (f x) ↔ iRV (x : A) := by
  have h := f.map_rel Rel.memRV ![x]
  have hg : (f ∘ ![x]) = ![f x] := by
    funext i
    fin_cases i
    rfl
  rw [hg] at h
  have hx : (fun i : Fin 1 => (((![x]) i : S) : A)) = ![↑x] := by
    funext i
    fin_cases i
    rfl
  have hS : (Structure.RelMap (L := LRV) (M := ↥S) Rel.memRV ![x]) ↔ iRV (x : A) := by
    show Structure.RelMap (L := LRV) (M := A) Rel.memRV (fun i => (((![x]) i : S) : A)) ↔ iRV (x : A)
    rw [hx]
    rfl
  exact h.trans hS

/-- An embedding reflects the preorder. -/
theorem iLe_map {S : LRV.Substructure A} (f : S ↪[LRV] B) (x y : S) :
    iLe (f x) (f y) ↔ iLe (x : A) (y : A) := by
  have h := f.map_rel Rel.rvLe ![x, y]
  have hg : (f ∘ ![x, y]) = ![f x, f y] := by
    funext i
    fin_cases i <;> rfl
  rw [hg] at h
  have hx : (fun i : Fin 2 => (((![x, y]) i : S) : A)) = ![↑x, ↑y] := by
    funext i
    fin_cases i <;> rfl
  have hS : (Structure.RelMap (L := LRV) (M := ↥S) Rel.rvLe ![x, y]) ↔ iLe (x : A) (y : A) := by
    show Structure.RelMap (L := LRV) (M := A) Rel.rvLe (fun i => (((![x, y]) i : S) : A)) ↔
      iLe (x : A) (y : A)
    rw [hx]
    rfl
  exact h.trans hS

/-- The `RV`-one is a closed term, so it lies in every substructure. -/
theorem rvOne_mem_substructure (S : LRV.Substructure A) : iRVOne (M := A) ∈ S :=
  S.fun_mem Fn.rvOne (fun i : Fin 0 => i.elim0) (fun i => i.elim0)

/-- The `RV`-zero (`= ∞`) is a closed term, so it lies in every substructure. -/
theorem rvZero_mem_substructure (S : LRV.Substructure A) : iRVZero (M := A) ∈ S :=
  S.fun_mem Fn.rvZero (fun i : Fin 0 => i.elim0) (fun i => i.elim0)

/-- The value of a closed term in a substructure, coerced to the ambient structure. -/
theorem funMap_zero_val (S : LRV.Substructure A) (g : LRV.Functions 0) (x : Fin 0 → ↥S) :
    ((Structure.funMap (L := LRV) (M := ↥S) g x : ↥S) : A)
      = Structure.funMap (L := LRV) (M := A) g (fun i => (x i : A)) := rfl

/-- The image of the `RV`-one under a substructure embedding. -/
theorem map_rvOne {S : LRV.Substructure A} (f : S ↪[LRV] B) :
    f ⟨iRVOne, rvOne_mem_substructure S⟩ = (iRVOne : B) := by
  have h1 : (⟨iRVOne, rvOne_mem_substructure S⟩ : ↥S)
      = Structure.funMap (L := LRV) (M := ↥S) Fn.rvOne (fun i : Fin 0 => (i.elim0 : ↥S)) := by
    apply Subtype.ext
    rw [funMap_zero_val (A := A) (S := S) (g := Fn.rvOne) (x := (fun i : Fin 0 => (i.elim0 : ↥S)))]
    show (iRVOne : A) = Structure.funMap (L := LRV) (M := A) Fn.rvOne
      (fun i : Fin 0 => (((fun j : Fin 0 => (j.elim0 : ↥S)) i) : A))
    rw [show (fun i : Fin 0 => (((fun j : Fin 0 => (j.elim0 : ↥S)) i) : A))
        = (fun i : Fin 0 => (i.elim0 : A)) from funext (fun i => i.elim0)]
    rfl
  rw [h1]
  have h := f.toHom.map_fun Fn.rvOne (fun i : Fin 0 => (i.elim0 : ↥S))
  rw [show (⇑f.toHom ∘ (fun i : Fin 0 => (i.elim0 : ↥S))) = (fun i : Fin 0 => (i.elim0 : B))
    from funext (fun i => i.elim0)] at h
  simpa [iRVOne] using h

/-- The image of the `RV`-zero (`= ∞`) under a substructure embedding. -/
theorem map_rvZero {S : LRV.Substructure A} (f : S ↪[LRV] B) :
    f ⟨iRVZero, rvZero_mem_substructure S⟩ = (iRVZero : B) := by
  have h1 : (⟨iRVZero, rvZero_mem_substructure S⟩ : ↥S)
      = Structure.funMap (L := LRV) (M := ↥S) Fn.rvZero (fun i : Fin 0 => (i.elim0 : ↥S)) := by
    apply Subtype.ext
    rw [funMap_zero_val (A := A) (S := S) (g := Fn.rvZero) (x := (fun i : Fin 0 => (i.elim0 : ↥S)))]
    show (iRVZero : A) = Structure.funMap (L := LRV) (M := A) Fn.rvZero
      (fun i : Fin 0 => (((fun j : Fin 0 => (j.elim0 : ↥S)) i) : A))
    rw [show (fun i : Fin 0 => (((fun j : Fin 0 => (j.elim0 : ↥S)) i) : A))
        = (fun i : Fin 0 => (i.elim0 : A)) from funext (fun i => i.elim0)]
    rfl
  rw [h1]
  have h := f.toHom.map_fun Fn.rvZero (fun i : Fin 0 => (i.elim0 : ↥S))
  rw [show (⇑f.toHom ∘ (fun i : Fin 0 => (i.elim0 : ↥S))) = (fun i : Fin 0 => (i.elim0 : B))
    from funext (fun i => i.elim0)] at h
  simpa [iRVZero] using h

end Embedding

/-! ## §1. The configurations contradict Archimedean-ness of their own model -/

section Configs

variable {A : Type} [LRV.Structure A] [hA : A ⊨ Axioms.ACVF]

/-- **The arithmetic core of §1.**  If a power of `b` is at most the previous power, then `b ≤ 1`.
This is `RVCalc.le_mul_iff` (scale invariance of the order by a nonzero element) together with
`b ≠ 0`. -/
theorem le_one_of_pow_succ_le_pow {b : A} (hb : iRV b) (hb0 : b ≠ iRVZero) {n : ℕ}
    (h : iLe (Assembly.rvPow b (n + 1)) (Assembly.rvPow b n)) : iLe b iRVOne := by
  have hp : iRV (Assembly.rvPow b n) := M7NonVac.rvPow_iRV hb n
  have hp0 : Assembly.rvPow b n ≠ iRVZero := M7NonVac.rvPow_ne hb hb0 n
  have hone : iRV (iRVOne : A) := Transfer.rv_one_mem hA
  have h1 : iLe (iRVMul (Assembly.rvPow b n) b) (iRVMul (Assembly.rvPow b n) (iRVOne : A)) := by
    rw [← Assembly.rvPow.eq_2, Transfer.rv_mul_one_any_right hA hp]
    exact h
  rw [Transfer.rv_mul_comm_of_model hA hp hb,
    Transfer.rv_mul_comm_of_model hA hp hone] at h1
  exact (RVCalc.le_mul_iff hA hb hone hp hp0).mpr h1

/-- **The huge configuration contradicts Archimedean-ness of its own model.**  `s > 1` and `m` above
every power of `s`: Archimedean-ness gives `m ≤ s ^ n` for some `n`, so `s ^ (n+1) ≤ m ≤ s ^ n` and
hence `s ≤ 1`. -/
theorem not_archimedean_of_huge {s m : A}
    (hsrv : iRV s) (hs0 : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    (hmrv : iRV m) (hm0 : m ≠ iRVZero) (hmgt : ¬ iLe m iRVOne)
    (hab : ∀ n : ℕ, iLe (Assembly.rvPow s n) m) : ¬ Hahn.ArchimedeanRV A := by
  intro hArch
  obtain ⟨n, hn⟩ := hArch s m hsrv hmrv hm0 hsgt hmgt
  have hle : iLe (Assembly.rvPow s (n + 1)) (Assembly.rvPow s n) :=
    RVCalc.le_trans_rv hA (M7NonVac.rvPow_iRV hsrv (n + 1)) hmrv (M7NonVac.rvPow_iRV hsrv n)
      (hab (n + 1)) hn
  exact hsgt (le_one_of_pow_succ_le_pow hsrv hs0 hle)

/-- **The tiny configuration contradicts Archimedean-ness of its own model.**  `m > 1` with every
power of `m` below `s > 1`: Archimedean-ness gives `s ≤ m ^ n`, so `m ^ (n+1) ≤ s ≤ m ^ n` and hence
`m ≤ 1`. -/
theorem not_archimedean_of_tiny {s m : A}
    (hsrv : iRV s) (hs0 : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    (hmrv : iRV m) (hm0 : m ≠ iRVZero) (hmgt : ¬ iLe m iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow m n) s) : ¬ Hahn.ArchimedeanRV A := by
  intro hArch
  obtain ⟨n, hn⟩ := hArch m s hmrv hsrv hs0 hmgt hsgt
  have hle : iLe (Assembly.rvPow m (n + 1)) (Assembly.rvPow m n) :=
    RVCalc.le_trans_rv hA (M7NonVac.rvPow_iRV hmrv (n + 1)) hsrv (M7NonVac.rvPow_iRV hmrv n)
      (hinf (n + 1)) hn
  exact hmgt (le_one_of_pow_succ_le_pow hmrv hm0 hle)

/-- `ConfigHuge` (`QE/NonVacuity.lean` §2) contradicts Archimedean-ness of its own model. -/
theorem not_archimedean_of_configHuge {S : LRV.Substructure A} {s m : A}
    (h : M7NonVac.ConfigHuge S s m) : ¬ Hahn.ArchimedeanRV A :=
  not_archimedean_of_huge h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2

/-- **`ConfigTiny` forces `iRv m ≠ 0`.**  It is not needed as an extra hypothesis: `iRv m = 0` forces
`m = 0` (`RVCalc.vf_eq_zero_of_rv_eq_zero`), `0` is a closed term and so lies in `S`, and
`ConfigTiny` has `m ∉ S`.  (Without this, `¬ iLe (iRv m) iRVOne` would be satisfiable at `m = 0`,
where it obstructs nothing — `0 = ∞` is the top of the preorder.) -/
theorem configTiny_rv_ne_zero {S : LRV.Substructure A} {s m : A}
    (h : M7NonVac.ConfigTiny S s m) : iRv m ≠ iRVZero := by
  intro h0
  refine h.2.2.2.2.2.1 ?_
  have hm0 := RVCalc.vf_eq_zero_of_rv_eq_zero hA h.2.2.2.2.1 h0
  rw [hm0]
  exact S.fun_mem Fn.vfZero (fun i : Fin 0 => i.elim0) (fun i => i.elim0)

/-- `ConfigTiny` (`QE/NonVacuity.lean` §2) contradicts Archimedean-ness of its own model. -/
theorem not_archimedean_of_configTiny {S : LRV.Substructure A} {s m : A}
    (h : M7NonVac.ConfigTiny S s m) : ¬ Hahn.ArchimedeanRV A :=
  not_archimedean_of_tiny h.2.1 h.2.2.1 h.2.2.2.1 (BallSec3.rv_mem_ax hA h.2.2.2.2.1)
    (configTiny_rv_ne_zero h) h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2

/-- **`ConfigHuge` does not depend on the substructure** beyond the membership `s ∈ S`: the same data
sits at `⊤`.  This is why the *huge* configuration refutes finite satisfiability without any
`Standing`/proper-substructure hypothesis (`G3.not_finSat_of_satRel_of_archimedean`). -/
theorem configHuge_top_iff {s m : A} :
    M7NonVac.ConfigHuge (⊤ : LRV.Substructure A) s m ↔
      iRV s ∧ s ≠ iRVZero ∧ ¬ iLe s iRVOne ∧ iRV m ∧ m ≠ iRVZero ∧ ¬ iLe m iRVOne ∧
        ∀ n : ℕ, iLe (Assembly.rvPow s n) m := by
  constructor
  · rintro ⟨-, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨h2, h3, h4, h5, h6, h7, h8⟩
  · rintro ⟨h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨Set.mem_univ s, h2, h3, h4, h5, h6, h7, h8⟩

/-- **The tiny configuration cannot sit at `S = ⊤`** (`m ∉ ⊤` is impossible).  So the tiny
refutations need a *proper* substructure and an embedding into the target, while the huge ones do
not — the asymmetry that the ledger in §4 turns on. -/
theorem not_configTiny_top {s m : A} : ¬ M7NonVac.ConfigTiny (⊤ : LRV.Substructure A) s m :=
  fun h => h.2.2.2.2.2.1 (Set.mem_univ m)

end Configs

/-! ## §2. The ordinal core in the target

The configurations live in the source; finite satisfiability is a statement about the *target*.
Everything in this section is proved for an arbitrary model `N` of `ACVF` — in particular for an
Archimedean one, which is where the tree's refutations fire. -/

section Target

variable {M N : Type} [LRV.Structure M] [LRV.Structure N] [hN : N ⊨ Axioms.ACVF]

/-- **The ordinal core of the huge configuration is realised in the target, for every bound on the
exponents.**  The witness is `(f s) ^ (N₀+1)`; no hypothesis on `Γ(N)` beyond `N ⊨ ACVF`. -/
theorem huge_ordinal_core_in_target {S : LRV.Substructure M} {f : S ↪[LRV] N} {s : M}
    (hsS : s ∈ S) (hsrv : iRV s) (hs0 : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne) (N₀ : ℕ) :
    ∃ b : N, iRV b ∧ b ≠ iRVZero ∧ ¬ iLe b iRVOne ∧
      ∀ n : ℕ, n ≤ N₀ → iLe (Assembly.rvPow (f ⟨s, hsS⟩) n) b := by
  have hxrv : iRV (f ⟨s, hsS⟩) := (iRV_map f ⟨s, hsS⟩).mpr hsrv
  have hx0 : (f ⟨s, hsS⟩ : N) ≠ iRVZero := by
    intro h
    have h' : f ⟨s, hsS⟩ = f ⟨iRVZero, rvZero_mem_substructure S⟩ := by
      rw [map_rvZero f]
      exact h
    exact hs0 (congrArg Subtype.val (f.injective h'))
  have hxgt : ¬ iLe (f ⟨s, hsS⟩) iRVOne := by
    rw [← map_rvOne f]
    intro h
    exact hsgt ((iLe_map f ⟨s, hsS⟩ ⟨iRVOne, rvOne_mem_substructure S⟩).mp h)
  have hx1 : iLe iRVOne (f ⟨s, hsS⟩) :=
    (RVCalc.le_total_rv hN hxrv (Transfer.rv_one_mem hN)).resolve_left hxgt
  have hmono : ∀ n m : ℕ, n ≤ m → iLe (Assembly.rvPow (f ⟨s, hsS⟩) n)
      (Assembly.rvPow (f ⟨s, hsS⟩) m) := fun n m hnm =>
    M7NonVac.rvPow_mono hxrv hx0 hx1 hnm
  refine ⟨Assembly.rvPow (f ⟨s, hsS⟩) (N₀ + 1), M7NonVac.rvPow_iRV hxrv (N₀ + 1),
    M7NonVac.rvPow_ne hxrv hx0 (N₀ + 1), ?_, fun n hn => hmono n (N₀ + 1) (by omega)⟩
  intro hle
  have h1 : iLe (f ⟨s, hsS⟩) (Assembly.rvPow (f ⟨s, hsS⟩) (N₀ + 1)) := by
    have h := hmono 1 (N₀ + 1) (by omega)
    rwa [Assembly.rvPow.eq_2, Assembly.rvPow.eq_1, Transfer.rv_mul_one_any hN hxrv] at h
  exact hxgt (RVCalc.le_trans_rv hN hxrv (M7NonVac.rvPow_iRV hxrv (N₀ + 1))
    (Transfer.rv_one_mem hN) h1 hle)

/-- **The ordinal core of the tiny configuration is realised in the target**: an `RV`-element above
`1` whose first `N₀+1` powers are all below `f s`.  This is
`M7NonVac.configTiny_ordinal_core_finsat` read at the target, which is where the divisibility of
`Γ(N)` lives. -/
theorem tiny_ordinal_core_in_target {S : LRV.Substructure M} {f : S ↪[LRV] N} {s : M}
    (hsS : s ∈ S) (hsrv : iRV s) (hs0 : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne) (N₀ : ℕ) :
    ∃ b : N, iRV b ∧ b ≠ iRVZero ∧ ¬ iLe b iRVOne ∧
      ∀ n : ℕ, n ≤ N₀ → iLe (Assembly.rvPow b n) (f ⟨s, hsS⟩) := by
  have hxrv : iRV (f ⟨s, hsS⟩) := (iRV_map f ⟨s, hsS⟩).mpr hsrv
  have hx0 : (f ⟨s, hsS⟩ : N) ≠ iRVZero := by
    intro h
    have h' : f ⟨s, hsS⟩ = f ⟨iRVZero, rvZero_mem_substructure S⟩ := by
      rw [map_rvZero f]
      exact h
    exact hs0 (congrArg Subtype.val (f.injective h'))
  have hxgt : ¬ iLe (f ⟨s, hsS⟩) iRVOne := by
    rw [← map_rvOne f]
    intro h
    exact hsgt ((iLe_map f ⟨s, hsS⟩ ⟨iRVOne, rvOne_mem_substructure S⟩).mp h)
  exact M7NonVac.configTiny_ordinal_core_finsat (M := N) hxrv hx0 hxgt N₀

/-- **The ordinal atoms of the huge configuration's pushed type are simultaneously realisable in the
target.**  This is the formula-level form of `huge_ordinal_core_in_target`: the atoms are the four
members of `Hahn`'s formula language — `iRV x`, `x ≠ 0`, `¬ x ≤ 1`, and `rv s ^ n ≤ x` for every
`n ≤ N₀` — and one `b` realises all of them at the pushed parameters `Realize.wv f`.  Hence no
conjunction of these atoms can be the failing formula of finite satisfiability. -/
theorem huge_ordinal_atoms_realizable {S : LRV.Substructure M} {f : S ↪[LRV] N} {s : M}
    (hsS : s ∈ S) (hsrv : iRV s) (hs0 : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne) (N₀ : ℕ) :
    ∃ b : N, (Hahn.fRV (Hahn.varX S)).Realize (Realize.wv f b) ∧
      (Hahn.fNe (Hahn.varX S) Hahn.rvZeroTm).Realize (Realize.wv f b) ∧
      (Hahn.fNotLe (Hahn.varX S) Hahn.rvOneTm).Realize (Realize.wv f b) ∧
      ∀ n : ℕ, n ≤ N₀ →
        (Hahn.fLe (Hahn.powTm (Hahn.varP ⟨s, hsS⟩) n) (Hahn.varX S)).Realize (Realize.wv f b) := by
  obtain ⟨b, hrv, hne, hgt, hle⟩ := huge_ordinal_core_in_target (f := f) hsS hsrv hs0 hsgt N₀
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · simpa using hrv
  · simpa using hne
  · simpa using hgt
  · intro n hn
    have := hle n hn
    simpa [Hahn.powTm_realize] using this

end Target

/-! ## §3. The finite-satisfiability input, and the vacuity ledger -/

/-- **The missing input.**  At every `SatRel` pair whose target is Archimedean, the pushed types are
finitely satisfiable.  §2 proves its ordinal part at every target; what is left is the
residue-field / quantifier part.  (This is the expected answer: it is §3 of
`QE/NonVacuity.lean`, stated as a `Prop`.) -/
def FinSatAtArchimedean : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N], M ⊨ Axioms.ACVF → N ⊨ Axioms.ACVF →
    M1Fix.SatRel M N → Hahn.ArchimedeanRV N → M2Saturation.QFFinSat M N

/-- **The data at which the tree refutes `Input5R`**: a `SatRel` gate pair of the right cardinality
whose target is Archimedean and whose source carries the tiny (infinitesimal) configuration at some
substructure embedding.  By `not_archimedean_of_configTiny` such a pair necessarily has a
non-Archimedean source. -/
structure RefutingConfig where
  /-- the source model -/
  M : Type
  /-- the target model -/
  N : Type
  [strM : LRV.Structure M]
  [strN : LRV.Structure N]
  [modM : M ⊨ Axioms.ACVF]
  [modN : N ⊨ Axioms.ACVF]
  /-- the substructure of the source -/
  S : LRV.Substructure M
  /-- the partial embedding into the target -/
  f : S ↪[LRV] N
  /-- the parameter of positive value -/
  s : M
  /-- the infinitesimal -/
  m : M
  /-- relative saturation of the pair -/
  sat : M1Fix.SatRel M N
  /-- the cardinality conjunct of the gate -/
  size : M7Paper.SizeHyp M N
  /-- the target is Archimedean -/
  arch : Hahn.ArchimedeanRV N
  /-- the configuration -/
  cfg : M7NonVac.ConfigTiny S s m

attribute [instance] RefutingConfig.strM RefutingConfig.strN RefutingConfig.modM
  RefutingConfig.modN

/-- **The tree's refutation, in ledger form**: a refuting configuration makes `Input5R` false, hence
the frozen route's second hypothesis vacuous at that pair. -/
theorem refutingConfig_not_input5R (W : RefutingConfig) : ¬ M5Shoenfield.Input5R :=
  letI := W.strM
  letI := W.strN
  letI := W.modM
  letI := W.modN
  M7NonVac.not_input5R_of_config_gate_pair (S := W.S) (f := W.f) (s := W.s) (m := W.m)
    W.sat W.size W.arch W.cfg

/-- The same configuration refutes the extension property *at the pair*, with no saturation and no
gate hypothesis (the tree's `G3.not_extendsHere_of_archimedean`). -/
theorem refutingConfig_not_extendsHere (W : RefutingConfig) : ¬ G3.ExtendsHere W.M W.N :=
  letI := W.strM
  letI := W.strN
  letI := W.modM
  letI := W.modN
  M7NonVac.not_extendsHere_of_configTiny (f := W.f) W.arch W.cfg

/-- **Finite satisfiability fails at a refuting configuration — from the *tiny* configuration.**
`G3.not_finSat_of_satRel_of_archimedean` does this for the huge configuration (where the pushed
element is itself an `RV`-element); here the pushed element is a `VF`-element and the type carries
`rv x` instead of `x`.  The proof is the same: a full realisation `b` has `rv b > 1` with all powers
of `rv b` below `f s`, which `ArchimedeanRV N` forbids. -/
theorem not_finSat_of_satRel_of_archimedean_tiny
    {M N : Type} [LRV.Structure M] [LRV.Structure N] [hM : M ⊨ Axioms.ACVF]
    [hN : N ⊨ Axioms.ACVF] (hSat : M1Fix.SatRel M N) (hArch : Hahn.ArchimedeanRV N)
    {S : LRV.Substructure M} {f : S ↪[LRV] N} {s m : M}
    (hsS : s ∈ S) (hsrv : iRV s) (hsne : s ≠ iRVZero) (hsgt : ¬ iLe s iRVOne)
    (hmVF : iVF m) (hmS : m ∉ S) (hmgt : ¬ iLe (iRv m) iRVOne)
    (hinf : ∀ n : ℕ, iLe (Assembly.rvPow (iRv m) n) s) :
    ¬ M2Saturation.QFFinSat M N := by
  intro hfin
  obtain ⟨b, hb⟩ := hSat S f m (hfin S f m)
  have hmrv : iRV (iRv m) := BallSec3.rv_mem_ax hM hmVF
  have hbrv : iRV (iRv b) := by
    have hφ : (Hahn.fRV (rvTm (Hahn.varX S))).Realize (Realize.mv S m) := by
      simpa using hmrv
    simpa using hb (Hahn.fRV (rvTm (Hahn.varX S))) hφ
  have hbne : iRv b ≠ iRVZero := by
    have hm0 : iRv m ≠ iRVZero := by
      intro h0
      refine hmS ?_
      have hm0' := RVCalc.vf_eq_zero_of_rv_eq_zero hM hmVF h0
      rw [hm0']
      exact S.fun_mem Fn.vfZero (fun i : Fin 0 => i.elim0) (fun i => i.elim0)
    have hφ : (Hahn.fNe (rvTm (Hahn.varX S)) Hahn.rvZeroTm).Realize (Realize.mv S m) := by
      simpa using hm0
    simpa using hb (Hahn.fNe (rvTm (Hahn.varX S)) Hahn.rvZeroTm) hφ
  have hbgt : ¬ iLe (iRv b) iRVOne := by
    have hφ : (Hahn.fNotLe (rvTm (Hahn.varX S)) Hahn.rvOneTm).Realize (Realize.mv S m) := by
      simpa using hmgt
    simpa using hb (Hahn.fNotLe (rvTm (Hahn.varX S)) Hahn.rvOneTm) hφ
  have hfinf : ∀ n : ℕ, iLe (Assembly.rvPow (iRv b) n) (f ⟨s, hsS⟩) := by
    intro n
    have hφ : (Hahn.fLe (Hahn.powTm (rvTm (Hahn.varX S)) n) (Hahn.varP ⟨s, hsS⟩)).Realize
        (Realize.mv S m) := by
      simpa [Hahn.powTm_realize] using hinf n
    have h := hb (Hahn.fLe (Hahn.powTm (rvTm (Hahn.varX S)) n) (Hahn.varP ⟨s, hsS⟩)) hφ
    simpa [Hahn.powTm_realize] using h
  have hfsrv : iRV (f ⟨s, hsS⟩) := by
    have hφ : (Hahn.fRV (Hahn.varP ⟨s, hsS⟩)).Realize (Realize.mv S m) := by
      simpa using hsrv
    simpa using hb (Hahn.fRV (Hahn.varP ⟨s, hsS⟩)) hφ
  have hfsne : (f ⟨s, hsS⟩ : N) ≠ iRVZero := by
    have hφ : (Hahn.fNe (Hahn.varP ⟨s, hsS⟩) Hahn.rvZeroTm).Realize (Realize.mv S m) := by
      simpa using hsne
    simpa using hb (Hahn.fNe (Hahn.varP ⟨s, hsS⟩) Hahn.rvZeroTm) hφ
  have hfsgt : ¬ iLe (f ⟨s, hsS⟩) iRVOne := by
    have hφ : (Hahn.fNotLe (Hahn.varP ⟨s, hsS⟩) Hahn.rvOneTm).Realize (Realize.mv S m) := by
      simpa using hsgt
    simpa using hb (Hahn.fNotLe (Hahn.varP ⟨s, hsS⟩) Hahn.rvOneTm) hφ
  obtain ⟨n, hn⟩ := hArch (iRv b) (f ⟨s, hsS⟩) hbrv hfsrv hfsne hbgt hfsgt
  have hle : iLe (Assembly.rvPow (iRv b) (n + 1)) (Assembly.rvPow (iRv b) n) :=
    RVCalc.le_trans_rv hN (M7NonVac.rvPow_iRV hbrv (n + 1)) hfsrv
      (M7NonVac.rvPow_iRV hbrv n) (hfinf (n + 1)) hn
  exact hbgt (le_one_of_pow_succ_le_pow hbrv hbne hle)

/-- **Finite satisfiability fails at any refuting configuration.** -/
theorem refutingConfig_not_finsat (W : RefutingConfig) : ¬ M2Saturation.QFFinSat W.M W.N :=
  letI := W.strM
  letI := W.strN
  letI := W.modM
  letI := W.modN
  not_finSat_of_satRel_of_archimedean_tiny (f := W.f) W.sat W.arch W.cfg.1 W.cfg.2.1 W.cfg.2.2.1
    W.cfg.2.2.2.1 W.cfg.2.2.2.2.1 W.cfg.2.2.2.2.2.1 W.cfg.2.2.2.2.2.2.1 W.cfg.2.2.2.2.2.2.2

/-- **The finite-satisfiability failure needs neither the size conjunct nor the gate**: at a
`SatRel` pair with an Archimedean target, the mere existence of the tiny configuration at a
substructure embedding kills `QFFinSat`, independently of `#M ≤ #N`.  (The size conjunct enters only
when the failure is upgraded to `¬ Input5R`, since `ExtendsAt`'s gate carries it.) -/
theorem not_finsat_of_configTiny_gateFree
    {M N : Type} [LRV.Structure M] [LRV.Structure N] [hM : M ⊨ Axioms.ACVF]
    [hN : N ⊨ Axioms.ACVF] {S : LRV.Substructure M} {f : S ↪[LRV] N} {s m : M}
    (hSat : M1Fix.SatRel M N) (hArch : Hahn.ArchimedeanRV N)
    (hcfg : M7NonVac.ConfigTiny S s m) : ¬ M2Saturation.QFFinSat M N :=
  not_finSat_of_satRel_of_archimedean_tiny (f := f) hSat hArch hcfg.1 hcfg.2.1 hcfg.2.2.1
    hcfg.2.2.2.1 hcfg.2.2.2.2.1 hcfg.2.2.2.2.2.1 hcfg.2.2.2.2.2.2.1 hcfg.2.2.2.2.2.2.2

/-- **The source of a refuting configuration is non-Archimedean.**  So the non-vacuity question is
exactly: *is there a `SatRel` pair with an Archimedean target and a non-Archimedean source?* -/
theorem refutingConfig_not_archimedean_source (W : RefutingConfig) : ¬ Hahn.ArchimedeanRV W.M :=
  letI := W.strM
  letI := W.strN
  letI := W.modM
  letI := W.modN
  not_archimedean_of_configTiny W.cfg

/-- **Under the expected finite-satisfiability answer there is no refuting configuration**: the whole
Archimedean family of refutations is vacuous, so `QE/NonVacuity.lean`'s
`not_extendsAt_rel_of_archimedean_config` / `not_prop39Sat_of_archimedean_config` refute nothing and
`Input5R` is not refuted by them. -/
theorem no_refutingConfig_of_finSat (h : FinSatAtArchimedean) : RefutingConfig → False := by
  intro W
  letI := W.strM
  letI := W.strN
  letI := W.modM
  letI := W.modN
  exact refutingConfig_not_finsat W (h W.M W.N W.modM W.modN W.sat W.arch)

/-- **The transfer form of §3.**  If the finite-satisfiability input holds, then a `SatRel` pair with
an Archimedean target whose source *embeds* into the target has Archimedean source.  (The
embeddability hypothesis is what a `SatRel` pair does not supply: `SatRel` constrains only the
substructures that do embed.) -/
theorem archimedean_of_finSatInput_of_embedding (h : FinSatAtArchimedean)
    {M N : Type} [LRV.Structure M] [LRV.Structure N] [hM : M ⊨ Axioms.ACVF]
    [hN : N ⊨ Axioms.ACVF] (hSat : M1Fix.SatRel M N) (hArch : Hahn.ArchimedeanRV N)
    (g : M ↪[LRV] N) : Hahn.ArchimedeanRV M := by
  by_contra hne
  obtain ⟨a, b, ha, hb, hb0, hagt, hbgt, hinf⟩ := (Hahn.notArchimedeanRV_iff M).mp hne
  have hinf' : ∀ n : ℕ, iLe (Assembly.rvPow a n) b := fun n =>
    (RVCalc.le_total_rv hM (M7NonVac.rvPow_iRV ha n) hb).resolve_right (hinf n)
  -- `a ≠ 0`: otherwise `rvPow a 1 = 0 = ∞` is above everything, contradicting `hinf 1`
  have ha0 : a ≠ iRVZero := by
    intro h0
    refine hinf 1 ?_
    rw [Assembly.rvPow.eq_2, Assembly.rvPow.eq_1, Transfer.rv_mul_one_any hM ha, h0]
    exact RVCalc.le_top_rv hM hb
  exact G3.not_finSat_of_satRel_of_archimedean (S := ⊤) (f := g.domRestrict ⊤) (s := a) (m := b)
    hSat hArch (Set.mem_univ a) ha ha0 hagt hb hb0 hbgt hinf'
    (h M N hM hN hSat hArch)

/-- **What the Archimedean analysis costs the final theorem: nothing, once `FinSatAtArchimedean` is
granted.**  The `QFFinSat`-at-`relGate` input of `G3.input5R_of_relGate_finSat` splits into an
Archimedean half and the rest; `FinSatAtArchimedean` is the Archimedean half, and the rest is exactly
what the case lemmas 3.4–3.8 have to prove (at non-Archimedean targets, where the tree's refutations
do not fire).  Conversely, a `RefutingConfig` would make the whole input false. -/
theorem input5R_of_finSat_split (hArch : FinSatAtArchimedean)
    (hRest : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N], M ⊨ Axioms.ACVF →
      N ⊨ Axioms.ACVF → M1Fix.SatRel M N → M7Paper.SizeHyp M N → ¬ Hahn.ArchimedeanRV N →
      M2Saturation.QFFinSat M N) :
    M5Shoenfield.Input5R := by
  refine G3.input5R_of_relGate_finSat ?_
  intro M N _ _ hM hN hgate
  by_cases hA : Hahn.ArchimedeanRV N
  · exact hArch M N hM hN hgate.1 hA
  · exact hRest M N hM hN hgate.1 hgate.2 hA

/-- **The vacuity statement in `∀`-form**: under the finite-satisfiability input, no `SatRel` pair
with an Archimedean target and the gate's cardinality conjunct carries the configuration at any
substructure.  These are exactly the hypotheses of `G3.not_extendsAt_rel_of_archimedean_config`, so
that theorem refutes nothing. -/
theorem no_archimedean_refutation_of_finSat (h : FinSatAtArchimedean) :
    ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N], M ⊨ Axioms.ACVF → N ⊨ Axioms.ACVF →
      M1Fix.SatRel M N → M7Paper.SizeHyp M N → Hahn.ArchimedeanRV N →
      ¬ ∃ (S : LRV.Substructure M) (f : S ↪[LRV] N) (s m : M), M7NonVac.ConfigTiny S s m := by
  intro M N _ _ hM hN hSat _ hArch ⟨S, f, s, m, hcfg⟩
  exact not_finSat_of_satRel_of_archimedean_tiny (f := f) hSat hArch hcfg.1 hcfg.2.1 hcfg.2.2.1
    hcfg.2.2.2.1 hcfg.2.2.2.2.1 hcfg.2.2.2.2.2.1 hcfg.2.2.2.2.2.2.1 hcfg.2.2.2.2.2.2.2
    (h M N hM hN hSat hArch)

/-- **The caveat made explicit.**  `SatRel M N` constrains only the substructures of `M` that embed
into `N`, so the transfer of Archimedean-ness to the source needs the non-commensurable pair to be
*realised over an embeddable substructure*.  Given the finite-satisfiability input, no such pair
exists at a `SatRel` pair with an Archimedean target: this is the exact form in which the ledger's
open question sits. -/
theorem not_archimedean_of_finSat_of_embeddable_param (h : FinSatAtArchimedean)
    {M N : Type} [LRV.Structure M] [LRV.Structure N] [hM : M ⊨ Axioms.ACVF]
    [hN : N ⊨ Axioms.ACVF] {S : LRV.Substructure M} (f : S ↪[LRV] N)
    (hSat : M1Fix.SatRel M N) (hArch : Hahn.ArchimedeanRV N)
    {a b : M} (haS : a ∈ S) (ha : iRV a) (hb : iRV b) (hb0 : b ≠ iRVZero)
    (hagt : ¬ iLe a iRVOne) (hbgt : ¬ iLe b iRVOne) (hinf : ∀ n : ℕ, ¬ iLe b (Assembly.rvPow a n)) :
    False := by
  have hinf' : ∀ n : ℕ, iLe (Assembly.rvPow a n) b := fun n =>
    (RVCalc.le_total_rv hM (M7NonVac.rvPow_iRV ha n) hb).resolve_right (hinf n)
  have ha0 : a ≠ iRVZero := by
    intro h0
    refine hinf 1 ?_
    rw [Assembly.rvPow.eq_2, Assembly.rvPow.eq_1, Transfer.rv_mul_one_any hM ha, h0]
    exact RVCalc.le_top_rv hM hb
  exact G3.not_finSat_of_satRel_of_archimedean (S := S) (f := f) (s := a) (m := b) hSat hArch
    haS ha ha0 hagt hb hb0 hbgt hinf' (h M N hM hN hSat hArch)

end SpecialTransformations.Milestone0.M8NV

/-! ## §4. The ledger (documented; the machine-checked content is §1–§3)

**Question.**  Is the Archimedean family of refutations — `G3.not_extendsHere_of_archimedean`,
`G3.not_extendsAt_rel_of_archimedean_config`, `G3.not_prop39Sat_of_archimedean_config`,
`G3.not_finSat_of_satRel_of_archimedean`, `M7NonVac.not_input5R_of_config_gate_pair` — vacuous?

**Answer, reduced to one model-existence question.**

* (`§1`) A pair at which any of them fires has `¬ ArchimedeanRV M` and `ArchimedeanRV N`; this is
  forced, not assumed.
* (`§2`) The obstruction is **not** an ordinal one: at *every* target, the ordinal atoms of the
  pushed type (all of them up to any finite exponent) are realised simultaneously.  So the failing
  formula that `M7NonVac.not_finSatAt_iff` extracts at such a pair is a formula that is not a
  conjunction of ordinal atoms: it must quantify over `VF` or use the residue field (`kAdd`, `kNeg`,
  `iUnits`).  `§2` also shows the *nearly* failing statement "the ordinal core can be satisfied by
  one element" holds at every model, so no strengthening of `§1` along that line is possible.
* (`§3`) `FinSatAtArchimedean → ¬ RefutingConfig`: if the pushed types are finitely satisfiable at
  Archimedean targets, then no `SatRel` pair with an Archimedean target carries the configuration,
  the refutations prove nothing, and `Input5R` survives them.  Conversely, if a refuting
  configuration exists then `Input5R` is *false* (`refutingConfig_not_input5R`), the frozen route's
  second hypothesis is vacuous, and `paper_theorem_rel_two` is proved but says nothing.

**What remains open, and why it cannot be closed inside the tree.**

1. *A model of `Axioms.ACVF` with a non-Archimedean value group.*  The tree has a machine-checked
   model only for the `p`-adic complex field (`Milestone0/accepted/ACVF_general_model_gamma.lean`),
   i.e. for `Γ` of rank 1 — and that file carries its own copy of `Milestone0/Encoding.lean`, so it
   cannot be imported next to the frozen encoding at all (this is the clash recorded by member m2's
   finding `f4` of this swarm, direction d9).  The configuration needs a rank-2 (or higher) value
   group; no Hahn-field construction of `Axioms.ACVF` exists in the tree.  Without one, neither
   `RefutingConfig` nor its negation is inhabited internally.
2. *A `SatRel` pair with an Archimedean target.*  `SatRel M N` is relative saturation, and no pair
   with a target that models `Axioms.ACVF` is exhibited anywhere in the tree.  Note that
   `Assembly.SaturatedFS` is *satisfiable on a subsingleton structure* (m2's `f4`: `SatRel M N` holds
   for every `M` when `N = PUnit`), so a degenerate witness exists — but `PUnit ⊭ Axioms.ACVF`, and
   everything in this file is stated for models, so it does not give a `SatRel` pair here.  The
   model-restricted statement `∀ N ⊨ Axioms.ACVF, ¬ SaturatedFS N` is itself open (`NoSatModel`).
3. *The residue-field / quantifier part of the pushed type.*  §2 disposes of the ordinal part.  The
   remaining obligation is: for every `VF`-formula `φ` with parameters in `S` true of the
   infinitesimal `m`, find `b ∈ N` realising it at the pushed parameters.  By quantifier elimination
   for `ACVF` (the theorem under proof) `φ` reduces to a Boolean combination of value and residue
   conditions on `x - a` (`a ∈ S`) and on `rv x`; the value conditions are exactly what §2 settles,
   and the residue conditions are free because `k(N)` is algebraically closed.  **This is where the
   project's own target re-enters**, which is why it is a residual and not a lemma: the input
   `FinSatAtArchimedean` is *not* weaker than what Lemma 3.4–3.8 must prove.
-/

#print axioms SpecialTransformations.Milestone0.M8NV.iRV_map
#print axioms SpecialTransformations.Milestone0.M8NV.iLe_map
#print axioms SpecialTransformations.Milestone0.M8NV.map_rvOne
#print axioms SpecialTransformations.Milestone0.M8NV.map_rvZero
#print axioms SpecialTransformations.Milestone0.M8NV.le_one_of_pow_succ_le_pow
#print axioms SpecialTransformations.Milestone0.M8NV.not_archimedean_of_configHuge
#print axioms SpecialTransformations.Milestone0.M8NV.not_archimedean_of_configTiny
#print axioms SpecialTransformations.Milestone0.M8NV.configHuge_top_iff
#print axioms SpecialTransformations.Milestone0.M8NV.not_configTiny_top
#print axioms SpecialTransformations.Milestone0.M8NV.configTiny_rv_ne_zero
#print axioms SpecialTransformations.Milestone0.M8NV.huge_ordinal_core_in_target
#print axioms SpecialTransformations.Milestone0.M8NV.tiny_ordinal_core_in_target
#print axioms SpecialTransformations.Milestone0.M8NV.huge_ordinal_atoms_realizable
#print axioms SpecialTransformations.Milestone0.M8NV.refutingConfig_not_input5R
#print axioms SpecialTransformations.Milestone0.M8NV.refutingConfig_not_extendsHere
#print axioms SpecialTransformations.Milestone0.M8NV.not_finSat_of_satRel_of_archimedean_tiny
#print axioms SpecialTransformations.Milestone0.M8NV.refutingConfig_not_finsat
#print axioms SpecialTransformations.Milestone0.M8NV.not_finsat_of_configTiny_gateFree
#print axioms SpecialTransformations.Milestone0.M8NV.refutingConfig_not_archimedean_source
#print axioms SpecialTransformations.Milestone0.M8NV.no_refutingConfig_of_finSat
#print axioms SpecialTransformations.Milestone0.M8NV.archimedean_of_finSatInput_of_embedding
#print axioms SpecialTransformations.Milestone0.M8NV.input5R_of_finSat_split
#print axioms SpecialTransformations.Milestone0.M8NV.no_archimedean_refutation_of_finSat
#print axioms SpecialTransformations.Milestone0.M8NV.not_archimedean_of_finSat_of_embeddable_param
