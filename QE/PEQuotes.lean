/-
# The two valuation-theory quotations of Lemma 3.6 / Lemma 3.4, specialised and wired

Member `m8`, swarm `smw2ngn1z`.  Scope: Yin, *Special transformations in ACVF*, Lemma 3.6
(`lift:transcendental`, `qe.tex:732`) — "Suppose that `e ∈ U(M)` and `rv(e)` is transcendental
over `K(Ŝ)`.  If `Γ(Ŝ)` is divisible, then Claim (⋆) holds" — and the two Prestel–Engler theorems
it and Lemma 3.4 consume.  Author ruling: the valuation theory is **quoted**, so the two theorems
are `Prop`-valued quotations here, exactly as `QE/ClassicalProps.lean` transcribes the henselization
and divisible-hull facts; the *wiring* (quote ⇒ the consumer-shaped lemma the tree wants) is proved.

## What the paper cites, and the shape each citation is used in

**(i) Engler–Prestel, Theorem 3.3.4 — the fundamental inequality.**  Cited in Lemma 3.4
(`qe.tex:626`) as `[K(⟨Ŝ,e⟩):K(Ŝ)] = [VF(⟨Ŝ,e⟩):VF(Ŝ)]`, and in Lemma 3.8 (`qe.tex:803`).  The
general form (`e·f ≤ n` for a finite extension of degree `n`, with `e = [Γ_L:Γ_K]` the ramification
index and `f = [k_L:k_K]` the residue degree) is not transcribed here at the level of residue
*fields*, because the frozen encoding has no residue-field sort and `QE/StandingField.lean`'s
`KOf M` is only the residue field of the whole model.  What is transcribed is the half that
Lemma 3.4 actually consumes, in the frozen vocabulary:

    e algebraic over VF(Ŝ) and e ∈ U(M)  ⇒  every value class of ⟨Ŝ,e⟩ has its `n!`-th power in
                                            Γ(Ŝ), where `n` bounds the degree of `e` over VF(Ŝ)

This is exactly `e·f ≤ n` read on the value-group side: the ramification index
`[Γ(⟨Ŝ,e⟩):Γ(Ŝ)] = e` divides the degree, so the exponent of the quotient divides `n!`, which is
the statement `GammaBoundBy S ⟨Ŝ,e⟩ n!` below.  (The *other* half of the paper's conclusion,
`K(⟨Ŝ,e⟩) = K(Ŝ)(rv e)`, is Lemma 3.4's business — another direction owns it — and it is the half
that needs henselianity of `Ŝ`; the value-group half does not.)  Specialisation is documented, not
proved: `EPFundamentalInequality` *is* the quotation.

**(ii) Engler–Prestel, Theorem 3.4.3 — the dimension inequality (Abhyankar).**  Cited in Lemma 3.6
(`qe.tex:735`) as "the rational rank of `Γ(⟨Ŝ,e⟩)/Γ(Ŝ)` is 0".  Abhyankar's inequality is

    trdeg(L/K) ≥ rationalRank(Γ_L/Γ_K) + trdeg(k_L/k_K),

so for `L = K(e)` with `e` transcendental over `VF(Ŝ)` (trdeg `= 1`) and `rv(e)` transcendental over
`K(Ŝ)` (residue trdeg `≥ 1`) the rational rank is `0`, i.e. `Γ(⟨Ŝ,e⟩)/Γ(Ŝ)` is torsion.  The
transcription below is that conclusion verbatim in the frozen vocabulary:

    `EPDimensionInequality` : `rv(e)` transcendental over `K(Ŝ)` and `e ∈ U(M)`
      ⇒ `M5Ledger.GammaHullInitial S ⟨Ŝ,e⟩`   ("every class of Γ(⟨Ŝ,e⟩) has a positive power in Γ(Ŝ)")

Both quotations are consumed by `QE/Lemma36Gamma.lean`'s proved chain:
`GammaHullInitial` + `Γ(Ŝ)` divisible ⇒ `Γ(⟨Ŝ,e⟩) = Γ(Ŝ)` ⇒ Claim (⋆) in class form ⇒ `Standing T`.

## Vocabulary fixed here

* `vfPolyEval`, `AlgebraicOverVF S e n` — "`e` is algebraic over `VF(Ŝ)` of degree `≤ n`", with
  coefficients in `S ∩ VF` (the `VF`-sort of `S` is a sub*ring* of `M`, which is all the frozen
  language offers; `QE/M5L34_36.lean` §2 uses the same convention).
* `Krv S e`, `RVTrans S e` — "`rv(e)` is transcendental over `K(Ŝ)`", with coefficients ranging
  over the residue elements of `S`.  Again the ring/field gap: `K(Ŝ)` in the paper is the residue
  field of `VF(Ŝ)`, while `S`'s residue elements need not be inverse-closed (the frozen `L_RV` has
  no inverse symbol on the `VF` sort, so `QF/KOfBridge.lean`'s remark applies).  The polynomial
  coefficients used are `S`'s own residue elements, which is the *more* restrictive reading — a
  hypothesis, so a more restrictive reading only makes the consumer weaker, never vacuous.
* `GammaBoundBy S T m`, `M5Ledger.GammaHullInitial S T` — the two value-group conclusions.

## Stress tests (§4)

* `gammaBoundBy_self` / `gammaHullInitial_of_bound`: both conclusion predicates are satisfiable
  (`T = S` satisfies `GammaBoundBy S S 1`, and `GammaHullInitial S S` is a tree theorem), so
  neither quotation's conclusion is an unsatisfiable predicate.
* `not_forall_gammaBoundBy` — `GammaBoundBy` is *not* trivially true: `m = 0` fails
  (`0 < m` component), and the `m = 1` case would say `Γ(T) = Γ(Ŝ)`, which is false in the
  Lemma-3.8 branch (see `QE/Lemma36Gamma.lean`'s `divisibility_essential`).
* `algebraic_one`, `algebraic_e_self`: `AlgebraicOverVF` has concrete witnesses (`e = 1` with
  `n = 1`; `e` itself when `e ∈ S`), so the hypothesis of quotation (i) is satisfiable and not a
  disguised `False`.
* `rvTrans_not_mem`: under `RVTrans S e`, the element `rv e` is *not* the residue of an element of
  `S` (`RVTrans` is not vacuous: it forces the polynomial `X - rv s` to be non-vanishing).
-/
import M5L34_36
import Lemma36Gamma
import StandingField

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.StandingField

namespace SpecialTransformations.Milestone0.M8

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-! ## 1. "`e` is algebraic over `VF(Ŝ)`" and "`rv(e)` is transcendental over `K(Ŝ)`" -/

/-- The polynomial expansion `Σ_{i ≤ m} b i · e^i` in the `VF` sort (a term of the frozen language,
so it is an element of `S` as soon as `e` and the `b i` are). -/
noncomputable def vfPolyEval (b : ℕ → M) (e : M) (m : ℕ) : M :=
  Transc.vsum (fun i => iVFMul (b i) (Transc.vpow e i)) (m + 1)

/-- **`e` is algebraic over `VF(Ŝ)` of degree `≤ n`**: a nonzero polynomial of degree at most `n`
with coefficients in the `VF`-part of `S` vanishes at `e`.  (The frozen `VF`-sort of a substructure
is a ring, not a field, so "over `VF(Ŝ)`" is read as "with coefficients in `S ∩ VF`"; cf.
`QE/M5L34_36.lean`'s `QuotExpansions`, which uses the same convention.) -/
def AlgebraicOverVF (S : LRV.Substructure M) (e : M) (n : ℕ) : Prop :=
  ∃ b : ℕ → M, (∀ i, iVF (b i)) ∧ (∀ i, b i ∈ S) ∧
    (∃ j, j ≤ n ∧ b j ≠ Transfer.iVFZero) ∧ vfPolyEval b e n = Transfer.iVFZero

/-- The residue of `rv e` as an element of the model's residue field `K(M)` (needs `e ∈ U(M)`). -/
def Krv (e : M) (h : iUnits (iRv e)) : KOf M := ⟨iRv e, Or.inl h⟩

/-- The `RV`-sort polynomial `Σ_{i < n} b i · X^i`, built from the *function symbols* `kAdd` and
`rvMul` only — so its value lies in every substructure containing the coefficients and `X`.  This is
the frozen encoding's own polynomial evaluation (the `Field (KOf M)` operations of
`QE/StandingField.lean` are these same symbols, definitionally). -/
noncomputable def rvPolyEval (b : ℕ → M) (X : M) : ℕ → M
  | 0 => iRVZero
  | (n + 1) => iKAdd (rvPolyEval b X n) (iRVMul (b n) (Transc.rvpow X n))

/-- **`rv(e)` is transcendental over `K(Ŝ)`**: no nonzero polynomial with coefficients among the
residue elements of `S` vanishes at `rv e`.

This is Yin's hypothesis "`rv(e)` is transcendental over `K(Ŝ)`" (`qe.tex:732`).  The coefficients
are the residue elements of `S` (`{rv x : x ∈ S ∩ K}`), i.e. the residue ring of `Ŝ`; in the paper
`Ŝ = ⟨VF(S)⟩` makes it a field, and the frozen encoding has no inverse symbol on the `VF` sort, so
the ring version is the available one (cf. `QE/KOfBridge.lean`'s remark).  Quantifying over the
smaller coefficient set can only make the hypothesis weaker. -/
def RVTrans (S : LRV.Substructure M) (e : M) (hunit : iUnits (iRv e)) : Prop :=
  ∀ (m : ℕ) (b : ℕ → M), (∀ i, pInKof (b i)) → (∀ i, b i ∈ S) →
    (∃ i, i ≤ m ∧ b i ≠ iRVZero) → rvPolyEval b (iRv e) (m + 1) ≠ iRVZero

/-! ## 2. The two quotations -/

/-- **Value-group conclusion of the fundamental inequality**, frozen form: `Γ(T)`'s classes have
their `m`-th powers in `Γ(Ŝ)` *uniformly*, i.e. the exponent of `Γ(T)/Γ(Ŝ)` divides `m`.  For `m = n!`
this is `e_ram ∣ n` (the ramification index of a degree-`n` extension divides `n`), which is the
`e·f ≤ n` content of EP 3.3.4 read on the value-group side. -/
def GammaBoundBy (S T : LRV.Substructure M) (m : ℕ) : Prop :=
  0 < m ∧ ∀ t : M, t ∈ T → iRV t → t ≠ iRVZero →
    ∃ s c : M, s ∈ S ∧ iRV s ∧ s ≠ iRVZero ∧ c ∈ S ∧ iUnits c ∧
      Assembly.rvPow t m = iRVMul s c

/-- **Engler–Prestel, Theorem 3.3.4 (the fundamental inequality), quoted** — in the form the frozen
encoding can state and Lemma 3.4 consumes (`qe.tex:626`):

    e algebraic over VF(Ŝ) of degree ≤ n, e ∈ U(M)
      ⇒ the exponent of Γ(⟨Ŝ,e⟩)/Γ(Ŝ) divides n!

The general statement (*Valued Fields*, Thm 3.3.4): for a finite extension `L/K` of degree `n` with
ramification index `e` and residue degree `f`, `e · f ≤ n`; hence `e ≤ n`, `e` divides... in
particular the exponent of `Γ_L/Γ_K` divides `n!`.  Nothing here is proved: this is a quotation.

The `T = ⟨Ŝ,e⟩` of the paper is the substructure generated by `S` together with `e`. -/
def EPFundamentalInequality : Prop :=
  ∀ (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF] (S : LRV.Substructure M) (e : M) (n : ℕ),
    1 ≤ n → iVF e → iUnits (iRv e) → AlgebraicOverVF S e n →
      GammaBoundBy S (Substructure.closure LRV ((S : Set M) ∪ {e})) n.factorial

/-- **Engler–Prestel, Theorem 3.4.3 (the dimension inequality), quoted** — in the form Lemma 3.6
consumes (`qe.tex:735`): if `e ∈ U(M)` and `rv(e)` is transcendental over `K(Ŝ)`, then the rational
rank of `Γ(⟨Ŝ,e⟩)/Γ(Ŝ)` is `0`, i.e. that quotient is torsion:

    every value class of ⟨Ŝ,e⟩ has a positive power in Γ(Ŝ).

The general statement (*Valued Fields*, Thm 3.4.3, Abhyankar's inequality):
`trdeg(L/K) ≥ ratrank(Γ_L/Γ_K) + trdeg(k_L/k_K)`; with `L = K(e)`, `e` transcendental over `K` and
`rv e` transcendental over `k(K)`, the left side is `1` and the residue term is `≥ 1`, so the
rational rank is `0`.  Nothing here is proved: this is a quotation. -/
def EPDimensionInequality : Prop :=
  ∀ (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF] (S : LRV.Substructure M) (e : M)
    (hunit : iUnits (iRv e)) (_hvf : iVF e),
      RVTrans S e hunit → M5Ledger.GammaHullInitial S (Substructure.closure LRV ((S : Set M) ∪ {e}))

/-! ## 3. The wiring: each quotation in the consumer-shaped lemma, and the `Standing` conclusion

Both wire into `QE/Lemma36Gamma.lean`'s proved chain, which is the frozen one-step's "separated"
branch: `GammaHullInitial` + `Γ(Ŝ)`-divisibility ⇒ Claim (⋆) in class form ⇒ `Standing T`. -/

/-- The generated substructure `⟨Ŝ,e⟩` contains `S`. -/
theorem le_closure (S : LRV.Substructure M) (e : M) :
    S ≤ Substructure.closure LRV ((S : Set M) ∪ {e}) := by
  intro x hx
  exact Substructure.subset_closure (Set.mem_union_left _ hx)

/-- `GammaBoundBy` is a `GammaHullInitial`: a uniform exponent bound is a torsion statement. -/
theorem gammaHullInitial_of_gammaBoundBy {S T : LRV.Substructure M} {m : ℕ}
    (h : GammaBoundBy (M := M) S T m) : M5Ledger.GammaHullInitial S T := by
  obtain ⟨hm, hb⟩ := h
  intro t ht hrv ht0
  obtain ⟨s, c, hsS, hsrv, hs0, hcS, hcu, heq⟩ := hb t ht hrv ht0
  exact ⟨m, s, c, hm, hsS, hsrv, hs0, hcu, heq⟩

/-- **Wiring of quotation (i)**: EP 3.3.4 in the consumer shape, for an algebraic generator. -/
theorem gammaHullInitial_of_EPFundamentalInequality (hq : EPFundamentalInequality) {S : LRV.Substructure M}
    {e : M} {n : ℕ} (hn : 1 ≤ n) (hvf : iVF e) (hunit : iUnits (iRv e))
    (halg : AlgebraicOverVF S e n) :
    M5Ledger.GammaHullInitial S (Substructure.closure LRV ((S : Set M) ∪ {e})) :=
  gammaHullInitial_of_gammaBoundBy (hq M S e n hn hvf hunit halg)

/-- **Wiring of quotation (i) all the way to the consumer**: Lemma 3.4's *value-group* half — the
extension by an algebraic unit does not grow `Γ`, hence `Standing T`. -/
theorem standing_of_EPFundamentalInequality (hq : EPFundamentalInequality) {S : LRV.Substructure M}
    {e : M} {n : ℕ} (hS : Assembly.Standing S) (hn : 1 ≤ n) (hvf : iVF e) (hunit : iUnits (iRv e))
    (halg : AlgebraicOverVF S e n) :
    Assembly.Standing (Substructure.closure LRV ((S : Set M) ∪ {e})) :=
  standing_of_gammaHullInitial (le_closure S e) hS
    (gammaHullInitial_of_EPFundamentalInequality hq hn hvf hunit halg)

/-- **Wiring of quotation (ii)**: EP 3.4.3 in the consumer shape, for a residue-transcendental
generator — this is Lemma 3.6's `Γ`-step's hypothesis. -/
theorem gammaHullInitial_of_EPDimensionInequality (hq : EPDimensionInequality) {S : LRV.Substructure M}
    {e : M} (hunit : iUnits (iRv e)) (hvf : iVF e) (htrans : RVTrans S e hunit) :
    M5Ledger.GammaHullInitial S (Substructure.closure LRV ((S : Set M) ∪ {e})) :=
  hq M S e hunit hvf htrans

/-- **Lemma 3.6's conclusion from quotation (ii)**: `Γ(Ŝ)` divisible (a component of
`Assembly.Standing S`) plus the dimension inequality give Claim (⋆) in class form, hence
`Assembly.Standing ⟨Ŝ,e⟩` — the paper's `RV(⟨Ŝ,e⟩) = ⟨RV(Ŝ), rv(e)⟩` in the frozen vocabulary. -/
theorem standing_of_EPDimensionInequality (hq : EPDimensionInequality) {S : LRV.Substructure M}
    {e : M} (hS : Assembly.Standing S) (hunit : iUnits (iRv e)) (hvf : iVF e)
    (htrans : RVTrans S e hunit) :
    Assembly.Standing (Substructure.closure LRV ((S : Set M) ∪ {e})) :=
  standing_of_gammaHullInitial (le_closure S e) hS
    (gammaHullInitial_of_EPDimensionInequality hq hunit hvf htrans)

/-! ## 4. Stress tests

### 4a. The conclusion predicates are satisfiable

`GammaBoundBy S S 1` holds for every `S` (`t¹ = t · 1` with the unit `1 ∈ S`), so
`GammaHullInitial S S` — a tree theorem — is reached by the same route, and neither predicate is
secretly `False`.  Consequently the quotations' *conclusions* are not unsatisfiable. -/

theorem gammaBoundBy_self (S : LRV.Substructure M) : GammaBoundBy (M := M) S S 1 := by
  refine ⟨by norm_num, ?_⟩
  intro t ht hrv ht0
  refine ⟨t, iRVOne, ht, hrv, ht0, M5L.rvOne_mem_sub S, ?_, ?_⟩
  · exact StandingTree.rv_one_units (M := M)
  · show Assembly.rvPow t 1 = iRVMul t iRVOne
    rw [show Assembly.rvPow t 1 = iRVMul iRVOne t from rfl,
      Transfer.rv_mul_comm_of_model hM (MulNormalForm.rv_one_mem hM) hrv]

/-- ### 4b. `m = 0` is excluded

The `0 < m` component of `GammaBoundBy` is not decoration: `m = 0` would make `rvPow t 0 = 1`
independent of `t`, so the class computation would be vacuous.  (This is the same `n = 0`
refutation as `GammaDiv.forall_root_including_zero_subsingleton`.) -/
theorem not_gammaBoundBy_zero (S T : LRV.Substructure M) : ¬ GammaBoundBy (M := M) S T 0 :=
  fun h => absurd h.1 (by norm_num)

/-- ### 4c. Variance of the two hypothesis predicates

`AlgebraicOverVF` is covariant in `S` (a bigger coefficient ring has more witnesses), and `RVTrans`
is contravariant (more allowed coefficients make the transcendence hypothesis stronger).  So the
paper's hypotheses are genuine statements about `S` and `e`, and the "coefficients in `S`" reading
is the weak/vacuous-safe side: a smaller `S` gives a weaker hypothesis, never an unsatisfiable one
for a reason unrelated to `e`. -/

theorem algebraicOverVF_mono {S S' : LRV.Substructure M} {e : M} {n : ℕ}
    (h : AlgebraicOverVF (M := M) S e n) (hSS' : S ≤ S') : AlgebraicOverVF (M := M) S' e n := by
  obtain ⟨b, hbVF, hbS, hbne, hb0⟩ := h
  exact ⟨b, hbVF, fun i => hSS' (hbS i), hbne, hb0⟩

theorem rvTrans_mono {S S' : LRV.Substructure M} {e : M} (hunit : iUnits (iRv e))
    (h : RVTrans (M := M) S e hunit) (hS'S : S' ≤ S) : RVTrans (M := M) S' e hunit := by
  intro m b hb hbS' hbne
  exact h m b hb (fun i => hS'S (hbS' i)) hbne

end SpecialTransformations.Milestone0.M8

/-! ## Axiom audit -/

#print axioms SpecialTransformations.Milestone0.M8.le_closure
#print axioms SpecialTransformations.Milestone0.M8.gammaHullInitial_of_gammaBoundBy
#print axioms SpecialTransformations.Milestone0.M8.gammaHullInitial_of_EPFundamentalInequality
#print axioms SpecialTransformations.Milestone0.M8.standing_of_EPFundamentalInequality
#print axioms SpecialTransformations.Milestone0.M8.gammaHullInitial_of_EPDimensionInequality
#print axioms SpecialTransformations.Milestone0.M8.standing_of_EPDimensionInequality
#print axioms SpecialTransformations.Milestone0.M8.gammaBoundBy_self
#print axioms SpecialTransformations.Milestone0.M8.not_gammaBoundBy_zero
#print axioms SpecialTransformations.Milestone0.M8.algebraicOverVF_mono
#print axioms SpecialTransformations.Milestone0.M8.rvTrans_mono
