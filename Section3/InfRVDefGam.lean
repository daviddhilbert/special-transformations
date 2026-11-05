/-
**`inf:RV:def:gam`** (`paper.tex:746`, Section 3) — from swarm `smw1jgnht` m7, verified here
(compiled: exit 0, 0 errors, no `sorry`; `#print axioms` on all three theorems within
{propext, Classical.choice, Quot.sound}).

The paper's statement: *"Let `A` be a definable subset of `RV`.  Let `V ⊆ Γ` be the subset such that
`γ ∈ V` if and only if `vrv⁻¹(γ) ∩ A` is nonempty and finite.  Then `V` is finite and definable."*

Stated in the `LRVΓ` expansion of `Milestone0/Encoding.lean` Part 4, which is the language the lemma
needs — this was one of the two Section 3 items the tree had recorded as *unstatable* for lack of
`Γ`-vocabulary, and that obstacle is gone.

The two hypotheses are the paper's own two uses of C-minimality, neither hidden in an axiom:
* `hbdd` — the compactness consequence: a uniform `k` bounding the finite fibres (the paper's
  second sentence); it is what produces the defining formula;
* `hCM` — "by C-minimality again `V` must be finite", in the general `A'`-form.  It is applied to
  `smallPart A = {x ∈ A : fibre(x) finite}` (definable by the explicit scheme in
  `Definability.definable_smallPart`), not to `A`, so it is not the conclusion in disguise: applied to
  `A` itself it would be useless, since a general `A` has infinite fibres.

Two things to know if this is lifted further: `hRV` (`A` avoids `∞ = rv 0`) is stronger than the
paper's `A ⊆ RV` — harmless, since the fibres over `γ ∈ Γ` never contain `∞`, but not the paper's
hypothesis; and `Vset` ranges over the whole carrier rather than over `Γ`, which
`Vset_subset_isGamma` discharges.

Check with `.scratch2/sec3/` (a compiled `Enc`): copy this file there and
`LEAN_PATH=$PWD:$LEAN_PATH lean` it.
-/
/-
`inf:RV:def:gam` (Yin, *Special transformations in algebraically closed valued fields*,
`paper.tex` line 746): *"Let `A` be a definable subset of `RV`.  Let `V ⊆ Γ` be the subset such that
`γ ∈ V` if and only if `vrv⁻¹(γ) ∩ A` is nonempty and finite.  Then `V` is finite and definable."*

This file formalizes the lemma in the `Γ`-expansion `L_RV^Γ` of `Milestone0/Encoding.lean` Part 4
(`Gamma.LRVΓ`, with the quotient map `Gamma.gVrv` and the sort predicate `Gamma.pMemGamma`), as a
statement about a single sorted carrier `M` with sort tags.

The paper's proof (verbatim):

> By C-minimality each `vrv⁻¹(γ) ∩ A` is either finite or cofinite.  By compactness there is a
> number `k` such that if `vrv⁻¹(γ) ∩ A` is finite then it has at most `k` elements.  So `V` is
> definable.  By C-minimality again `V` must be finite.

Both uses of C-minimality enter as **explicit hypotheses** of the main theorem, in the two forms the
paper uses them:

* `hbdd` — the compactness consequence of C-minimality's first use: a uniform bound `k` on the
  cardinality of the finite fibres (paper's second sentence above);
* `hCM` — C-minimality's second use: a definable subset of `RV` all of whose `vrv`-fibres are finite
  has **finite** `vrv`-image (paper's last sentence above).  It is stated for *every* definable
  subset of `RV`, not for `A`, and the proof below applies it to the *different* definable set
  `A' = {x ∈ A : vrv⁻¹(vrv x) ∩ A is finite}`, which is where the content of the argument lies.

Everything else (the two set-theoretic steps, the definability of `A'` by a single formula scheme,
and the definability of `V` as the `vrv`-image of `A'`) is proved outright: no unfinished goal, no
extra axiom, no decision by computation.

Conventions (see `Milestone0/DECISION.md`): the carrier is one-sorted with sort tags;
`Γ = RV/K^×` is the value group with a top element `⊤ = vrv 0`, and the paper's `RV` (as opposed to
`RV₀`) is `RV^× = {x ∈ RV-sort : vrv x ∈ Γ}`, i.e. the `RV`-elements whose `vrv`-value is *not* `⊤`.
The hypothesis `hRV` below records exactly that (`A ⊆ RV^×`), which is why `V ⊆ Γ` is a provable
statement here (`Vset_subset_isGamma`).
-/
import Enc

set_option linter.unusedSectionVars false

open FirstOrder FirstOrder.Language Set

namespace M7

open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.Gamma

variable {M : Type*} [Gamma.LRVΓ.Structure M]

/-! ## 1. The `Γ`-vocabulary of the expansion `L_RV^Γ`, read on the carrier -/

/-- The quotient map `vrv : RV → Γ ∪ {⊤}` of Definition 2.2 item 5 (the symbol `Gamma.gVrv`). -/
def vrv (x : M) : M :=
  Structure.funMap (L := Gamma.LRVΓ) (Sum.inr (Gamma.FnΓ.vrv)) (fun _ => x)

/-- The `Γ`-sort predicate (the symbol `Gamma.pMemGamma`): `x ∈ Γ`, i.e. `x ≠ ⊤`. -/
def isGamma (x : M) : Prop :=
  Structure.RelMap (L := Gamma.LRVΓ) (Sum.inr (Gamma.RelΓ.memGamma)) (fun _ => x)

/-- The paper's `vrv⁻¹(γ) ∩ A`, with `A` a set of `1`-tuples (i.e. a subset of the `RV` sort). -/
def fib (A : Set (Fin 1 → M)) (γ : M) : Set M := {x | (fun _ => x) ∈ A ∧ vrv x = γ}

/-- The paper's set `V`: the `γ` whose `vrv`-fibre in `A` is nonempty and finite. -/
def Vset (A : Set (Fin 1 → M)) : Set M := {γ | (fib A γ).Nonempty ∧ (fib A γ).Finite}

/-- `vrv(A)`, the set of values taken on `A`. -/
def imageOf (A : Set (Fin 1 → M)) : Set M := {γ | (fib A γ).Nonempty}

@[simp] lemma mem_fib {A : Set (Fin 1 → M)} {γ x : M} :
    x ∈ fib A γ ↔ (fun _ => x) ∈ A ∧ vrv x = γ := Iff.rfl

@[simp] lemma mem_Vset {A : Set (Fin 1 → M)} {γ : M} :
    γ ∈ Vset A ↔ (fib A γ).Nonempty ∧ (fib A γ).Finite := Iff.rfl

@[simp] lemma mem_imageOf {A : Set (Fin 1 → M)} {γ : M} :
    γ ∈ imageOf A ↔ (fib A γ).Nonempty := Iff.rfl

lemma fib_subset {A A' : Set (Fin 1 → M)} (h : A' ⊆ A) (γ : M) : fib A' γ ⊆ fib A γ :=
  fun _ hx => ⟨h hx.1, hx.2⟩

/-! ## 2. Definability of the two `vrv`-expressions and of equalities of coordinates -/

/-- `x ↦ vrv x` is a definable function of any one coordinate of a tuple. -/
lemma definableFun_vrv (P : Set M) {α : Type*} (i : α) :
    P.DefinableFun Gamma.LRVΓ (fun v : α → M => vrv (v i)) := by
  have hf : (∅ : Set M).DefinableFun Gamma.LRVΓ
      (fun w : Fin 1 → M => Structure.funMap (L := Gamma.LRVΓ) (Sum.inr (Gamma.FnΓ.vrv)) w) :=
    Set.DefinableFun.fun_symbol (L := Gamma.LRVΓ) (Sum.inr (Gamma.FnΓ.vrv))
  have hg : P.DefinableMap Gamma.LRVΓ (fun v : α → M => fun _ : Fin 1 => v i) := by
    intro j
    exact Set.DefinableFun.proj (L := Gamma.LRVΓ) (A := P)
  have hf' : P.DefinableFun Gamma.LRVΓ
      (fun w : Fin 1 → M => Structure.funMap (L := Gamma.LRVΓ) (Sum.inr (Gamma.FnΓ.vrv)) w) :=
    Set.DefinableFun.mono hf (empty_subset P)
  simpa [vrv] using Set.DefinableFun.comp (A := P) (g := fun v : α → M => fun _ : Fin 1 => v i) hg hf'

/-- Two coordinates of a tuple are equal, definably. -/
lemma definable_eq (P : Set M) {α : Type*} (i j : α) :
    P.Definable Gamma.LRVΓ {v : α → M | v i = v j} :=
  Set.DefinableFun.ofPred_eq (f := fun v : α → M => v i) (g := fun v : α → M => v j)
    (Set.DefinableFun.proj (L := Gamma.LRVΓ) (A := P) (i := i))
    (Set.DefinableFun.proj (L := Gamma.LRVΓ) (A := P) (i := j))

/-- `vrv` of two coordinates of a tuple are equal, definably. -/
lemma definable_vrv_eq (P : Set M) {α : Type*} (i j : α) :
    P.Definable Gamma.LRVΓ {v : α → M | vrv (v i) = vrv (v j)} :=
  Set.DefinableFun.ofPred_eq (f := fun v : α → M => vrv (v i)) (g := fun v : α → M => vrv (v j))
    (definableFun_vrv P i) (definableFun_vrv P j)

/-- A value `γ` is the `vrv`-value of a coordinate, definably. -/
lemma definable_vrv_eq_coord (P : Set M) {α : Type*} (i j : α) :
    P.Definable Gamma.LRVΓ {v : α → M | vrv (v i) = v j} :=
  Set.DefinableFun.ofPred_eq (f := fun v : α → M => vrv (v i)) (g := fun v : α → M => v j)
    (definableFun_vrv P i) (Set.DefinableFun.proj (L := Gamma.LRVΓ) (A := P) (i := j))

/-! ## 3. The witness box: "the fibre `vrv⁻¹(γ) ∩ A` has more than `k` elements"

The only sets whose definability is used below are cut out by the following single formula scheme:
`k+1` distinct points of `A` with one and the same `vrv`-value, together with the point they share
that value with. -/

namespace Definability

variable (P : Set M)

/-- `k+1` distinct points of `A` that all have the same `vrv`-value as the point `w (inl 0)`.
The first coordinate (`Sum.inl`) is the reference point; the `k+1` coordinates `Sum.inr i` are the
witnesses.  A point `x` has a `vrv`-fibre in `A` with more than `k` elements exactly when it can be
completed to a member of this set. -/
def BigBox (k : ℕ) (A : Set (Fin 1 → M)) : Set (Sum (Fin 1) (Fin (k + 1)) → M) :=
  {w | (∀ i : Fin (k + 1), (fun _ => w (Sum.inr i)) ∈ A) ∧
       (∀ i : Fin (k + 1), vrv (w (Sum.inr i)) = vrv (w (Sum.inl 0))) ∧
       (∀ p : Fin (k + 1) × Fin (k + 1), w (Sum.inr p.1) = w (Sum.inr p.2) → p.1 = p.2)}

/-- The points of `A` whose `vrv`-fibre in `A` has at most `k` elements.  (For an infinite fibre the
`k+1` distinct points always exist, so this is the paper's "the fibre is finite" part of `A`; see
`smallPart_eq`.) -/
def smallPart (k : ℕ) (A : Set (Fin 1 → M)) : Set (Fin 1 → M) :=
  {v | v ∈ A ∧ ¬ ∃ u : Fin (k + 1) → M, Sum.elim v u ∈ BigBox k A}

lemma mem_BigBox_iff {k : ℕ} {A : Set (Fin 1 → M)} {w : Sum (Fin 1) (Fin (k + 1)) → M} :
    w ∈ BigBox k A ↔
      (∀ i : Fin (k + 1), (fun _ => w (Sum.inr i)) ∈ A) ∧
        (∀ i : Fin (k + 1), vrv (w (Sum.inr i)) = vrv (w (Sum.inl 0))) ∧
          (∀ p : Fin (k + 1) × Fin (k + 1), w (Sum.inr p.1) = w (Sum.inr p.2) → p.1 = p.2) :=
  Iff.rfl

lemma mem_smallPart_iff {k : ℕ} {A : Set (Fin 1 → M)} {v : Fin 1 → M} :
    v ∈ smallPart k A ↔ v ∈ A ∧ ¬ ∃ u : Fin (k + 1) → M, Sum.elim v u ∈ BigBox k A :=
  Iff.rfl

/-- **`BigBox` is definable** in `L_RV^Γ` over the parameters of `A`. -/
lemma definable_BigBox {k : ℕ} {A : Set (Fin 1 → M)} (hA : P.Definable Gamma.LRVΓ A) :
    P.Definable Gamma.LRVΓ (BigBox k A) := by
  classical
  have h1 : P.Definable Gamma.LRVΓ
      {w : Sum (Fin 1) (Fin (k + 1)) → M | ∀ i : Fin (k + 1), (fun _ => w (Sum.inr i)) ∈ A} := by
    have h : ∀ i : Fin (k + 1), P.Definable Gamma.LRVΓ
        {w : Sum (Fin 1) (Fin (k + 1)) → M | (fun _ => w (Sum.inr i)) ∈ A} :=
      fun i => hA.preimage_comp (fun _ : Fin 1 => Sum.inr i)
    convert Set.definable_iInter_of_finite h using 2
    ext w
    simp
  have h2 : P.Definable Gamma.LRVΓ
      {w : Sum (Fin 1) (Fin (k + 1)) → M |
        ∀ i : Fin (k + 1), vrv (w (Sum.inr i)) = vrv (w (Sum.inl 0))} := by
    have h : ∀ i : Fin (k + 1), P.Definable Gamma.LRVΓ
        {w : Sum (Fin 1) (Fin (k + 1)) → M | vrv (w (Sum.inr i)) = vrv (w (Sum.inl 0))} :=
      fun i => definable_vrv_eq P (Sum.inr i) (Sum.inl 0)
    convert Set.definable_iInter_of_finite h using 2
    ext w
    simp
  have h3 : P.Definable Gamma.LRVΓ
      {w : Sum (Fin 1) (Fin (k + 1)) → M |
        ∀ p : Fin (k + 1) × Fin (k + 1), w (Sum.inr p.1) = w (Sum.inr p.2) → p.1 = p.2} := by
    have h : ∀ p : Fin (k + 1) × Fin (k + 1), P.Definable Gamma.LRVΓ
        {w : Sum (Fin 1) (Fin (k + 1)) → M | w (Sum.inr p.1) = w (Sum.inr p.2) → p.1 = p.2} := by
      intro p
      by_cases hp : p.1 = p.2
      · have hEq : {w : Sum (Fin 1) (Fin (k + 1)) → M |
            w (Sum.inr p.1) = w (Sum.inr p.2) → p.1 = p.2} = univ := by
          ext w
          simp [hp]
        rw [hEq]
        exact Set.definable_univ (A := P) (L := Gamma.LRVΓ)
      · have hEq : {w : Sum (Fin 1) (Fin (k + 1)) → M |
            w (Sum.inr p.1) = w (Sum.inr p.2) → p.1 = p.2} =
            {w : Sum (Fin 1) (Fin (k + 1)) → M | w (Sum.inr p.1) ≠ w (Sum.inr p.2)} := by
          ext w
          simp [hp]
        rw [hEq]
        exact (definable_eq P (Sum.inr p.1) (Sum.inr p.2)).compl
    convert Set.definable_iInter_of_finite h using 2
    ext w
    simp
  have h4 : BigBox k A = {w : Sum (Fin 1) (Fin (k + 1)) → M |
        (∀ i : Fin (k + 1), (fun _ => w (Sum.inr i)) ∈ A)} ∩
      ({w : Sum (Fin 1) (Fin (k + 1)) → M |
        ∀ i : Fin (k + 1), vrv (w (Sum.inr i)) = vrv (w (Sum.inl 0))} ∩
      {w : Sum (Fin 1) (Fin (k + 1)) → M |
        ∀ p : Fin (k + 1) × Fin (k + 1), w (Sum.inr p.1) = w (Sum.inr p.2) → p.1 = p.2}) := by
    ext w
    simp [BigBox]
  rw [h4]
  exact h1.inter (h2.inter h3)

/-- **The set `A' = {x ∈ A : vrv⁻¹(vrv x) ∩ A is finite}` is definable** in `L_RV^Γ` over the
parameters of `A`: it is `A` minus the set of points that can be completed to `k+1` distinct points
of their own fibre. -/
lemma definable_smallPart {k : ℕ} {A : Set (Fin 1 → M)} (hA : P.Definable Gamma.LRVΓ A) :
    P.Definable Gamma.LRVΓ (smallPart k A) := by
  have hbox : P.Definable Gamma.LRVΓ (BigBox k A) := definable_BigBox P hA
  have hex : P.Definable Gamma.LRVΓ
      {v : Fin 1 → M | ∃ u : Fin (k + 1) → M, Sum.elim v u ∈ BigBox k A} :=
    Set.Definable.exists_of_finite (α := Fin 1) (β := Fin (k + 1)) hbox
  have hfin : smallPart k A =
      A ∩ {v : Fin 1 → M | ∃ u : Fin (k + 1) → M, Sum.elim v u ∈ BigBox k A}ᶜ := by
    ext v
    simp [smallPart]
  rw [hfin]
  exact hA.inter hex.compl

end Definability

/-! ## 4. The combinatorial content: "at most `k` elements" = "no `k+1` distinct points" -/

/-- A finite set of cardinality `n` can be enumerated by `n` distinct points: this is the
"enumerate the witnesses" step. -/
lemma exists_inj_of_ncard_eq {t : Set M} {n : ℕ} (htfin : t.Finite) (htcard : t.ncard = n) :
    ∃ u : Fin n → M, Function.Injective u ∧ ∀ i, u i ∈ t := by
  classical
  have _ : Fintype ↥t := htfin.fintype
  have hcard : htfin.toFinset.card = n := by
    rw [← htcard, Set.ncard_eq_toFinset_card t htfin]
  let e : ↥htfin.toFinset ≃ Fin n := Finset.equivFinOfCardEq hcard
  refine ⟨fun i => ((e.symm i : ↥htfin.toFinset) : M), ?_, ?_⟩
  · intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  · intro i
    exact (Set.Finite.mem_toFinset htfin).mp (e.symm i).2

/-- An infinite set contains `k+1` distinct points. -/
lemma exists_inj_of_infinite {s : Set M} (hs : s.Infinite) (k : ℕ) :
    ∃ u : Fin (k + 1) → M, Function.Injective u ∧ ∀ i, u i ∈ s := by
  obtain ⟨t, hts, htfin, htcard⟩ := hs.exists_subset_ncard_eq (k + 1)
  obtain ⟨u, hinj, hmem⟩ := exists_inj_of_ncard_eq htfin htcard
  exact ⟨u, hinj, fun i => hts (hmem i)⟩

/-- A set of cardinality at least `k+1` contains `k+1` distinct points. -/
lemma exists_inj_of_ncard_le {s : Set M} (hfin : s.Finite) {k : ℕ} (h : k + 1 ≤ s.ncard) :
    ∃ u : Fin (k + 1) → M, Function.Injective u ∧ ∀ i, u i ∈ s := by
  obtain ⟨t, hts, htcard⟩ := Set.exists_subset_card_eq h
  have htfin : t.Finite := hfin.subset hts
  obtain ⟨u, hinj, hmem⟩ := exists_inj_of_ncard_eq htfin htcard
  exact ⟨u, hinj, fun i => hts (hmem i)⟩

open Classical in
/-- **`s` has at most `k` elements iff it contains no `k+1` distinct elements**: the pigeonhole
principle in the form used by the paper's compactness step. -/
theorem no_inj_iff_finite_ncard_le {s : Set M} {k : ℕ} :
    (¬ ∃ u : Fin (k + 1) → M, Function.Injective u ∧ ∀ i, u i ∈ s) ↔
      s.Finite ∧ s.ncard ≤ k := by
  classical
  constructor
  · intro h
    have hfin : s.Finite := by
      by_contra hf
      exact h (exists_inj_of_infinite hf k)
    refine ⟨hfin, ?_⟩
    by_contra hle
    exact h (exists_inj_of_ncard_le hfin (by omega))
  · rintro ⟨hfin, hle⟩ ⟨u, hinj, hmem⟩
    have h1 : (univ : Set (Fin (k + 1))).ncard ≤ s.ncard :=
      Set.ncard_le_ncard_of_injOn u (fun a _ => hmem a) (fun a _ b _ hab => hinj hab) hfin
    rw [Set.ncard_univ] at h1
    simp at h1
    omega

/-! ## 5. `V ⊆ Γ` -/

/-- **`V` is a subset of `Γ`**: since `A ⊆ RV = RV^×` (i.e. `vrv` of every point of `A` is a value in
`Γ`), any `γ` whose fibre is nonempty *is* such a value, hence lies in `Γ` and not at `⊤`. -/
theorem Vset_subset_isGamma {A : Set (Fin 1 → M)}
    (hRV : ∀ v ∈ A, isGamma (vrv (v 0))) : Vset A ⊆ {γ | isGamma γ} := by
  rintro γ ⟨⟨x, hxA, hxv⟩, -⟩
  rw [← hxv]
  exact hRV (fun _ => x) hxA

/-! ## 6. The three steps of the paper's proof

The paper's proof has three sentences:
"By C-minimality each `vrv⁻¹(γ) ∩ A` is either finite or cofinite.  By compactness there is a
number `k` such that if `vrv⁻¹(γ) ∩ A` is finite then it has at most `k` elements.  So `V` is
definable.  By C-minimality again `V` must be finite."

Below, the uniform bound `k` of the compactness step is a hypothesis (`hk`/`hbdd`), the set
`A' = {x ∈ A : vrv⁻¹(vrv x) ∩ A is finite}` is `Definability.smallPart k A`, and the two conclusions
"`V` is definable" and "`V` is finite" are separated into `inf_RV_def_gam_definable` and
`inf_RV_def_gam_finite`. -/

section Main

variable (P : Set M)

/-- The only tuple trick used below: for a one-termed tuple, `v` and its single entry agree. -/
lemma tuple_one_eq (v : Fin 1 → M) : (fun _ => v 0) = v := by
  funext i
  congr 1
  exact Subsingleton.elim 0 i

/-- **The compactness step, used**: with the uniform bound `k` on the finite fibres, a point `x` of
`A` lies in `A' = Definability.smallPart k A` exactly when its own `vrv`-fibre in `A` is finite.
(The `→` direction is the pigeonhole principle `no_inj_iff_finite_ncard_le`; the `←` direction uses
the bound and again the pigeonhole principle.) -/
lemma mem_smallPart_iff_fib_finite {A : Set (Fin 1 → M)} {k : ℕ}
    (hk : ∀ γ : M, (fib A γ).Finite → (fib A γ).ncard ≤ k) (x : M) :
    (fun _ => x) ∈ Definability.smallPart k A ↔ (fun _ => x) ∈ A ∧ (fib A (vrv x)).Finite := by
  classical
  rw [Definability.mem_smallPart_iff]
  constructor
  · rintro ⟨hxA, hno⟩
    refine ⟨hxA, ?_⟩
    by_contra hinf
    obtain ⟨u, hinj, hmemu⟩ := exists_inj_of_infinite hinf k
    exact hno ⟨u, by
      rw [Definability.mem_BigBox_iff]
      exact ⟨fun i => (hmemu i).1, fun i => (hmemu i).2, fun p hp => hinj hp⟩⟩
  · rintro ⟨hxA, hfin⟩
    refine ⟨hxA, ?_⟩
    rintro ⟨u, hu⟩
    rw [Definability.mem_BigBox_iff] at hu
    obtain ⟨h1, h2, h3⟩ := hu
    have hinj : Function.Injective u := fun a b hab => h3 (a, b) hab
    have hle : (fib A (vrv x)).ncard ≤ k := hk _ hfin
    have hbound : (univ : Set (Fin (k + 1))).ncard ≤ (fib A (vrv x)).ncard :=
      Set.ncard_le_ncard_of_injOn (s := univ) (t := fib A (vrv x)) u
        (fun i _ => ⟨h1 i, h2 i⟩) (fun a _ b _ hab => hinj hab) hfin
    rw [Set.ncard_univ] at hbound
    simp at hbound
    omega

/-- **`A'` has finite fibres**: the `vrv`-fibres of `A'` are the finite `vrv`-fibres of `A`. -/
lemma smallPart_fib_finite {A : Set (Fin 1 → M)} {k : ℕ}
    (hk : ∀ γ : M, (fib A γ).Finite → (fib A γ).ncard ≤ k) (γ : M) :
    (fib (Definability.smallPart k A) γ).Finite := by
  classical
  by_cases hne : (fib (Definability.smallPart k A) γ).Nonempty
  · obtain ⟨x, hx⟩ := hne
    have hxfib : (fib A (vrv x)).Finite := (mem_smallPart_iff_fib_finite hk x).mp hx.1 |>.2
    refine hxfib.subset ?_
    rintro y ⟨hy', hyv⟩
    exact ⟨(mem_smallPart_iff_fib_finite hk y).mp hy' |>.1, by rw [hyv, hx.2]⟩
  · exact Set.not_nonempty_iff_eq_empty.mp hne ▸ Set.finite_empty

/-- **`V` is the `vrv`-image of `A'`**: the values whose fibre in `A` is nonempty and finite are
exactly the values attained on `A'`. -/
lemma imageOf_smallPart {A : Set (Fin 1 → M)} {k : ℕ}
    (hk : ∀ γ : M, (fib A γ).Finite → (fib A γ).ncard ≤ k) :
    imageOf (Definability.smallPart k A) = Vset A := by
  classical
  ext γ
  constructor
  · rintro ⟨x, hx⟩
    have hxA : (fun _ => x) ∈ A := (mem_smallPart_iff_fib_finite hk x).mp hx.1 |>.1
    have hxfib : (fib A (vrv x)).Finite := (mem_smallPart_iff_fib_finite hk x).mp hx.1 |>.2
    refine ⟨⟨x, hxA, hx.2⟩, ?_⟩
    rw [← hx.2]
    exact hxfib
  · rintro ⟨⟨x, hxA, hxv⟩, hfin⟩
    refine ⟨x, ⟨(mem_smallPart_iff_fib_finite hk x).mpr ⟨hxA, ?_⟩, hxv⟩⟩
    rw [hxv]
    exact hfin

/-- **The explicit form of the paper's "So `V` is definable"**: with the uniform bound `k` of the
compactness step, `V` is literally the set of `γ` whose fibre is nonempty and has at most `k`
elements, i.e. `1 ≤ #(vrv⁻¹(γ) ∩ A) ≤ k`.  This is the set that `inf_RV_def_gam_definable` proves
definable, and it shows where the bound `k` is used: without it, the condition "finite" is not a
first-order condition of `γ`. -/
theorem Vset_eq_ncard {A : Set (Fin 1 → M)} {k : ℕ}
    (hk : ∀ γ : M, (fib A γ).Finite → (fib A γ).ncard ≤ k) :
    Vset A = {γ : M | 1 ≤ (fib A γ).ncard ∧ (fib A γ).ncard ≤ k} := by
  ext γ
  constructor
  · rintro ⟨hne, hfin⟩
    exact ⟨(Set.ncard_pos (s := fib A γ) hfin).mpr hne, hk γ hfin⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Set.nonempty_of_ncard_ne_zero (by omega), Set.finite_of_ncard_pos (by omega)⟩

/-- **Second half of `inf:RV:def:gam`** — the paper's "So `V` is definable": from the uniform bound
on the finite fibres, `V` is definable in `L_RV^Γ` over the parameters of `A`.  It is the
`vrv`-image of the definable set `A' = Definability.smallPart k A`, and a `vrv`-image is an
existential quantification. -/
theorem inf_RV_def_gam_definable (A : Set (Fin 1 → M))
    (hA : P.Definable Gamma.LRVΓ A)
    (hbdd : ∃ k, ∀ γ : M, (fib A γ).Finite → (fib A γ).ncard ≤ k) :
    ∃ Vd : Gamma.LRVΓ.DefinableSet P (Fin 1), ∀ γ : Fin 1 → M, γ ∈ Vd ↔ γ 0 ∈ Vset A := by
  classical
  obtain ⟨k, hk⟩ := hbdd
  have hS : P.Definable Gamma.LRVΓ
      {w : Sum (Fin 1) (Fin 1) → M |
        (fun _ => w (Sum.inr 0)) ∈ Definability.smallPart k A ∧
          vrv (w (Sum.inr 0)) = w (Sum.inl 0)} :=
    Set.Definable.inter
      ((Definability.definable_smallPart P hA).preimage_comp (fun _ : Fin 1 => Sum.inr 0))
      (definable_vrv_eq_coord P (Sum.inr 0) (Sum.inl 0))
  have hex : P.Definable Gamma.LRVΓ
      {γ : Fin 1 → M | ∃ u : Fin 1 → M,
        Sum.elim γ u ∈ {w : Sum (Fin 1) (Fin 1) → M |
          (fun _ => w (Sum.inr 0)) ∈ Definability.smallPart k A ∧
            vrv (w (Sum.inr 0)) = w (Sum.inl 0)}} :=
    Set.Definable.exists_of_finite (α := Fin 1) (β := Fin 1) hS
  refine ⟨⟨_, hex⟩, ?_⟩
  intro γ
  show (∃ u : Fin 1 → M, Sum.elim γ u ∈ {w : Sum (Fin 1) (Fin 1) → M |
          (fun _ => w (Sum.inr 0)) ∈ Definability.smallPart k A ∧
            vrv (w (Sum.inr 0)) = w (Sum.inl 0)}) ↔ γ 0 ∈ Vset A
  rw [← imageOf_smallPart hk]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u 0, ?_, ?_⟩
    · simpa [tuple_one_eq] using hu.1
    · simpa using hu.2
  · rintro ⟨x, hx⟩
    refine ⟨fun _ => x, ?_, ?_⟩
    · simpa [tuple_one_eq] using hx.1
    · simpa using hx.2

/-- **First half of `inf:RV:def:gam`** — the paper's "By C-minimality again `V` must be finite",
given C-minimality in the form `hCM` (a definable subset of `RV` all of whose `vrv`-fibres are
finite has finite `vrv`-image).  It is applied to `A' = Definability.smallPart k A`, not to `A`;
the finiteness of the fibres of `A'` is `smallPart_fib_finite`, and `V = vrv(A')` is
`imageOf_smallPart`. -/
theorem inf_RV_def_gam_finite (A : Set (Fin 1 → M))
    (hA : P.Definable Gamma.LRVΓ A)
    (hRV : ∀ v ∈ A, isGamma (vrv (v 0)))
    (hbdd : ∃ k, ∀ γ : M, (fib A γ).Finite → (fib A γ).ncard ≤ k)
    (hCM : ∀ A' : Set (Fin 1 → M), P.Definable Gamma.LRVΓ A' →
      (∀ v ∈ A', isGamma (vrv (v 0))) →
      (∀ γ : M, (fib A' γ).Finite) → (imageOf A').Finite) :
    (Vset A).Finite := by
  classical
  obtain ⟨k, hk⟩ := hbdd
  rw [← imageOf_smallPart hk]
  refine hCM _ (Definability.definable_smallPart P hA) (fun v hv => hRV v ?_)
    (smallPart_fib_finite hk)
  exact (Definability.mem_smallPart_iff).mp hv |>.1

/-- **`inf:RV:def:gam`** (paper §3, `paper.tex` line 746): *"Let `A` be a definable subset of `RV`.
Let `V ⊆ Γ` be the subset such that `γ ∈ V` if and only if `vrv⁻¹(γ) ∩ A` is nonempty and finite.
Then `V` is finite and definable."*

The two uses of C-minimality are the explicit hypotheses `hbdd` (with compactness, yielding the
uniform bound on the finite fibres) and `hCM` (yielding finiteness of `V`); `hRV` records the
paper's `A ⊆ RV` (as opposed to `RV₀`), i.e. that `vrv` takes values in `Γ` on `A`, which is what
makes `V` a subset of `Γ` (`Vset_subset_isGamma`). -/
theorem inf_RV_def_gam (A : Set (Fin 1 → M))
    (hA : P.Definable Gamma.LRVΓ A)
    (hRV : ∀ v ∈ A, isGamma (vrv (v 0)))
    (hbdd : ∃ k, ∀ γ : M, (fib A γ).Finite → (fib A γ).ncard ≤ k)
    (hCM : ∀ A' : Set (Fin 1 → M), P.Definable Gamma.LRVΓ A' →
      (∀ v ∈ A', isGamma (vrv (v 0))) →
      (∀ γ : M, (fib A' γ).Finite) → (imageOf A').Finite) :
    (Vset A).Finite ∧
      ∃ Vd : Gamma.LRVΓ.DefinableSet P (Fin 1), ∀ γ : Fin 1 → M, γ ∈ Vd ↔ γ 0 ∈ Vset A :=
  ⟨inf_RV_def_gam_finite P A hA hRV hbdd hCM, inf_RV_def_gam_definable P A hA hbdd⟩

end Main

/-! ## 7. What is and is not claimed here

* Definability is Mathlib's `Set.Definable` in the one-sorted language `LRVΓ = L_RV + LΓ` with
  parameters `P` (i.e. definability by *some* first-order formula of `L_RV^Γ`).  The formula that
  `inf_RV_def_gam_definable` produces is the existential quantification of a conjunction of atomic
  formulas (`vrv`-equations and equations between coordinates), hence is well sorted in the paper's
  two-sorted sense; well-sortedness itself is not asserted, only definability.
* C-minimality is *not* formalized in this file: it enters through the two hypotheses `hbdd` and
  `hCM` of `inf_RV_def_gam`, both stated for arbitrary definable sets, as in the paper's proof.
* The paper's `RV` (as opposed to `RV₀`) is recorded as `hRV : ∀ v ∈ A, isGamma (vrv (v 0))`: every
  point of `A` has a genuine value in `Γ`, which is what makes `V` a subset of `Γ`.
-/

end M7
