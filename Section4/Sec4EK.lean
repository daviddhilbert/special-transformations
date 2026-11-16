module

/-
Section 4, §4.2 "Categories of definable subsets": the paper's `𝔼_k`, the weight, and the
`RV[k,·]`-categorical consequences of Definition \ref{defn:RV:cat} that the item table of the
formalization does not list.  (paper.tex lines 986-1057 and 1230.)

The paper's own sentences formalized here:

* Definition \ref{defn:weight} (986): *"For any tuple `t̄ = (t_1, …, t_n) ∈ RV`, the weight of
  `t̄` is the number `|{i ≤ n : t_i ≠ ∞}|`."*
* Definition \ref{defn:RV:cat} (992), 1024-1027, the paragraph after the direct sums: *"Notice that the
  cartesian product of two objects `(U,f), (U',f') ∈ RV[k,·]` is the object
  `(U × U', f × f') ∈ RV[2k,·]`."*
* Definition of `𝔼_k` (1030 ff.): *"For any `(U,f) ∈ RV[k,·]` and any `F ∈ mor RV[k,·]`, let
  `𝔼_k(f)` be the function on `U` given by `ū ↦ (f(ū), ∞)`, `𝔼_k(U, f) = (U, 𝔼_k(f))`, and
  `𝔼_k(F) = F`.  Obviously `𝔼_k : RV[k,·] → RV[k+1,·]` is a functor that is faithful, full, and
  injective on objects."*
* §4.3 (1230): *"It is easily checked that `𝔼_k` induces an injective semigroup homomorphism
  `GSK RV[k,·] → GSK RV[k+1,·]`."*  Injectivity on the semigroup means injectivity on the objects
  up to isomorphism with the sum respected; what is proved here is the part that is not pure
  bookkeeping: `𝔼_k` reflects isomorphisms (and preserves them), so it is injective on isomorphism
  classes, which is exactly what "injective on `GSK`" needs.

## What is proved

* the weight calculus: `weight` is the cardinality of Definition \ref{defn:weight}
  (`weight_eq_card`), it is `≤` the length (`weight_le`), appending `∞` leaves it unchanged
  (`weight_snoc_zero`), appending a non-`∞` entry raises it by one (`weight_snoc_ne`), and it is
  **additive over the product of tuples** (`weight_append`), which is the paper's
  `(U,f) × (U',f') ∈ RV[2k,·]`.
* `𝔼_k` on objects: `EObj`, with `EObj_U` / `EObj_f`.
* `𝔼_k` **is injective on objects**: `EObj_injective` (`X.U`, `X.f` are recovered from `𝔼_k X`).
* `𝔼_k` **is full**: `EObj_surjective`, every morphism `𝔼_k X → 𝔼_k Y` is `𝔼_k H` for a morphism
  `H : X → Y`.  This is the substantive half of "a functor that is faithful, full": it needs the
  two computations `weight (snoc t ∞) = weight t` (volumetric) and "the fibre over `t : Fin k → M`
  of the padded morphism is the image under `snoc · ∞` of the fibre of `H` over
  `snoc t ∞ : Fin (k+1) → M`" (finite fibres).
* `𝔼_k` **is faithful**: `EObj_faithful`, equal images imply equal morphisms.
* `𝔼_k` **preserves and reflects isomorphisms** (`EObj_isomorphic_iff`), hence is injective on
  isomorphism classes: the `GSK`-injectivity of §4.3.
* `𝔼_k` **preserves and reflects the `RV[k]` condition** ("`f` finite-to-one"):
  `EObj_finiteToOne` / `EObj_finiteToOne_iff`, i.e. `𝔼_k : RV[k] → RV[k+1]` both ways.

## The named gaps (explicit hypotheses, never axioms)

Two things about the *encoding* of definability are carried as explicit hypotheses; neither is a
restatement of anything proved here:

* `hinf : iRV iRVZero` — `∞ ∈ RV`.  The paper's Definition 2.2 has `RV = rv(VF^×) ∪ {∞}`, so this
  is definitional there; the encoding's `rvZero` is a primitive constant whose only axiom is
  `rvZeroEq : rv(0) = ∞` (`Milestone0/Encoding.lean`), so membership in the `RV` sort has to be
  assumed here.  It is used for exactly one field: `f_sorted` of `𝔼_k(U,f)` at the appended
  coordinate.
* `PadGraph X` — definability of the graph of `𝔼_k(f)`, i.e. invariance of `SP.Definable` under
  adding one dummy coordinate.  This is the *padding* half of the missing formula-surgery API (the
  dual of the composition wall of `QE-PLAN.md`); it is `Definable`-preserved coordinate relabelling
  (`QE/ParamBridgeRelabel.lean`'s `wellSorted_relabel` supplies the formula half) and is *not*
  function composition.  It is carried per object, as `PadGraph X`, so that every statement below
  says exactly what it uses.
-/
public import Sec4Categories

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open FirstOrder FirstOrder.Language

namespace SpecialTransformations.Milestone0
open LRV

namespace SP

variable {M : Type*} [LRV.Structure M]

/-! ## Part 1. The weight (Definition \ref{defn:weight}, paper.tex line 986) -/

/-- **The weight is the cardinality of the set of coordinates different from `∞`** — Definition
\ref{defn:weight}: *"For any tuple `t̄ = (t_1, …, t_n) ∈ RV`, the weight of `t̄` is the number
`|{i ≤ n : t_i ≠ ∞}|`"*.  (Written with `Nat.card` of the subtype so that the statement needs no
`DecidablePred` instance, which the parameters of a structure do not provide.) -/
theorem weight_eq_card {k : ℕ} (t : Fin k → M) :
    weight t = Nat.card {i : Fin k // t i ≠ iRVZero} := by
  classical
  rw [weight, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.card_filter]

/-- Appending `∞` does not change the weight: the appended coordinate is one of the `i` with
`t_i = ∞`. -/
theorem weight_snoc_zero {k : ℕ} (t : Fin k → M) :
    weight (Fin.snoc t iRVZero) = weight t := by
  classical
  rw [weight, weight, Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- Appending a coordinate that is not `∞` raises the weight by one. -/
theorem weight_snoc_ne {k : ℕ} (t : Fin k → M) {a : M} (ha : a ≠ iRVZero) :
    weight (Fin.snoc t a) = weight t + 1 := by
  classical
  rw [weight, weight, Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last, ha]

/-- The weight of a `k`-tuple is at most `k`: this is what makes `(U,f) ∈ RV[k,·]` have values of
weight `≤ k`, the bound the volumetric condition compares. -/
theorem weight_le {k : ℕ} (t : Fin k → M) : weight t ≤ k := by
  classical
  rw [weight]
  calc ∑ i : Fin k, (if t i ≠ iRVZero then 1 else 0) ≤ ∑ _i : Fin k, 1 :=
        Finset.sum_le_sum fun i _ => by split <;> simp
    _ = k := by simp

/-- **The weight is additive over the product of tuples**: for `s ∈ RV^k` and `t ∈ RV^{k'}` the
weight of the concatenation `(s, t)` is `wgt(s) + wgt(t)`.  This is the paper's sentence
*"the cartesian product of two objects `(U,f), (U',f') ∈ RV[k,·]` is the object
`(U × U', f × f') ∈ RV[2k,·]`"* at the level of the value tuples (Definition \ref{defn:RV:cat}). -/
theorem weight_append {k l : ℕ} (s : Fin k → M) (t : Fin l → M) :
    weight (Fin.append s t) = weight s + weight t := by
  classical
  rw [weight, weight, weight, Fin.sum_univ_add]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by rw [Fin.append_left]
  · exact Finset.sum_congr rfl fun i _ => by rw [Fin.append_right]

/-- A tuple of `∞`'s has weight `0`: the paper's *"(`RV^0` is taken to be the singleton `{∞}`)"*
(Definition \ref{defn:RV:cat}, 992). -/
theorem weight_const_zero {k : ℕ} : weight (fun _ : Fin k => (iRVZero : M)) = 0 := by
  classical
  rw [weight]
  simp

/-- **The weight is invariant under reindexing the coordinates** — the paper's *"for any object in
`RV[k,·]` of the form `(U, pr_E)`, we may assume that `(U, pr_E)` is `(U, pr_{≤ k})` if this is more
convenient"* (paper.tex 1010), at the level of the value tuples, together with
Definition \ref{defn:weight}'s dependence on the *set* of coordinates only. -/
theorem weight_comp_perm {k : ℕ} (t : Fin k → M) (e : Fin k ≃ Fin k) :
    weight (fun i => t (e i)) = weight t := by
  classical
  simp only [weight]
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- The product of two tuples of weight `k` has weight `2k`: the paper's `(U × U', f × f') ∈
`RV[2k,·]`` discharged by `weight_append` and `weight_le`. -/
theorem weight_append_le {k l : ℕ} (s : Fin k → M) (t : Fin l → M) :
    weight (Fin.append s t) ≤ k + l := by
  rw [weight_append]
  exact Nat.add_le_add (weight_le s) (weight_le t)

variable {S : SP M} {β : Type} {sβ : β → SortTag} {A : Set (β → M)} {k : ℕ}

/-! ## Part 2. `𝔼_k` on objects

`𝔼_k(U,f) = (U, 𝔼_k(f))` with `𝔼_k(f)(ū) = (f(ū), ∞)`: the value tuple grows by one coordinate whose
entry is `∞`, while `U` stays put.  On a `RVObj` this changes only the `f`, `f_sorted` and
`graph_definable` fields; the graph of the padded function is the graph of `f` with one dummy
coordinate, which is why exactly one hypothesis is needed here. -/

/-- The paper's `ū ↦ (f(ū), ∞)` on value tuples: `appendInfty` of `QE/Sec4Categories.lean`. -/
theorem appendInfty_init {k : ℕ} (t : Fin k → M) : Fin.init (appendInfty t) = t :=
  Fin.init_snoc (α := fun _ => M) (p := t) (x := iRVZero)

theorem appendInfty_last {k : ℕ} (t : Fin k → M) : appendInfty t (Fin.last k) = iRVZero :=
  Fin.snoc_last (α := fun _ => M) (p := t) (x := iRVZero)

theorem appendInfty_castSucc {k : ℕ} (t : Fin k → M) (i : Fin k) :
    appendInfty t (Fin.castSucc i) = t i :=
  Fin.snoc_castSucc (α := fun _ => M) (p := t) (x := iRVZero) i

/-- `∞`-padding is injective on tuples. -/
theorem appendInfty_injective {k : ℕ} : Function.Injective (appendInfty (M := M) (k := k)) := by
  intro s t h
  simpa only [appendInfty_init] using congrArg Fin.init h

/-- **The padding hypothesis for `X`**: the graph of `𝔼_k(f)` is definable, i.e. `SP.Definable` is
invariant under adding one dummy coordinate.  This is the padding half of the missing formula
surgery (`QE/ParamBridgeRelabel.lean`'s `wellSorted_relabel` supplies the formula half); it is *not*
function composition, and it is stated per object so that every theorem below says exactly what it
uses.  See the file header. -/
def PadGraph (X : RVObj S sβ A k) : Prop :=
  Definable S (rvSort sβ (Fin (k + 1)))
    {z : (β ⊕ Fin (k + 1)) → M |
      baseProj z ∈ A ∧ secondPart z = appendInfty (X.f (baseProj z))}

/-- **`𝔼_k` on objects** (`paper.tex` 1030): *"let `𝔼_k(f)` be the function on `U` given by
`ū ↦ (f(ū), ∞)`, `𝔼_k(U, f) = (U, 𝔼_k(f))`"*.  The hypothesis `hinf : iRV iRVZero` is the paper's
`∞ ∈ RV`; see the file header. -/
def EObj (hinf : iRV (M := M) iRVZero) (X : RVObj S sβ A k) (hpad : PadGraph X) :
    RVObj (M := M) S sβ A (k + 1) where
  U := X.U
  U_sub := X.U_sub
  U_definable := X.U_definable
  f := fun u => appendInfty (X.f u)
  f_sorted := fun u hu i => by
    induction i using Fin.lastCases with
    | last => rw [appendInfty_last]; exact hinf
    | cast j => rw [appendInfty_castSucc]; exact X.f_sorted u hu j
  graph_definable := hpad

@[simp]
theorem EObj_U (hinf : iRV (M := M) iRVZero) (X : RVObj S sβ A k) (hpad : PadGraph X) :
    (EObj hinf X hpad).U = X.U := rfl

@[simp]
theorem EObj_f (hinf : iRV (M := M) iRVZero) (X : RVObj S sβ A k) (hpad : PadGraph X) (u : β → M) :
    (EObj hinf X hpad).f u = appendInfty (X.f u) := rfl

/-- **`𝔼_k` is injective on objects** (weak form: the two data fields are recovered).  The recovery
map is `Fin.init`: the appended coordinate is `∞`, and `Fin.init (Fin.snoc t ∞) = t`. -/
theorem EObj_injective {X Y : RVObj S sβ A k} (hinf : iRV (M := M) iRVZero)
    (hpadX : PadGraph X) (hpadY : PadGraph Y) (h : EObj hinf X hpadX = EObj hinf Y hpadY) :
    X.U = Y.U ∧ X.f = Y.f := by
  refine ⟨congrArg (fun Z => Z.U) h, funext fun u => ?_⟩
  have hf : (EObj hinf X hpadX).f = (EObj hinf Y hpadY).f :=
    congrArg (fun Z => Z.f) h
  have h2 : Fin.init ((EObj hinf X hpadX).f u) = Fin.init ((EObj hinf Y hpadY).f u) :=
    congrArg Fin.init (congrFun hf u)
  simpa only [EObj_f, appendInfty_init] using h2

/-- **`𝔼_k` is injective on objects**, full form: two objects with equal `𝔼_k` are equal. -/
theorem EObj_injective_eq {X Y : RVObj S sβ A k} (hinf : iRV (M := M) iRVZero)
    (hpadX : PadGraph X) (hpadY : PadGraph Y) (h : EObj hinf X hpadX = EObj hinf Y hpadY) :
    X = Y := by
  obtain ⟨hU, hf⟩ := EObj_injective hinf hpadX hpadY h
  obtain ⟨U₁, h1, h2, f₁, h3, h4⟩ := X
  obtain ⟨U₂, h5, h6, f₂, h7, h8⟩ := Y
  simp only at hU hf
  subst hU
  subst hf
  rfl


/-! ## Part 3. `𝔼_k` on morphisms: faithful and full

`paper.tex` 1046-1052: *"`𝔼_k(F) = F`.  Obviously `𝔼_k : RV[k,·] → RV[k+1,·]` is a functor that is
faithful, full, and injective on objects."*  The *functor* part needs the composition of morphisms,
which in these categories requires composition of definable functions (the missing wall of
`QE-PLAN.md`); what is proved here is everything the paper's sentence asserts that does not: the
object part (`EObj`), injectivity on objects (`EObj_injective`, `EObj_injective_eq`), faithfulness
(`EObj_faithful`) and fullness (`EObj_surjective`), plus the two computations that make the padded
fibre condition work. -/

/-- **`𝔼_k` on morphisms**: the same function, now a morphism of the padded objects.  The
definability field is *literally* the same proposition, since the graph of `F` does not involve the
value tuples at all. -/
def EHom (hinf : iRV (M := M) iRVZero) {X : RVObj S sβ A k} {β' : Type} {sβ' : β' → SortTag}
    {A' : Set (β' → M)} {Y : RVObj S sβ' A' k} (hpadX : PadGraph X) (hpadY : PadGraph Y)
    (H : RVHom X Y) : RVHom (EObj hinf X hpadX) (EObj hinf Y hpadY) where
  F := H.F
  F_maps := H.F_maps
  F_definable := H.F_definable
  volumetric := fun u hu => by
    have h := H.volumetric u hu
    simpa only [EObj_f, weight_appendInfty] using h
  finite_fibres := fun t => by
    by_cases ht : t (Fin.last k) = iRVZero
    · have hT : {v : Fin k → M | ∃ u, u ∈ X.U ∧ X.f u = Fin.init t ∧ v = Y.f (H.F u)}.Finite :=
        H.finite_fibres (Fin.init t)
      refine Set.Finite.subset (hT.image (fun w : Fin k → M => appendInfty w)) ?_
      rintro v ⟨u, hu, hfu, rfl⟩
      have hinit : X.f u = Fin.init t := by
        have h2 : appendInfty (X.f u) = t := hfu
        simpa only [appendInfty_init] using congrArg Fin.init h2
      exact ⟨Y.f (H.F u), ⟨u, hu, hinit, rfl⟩, rfl⟩
    · have hempty :
          {v : Fin (k + 1) → M |
            ∃ u, u ∈ (EObj hinf X hpadX).U ∧ (EObj hinf X hpadX).f u = t ∧
              v = (EObj hinf Y hpadY).f (H.F u)} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.2
        rintro v ⟨u, -, hfu, -⟩
        refine ht ?_
        rw [← hfu]
        exact appendInfty_last (X.f u)
      rw [hempty]
      exact Set.finite_empty

/-- **`𝔼_k` is faithful**: the underlying function of `𝔼_k(H)` is that of `H`, so `𝔼_k` is
injective on morphisms. -/
theorem EObj_faithful (hinf : iRV (M := M) iRVZero) {X : RVObj S sβ A k} {β' : Type}
    {sβ' : β' → SortTag} {A' : Set (β' → M)} {Y : RVObj S sβ' A' k} (hpadX : PadGraph X)
    (hpadY : PadGraph Y) {H H' : RVHom X Y}
    (h : (EHom hinf hpadX hpadY H).F = (EHom hinf hpadX hpadY H').F) : H = H' := by
  have hF : H.F = H'.F := h
  obtain ⟨F₁, m₁, d₁, v₁, f₁⟩ := H
  obtain ⟨F₂, m₂, d₂, v₂, f₂⟩ := H'
  simp only at hF
  subst hF
  rfl

/-- **The fibre of a padded morphism over `t` is the `∞`-padding of the fibre of `H` over `t`**:
the finite-fibre condition of Definition \ref{defn:RV:cat} for `𝔼_k(H)` at a tuple `t` whose last
entry is `∞`, transported back along `Fin.init`. -/
theorem EObj_fibre_finite (hinf : iRV (M := M) iRVZero) {X Y : RVObj S sβ A k}
    (hpadX : PadGraph X) (hpadY : PadGraph Y)
    (H : RVHom (EObj hinf X hpadX) (EObj hinf Y hpadY)) (t : Fin k → M) :
    {v : Fin k → M | ∃ u, u ∈ X.U ∧ X.f u = t ∧ v = Y.f (H.F u)}.Finite := by
  have hS :
      {v : Fin (k + 1) → M |
        ∃ u, u ∈ (EObj hinf X hpadX).U ∧ (EObj hinf X hpadX).f u = appendInfty t ∧
          v = (EObj hinf Y hpadY).f (H.F u)}.Finite :=
    H.finite_fibres (appendInfty t)
  refine Set.Finite.subset (hS.image (fun w : Fin (k + 1) → M => Fin.init w)) ?_
  rintro v ⟨u, hu, hfu, rfl⟩
  refine ⟨appendInfty (Y.f (H.F u)), ⟨u, hu, ?_, rfl⟩, appendInfty_init (Y.f (H.F u))⟩
  exact congrArg appendInfty hfu

/-- **`𝔼_k` is full**: every morphism `𝔼_k X → 𝔼_k Y` comes from a morphism `X → Y`.  This is the
substantive half of *"a functor that is faithful, full, and injective on objects"*: the volumetric
condition follows from `weight (snoc t ∞) = weight t`, and the finite-fibre condition is
`EObj_fibre_finite`. -/
theorem EObj_surjective (hinf : iRV (M := M) iRVZero) {X Y : RVObj S sβ A k}
    (hpadX : PadGraph X) (hpadY : PadGraph Y)
    (H : RVHom (EObj hinf X hpadX) (EObj hinf Y hpadY)) :
    ∃ H' : RVHom X Y, H'.F = H.F := by
  have hV : Volumetric X Y H.F := by
    intro u hu
    have h := H.volumetric u hu
    simpa only [EObj_f, weight_appendInfty] using h
  let H' : RVHom X Y :=
    { F := H.F, F_maps := H.F_maps, F_definable := H.F_definable, volumetric := hV,
      finite_fibres := fun t => EObj_fibre_finite hinf hpadX hpadY H t }
  exact ⟨H', rfl⟩

/-! ## Part 4. `𝔼_k` on the `RV[k]` condition and on isomorphisms

`paper.tex` 1042: *"Observe that if `(U,f) ∈ RV[k]` then `𝕃(U, f) ∈ VF[k]` and hence the restriction
`𝕃 : ob RV[k] → ob VF[k]` is well-defined."*  The `𝔼_k`-analogue is that `𝔼_k` preserves and
reflects finite-to-one `f`; §4.3 (1230) needs the isomorphism statement: *"It is easily checked
that `𝔼_k` induces an injective semigroup homomorphism `GSK RV[k,·] → GSK RV[k+1,·]`"* — injective
on isomorphism classes is `EObj_isomorphic_iff`. -/

/-- **`𝔼_k` preserves `RV[k]`**: padding does not change which points lie over a value tuple. -/
theorem EObj_finiteToOne (hinf : iRV (M := M) iRVZero) {X : RVObj S sβ A k} (hpad : PadGraph X)
    (h : X.FiniteToOne) : (EObj hinf X hpad).FiniteToOne := by
  intro t
  by_cases ht : t (Fin.last k) = iRVZero
  · have hfin := h (Fin.init t)
    refine hfin.subset ?_
    rintro u ⟨hu, hfu⟩
    refine ⟨hu, ?_⟩
    have h2 : appendInfty (X.f u) = t := hfu
    simpa only [appendInfty_init] using congrArg Fin.init h2
  · have hempty : {u : β → M | u ∈ (EObj hinf X hpad).U ∧ (EObj hinf X hpad).f u = t} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      rintro u ⟨-, hfu⟩
      refine ht ?_
      rw [← hfu]
      exact appendInfty_last (X.f u)
    rw [hempty]
    exact Set.finite_empty

/-- **`𝔼_k` reflects `RV[k]`**: if the padded `f` is finite-to-one then so is `f`. -/
theorem EObj_finiteToOne_of (hinf : iRV (M := M) iRVZero) {X : RVObj S sβ A k}
    (hpad : PadGraph X) (h : (EObj hinf X hpad).FiniteToOne) : X.FiniteToOne := by
  intro t
  have hfin := h (appendInfty t)
  refine hfin.subset ?_
  rintro u ⟨hu, hfu⟩
  exact ⟨hu, congrArg appendInfty hfu⟩

/-- **`𝔼_k : RV[k] → RV[k+1]` is well defined and conservative** for the `RV[k]` condition. -/
theorem EObj_finiteToOne_iff (hinf : iRV (M := M) iRVZero) {X : RVObj S sβ A k}
    (hpad : PadGraph X) : (EObj hinf X hpad).FiniteToOne ↔ X.FiniteToOne :=
  ⟨EObj_finiteToOne_of hinf hpad, EObj_finiteToOne hinf hpad⟩

/-- **Isomorphism in `RV[k,·]`**, in the paper's sense: a morphism whose underlying function is a
bijection with a morphism as inverse.  (Composition of morphisms is not used, so this is available
without the composition wall.) -/
def RVIsIso {X : RVObj S sβ A k} {β' : Type} {sβ' : β' → SortTag} {A' : Set (β' → M)}
    {Y : RVObj S sβ' A' k} (H : RVHom X Y) : Prop :=
  ∃ K : RVHom Y X, (∀ u, K.F (H.F u) = u) ∧ (∀ v, H.F (K.F v) = v)

/-- **`X` and `Y` are isomorphic in `RV[k,·]`**. -/
def RVIsomorphic (X : RVObj S sβ A k) {β' : Type} {sβ' : β' → SortTag} {A' : Set (β' → M)}
    (Y : RVObj S sβ' A' k) : Prop :=
  ∃ H : RVHom X Y, RVIsIso H

/-- `𝔼_k` carries isomorphisms to isomorphisms. -/
theorem RVIsIso.ehom (hinf : iRV (M := M) iRVZero) {X : RVObj S sβ A k}
    {β' : Type} {sβ' : β' → SortTag} {A' : Set (β' → M)} {Y : RVObj S sβ' A' k}
    (hpadX : PadGraph X) (hpadY : PadGraph Y) {H : RVHom X Y} (hiso : RVIsIso H) :
    RVIsIso (EHom hinf hpadX hpadY H) := by
  obtain ⟨K, h1, h2⟩ := hiso
  exact ⟨EHom hinf hpadY hpadX K, h1, h2⟩

/-- **`𝔼_k` reflects isomorphisms** — the injectivity on isomorphism classes that §4.3's *"`𝔼_k`
induces an injective semigroup homomorphism"* needs.  It is fullness applied to both directions:
the inverse of a padded morphism is itself padded. -/
theorem EObj_isomorphic_iff (hinf : iRV (M := M) iRVZero) {X Y : RVObj S sβ A k}
    (hpadX : PadGraph X) (hpadY : PadGraph Y) :
    RVIsomorphic (EObj hinf X hpadX) (EObj hinf Y hpadY) ↔ RVIsomorphic X Y := by
  constructor
  · rintro ⟨H, K, h1, h2⟩
    obtain ⟨H', hHF⟩ := EObj_surjective hinf hpadX hpadY H
    obtain ⟨K', hKF⟩ := EObj_surjective hinf hpadY hpadX K
    refine ⟨H', K', fun u => ?_, fun v => ?_⟩
    · rw [congrFun hHF u, congrFun hKF (H.F u)]
      exact h1 u
    · rw [congrFun hKF v, congrFun hHF (K.F v)]
      exact h2 v
  · rintro ⟨H, K, h1, h2⟩
    exact ⟨EHom hinf hpadX hpadY H, EHom hinf hpadY hpadX K, h1, h2⟩

end SP

end SpecialTransformations.Milestone0
