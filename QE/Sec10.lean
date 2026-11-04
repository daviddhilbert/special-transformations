/-
**Section 10, part 1: `defn:mVF:cat:vol` and `mor:equi` — the `VF`-categories with volume forms.**

Yin, *Special transformations in algebraically closed valued fields* (arXiv:1006.2467),
`\section{Categories with volume forms}` (`paper.tex` line 2195 ff.): Definition
`defn:mVF:cat:vol` (line 2201) and Remark `mor:equi` (line 2223).

Per the standing instruction this file is written **independently of Sections 6-9**: everything
§10 takes from earlier sections is carried as an explicit `Prop`-valued hypothesis or as a
structure field, never as an `axiom` and never as a `sorry`, and each such hypothesis quotes the
paper's own sentence and label in its docstring:

* §2 — `RVLaws`: the multiplicative laws of `RV^×` (Definition 2.1/2.2 items 2 and 6);
* §4 — `Small` (the paper's *"definable subsets of `A`, `A'` of `VF`-dimension `< k`"*) and
  `DimLayer`: the three dimension/definability facts about it that the tree lacks;
* §9 — `Jcb`: Definition `defn:diff`'s Jacobian `Jcb_VF` together with Lemma `jcb:chain`, the
  sentence *"the Jacobian of the identity map is equal to 1 almost everywhere"* of `mor:equi`,
  and the a.e. locality of the Jacobian.

Everything else — the objects, the morphisms, the identity morphism, composition, and the
conclusion of Remark `mor:equi` that every morphism is an isomorphism (i.e. that the inverse of a
morphism is again measure-preserving) — is proved here, with `#print axioms` footprint
`propext, Classical.choice, Quot.sound`, no `sorry` and no `axiom`.  The other half of
Remark `mor:equi` (that morphisms agreeing almost everywhere may be identified) is **not** in this
file: it is recorded as open in the report.
-/
import Sec4Dim

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open FirstOrder FirstOrder.Language

namespace SpecialTransformations.Milestone0
open LRV

namespace Sec10

open Sec4Dim

variable {M : Type*} [LRV.Structure M]

/-! ## Part 1. Definable functions into the carrier

`QE/Sec4Dim.lean`'s `DefinableFun` is definability of a function *into a power* `VF^k × RV^l`.
§10's volume forms `ω : A → RV^×` and `ω : A → Γ` are functions into a *single* sort, so that case
is recorded separately here. -/

/-- The variable assignment `(x̄, y)`: the tuple `x̄` in the block of `n + m` free variables and the
single value `y` in the last one. -/
def assign1 {n m : ℕ} (x : Tup M n m) (y : M) : Fin ((n + m) + 1) → M :=
  Fin.append (fun t => x (finSumFinEquiv.symm t)) (fun _ => y)

@[simp]
theorem assign1_left {n m : ℕ} (x : Tup M n m) (y : M) (t : Fin (n + m)) :
    assign1 x y (Fin.castAdd 1 t) = x (finSumFinEquiv.symm t) := Fin.append_left _ _ t

@[simp]
theorem assign1_right {n m : ℕ} (x : Tup M n m) (y : M) (i : Fin 1) :
    assign1 x y (Fin.natAdd (n + m) i) = y := Fin.append_right _ _ i

/-- **`f : A → M` is `S`-definable, with values of sort `s`**: the graph of `f` on `A` is cut out by
a well-sorted formula of `L_RV` whose last free variable has sort `s`.  This is `DefinableFun` of
`QE/Sec4Dim.lean` for a one-coordinate target. -/
def DefinableFun1 (S : SP M) {n m : ℕ} (A : Set (Tup M n m)) (s : SortTag)
    (f : Tup M n m → M) : Prop :=
  (∀ x ∈ A, sortEval s (f x)) ∧
    ∃ φ : LRV.BoundedFormula (Fin S.n ⊕ Fin S.m) ((n + m) + 1),
      WellSorted S.sortMap (Fin.append (fSort n m) (fun _ => s)) φ ∧
        ∀ x : Tup M n m, x ∈ A → ∀ y : M, sortEval s y →
          (φ.Realize S.toFun (assign1 x y) ↔ f x = y)

/-- A function definable on `B` is definable on any `A ⊆ B`: the definition asks only for the graph
on the domain (the same formula witnesses both). -/
theorem DefinableFun1.mono {S : SP M} {n m : ℕ} {A B : Set (Tup M n m)} {s : SortTag}
    {f : Tup M n m → M} (hAB : A ⊆ B) (hf : DefinableFun1 S B s f) :
    DefinableFun1 S A s f := by
  refine ⟨fun x hx => hf.1 x (hAB hx), ?_⟩
  obtain ⟨φ, hφ, h⟩ := hf.2
  exact ⟨φ, hφ, fun x hx => h x (hAB hx)⟩

/-! ## Part 2. The paper's "`VF`-dimension `< k`" and the dimension layer of §4

§10's a.e. conditions are *"defined outside of definable subsets of `A`, `A'` of `VF`-dimension
`< k`"*.  `QE/Sec4Dim.lean` supplies `dim_VF` (`dimVF`) and its elementary theory; `Small` below is
the paper's phrase, and `DimLayer` records the §4 facts about it that the tree does not have. -/

/-- **The paper's "definable subset of `VF`-dimension `< k`"** (Definition `defn:mVF:cat:vol`):
*"a bijection that is defined outside of definable subsets of `A`, `A'` of `VF`-dimension `< k`"*.
The dimension is `QE/Sec4Dim.lean`'s `dim_VF` (the paper's, `paper.tex` line 807). -/
def Small (S : SP M) (k : ℕ) {n m : ℕ} (B : Set (Tup M n m)) : Prop := dimVF S B < k

variable {S : SP M} {k : ℕ}

/-- A subset of a set of `VF`-dimension `< k` has `VF`-dimension `< k` — `dimVF_mono` of §4. -/
theorem small_subset {n m : ℕ} {B C : Set (Tup M n m)} (hBC : B ⊆ C) (h : Small S k C) :
    Small S k B := lt_of_le_of_lt (dimVF_mono S hBC) h

/-- The empty set has `VF`-dimension `0` (`HasDim` for `∅` is witnessed by `VF^0 × RV^0`), hence
`VF`-dimension `< k` for `k > 0`. -/
theorem hasDim_empty (S : SP M) {n m : ℕ} : HasDim S (∅ : Set (Tup M n m)) 0 := by
  refine ⟨0, le_rfl, 0, fun _ => ⟨fun i => Sum.elim (fun j : Fin 0 => Fin.elim0 j) (fun j : Fin 0 => Fin.elim0 j) i,
      fun i => Sum.elim (fun j : Fin 0 => Fin.elim0 j) (fun j : Fin 0 => Fin.elim0 j) i⟩, ?_, ?_⟩
  · refine ⟨⊤, wellSorted_top S.sortMap _, ?_⟩
    intro x hx
    exact absurd hx (by simp)
  · intro y
    simp

theorem small_empty (S : SP M) {k : ℕ} (hk : 0 < k) {n m : ℕ} :
    Small S k (∅ : Set (Tup M n m)) := by
  have h : dimVF S (∅ : Set (Tup M n m)) = 0 :=
    Nat.le_antisymm (Nat.sInf_le (hasDim_empty S)) (Nat.zero_le _)
  rw [Small, h]; exact hk

/-- **The §4 layer that §10 uses.**  Facts about the `VF`-dimension and about definability that the
paper uses without comment in §10 and that `QE/Sec4Dim.lean` does not have (it has `dimVF_mono`,
i.e. `small_subset`, only).  Each is a theorem of the paper's §4, not of §10:

* `small_union`: a finite union of subsets of `VF`-dimension `< k` has `VF`-dimension `< k`
  (§4: `dim_VF(A ∪ B) ≤ max(dim_VF A, dim_VF B)`);
* `small_image`: *the image of a definable set of `VF`-dimension `< k` under a definable function
  has `VF`-dimension `< k`* (§4: `dim_VF` is monotone under definable images — the paper uses this
  when it writes, in §9, *"the subset of those `f(x̄) ∈ A` such that `Jcb F` is not defined is of
  dimension `< n`"*);
* `comp`: definable functions compose.

`comp` is not a numbered statement of the paper but a fact of the encoding's metatheory that the
paper uses silently everywhere (substituting one definable function into another).  It is missing
exactly as `QE/Sec4Categories.lean`'s header and `QE-PLAN.md` ("the one wall, three times") record:
`Definable`/`DefinableFun` are not known to be closed under preimage or composition along a
definable map, because renaming free variables by the terms of another definable function is not
available for `LRV.Term.subst`.  §10's closure lemmas need it in this one form. -/
structure DimLayer (S : SP M) (k : ℕ) : Prop where
  small_union : ∀ {n m : ℕ} {B C : Set (Tup M n m)},
    Small S k B → Small S k C → Small S k (B ∪ C)
  small_image : ∀ {n m n' m' : ℕ} {B : Set (Tup M n m)} {f : Tup M n m → Tup M n' m'},
    DefinableFun S B f → Small S k B → Small S k (f '' B)
  comp : ∀ {n m n' m' n'' m'' : ℕ} {A : Set (Tup M n m)} {A' : Set (Tup M n' m')}
    {f : Tup M n m → Tup M n' m'} {g : Tup M n' m' → Tup M n'' m''},
    DefinableFun S A f → DefinableFun S A' g → (∀ x ∈ A, f x ∈ A') →
    DefinableFun S A (fun x => g (f x))

variable (D : DimLayer S k)

/-- Finite unions of sets of `VF`-dimension `< k` have `VF`-dimension `< k`. -/
theorem small_biUnion {n m : ℕ} {ι : Type} (D : DimLayer S k) (hk : 0 < k) (s : Finset ι)
    (Bs : ι → Set (Tup M n m)) (h : ∀ i ∈ s, Small S k (Bs i)) :
    Small S k (⋃ i ∈ (s : Set ι), Bs i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hz : (⋃ i ∈ ((∅ : Finset ι) : Set ι), Bs i) = (∅ : Set (Tup M n m)) := by
        ext x; simp
      rw [hz]
      exact small_empty S hk
  | insert a s ha ih =>
      have hstep : (⋃ i ∈ ((insert a s : Finset ι) : Set ι), Bs i) =
          Bs a ∪ ⋃ i ∈ (s : Set ι), Bs i := by
        ext x; simp [exists_prop]
      rw [hstep]
      exact D.small_union (h a (by simp)) (ih (fun i hi => h i (by simp [hi])))

/-- The image of a set of `VF`-dimension `< k` under a definable function has `VF`-dimension
`< k`: the §4 monotonicity of `dim_VF` under definable images. -/
theorem small_image (D : DimLayer S k) {n m n' m' : ℕ} {B : Set (Tup M n m)}
    {f : Tup M n m → Tup M n' m'} (hf : DefinableFun S B f) (hB : Small S k B) :
    Small S k (f '' B) :=
  D.small_image hf hB

/-! ## Part 3. The multiplicative laws of `RV^×` (Definition 2.2 items 2 and 6)

§10's morphism conditions are equations in `RV^×`, and the closure lemmas rewrite with them.  The
paper's `RV^× = K^×/(1 + MM) = RV ∖ {rv 0}` is a divisible abelian group (Definition 2.2 item 2) and
`rv : VF → RV` is multiplicative (item 6).  `Milestone0/Encoding.lean` states these as the sentences
`rvMulMem`, `rvMulAssoc`, `rvMulComm`, `rvMulOne`, `rvMulInfty`, `rvMulOneRV`, `rvMulHom` of
`Axioms.rvGroup` / `Axioms.rvAxioms`; reading them semantically needs the
satisfaction-instantiation bridge, which §10 does not contain, so they are carried here as one
named hypothesis. -/
structure RVLaws (M : Type*) [LRV.Structure M] : Prop where
  /-- `Kˣ` is closed under `×` (`Axioms.rvMulMem`) -/
  mul_rv : ∀ {a b : M}, iRV a → iRV b → iRV (iRVMul a b)
  /-- the absorbing element: `t × 0 = 0`, i.e. `t × ∞ = ∞` (`Axioms.rvMulInfty`) -/
  mul_zero : ∀ (a : M), iRVMul a iRVZero = iRVZero
  /-- the product of two nonzero `RV`-elements is nonzero (the group axioms of `Axioms.rvGroup`
  together with `Axioms.rvMulInfty`) -/
  mul_ne : ∀ {a b : M}, iRV a → iRV b → a ≠ iRVZero → b ≠ iRVZero → iRVMul a b ≠ iRVZero
  /-- `0 ≠ 1` in `RV` (`Axioms.kField`) -/
  one_ne : iRVOne (M := M) ≠ iRVZero
  /-- `×` is associative (`Axioms.rvMulAssoc`) -/
  mul_assoc : ∀ {a b c : M}, iRV a → iRV b → iRV c →
    iRVMul (iRVMul a b) c = iRVMul a (iRVMul b c)
  /-- `×` is commutative (`Axioms.rvMulComm`) -/
  mul_comm : ∀ {a b : M}, iRV a → iRV b → iRVMul a b = iRVMul b a
  /-- `1` is neutral for `×` on `RV^×` (`Axioms.rvMulOne`, repaired: `Axioms.rvMulOneRV`) -/
  mul_one : ∀ {a : M}, iRV a → a ≠ iRVZero → iRVMul a iRVOne = a
  /-- `rv` of a `VF`-element is an `RV`-element -/
  rv_rv : ∀ {x : M}, iVF x → iRV (iRv x)
  /-- `rv` is multiplicative (`Axioms.rvMulHom`) -/
  rv_mul : ∀ {x y : M}, iVF x → iVF y → iRv (iVFMul x y) = iRVMul (iRv x) (iRv y)

/-- In a group, `d ≠ 0` follows from `c · d = 1`: if `d = 0` then `c · d = 0 ≠ 1`. -/
theorem ne_zero_of_mul_eq_one (R : RVLaws M) {c d : M} (hcd : iRVMul c d = iRVOne) :
    d ≠ iRVZero := by
  intro h0
  rw [h0, R.mul_zero] at hcd
  exact R.one_ne hcd.symm

/-! ## Part 4. The §9 Jacobian, as §10 uses it

Definition `defn:diff` (`paper.tex:1966`) defines the derivative of a definable `f : VF^n → VF^m`
and, *"if `n = n'` and all the partial derivatives exist at a point"*, *"the Jacobian of `f` …, the
determinant of the Jacobian matrix, … denoted by `Jcb_VF f(x̄)`"* (line 2039).  §10 needs four facts
about it, each carried below as a field:

* the Jacobian of a composite is the product of the Jacobians — Lemma `jcb:chain` (line 2049):
  *"Let `f : A → B` and `g : B → C` be definable functions. Then for any `x̄ ∈ A`,
  `Jcb_VF (g ∘ f)(x̄) = Jcb_VF g(f(x̄)) · Jcb_VF f(x̄)`, if both sides are defined."*  The paper's
  Jacobian is a *partial* function, defined almost everywhere (§9 after `defn:diff`); the field
  `jcb_chain` states the identity off a set of `VF`-dimension `< k`, which is the form §10 uses;
* `Jcb_VF` of the identity is `1` — Remark `mor:equi`: *"the Jacobian of the identity map is equal
  to `1` almost everywhere"*;
* the Jacobian is a *local* notion, determined up to a set of `VF`-dimension `< k` by the values of
  the function on a set of `VF`-dimension `< k`'s complement — this is what makes the paper's
  *"by Lemma `jcb:chain`, every morphism is actually an isomorphism"* go through: only
  `Jcb_VF(F⁻¹ ∘ F) = Jcb_VF id` is needed, and `F⁻¹ ∘ F = id` off a set of `VF`-dimension `< k`;
* `Jcb_VF` takes values in `VF` (`Jcb_VF f` is a determinant of a matrix over `VF`).

`J` is total on all functions, whereas the paper's `Jcb_VF` is defined only a.e. on definable
functions: this is the totalisation used by every a.e. statement (the paper's own convention for
`dom(F)`).  Nothing is assumed beyond these four facts. -/
structure Jcb (S : SP M) (k : ℕ) where
  /-- the Jacobian `Jcb_VF f(x̄)` of Definition `defn:diff`, totalised off its a.e. domain -/
  J : ∀ {n m n' m' : ℕ}, (Tup M n m → Tup M n' m') → Tup M n m → M
  /-- `Jcb_VF f(x̄)` is an element of the `VF` sort for every `x̄` (choose the totalisation to be
  `0` where the Jacobian is undefined) -/
  J_vf : ∀ {n m n' m'} (f : Tup M n m → Tup M n' m') (x : Tup M n m), iVF (J f x)
  /-- **Lemma `jcb:chain`** at the `rv`-stage, off a set of `VF`-dimension `< k` -/
  jcb_chain : ∀ {n m n' m' n'' m'' : ℕ} (A : Set (Tup M n m)) (B : Set (Tup M n' m'))
    (f : Tup M n m → Tup M n' m') (g : Tup M n' m' → Tup M n'' m''),
    DefinableFun S A f → DefinableFun S B g →
    Small S k {x : Tup M n m | x ∈ A ∧
      iRv (J (fun y => g (f y)) x) ≠ iRVMul (iRv (J g (f x))) (iRv (J f x))}
  /-- Remark `mor:equi`: *"the Jacobian of the identity map is equal to `1` almost everywhere"* -/
  jcb_id : ∀ {n m : ℕ},
    Small S k {x : Tup M n m | iRv (J (id : Tup M n m → Tup M n m) x) ≠ iRVOne}
  /-- the Jacobian is determined by the function off a set of `VF`-dimension `< k` -/
  jcb_loc : ∀ {n m n' m' : ℕ} (A B : Set (Tup M n m)) (f g : Tup M n m → Tup M n' m'),
    DefinableFun S A f → DefinableFun S A g → B ⊆ A → Small S k (A \ B) →
    (∀ x ∈ B, f x = g x) →
    Small S k {x : Tup M n m | x ∈ B ∧ iRv (J f x) ≠ iRv (J g x)}

/-! ## Part 5. Definable essential bijections (Definition `defn:mVF:cat:vol`)

*"A morphism between two objects `(A, ω)`, `(A', ω')` is a definable **essential bijection**
`F : A → A'`, that is, a bijection that is defined outside of definable subsets of `A`, `A'` of
`VF`-dimension `< k`"*. -/
structure EssBij (S : SP M) (k : ℕ) {n m : ℕ} (A : Set (Tup M n m))
    {n' m' : ℕ} (A' : Set (Tup M n' m')) where
  /-- the paper's `dom(F) ⊆ A` -/
  dom : Set (Tup M n m)
  dom_sub : dom ⊆ A
  /-- `F` is defined outside of a definable subset of `A` of `VF`-dimension `< k` -/
  small_compl_dom : Small S k (A \ dom)
  /-- the function `F`, totalised off `dom` -/
  toFun : Tup M n m → Tup M n' m'
  maps : ∀ x ∈ dom, toFun x ∈ A'
  /-- `F` is a bijection: injective on `dom` -/
  injOn : Set.InjOn toFun dom
  /-- `F` is definable -/
  definable : DefinableFun S dom toFun
  /-- `F` is defined outside of a definable subset of `A'` of `VF`-dimension `< k` -/
  small_compl_image : Small S k (A' \ toFun '' dom)
  /-- the inverse map `F⁻¹`, totalised off `F '' dom` -/
  inv : Tup M n' m' → Tup M n m
  /-- the inverse is definable.  (That the inverse of a definable bijection is definable is a fact
  of the encoding's metatheory, not of §10: it needs the quantifier manipulation recorded in
  `QE/Sec4Categories.lean`'s header, so it is carried here as data.) -/
  inv_definable : DefinableFun S (toFun '' dom) inv
  inv_left : ∀ x ∈ dom, inv (toFun x) = x
  inv_right : ∀ y ∈ toFun '' dom, toFun (inv y) = y

namespace EssBij

variable {A : Set (Tup M n m)} {A' : Set (Tup M n' m')}

/-- `F⁻¹` maps `F '' dom` back into `dom`. -/
theorem inv_maps (E : EssBij S k A A') : ∀ y ∈ E.toFun '' E.dom, E.inv y ∈ E.dom := by
  rintro y ⟨x, hx, rfl⟩
  rw [E.inv_left x hx]
  exact hx

/-- The inverse map is injective on its domain. -/
theorem inv_injOn (E : EssBij S k A A') : Set.InjOn E.inv (E.toFun '' E.dom) := by
  rintro _ ⟨x₁, hx₁, rfl⟩ _ ⟨x₂, hx₂, rfl⟩ h
  rw [E.inv_left x₁ hx₁, E.inv_left x₂ hx₂] at h
  rw [h]

/-- The inverse of an essential bijection maps `A'` into `A` up to a set of `VF`-dimension `< k`,
and it maps onto `A` up to such a set. -/
theorem image_inv_image (E : EssBij S k A A') : E.inv '' (E.toFun '' E.dom) = E.dom := by
  ext x
  constructor
  · rintro ⟨y, ⟨x', hx', rfl⟩, rfl⟩
    rw [E.inv_left x' hx']
    exact hx'
  · intro hx
    exact ⟨E.toFun x, ⟨x, hx, rfl⟩, E.inv_left x hx⟩

end EssBij

/-! ## Part 6. The category `mVF[k,·]` of Definition `defn:mVF:cat:vol`

*"An object in the category `mVF[k, ·]` is a definable pair `(A, ω)`, where `pvf(A) ⊆ VF^k` and
`ω : A → RV^×` is a function.  The latter is understood as a *definable `RV`-volume form* on `A`."*

`pvf(A) ⊆ VF^k` is the paper's notation for `A ∈ VF[k,·]`: `A` is a definable subset of `VF`-dimension
`≤ k` (§4, Definition `defn:VF:cat`), which in the encoding is `HasDim S A k`. -/

variable {n m n' m' n'' m'' : ℕ}

structure MVFObj (S : SP M) (k : ℕ) (n m : ℕ) where
  /-- the definable set `A ⊆ VF^n × RV^m` -/
  A : Set (Tup M n m)
  A_definable : Definable S A
  /-- `A ∈ VF[k,·]`: `A` has `VF`-dimension `≤ k` (Definition `defn:VF:cat`) -/
  dim_le : HasDim S A k
  /-- the volume form `ω : A → RV^×` -/
  omega : Tup M n m → M
  /-- `ω` takes values in `RV^× = RV ∖ {rv 0}` -/
  omega_ne : ∀ x ∈ A, omega x ≠ iRVZero
  /-- `ω` is definable (and `RV`-sorted) -/
  omega_definable : DefinableFun1 S A .rv omega

/-- **A morphism of `mVF[k,·]`** (Definition `defn:mVF:cat:vol`): *"A morphism between two objects
`(A, ω)`, `(A', ω')` is a definable essential bijection `F : A → A'` … such that for every
`x̄ ∈ dom(F)`, `ω(x̄) = ω'(F(x̄)) · rv(Jcb_VF F(x̄))`.  We also say that such an `F` is an
`RV`-measure-preserving map."*

`good` is the paper's `dom(F)` on which the measure-preserving identity is required; by definition
its complement in `A` has `VF`-dimension `< k`.  (The paper's `dom(F)` is the set where the
*equation* holds, since `F`, `ω`, `ω'` and `Jcb_VF F` are totalised off their a.e. domains.) -/
structure MVFHom (J : Jcb S k) {n m : ℕ} (X : MVFObj S k n m) {n' m' : ℕ}
    (Y : MVFObj S k n' m') where
  /-- the definable essential bijection `F : A → A'` -/
  E : EssBij S k X.A Y.A
  /-- the paper's `dom(F)` -/
  good : Set (Tup M n m)
  good_sub : good ⊆ E.dom
  /-- `F` is defined outside of a definable subset of `A` of `VF`-dimension `< k` -/
  small_compl : Small S k (X.A \ good)
  /-- **the measure-preserving identity of Definition `defn:mVF:cat:vol`** -/
  vol : ∀ x ∈ good, X.omega x = iRVMul (Y.omega (E.toFun x)) (iRv (J.J E.toFun x))

namespace MVFHom

variable {J : Jcb S k} {X : MVFObj S k n m} {Y : MVFObj S k n' m'} {Z : MVFObj S k n'' m''}

/-- **The identity is a morphism** — Remark `mor:equi`: *"since the Jacobian of the identity map is
equal to `1` almost everywhere"*, the identity map is measure-preserving a.e., hence a morphism. -/
def idHom (R : RVLaws M) (hk : 0 < k) (X : MVFObj S k n m) : MVFHom J X X where
  E :=
    { dom := X.A
      dom_sub := fun _ hx => hx
      small_compl_dom := by
        have h : X.A \ X.A = (∅ : Set (Tup M n m)) := by ext x; simp
        rw [h]; exact small_empty S hk
      toFun := id
      maps := fun _ hx => hx
      injOn := fun _ _ _ _ h => h
      definable := definableFun_id S X.A
      small_compl_image := by
        have h : X.A \ id '' X.A = (∅ : Set (Tup M n m)) := by ext x; simp
        rw [h]; exact small_empty S hk
      inv := id
      inv_definable := DefinableFun.mono (A := id '' X.A) (B := X.A)
        (fun x hx => by simpa using hx) (definableFun_id S X.A)
      inv_left := fun _ _ => rfl
      inv_right := fun _ _ => rfl }
  good := {x | x ∈ X.A ∧ iRv (J.J (id : Tup M n m → Tup M n m) x) = iRVOne}
  good_sub := fun x hx => hx.1
  small_compl :=
    small_subset (fun x hx => by
      rcases hx with ⟨hxA, hxnot⟩
      exact fun h1 => hxnot ⟨hxA, h1⟩) (J.jcb_id)
  vol := by
    intro x hx
    have hr : iRV (X.omega x) := X.omega_definable.1 x hx.1
    have hn : X.omega x ≠ iRVZero := X.omega_ne x hx.1
    show X.omega x = iRVMul (X.omega (id x)) (iRv (J.J id x))
    rw [hx.2]
    exact (R.mul_one hr hn).symm

/-- **Morphisms compose**: Definition `defn:mVF:cat:vol`'s measure-preserving maps are closed under
composition, by Lemma `jcb:chain` at the `rv`-stage and the multiplicative laws of `RV^×`. -/
def comp (D : DimLayer S k) (R : RVLaws M) (F : MVFHom J X Y) (G : MVFHom J Y Z) :
    MVFHom J X Z where
  E :=
    { dom := {x | x ∈ F.E.dom ∧ F.E.toFun x ∈ G.E.dom}
      dom_sub := fun _ hx => F.E.dom_sub hx.1
      small_compl_dom := by
        have hB : Small S k ((F.E.toFun '' F.E.dom) \ G.E.dom) := by
          refine small_subset (fun x hx => ?_) G.small_compl
          obtain ⟨y, hy, rfl⟩ := hx.1
          exact ⟨F.E.maps y hy, fun hG => hx.2 (G.good_sub hG)⟩
        have himg : Small S k (F.E.inv '' ((F.E.toFun '' F.E.dom) \ G.E.dom)) :=
          D.small_image (DefinableFun.mono (A := (F.E.toFun '' F.E.dom) \ G.E.dom)
            (fun x hx => hx.1) F.E.inv_definable) hB
        refine small_subset (C := (X.A \ F.E.dom) ∪ F.E.inv '' ((F.E.toFun '' F.E.dom) \ G.E.dom))
          (fun x hx => ?_) (D.small_union F.E.small_compl_dom himg)
        by_cases h1 : x ∈ F.E.dom
        · right
          exact ⟨F.E.toFun x, ⟨⟨x, h1, rfl⟩, fun hG => hx.2 ⟨h1, hG⟩⟩, F.E.inv_left x h1⟩
        · left; exact ⟨hx.1, h1⟩
      toFun := fun x => G.E.toFun (F.E.toFun x)
      maps := fun x hx => G.E.maps (F.E.toFun x) hx.2
      injOn := by
        intro x₁ hx₁ x₂ hx₂ h
        exact F.E.injOn hx₁.1 hx₂.1 (G.E.injOn hx₁.2 hx₂.2 h)
      definable := D.comp (DefinableFun.mono (fun x hx => hx.1) F.E.definable) G.E.definable
        (fun x hx => hx.2)
      small_compl_image := by
        have hB : Small S k (G.E.dom \ F.E.toFun '' F.E.dom) := by
          refine small_subset (C := Y.A \ F.E.toFun '' F.E.dom) (fun x hx => ?_)
            F.E.small_compl_image
          exact ⟨G.E.dom_sub hx.1, hx.2⟩
        have himg : Small S k (G.E.toFun '' (G.E.dom \ F.E.toFun '' F.E.dom)) :=
          D.small_image (DefinableFun.mono (A := G.E.dom \ F.E.toFun '' F.E.dom)
            (fun x hx => hx.1) G.E.definable) hB
        refine small_subset (C := (Z.A \ G.E.toFun '' G.E.dom) ∪
          G.E.toFun '' (G.E.dom \ F.E.toFun '' F.E.dom))
          (fun z hz => ?_) (D.small_union G.E.small_compl_image himg)
        by_cases h2 : z ∈ G.E.toFun '' G.E.dom
        · right
          obtain ⟨y, hy, rfl⟩ := h2
          refine ⟨y, ⟨hy, ?_⟩, rfl⟩
          intro hmem
          obtain ⟨x, hx, rfl⟩ := hmem
          exact hz.2 ⟨x, ⟨hx, hy⟩, rfl⟩
        · left; exact ⟨hz.1, h2⟩
      inv := fun z => F.E.inv (G.E.inv z)
      inv_definable := by
        refine D.comp (A := (fun x => G.E.toFun (F.E.toFun x)) '' {x | x ∈ F.E.dom ∧ F.E.toFun x ∈ G.E.dom})
          (A' := F.E.toFun '' F.E.dom) ?_ F.E.inv_definable ?_
        · exact DefinableFun.mono (A := (fun x => G.E.toFun (F.E.toFun x)) ''
            {x | x ∈ F.E.dom ∧ F.E.toFun x ∈ G.E.dom}) (fun z hz => by
              obtain ⟨x, hx, rfl⟩ := hz
              exact ⟨F.E.toFun x, hx.2, rfl⟩) G.E.inv_definable
        · rintro z ⟨x, hx, rfl⟩
          rw [G.E.inv_left (F.E.toFun x) hx.2]
          exact ⟨x, hx.1, rfl⟩
      inv_left := by
        intro x hx
        show F.E.inv (G.E.inv (G.E.toFun (F.E.toFun x))) = x
        rw [G.E.inv_left (F.E.toFun x) hx.2, F.E.inv_left x hx.1]
      inv_right := by
        rintro z ⟨x, hx, rfl⟩
        show G.E.toFun (F.E.toFun (F.E.inv (G.E.inv (G.E.toFun (F.E.toFun x))))) = G.E.toFun (F.E.toFun x)
        rw [G.E.inv_left (F.E.toFun x) hx.2, F.E.inv_left x hx.1] }
  good := {x | x ∈ F.good ∧ F.E.toFun x ∈ G.good ∧
    iRv (J.J (fun y => G.E.toFun (F.E.toFun y)) x) =
      iRVMul (iRv (J.J G.E.toFun (F.E.toFun x))) (iRv (J.J F.E.toFun x))}
  good_sub := fun x hx => ⟨F.good_sub hx.1, G.good_sub hx.2.1⟩
  small_compl := by
    have hB : Small S k ((F.E.toFun '' F.E.dom) \ G.good) := by
      refine small_subset (fun x hx => ?_) G.small_compl
      obtain ⟨y, hy, rfl⟩ := hx.1
      exact ⟨F.E.maps y hy, hx.2⟩
    have himg : Small S k (F.E.inv '' ((F.E.toFun '' F.E.dom) \ G.good)) :=
      D.small_image (DefinableFun.mono (A := (F.E.toFun '' F.E.dom) \ G.good)
        (fun x hx => hx.1) F.E.inv_definable) hB
    have hchain : Small S k {x | x ∈ F.good ∧
        iRv (J.J (fun y => G.E.toFun (F.E.toFun y)) x) ≠
          iRVMul (iRv (J.J G.E.toFun (F.E.toFun x))) (iRv (J.J F.E.toFun x))} :=
      J.jcb_chain F.good G.good F.E.toFun G.E.toFun
        (DefinableFun.mono (fun x hx => F.good_sub hx) F.E.definable)
        (DefinableFun.mono (fun x hx => G.good_sub hx) G.E.definable)
    refine small_subset (C := (X.A \ F.good) ∪ F.E.inv '' ((F.E.toFun '' F.E.dom) \ G.good) ∪
      {x | x ∈ F.good ∧
        iRv (J.J (fun y => G.E.toFun (F.E.toFun y)) x) ≠
          iRVMul (iRv (J.J G.E.toFun (F.E.toFun x))) (iRv (J.J F.E.toFun x))})
      (fun x hx => ?_) (D.small_union (D.small_union F.small_compl himg) hchain)
    by_cases h1 : x ∈ F.good
    · by_cases h2 : F.E.toFun x ∈ G.good
      · right
        exact ⟨h1, fun h => hx.2 ⟨h1, h2, h⟩⟩
      · left; right
        exact ⟨F.E.toFun x, ⟨⟨x, F.good_sub h1, rfl⟩, h2⟩, F.E.inv_left x (F.good_sub h1)⟩
    · left; left; exact ⟨hx.1, h1⟩
  vol := by
    intro x hx
    obtain ⟨hxF, hxG, hxJ⟩ := hx
    have h2 := F.vol x hxF
    have h3 := G.vol (F.E.toFun x) hxG
    have hrZ : iRV (Z.omega (G.E.toFun (F.E.toFun x))) :=
      Z.omega_definable.1 _ (G.E.maps _ (G.good_sub hxG))
    have hrJ1 : iRV (iRv (J.J G.E.toFun (F.E.toFun x))) :=
      R.rv_rv (J.J_vf G.E.toFun (F.E.toFun x))
    have hrJ2 : iRV (iRv (J.J F.E.toFun x)) := R.rv_rv (J.J_vf F.E.toFun x)
    show X.omega x = iRVMul (Z.omega (G.E.toFun (F.E.toFun x)))
      (iRv (J.J (fun y => G.E.toFun (F.E.toFun y)) x))
    calc X.omega x
        = iRVMul (Y.omega (F.E.toFun x)) (iRv (J.J F.E.toFun x)) := h2
      _ = iRVMul (iRVMul (Z.omega (G.E.toFun (F.E.toFun x)))
            (iRv (J.J G.E.toFun (F.E.toFun x)))) (iRv (J.J F.E.toFun x)) := by rw [h3]
      _ = iRVMul (Z.omega (G.E.toFun (F.E.toFun x)))
            (iRVMul (iRv (J.J G.E.toFun (F.E.toFun x))) (iRv (J.J F.E.toFun x))) :=
          R.mul_assoc hrZ hrJ1 hrJ2
      _ = iRVMul (Z.omega (G.E.toFun (F.E.toFun x)))
            (iRv (J.J (fun y => G.E.toFun (F.E.toFun y)) x)) := by rw [hxJ]

end MVFHom

/-! ## Part 7. Remark `mor:equi`: every morphism is an isomorphism

*"Consequently, since the Jacobian of the identity map is equal to `1` almost everywhere, by
Lemma `jcb:chain`, every morphism is actually an isomorphism."*

The proof is the paper's: if `F` is a morphism with inverse `F⁻¹`, then on the set where
`Jcb_VF (F⁻¹ ∘ F)`, `Jcb_VF F⁻¹(F(x̄)) · Jcb_VF F(x̄)` are both defined (and `F⁻¹ ∘ F` is the
identity, hence has Jacobian `1`) one has `rv(Jcb F⁻¹(F x̄)) · rv(Jcb F x̄) = 1`; multiplying the
defining identity `ω(x̄) = ω'(F x̄) · rv(Jcb F x̄)` by `rv(Jcb F⁻¹(F x̄))` gives the defining
identity of `F⁻¹`, i.e. `F⁻¹` is measure-preserving as well. -/
namespace MVFHom

variable {J : Jcb S k} {X : MVFObj S k n m} {Y : MVFObj S k n' m'}

/-- **Every morphism is an isomorphism** (Remark `mor:equi`): the inverse of a morphism of
`mVF[k,·]` is again a morphism. -/
def inv (D : DimLayer S k) (R : RVLaws M) (hk : 0 < k) (F : MVFHom J X Y) : MVFHom J Y X := by
  classical
  -- the three sets of `VF`-dimension `< k` where the Jacobian identities fail
  set badC : Set (Tup M n m) := {x | x ∈ F.good ∧
    iRv (J.J (fun y => F.E.inv (F.E.toFun y)) x) ≠
      iRVMul (iRv (J.J F.E.inv (F.E.toFun x))) (iRv (J.J F.E.toFun x))} with hbadC
  set badL : Set (Tup M n m) := {x | x ∈ F.good ∧
    iRv (J.J (fun y => F.E.inv (F.E.toFun y)) x) ≠
      iRv (J.J (id : Tup M n m → Tup M n m) x)} with hbadL
  set badI : Set (Tup M n m) :=
    {x | iRv (J.J (id : Tup M n m → Tup M n m) x) ≠ iRVOne} with hbadI
  have hC : Small S k badC :=
    J.jcb_chain F.good (F.E.toFun '' F.E.dom) F.E.toFun F.E.inv
      (DefinableFun.mono (fun x hx => F.good_sub hx) F.E.definable) F.E.inv_definable
  have hL : Small S k badL :=
    J.jcb_loc F.good F.good (fun y => F.E.inv (F.E.toFun y)) (id : Tup M n m → Tup M n m)
      (D.comp (DefinableFun.mono (fun x hx => F.good_sub hx) F.E.definable) F.E.inv_definable
        (fun x hx => ⟨x, F.good_sub hx, rfl⟩))
      (definableFun_id S F.good) (fun _ hx => hx)
      (by have h : F.good \ F.good = (∅ : Set (Tup M n m)) := by ext x; simp
          rw [h]; exact small_empty S hk)
      (fun x hx => F.E.inv_left x (F.good_sub hx))
  have hI : Small S k badI := J.jcb_id
  have hbad : Small S k (badC ∪ badL ∪ badI) := D.small_union (D.small_union hC hL) hI
  refine
    { E :=
        { dom := F.E.toFun '' F.E.dom
          dom_sub := fun y hy => by
            obtain ⟨x, hx, rfl⟩ := hy
            exact F.E.maps x hx
          small_compl_dom := F.E.small_compl_image
          toFun := F.E.inv
          maps := fun y hy => F.E.dom_sub (F.E.inv_maps y hy)
          injOn := F.E.inv_injOn
          definable := F.E.inv_definable
          small_compl_image := by
            rw [F.E.image_inv_image]
            exact F.E.small_compl_dom
          inv := F.E.toFun
          inv_definable := by
            rw [F.E.image_inv_image]
            exact F.E.definable
          inv_left := fun y hy => F.E.inv_right y hy
          inv_right := fun x hx => by
            have hmem : x ∈ F.E.dom := by
              rw [F.E.image_inv_image] at hx
              exact hx
            exact F.E.inv_left x hmem }
      good := F.E.toFun '' (F.good \ (badC ∪ badL ∪ badI))
      good_sub := fun y hy => by
        obtain ⟨x, hx, rfl⟩ := hy
        exact ⟨x, F.good_sub hx.1, rfl⟩
      small_compl := by
        have h1 : Small S k (F.E.toFun '' (F.E.dom \ (F.good \ (badC ∪ badL ∪ badI)))) := by
          refine D.small_image (DefinableFun.mono
            (A := F.E.dom \ (F.good \ (badC ∪ badL ∪ badI))) (fun x hx => hx.1)
            F.E.definable) ?_
          refine small_subset (C := (X.A \ F.good) ∪ (badC ∪ badL ∪ badI)) (fun x hx => ?_)
            (D.small_union F.small_compl hbad)
          by_cases hx' : x ∈ F.good
          · right
            by_contra hxb
            exact hx.2 ⟨hx', hxb⟩
          · left; exact ⟨F.E.dom_sub hx.1, hx'⟩
        refine small_subset (C := (Y.A \ F.E.toFun '' F.E.dom) ∪
          F.E.toFun '' (F.E.dom \ (F.good \ (badC ∪ badL ∪ badI))))
          (fun y hy => ?_) (D.small_union F.E.small_compl_image h1)
        by_cases hy' : y ∈ F.E.toFun '' F.E.dom
        · right
          obtain ⟨x, hx, rfl⟩ := hy'
          exact ⟨x, ⟨hx, fun hgood => hy.2 ⟨x, hgood, rfl⟩⟩, rfl⟩
        · left; exact ⟨hy.1, hy'⟩
      vol := by
        rintro y ⟨x, hx, rfl⟩
        obtain ⟨hxgood, hxbad⟩ := hx
        simp only [Set.mem_union, not_or] at hxbad
        obtain ⟨⟨hxc, hxl⟩, hxi⟩ := hxbad
        have hchain : iRv (J.J (fun y => F.E.inv (F.E.toFun y)) x) =
            iRVMul (iRv (J.J F.E.inv (F.E.toFun x))) (iRv (J.J F.E.toFun x)) := by
          by_contra h
          exact hxc ⟨hxgood, h⟩
        have hloc : iRv (J.J (fun y => F.E.inv (F.E.toFun y)) x) =
            iRv (J.J (id : Tup M n m → Tup M n m) x) := by
          by_contra h
          exact hxl ⟨hxgood, h⟩
        have hid : iRv (J.J (id : Tup M n m → Tup M n m) x) = iRVOne := by
          by_contra h
          exact hxi h
        have hone : iRVMul (iRv (J.J F.E.inv (F.E.toFun x))) (iRv (J.J F.E.toFun x)) =
            iRVOne := by
          rw [← hchain, hloc, hid]
        have hF := F.vol x hxgood
        have hright : F.E.inv (F.E.toFun x) = x := F.E.inv_left x (F.good_sub hxgood)
        have hrY : iRV (Y.omega (F.E.toFun x)) :=
          Y.omega_definable.1 _ (F.E.maps x (F.good_sub hxgood))
        have hneY : Y.omega (F.E.toFun x) ≠ iRVZero :=
          Y.omega_ne _ (F.E.maps x (F.good_sub hxgood))
        have hc : iRV (iRv (J.J F.E.toFun x)) := R.rv_rv (J.J_vf F.E.toFun x)
        have hd : iRV (iRv (J.J F.E.inv (F.E.toFun x))) :=
          R.rv_rv (J.J_vf F.E.inv (F.E.toFun x))
        have hcd : iRVMul (iRv (J.J F.E.toFun x)) (iRv (J.J F.E.inv (F.E.toFun x))) =
            iRVOne := by
          rw [R.mul_comm hc hd]; exact hone
        show Y.omega (F.E.toFun x) =
          iRVMul (X.omega (F.E.inv (F.E.toFun x))) (iRv (J.J F.E.inv (F.E.toFun x)))
        rw [hright]
        exact
          calc Y.omega (F.E.toFun x)
              = iRVMul (Y.omega (F.E.toFun x)) iRVOne :=
                (R.mul_one hrY hneY).symm
            _ = iRVMul (Y.omega (F.E.toFun x))
                  (iRVMul (iRv (J.J F.E.toFun x)) (iRv (J.J F.E.inv (F.E.toFun x)))) := by
                rw [hcd]
            _ = iRVMul (iRVMul (Y.omega (F.E.toFun x)) (iRv (J.J F.E.toFun x)))
                  (iRv (J.J F.E.inv (F.E.toFun x))) := (R.mul_assoc hrY hc hd).symm
            _ = iRVMul (X.omega x) (iRv (J.J F.E.inv (F.E.toFun x))) := by rw [← hF] }

end MVFHom

end Sec10

end SpecialTransformations.Milestone0
