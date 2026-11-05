/-
# Stage 1: the `L_RV` side of the residue-induction gap

For a substructure `S ⊆ M` of a model of `ACVF` and an `L_RV`-embedding `f : S ↪[LRV] N` into a
model `N`:

* `RS S` — the subring of `K(M)` carried by the substructure `S` (`S` is closed under `kAdd`,
  `rvMul`, `kNeg` and the constants);
* `tr S f : RS S →+* K(N)` — the residue-field map induced by `f` on that subring.  It is a ring
  homomorphism exactly because `f` preserves the *function symbols* of `L_RV`;
* `tr_injective` — from injectivity of `f`;
* `tr_comp_phiM'` — `tr ∘ φ' = φ_N`, `φ'`/`φ_N` being polynomial evaluation at the units of `S`
  and at their images;
* `ker_eq` — `ker φ_M = ker φ_N`.

`ker_eq` is the whole `L_RV`-specific content of `ResidueInduced`; it says that `f` preserves *and
reflects* the polynomial relations among the units of `S`, i.e. that the partial map it induces on
the residue field is quantifier-free-type preserving.  Everything after it (Stage 2) is algebra.
-/
import SatQuotes
import Mathlib.RingTheory.Localization.FractionRing

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.StandingField

namespace M4Residue

/-- The `L_RV`-function-symbol map on a substructure. -/
abbrev sfm {M : Type} [LRV.Structure M] {S : LRV.Substructure M} {n : ℕ}
    (g : LRV.Functions n) (x : Fin n → S) : S :=
  FirstOrder.Language.Structure.funMap (L := LRV) g x

/-- The `L_RV`-function-symbol map on a structure. -/
abbrev mfm {M : Type} [LRV.Structure M] {n : ℕ} (g : LRV.Functions n) (x : Fin n → M) : M :=
  FirstOrder.Language.Structure.funMap (L := LRV) g x

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
  [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]

section Ring

variable (S : LRV.Substructure M)

/-! ### The subring of `K(M)` carried by a substructure -/

theorem rvZero_mem : iRVZero (M := M) ∈ S :=
  S.fun_mem Fn.rvZero (fun i : Fin 0 => i.elim0) (fun i => i.elim0)

theorem rvOne_mem : iRVOne (M := M) ∈ S :=
  S.fun_mem Fn.rvOne (fun i : Fin 0 => i.elim0) (fun i => i.elim0)

theorem kAdd_mem {a b : KOf M} (ha : a.1 ∈ S) (hb : b.1 ∈ S) : (a + b).1 ∈ S :=
  S.fun_mem Fn.kAdd ![a.1, b.1] (by
    intro i
    fin_cases i
    · simpa using ha
    · simpa using hb)

theorem kMul_mem {a b : KOf M} (ha : a.1 ∈ S) (hb : b.1 ∈ S) : (a * b).1 ∈ S :=
  S.fun_mem Fn.rvMul ![a.1, b.1] (by
    intro i
    fin_cases i
    · simpa using ha
    · simpa using hb)

theorem kNeg_mem {a : KOf M} (ha : a.1 ∈ S) : (-a).1 ∈ S := by
  show TrivCase.iKNeg a.1 ∈ S
  exact S.fun_mem Fn.kNeg ![a.1] (by
    intro i
    fin_cases i
    simpa using ha)

/-- The residue elements of `M` carried by the substructure `S`, as a subring of `K(M)`. -/
def RS : Subring (KOf M) where
  carrier := {a : KOf M | a.1 ∈ S}
  zero_mem' := rvZero_mem S
  one_mem' := rvOne_mem S
  add_mem' := fun ha hb => kAdd_mem S ha hb
  neg_mem' := fun ha => kNeg_mem S ha
  mul_mem' := fun ha hb => kMul_mem S ha hb

end Ring

section Transfer

variable (S : LRV.Substructure M) (f : S ↪[LRV] N)

/-! ### Compatibilities of the two presentations of a tuple -/

theorem funMap_congr {n : ℕ} (g : LRV.Functions n) {x y : Fin n → M} (h : ∀ i, x i = y i) :
    mfm g x = mfm g y := by
  congr 1
  funext i
  exact h i

theorem pair_coe (p q : S) :
    (fun i : Fin 2 => ((![p, q] : Fin 2 → S) i : M)) = ![(p : M), (q : M)] := by
  funext i
  fin_cases i <;> rfl

theorem pair_img (p q : S) :
    (⇑f ∘ (![p, q] : Fin 2 → S)) = ![f p, f q] := by
  funext i
  fin_cases i <;> rfl

/-- `![y]` and the constant tuple are the same set of values. -/
theorem singleton_tuple (y : M) : (![y] : Fin 1 → M) = fun _ => y := by
  funext i
  fin_cases i
  rfl

theorem units_map (x : S) (hx : iUnits (x : M)) : iUnits (f x) := by
  have hx1 : FirstOrder.Language.Structure.RelMap (L := LRV) Rel.memUnits
      (![(x : M)] : Fin 1 → M) := by simpa [iUnits] using hx
  rw [singleton_tuple] at hx1
  have hx2 : FirstOrder.Language.Structure.RelMap (L := LRV) Rel.memUnits
      (fun _ : Fin 1 => x) := hx1
  have h := (f.map_rel Rel.memUnits (fun _ : Fin 1 => x)).mpr hx2
  have himg : (⇑f ∘ (fun _ : Fin 1 => x)) = (fun _ : Fin 1 => f x) := rfl
  rw [himg] at h
  simpa [iUnits, singleton_tuple] using h

/-- The empty-tuple presentation of a constant. -/
theorem const_tuple_zero : (fun i : Fin 0 => ((fun i : Fin 0 => (i.elim0 : S)) i : M))
    = (fun i : Fin 0 => i.elim0) := by
  funext i
  exact i.elim0

theorem map_rvZero : f ⟨iRVZero, rvZero_mem S⟩ = (iRVZero : N) := by
  have hsub : (⟨iRVZero, rvZero_mem S⟩ : S) = sfm Fn.rvZero (fun i : Fin 0 => i.elim0) := by
    apply Subtype.ext
    show mfm Fn.rvZero (fun i : Fin 0 => i.elim0)
      = mfm Fn.rvZero (fun i : Fin 0 => (((fun i : Fin 0 => (i.elim0 : S)) i) : M))
    exact funMap_congr Fn.rvZero (fun i => i.elim0)
  rw [hsub]
  have h := f.map_fun Fn.rvZero (fun i : Fin 0 => i.elim0)
  have himg : (⇑f ∘ (fun i : Fin 0 => i.elim0)) = (fun i : Fin 0 => i.elim0) := by
    funext i
    exact i.elim0
  rw [himg] at h
  exact h

theorem map_rvOne : f ⟨iRVOne, rvOne_mem S⟩ = (iRVOne : N) := by
  have hsub : (⟨iRVOne, rvOne_mem S⟩ : S) = sfm Fn.rvOne (fun i : Fin 0 => i.elim0) := by
    apply Subtype.ext
    show mfm Fn.rvOne (fun i : Fin 0 => i.elim0)
      = mfm Fn.rvOne (fun i : Fin 0 => (((fun i : Fin 0 => (i.elim0 : S)) i) : M))
    exact funMap_congr Fn.rvOne (fun i => i.elim0)
  rw [hsub]
  have h := f.map_fun Fn.rvOne (fun i : Fin 0 => i.elim0)
  have himg : (⇑f ∘ (fun i : Fin 0 => i.elim0)) = (fun i : Fin 0 => i.elim0) := by
    funext i
    exact i.elim0
  rw [himg] at h
  exact h

theorem units_or_zero_of_mem {a : KOf M} (ha : a.1 ∈ S) :
    iUnits (f ⟨a.1, ha⟩) ∨ f ⟨a.1, ha⟩ = (iRVZero : N) := by
  rcases a.2 with hu | hz
  · exact Or.inl (units_map S f ⟨a.1, ha⟩ hu)
  · right
    have hsub : (⟨a.1, ha⟩ : S) = ⟨iRVZero, rvZero_mem S⟩ := Subtype.ext hz
    rw [hsub]
    exact map_rvZero S f

/-- The map of residue fields induced by `f` on the subring carried by `S`. -/
noncomputable def trFun (a : RS S) : KOf N :=
  ⟨f ⟨a.1.1, a.2⟩, units_or_zero_of_mem S f a.2⟩

theorem trFun_coe (a : RS S) : (trFun S f a).1 = f ⟨a.1.1, a.2⟩ := rfl

/-- **`f` induces a ring homomorphism on the residue elements it is defined on.** -/
noncomputable def tr : RS S →+* KOf N where
  toFun := trFun S f
  map_zero' := by
    apply Subtype.ext
    show f ⟨iRVZero, _⟩ = (iRVZero : N)
    exact map_rvZero S f
  map_one' := by
    apply Subtype.ext
    show f ⟨iRVOne, _⟩ = (iRVOne : N)
    exact map_rvOne S f
  map_add' := fun a b => by
    have h := f.map_fun Fn.kAdd (![⟨a.1.1, a.2⟩, ⟨b.1.1, b.2⟩] : Fin 2 → S)
    rw [pair_img S f ⟨a.1.1, a.2⟩ ⟨b.1.1, b.2⟩] at h
    apply Subtype.ext
    have hL : (trFun S f (a + b)).1
        = f (sfm Fn.kAdd ![⟨a.1.1, a.2⟩, ⟨b.1.1, b.2⟩]) := by
      show f ⟨mfm Fn.kAdd ![a.1.1, b.1.1], _⟩ = f (sfm Fn.kAdd _)
      congr 1
      apply Subtype.ext
      show mfm Fn.kAdd ![a.1.1, b.1.1]
        = mfm Fn.kAdd (fun i : Fin 2 =>
            ((![⟨a.1.1, a.2⟩, ⟨b.1.1, b.2⟩] : Fin 2 → S) i : M))
      rw [pair_coe S]
    rw [hL]
    exact h
  map_mul' := fun a b => by
    have h := f.map_fun Fn.rvMul (![⟨a.1.1, a.2⟩, ⟨b.1.1, b.2⟩] : Fin 2 → S)
    rw [pair_img S f ⟨a.1.1, a.2⟩ ⟨b.1.1, b.2⟩] at h
    apply Subtype.ext
    have hL : (trFun S f (a * b)).1
        = f (sfm Fn.rvMul ![⟨a.1.1, a.2⟩, ⟨b.1.1, b.2⟩]) := by
      show f ⟨mfm Fn.rvMul ![a.1.1, b.1.1], _⟩ = f (sfm Fn.rvMul _)
      congr 1
      apply Subtype.ext
      show mfm Fn.rvMul ![a.1.1, b.1.1]
        = mfm Fn.rvMul (fun i : Fin 2 =>
            ((![⟨a.1.1, a.2⟩, ⟨b.1.1, b.2⟩] : Fin 2 → S) i : M))
      rw [pair_coe S]
    rw [hL]
    exact h

theorem tr_apply (a : RS S) : (tr S f a).1 = f ⟨a.1.1, a.2⟩ := rfl

theorem tr_injective : Function.Injective (tr S f) := by
  intro a b h
  have h1 : f ⟨a.1.1, a.2⟩ = f ⟨b.1.1, b.2⟩ := congrArg Subtype.val h
  have h2 : (⟨a.1.1, a.2⟩ : S) = ⟨b.1.1, b.2⟩ := f.injective h1
  have h3 : a.1.1 = b.1.1 := congrArg (fun z : S => (z : M)) h2
  exact Subtype.ext (Subtype.ext h3)

/-! ### The polynomial evaluations at the units of `S` -/

/-- The units of `S`, as an index type. -/
abbrev Iota : Type := {x : S // iUnits (x : M)}

/-- The units of `S` as elements of the subring `RS S`. -/
def uM (i : Iota S) : RS S := ⟨⟨(i.1 : M), Or.inl i.2⟩, i.1.2⟩

/-- The images of the units of `S` under `f`, as elements of `K(N)`. -/
def uN (i : Iota S) : KOf N := ⟨f i.1, Or.inl (units_map S f i.1 i.2)⟩

/-- Polynomial evaluation at the units of `S`, into `K(M)`. -/
noncomputable def phiM : MvPolynomial (Iota S) ℤ →+* KOf M :=
  MvPolynomial.eval₂Hom (Int.castRingHom (KOf M)) fun i => (uM S i : KOf M)

/-- Polynomial evaluation at the units of `S`, into the subring `RS S`. -/
noncomputable def phiM' : MvPolynomial (Iota S) ℤ →+* RS S :=
  MvPolynomial.eval₂Hom (Int.castRingHom (RS S)) (uM S)

/-- Polynomial evaluation at the images of the units of `S`, into `K(N)`. -/
noncomputable def phiN : MvPolynomial (Iota S) ℤ →+* KOf N :=
  MvPolynomial.eval₂Hom (Int.castRingHom (KOf N)) (uN S f)

theorem phiM_eq : phiM S = (RS S).subtype.comp (phiM' S) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [phiM, phiM', MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
    show (r : KOf M) = (RS S).subtype (r : ↥(RS S))
    rfl
  · intro i
    simp only [phiM, phiM', MvPolynomial.eval₂Hom_X', RingHom.comp_apply]
    rfl

theorem tr_comp_phiM' : (tr S f).comp (phiM' S) = phiN S f := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [phiM', phiN, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
    show tr S f (r : RS S) = (r : KOf N)
    exact map_intCast (tr S f) r
  · intro i
    simp only [phiM', phiN, MvPolynomial.eval₂Hom_X', RingHom.comp_apply]
    apply Subtype.ext
    show f ⟨(uM S i).1.1, (uM S i).2⟩ = f i.1
    rfl

/-- **Kernel inclusion**: a polynomial relation among the units of `S` that holds in `K(M)` holds
in `K(N)` at the images (term preservation). -/
theorem ker_subset : RingHom.ker (phiM S) ≤ RingHom.ker (phiN S f) := by
  intro p hp
  have hp' : phiM S p = 0 := RingHom.mem_ker.mp hp
  have h1 : phiM' S p = 0 := by
    apply (RS S).subtype_injective
    rw [phiM_eq] at hp'
    simpa using hp'
  rw [RingHom.mem_ker, ← tr_comp_phiM']
  simp only [RingHom.comp_apply, h1, map_zero]

/-- **Kernel reflection**: a polynomial relation that holds at the images holds at the units
(injectivity of `f`). -/
theorem ker_subset' : RingHom.ker (phiN S f) ≤ RingHom.ker (phiM S) := by
  intro p hp
  have hp' : phiN S f p = 0 := RingHom.mem_ker.mp hp
  have h2 : (tr S f) (phiM' S p) = 0 := by
    have h3 : (tr S f) (phiM' S p) = phiN S f p := by
      rw [← tr_comp_phiM']
      rfl
    rw [h3]
    exact hp'
  have h1 : phiM' S p = 0 := by
    apply tr_injective S f
    simpa using h2
  rw [RingHom.mem_ker, phiM_eq]
  simp only [RingHom.comp_apply, h1, map_zero]

theorem ker_eq : RingHom.ker (phiM S) = RingHom.ker (phiN S f) :=
  le_antisymm (ker_subset S f) (ker_subset' S f)

end Transfer


/-! ## Stage 2: the algebra — a subfield of `K(M)` generated by the units, and its map to `K(N)`

`ker_eq` says the two polynomial evaluations at `uM` and at `uN` have the same kernel.  Quotient by
that kernel, pass to the fraction field — legal because this is a *kernel equality*, not a mere
inclusion: the quotient embeds in both fields — and take the image in `K(M)`.  That subfield is the
one `ResidueInduced` needs, and the map to `K(N)` is the required ring homomorphism. -/

namespace Algebra

/-- The ideal of polynomial relations among the units of `S`. -/
noncomputable def Ip (S : LRV.Substructure M) : Ideal (MvPolynomial (Iota S) ℤ) :=
  RingHom.ker (phiM S)

/-- The quotient of the polynomial ring by those relations. -/
abbrev Qp (S : LRV.Substructure M) : Type := MvPolynomial (Iota S) ℤ ⧸ Ip S

theorem isPrime_Ip (S : LRV.Substructure M) : (Ip S).IsPrime := RingHom.ker_isPrime (phiM S)

instance instIsDomainQp (S : LRV.Substructure M) : IsDomain (Qp S) := by
  haveI : (Ip S).IsPrime := isPrime_Ip S
  infer_instance

/-- The fraction field of the relation quotient. -/
abbrev Fp (S : LRV.Substructure M) : Type := FractionRing (Qp S)

/-- The evaluation at the units, factored through the relations. -/
noncomputable def phiBarM (S : LRV.Substructure M) : Qp S →+* KOf M :=
  Ideal.Quotient.lift (Ip S) (phiM S) fun _ ha => RingHom.mem_ker.mp ha

/-- The evaluation at the images, factored through the *same* relations (`ker_eq`). -/
noncomputable def phiBarN (S : LRV.Substructure M) (f : S ↪[LRV] N) : Qp S →+* KOf N :=
  Ideal.Quotient.lift (Ip S) (phiN S f) fun _ ha => by
    have h : (RingHom.ker (phiM S) : Ideal (MvPolynomial (Iota S) ℤ)) =
        RingHom.ker (phiN S f) := ker_eq S f
    exact RingHom.mem_ker.mp (h ▸ ha)

theorem phiBarM_mk (S : LRV.Substructure M) (a : MvPolynomial (Iota S) ℤ) :
    phiBarM S (Ideal.Quotient.mk (Ip S) a) = phiM S a := rfl

theorem phiBarN_mk (S : LRV.Substructure M) (f : S ↪[LRV] N) (a : MvPolynomial (Iota S) ℤ) :
    phiBarN S f (Ideal.Quotient.mk (Ip S) a) = phiN S f a := rfl

theorem phiBarM_injective (S : LRV.Substructure M) : Function.Injective (phiBarM S) := by
  have hzero : ∀ x : Qp S, phiBarM S x = 0 → x = 0 := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.eq_zero_iff_mem]
    rw [show phiBarM S (Ideal.Quotient.mk (Ip S) a) = phiM S a from rfl] at hx
    exact hx
  intro x y hxy
  have hsub : x - y = 0 := hzero (x - y) (by rw [map_sub, hxy, sub_self])
  exact sub_eq_zero.mp hsub

theorem phiBarN_injective (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    Function.Injective (phiBarN S f) := by
  have hzero : ∀ x : Qp S, phiBarN S f x = 0 → x = 0 := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h1 : phiN S f a = 0 := by
      rw [← phiBarN_mk S f a]
      exact hx
    rw [Ideal.Quotient.eq_zero_iff_mem]
    show a ∈ RingHom.ker (phiM S)
    rw [ker_eq S f]
    exact RingHom.mem_ker.mpr h1
  intro x y hxy
  have hsub : x - y = 0 := hzero (x - y) (by rw [map_sub, hxy, sub_self])
  exact sub_eq_zero.mp hsub

/-- The evaluation at the units, extended to the fraction field. -/
noncomputable def psiM (S : LRV.Substructure M) : Fp S →+* KOf M :=
  IsFractionRing.lift (phiBarM_injective S)

/-- The evaluation at the images, extended to the fraction field. -/
noncomputable def psiN (S : LRV.Substructure M) (f : S ↪[LRV] N) : Fp S →+* KOf N :=
  IsFractionRing.lift (phiBarN_injective S f)

theorem psiM_algebraMap (S : LRV.Substructure M) (x : Qp S) :
    psiM S (algebraMap (Qp S) (Fp S) x) = phiBarM S x :=
  IsFractionRing.lift_algebraMap (phiBarM_injective S) x

theorem psiN_algebraMap (S : LRV.Substructure M) (f : S ↪[LRV] N) (x : Qp S) :
    psiN S f (algebraMap (Qp S) (Fp S) x) = phiBarN S f x :=
  IsFractionRing.lift_algebraMap (phiBarN_injective S f) x

theorem psiM_injective (S : LRV.Substructure M) : Function.Injective (psiM S) :=
  RingHom.injective _

/-- The image of the fraction field in `K(M)`: the subfield generated by the units of `S`. -/
noncomputable abbrev Ksub (S : LRV.Substructure M) : Subfield (KOf M) := (psiM S).fieldRange

/-- The induced map on that subfield. -/
noncomputable def jmap (S : LRV.Substructure M) (f : S ↪[LRV] N) : Ksub S →+* KOf N :=
  (psiN S f).comp (((psiM S).rangeRestrictFieldEquiv.symm : Ksub S →+* Fp S))

theorem uM_mem_fieldRange (S : LRV.Substructure M) (i : Iota S) :
    (uM S i : KOf M) ∈ (psiM S).fieldRange := by
  refine ⟨algebraMap (Qp S) (Fp S) (Ideal.Quotient.mk (Ip S) (MvPolynomial.X i)), ?_⟩
  rw [psiM_algebraMap]
  change (MvPolynomial.eval₂Hom (Int.castRingHom (KOf M)) (fun i => (uM S i : KOf M)))
    (MvPolynomial.X i) = (uM S i : KOf M)
  rw [MvPolynomial.eval₂Hom_X']

theorem phiM_range (S : LRV.Substructure M) :
    (phiM S).range = Subring.closure (Set.range fun i : Iota S => (uM S i : KOf M)) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨p, rfl⟩
    induction p using MvPolynomial.induction_on with
    | C a =>
        have hC : phiM S (MvPolynomial.C a) = (a : KOf M) := by
          rw [phiM, MvPolynomial.eval₂Hom_C]
          rfl
        rw [hC, ← zsmul_one]
        exact Subring.zsmul_mem _ (Subring.one_mem _) a
    | add p q hp hq =>
        rw [map_add]
        exact Subring.add_mem _ hp hq
    | mul_X p i hp =>
        have hX : phiM S (MvPolynomial.X i) = (uM S i : KOf M) := by
          rw [phiM, MvPolynomial.eval₂Hom_X']
        rw [map_mul, hX]
        exact Subring.mul_mem _ hp (Subring.subset_closure ⟨i, rfl⟩)
  · rw [Subring.closure_le]
    rintro y ⟨i, rfl⟩
    exact ⟨MvPolynomial.X i, by rw [phiM, MvPolynomial.eval₂Hom_X']⟩

theorem phiBarM_range (S : LRV.Substructure M) : (phiBarM S).range = (phiM S).range := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨a, phiBarM_mk S a⟩
  · rintro _ ⟨a, rfl⟩
    exact ⟨Ideal.Quotient.mk (Ip S) a, phiBarM_mk S a⟩

/-- **The subfield is exactly the one generated by the units of `S`** (no larger choice is made). -/
theorem Ksub_eq (S : LRV.Substructure M) :
    Ksub S = Subfield.closure (Set.range fun i : Iota S => (uM S i : KOf M)) :=
  IsFractionRing.lift_fieldRange_eq_of_range_eq (phiBarM_injective S)
    (by rw [phiBarM_range, phiM_range])

/-- **Minimality**: any subfield of `K(M)` containing the units of `S` contains `Ksub S`. -/
theorem Ksub_minimal (S : LRV.Substructure M) (K : Subfield (KOf M))
    (hU : ∀ i : Iota S, (uM S i : KOf M) ∈ K) : Ksub S ≤ K := by
  rw [Ksub_eq]
  exact Subfield.closure_le.mpr fun y hy => by
    rcases hy with ⟨i, rfl⟩
    exact hU i

theorem jmap_uM (S : LRV.Substructure M) (f : S ↪[LRV] N) (i : Iota S) :
    (jmap S f ⟨(uM S i : KOf M), uM_mem_fieldRange S i⟩ : KOf N) = uN S f i := by
  have hsymm : (psiM S)
      ((psiM S).rangeRestrictFieldEquiv.symm ⟨(uM S i : KOf M), uM_mem_fieldRange S i⟩)
      = (uM S i : KOf M) := RingHom.rangeRestrictFieldEquiv_apply_symm_apply _ _
  have hX : (psiM S) (algebraMap (Qp S) (Fp S) (Ideal.Quotient.mk (Ip S) (MvPolynomial.X i)))
      = (uM S i : KOf M) := by
    rw [psiM_algebraMap]
    change (MvPolynomial.eval₂Hom (Int.castRingHom (KOf M)) (fun i => (uM S i : KOf M)))
      (MvPolynomial.X i) = (uM S i : KOf M)
    rw [MvPolynomial.eval₂Hom_X']
  have heq : (psiM S).rangeRestrictFieldEquiv.symm ⟨(uM S i : KOf M), uM_mem_fieldRange S i⟩
      = algebraMap (Qp S) (Fp S) (Ideal.Quotient.mk (Ip S) (MvPolynomial.X i)) := by
    apply psiM_injective S
    rw [hsymm, hX]
  show (psiN S f) ((psiM S).rangeRestrictFieldEquiv.symm
      ⟨(uM S i : KOf M), uM_mem_fieldRange S i⟩) = uN S f i
  rw [heq, psiN_algebraMap]
  change (MvPolynomial.eval₂Hom (Int.castRingHom (KOf N)) (uN S f)) (MvPolynomial.X i)
    = uN S f i
  rw [MvPolynomial.eval₂Hom_X']

end Algebra

/-! ## Stage 3: the induction — `ResidueInduced` holds with no hypothesis beyond the two models

The constructed `(Ksub S, jmap S f)` is exactly the partial field embedding whose existence
`SatQuotes.ResidueInduced` asserts, so the named gap in `QE/SatQuotes.lean` is closed.  Note what
this theorem does *not* consume: no saturation of `N`, no `SaturatedFS`, no `M1Fix.SatRel`, no
cardinality gate `#M ≤ #N`, no quoted fact of any kind.  The size side condition of the neighbouring
`acfExtends_of_universal_induced` is *only* about extending this partial map to all of `K(M)` by
Marker's universality. -/

section Main

theorem residueInduced : SatQuotes.ResidueInduced (M := M) (N := N) := by
  intro S f
  refine ⟨Algebra.Ksub S, Algebra.jmap S f, ?_⟩
  intro x hx
  refine ⟨Algebra.uM_mem_fieldRange S ⟨x, hx⟩, ?_⟩
  show (Algebra.jmap S f ⟨(uM S ⟨x, hx⟩ : KOf M),
      Algebra.uM_mem_fieldRange S ⟨x, hx⟩⟩ : KOf N).1 = f x
  rw [Algebra.jmap_uM S f ⟨x, hx⟩]
  rfl

/-- The paper's step (i) at a `κ`-universal residue field: with the gap closed, nothing beyond
Marker's universality and `#K(M) < κ` is needed. -/
theorem acfExtends_of_universal {κ : Cardinal} (hU : SatQuotes.FieldUniversal (KOf N) κ)
    (hMκ : Cardinal.mk M < κ) : M5Ledger.ACFExtends (M := M) (N := N) :=
  SatQuotes.acfExtends_of_universal_induced hU hMκ (residueInduced (M := M) (N := N))

/-- The paper's ledger input 1 from Marker's universality alone: the hypothesis `ResidueInduced`
that `SatQuotes.ledgerInput1P_of_marker` took as an extra input is now a theorem, so the *canonical*
theorem of `QE/SatQuotes.lean` is derivable with that input discharged. -/
theorem ledgerInput1P_of_marker (hMarker : SatQuotes.MarkerSaturatedFieldUniversal)
    (hSatRes : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF], M7Paper.PaperHyp M N → ∃ κ, Cardinal.mk M < κ ∧ SatQuotes.SatField (KOf N) κ) :
    M5Ledger.LedgerInput1P :=
  SatQuotes.ledgerInput1P_of_marker hMarker hSatRes
    (fun M N _ _ _ _ _ => residueInduced (M := M) (N := N))

/-- Non-vacuousness: at `N = M` and `f` the inclusion of a substructure, the construction gives a
subfield of `K(M)` and a ring endomorphism of `K(M)` agreeing with the inclusion on the units. -/
theorem residueInduced_subtype (S : LRV.Substructure M) :
    ∃ (K : Subfield (KOf M)) (j : ↥K →+* KOf M),
      ∀ (x : S) (hx : iUnits (x : M)),
        ∃ h : (⟨(x : M), Or.inl hx⟩ : KOf M) ∈ K, (j ⟨_, h⟩ : KOf M).1 = (x : M) :=
  residueInduced (M := M) (N := M) S (FirstOrder.Language.Substructure.subtype S)

end Main

end M4Residue

#print axioms M4Residue.tr
#print axioms M4Residue.ker_eq
#print axioms M4Residue.Algebra.jmap_uM
#print axioms M4Residue.residueInduced
#print axioms M4Residue.acfExtends_of_universal
#print axioms M4Residue.ledgerInput1P_of_marker
#print axioms M4Residue.residueInduced_subtype
#print axioms M4Residue.Algebra.Ksub_eq
#print axioms M4Residue.Algebra.Ksub_minimal
