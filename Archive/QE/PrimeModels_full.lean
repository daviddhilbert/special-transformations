/-
  **Prime models over arbitrary substructures of fields** (Johnson, *Fun with Fields*,
  Definition 2.1.1) for `T₀ = Theory.field`, `T = acf`: `HasPrimeModels Theory.field acf`,
  unconditionally.  This closes the only hypothesis of `ACFValidation.acf_qfDetermined_general`
  that was left open in `QE/ACF_validation.lean`.

  Given an abstract `S : Type u` with `Language.ring.Structure S` that embeds into a field `M`
  (`e : S ↪[Language.ring] M`), let

    `R := FreeCommRing S ⧸ ker (FreeCommRing.lift (fun s => e s))`   (`coordRing`)

  be the coordinate ring of `S`: the free commutative ring on the generators `S` modulo the
  polynomial relations that hold in `M`.  `R` is a domain, and the prime model of the theory of
  fields over `S` is its fraction field

    `F := FractionRing R`   (`primeField`)

  together with `S ↪[Language.ring] F`, `s ↦ of s / 1` (`primeEmbedding`), which is an embedding
  because `S ↪ M` is injective.

  The universal property (`primeField_universal`): for every field `N` and every embedding
  `f : S ↪[Language.ring] N` there is `g : F ↪[Language.ring] N` with `g.comp e₀ = f`.  Proof:
  `FreeCommRing.lift f` and `FreeCommRing.lift e` have the SAME kernel (`ker_lift_eq`: the
  polynomial relations of `S` do not depend on the field it is embedded into), so the induced
  map `R →+* N` is injective, and `IsFractionRing.lift` extends it to `F →+* N`; a ring
  homomorphism out of a field into a nontrivial ring is injective.

  This file is self-contained (`import Mathlib` only).  The definitions `HasPrimeModels` and
  `acf` are copies of those in `QE/Johnson_criterion.lean` and `QE/ACF_validation.lean` (same
  definitions), so that the final statement is literally
  `JohnsonCriterion.HasPrimeModels Theory.field acf`.

  Main results:
  * `PrimeField.primeEmbedding`, `PrimeField.primeField_universal`
  * `hasPrimeModels_field_acf : JohnsonCriterion.HasPrimeModels Theory.field acf`

  No `sorry`, no `axiom`; axioms are checked at the end of the file.
-/
import Mathlib

open FirstOrder FirstOrder.Language
open FirstOrder.Ring
open scoped FirstOrder

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-! ## 0. Copies of the two definitions appearing in the statement -/

/-- Copy of `ACFValidation.acf` (`QE/ACF_validation.lean`): the theory of algebraically closed
fields, characteristic not fixed. -/
noncomputable def acf : Theory Language.ring :=
  Theory.field ∪ Field.genericMonicPolyHasRoot '' {n : ℕ | 0 < n}

namespace JohnsonCriterion

universe u v w

variable {L : FirstOrder.Language.{u, v}}

/-- Copy of `JohnsonCriterion.HasPrimeModels` (`QE/Johnson_criterion.lean`), with the same
universe signature.  Prime models over substructures (Johnson, Definition 2.1.1): every structure
`S` that embeds into a model of `T` has an extension `S'` modelling `T₀` which embeds into every
model of `T₀` under `S`. -/
def HasPrimeModels (T₀ T : L.Theory) : Prop :=
  ∀ (S : Type w) [L.Structure S],
    (∃ (M : T₀.ModelType.{u, v, w}), M ⊨ T ∧ Nonempty (S ↪[L] M)) →
    ∃ (S' : T₀.ModelType.{u, v, w}) (e : S ↪[L] S'),
      ∀ (N : T₀.ModelType.{u, v, w}) (f : S ↪[L] N),
        ∃ g : S' ↪[L] N, g.comp e = f

end JohnsonCriterion

namespace PrimeField

universe u

/-! ## 1. Ring homomorphisms and `Language.ring`-embeddings

(Copied from `QE/PrimeModels_partial.lean`, where the same lemmas are proved.) -/

section Conversions

variable {A B : Type*} [CommRing A] [CommRing B] [CompatibleRing A] [CompatibleRing B]

theorem ringHom_map_fun (f : A →+* B) {n : ℕ} (g : Language.ring.Functions n)
    (x : Fin n → A) : f (Structure.funMap g x) = Structure.funMap g (f ∘ x) := by
  cases g <;> simp

/-- An injective ring homomorphism is an embedding for the language of rings. -/
def embeddingOfInjectiveRingHom (f : A →+* B) (hf : Function.Injective f) :
    A ↪[Language.ring] B where
  toFun := f
  inj' := hf
  map_fun' := ringHom_map_fun f
  map_rel' := by intro n R; exact isEmptyElim R

end Conversions

/-! ## 2. Two embeddings of one structure have the same polynomial relations

(Copied from `QE/PrimeModels_partial.lean`.) -/

section Kernel

variable {S : Type u} [Language.ring.Structure S]
variable {M : Type u} [CommRing M] [CompatibleRing M]
variable {N : Type u} [CommRing N] [CompatibleRing N]

/-- `FreeCommRing.lift (fun s => e s) p` only depends on the term that `p` represents. -/
theorem lift_eq_apply_term (e : S ↪[Language.ring] M) (p : FreeCommRing S) :
    FreeCommRing.lift (fun s => e s) p
      = e (Term.realize (fun s => s) (Ring.termOfFreeCommRing p)) := by
  rw [← Ring.realize_termOfFreeCommRing p (fun s => e s)]
  exact HomClass.realize_term (g := e) (v := fun s => s)

/-- The zero of `S`, described intrinsically (as the value of the zero term), so that no ring
structure on `S` is needed. -/
def zeroTerm : Language.ring.Term S :=
  Term.func (FirstOrder.Ring.zeroFunc) (fun i => (i.elim0 : Language.ring.Term S))

theorem apply_zeroTerm {R : Type u} [CommRing R] [CompatibleRing R] (g : S ↪[Language.ring] R) :
    g (Term.realize (fun s => s) (zeroTerm (S := S))) = 0 := by
  rw [zeroTerm, Term.realize_func]
  rw [g.map_fun (FirstOrder.Ring.zeroFunc)]
  exact CompatibleRing.funMap_zero _

theorem apply_eq_zero_iff {R : Type u} [CommRing R] [CompatibleRing R]
    (g : S ↪[Language.ring] R) (w : S) :
    g w = 0 ↔ w = Term.realize (fun s => s) (zeroTerm (S := S)) := by
  constructor
  · intro h
    apply g.injective
    rw [h, apply_zeroTerm]
  · intro h
    rw [h, apply_zeroTerm]

/-- **The polynomial relations of an abstract structure are the same in every field it embeds
into.** -/
theorem ker_lift_eq (e : S ↪[Language.ring] M) (f : S ↪[Language.ring] N) :
    RingHom.ker (FreeCommRing.lift (fun s => e s))
      = RingHom.ker (FreeCommRing.lift (fun s => f s)) := by
  ext p
  rw [RingHom.mem_ker, RingHom.mem_ker, lift_eq_apply_term e, lift_eq_apply_term f,
    apply_eq_zero_iff e, apply_eq_zero_iff f]

end Kernel

/-! ## 3. The prime model of `Theory.field` over `S`: the fraction field of the coordinate ring -/

section Construction

variable {S : Type u} [Language.ring.Structure S]
variable {M : Type u} [CommRing M] [CompatibleRing M] [IsDomain M]

/-- The ideal of polynomial relations of `S`, computed in `M`. -/
noncomputable abbrev relIdeal (e : S ↪[Language.ring] M) : Ideal (FreeCommRing S) :=
  RingHom.ker (FreeCommRing.lift (fun s => e s))

/-- The coordinate ring of `S` relative to an embedding into a field `M`: the free commutative
ring on the generators `S` modulo the polynomial relations holding in `M`.  By `ker_lift_eq` it
does not depend on `M`. -/
noncomputable abbrev coordRing (e : S ↪[Language.ring] M) : Type u :=
  FreeCommRing S ⧸ relIdeal e

/-- The relations of `S` form a prime ideal, because they are the kernel of a homomorphism into
the domain `M`. -/
instance relIdeal.isPrime (e : S ↪[Language.ring] M) : (relIdeal e).IsPrime :=
  RingHom.ker_isPrime _

noncomputable instance coordRing.instCommRing (e : S ↪[Language.ring] M) :
    CommRing (coordRing e) :=
  inferInstanceAs (CommRing (FreeCommRing S ⧸ relIdeal e))

noncomputable instance coordRing.instIsDomain (e : S ↪[Language.ring] M) :
    IsDomain (coordRing e) :=
  inferInstanceAs (IsDomain (FreeCommRing S ⧸ relIdeal e))

noncomputable instance coordRing.instCompatibleRing (e : S ↪[Language.ring] M) :
    CompatibleRing (coordRing e) :=
  compatibleRingOfRing _

/-- The prime model of the theory of fields over `S`: the fraction field of the coordinate
ring. -/
noncomputable abbrev primeField (e : S ↪[Language.ring] M) : Type u :=
  FractionRing (coordRing e)

noncomputable instance primeField.instField (e : S ↪[Language.ring] M) : Field (primeField e) :=
  inferInstanceAs (Field (FractionRing (coordRing e)))

noncomputable instance primeField.instCompatibleRing (e : S ↪[Language.ring] M) :
    CompatibleRing (primeField e) :=
  compatibleRingOfRing _

/-- The map from `S` to its prime model, `s ↦ of s / 1`. -/
noncomputable abbrev primeMapFun (e : S ↪[Language.ring] M) : S → primeField e :=
  fun s => algebraMap (coordRing e) (primeField e)
    (Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of s))

/-- In the coordinate ring, evaluating a term built from `x` in `S` agrees with the ring
operation on the images: for every function symbol `g` of the language of rings,
`of (g(x)) = g(of x)` holds modulo the relations.  This is where the choice of the relations
(as the kernel of an embedding into a domain) is used. -/
theorem mk_of_funMap (e : S ↪[Language.ring] M) {n : ℕ}
    (g : Language.ring.Functions n) (x : Fin n → S) :
    Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of (Structure.funMap g x))
      = Structure.funMap g
          (fun i => Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of (x i))) := by
  letI : CompatibleRing (FreeCommRing S) := compatibleRingOfRing _
  have hq := ringHom_map_fun (Ideal.Quotient.mk (relIdeal e)) g
    (fun i => FreeCommRing.of (x i))
  simp only [Function.comp_def] at hq
  rw [← hq]
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, RingHom.mem_ker, map_sub, FreeCommRing.lift_of]
  have h2 : FreeCommRing.lift (fun s => e s)
      (Structure.funMap g (fun i => FreeCommRing.of (x i)))
        = e (Structure.funMap g x) := by
    have he := ringHom_map_fun (FreeCommRing.lift (fun s => e s)) g
      (fun i => FreeCommRing.of (x i))
    simp only [Function.comp_def, FreeCommRing.lift_of] at he
    have he2 := e.map_fun g x
    simp only [Function.comp_def] at he2
    exact he.trans he2.symm
  rw [h2, sub_self]

@[simp]
theorem primeMapFun_apply (e : S ↪[Language.ring] M) (s : S) :
    primeMapFun e s = algebraMap (coordRing e) (primeField e)
      (Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of s)) := rfl

/-- The map `s ↦ of s / 1` commutes with the ring operations of the language. -/
theorem primeMapFun_funMap (e : S ↪[Language.ring] M) {n : ℕ}
    (g : Language.ring.Functions n) (x : Fin n → S) :
    primeMapFun e (Structure.funMap g x)
      = Structure.funMap g (fun i => primeMapFun e (x i)) := by
  have hq := ringHom_map_fun (algebraMap (coordRing e) (primeField e)) g
    (fun i => Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of (x i)))
  simp only [Function.comp_def] at hq
  rw [primeMapFun_apply, mk_of_funMap e g x]
  simpa only [primeMapFun_apply] using hq

/-- The same statement in the shape of `Language.Embedding.map_fun'`. -/
theorem primeMapFun_comp (e : S ↪[Language.ring] M) {n : ℕ}
    (g : Language.ring.Functions n) (x : Fin n → S) :
    primeMapFun e (Structure.funMap g x) = Structure.funMap g (primeMapFun e ∘ x) := by
  rw [primeMapFun_funMap e g x]
  simp only [Function.comp_def]

/-- **The embedding of `S` into its prime model.** -/
noncomputable def primeEmbedding (e : S ↪[Language.ring] M) :
    S ↪[Language.ring] primeField e where
  toFun := primeMapFun e
  inj' := by
    intro a b hab
    have h1 : Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of a)
        = Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of b) :=
      IsFractionRing.injective (coordRing e) (primeField e) hab
    have h2 : FreeCommRing.of a - FreeCommRing.of b ∈ relIdeal e :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem
        (I := relIdeal e) (x := FreeCommRing.of a) (y := FreeCommRing.of b)).mp h1
    have h3 : FreeCommRing.lift (fun s => e s)
        (FreeCommRing.of a - FreeCommRing.of b) = 0 := RingHom.mem_ker.mp h2
    rw [map_sub, FreeCommRing.lift_of, FreeCommRing.lift_of, sub_eq_zero] at h3
    exact e.injective h3
  map_fun' := fun {n} g x => primeMapFun_comp e g x
  map_rel' := by intro n R; exact isEmptyElim R

/-! ## 4. The universal property of the prime model -/

section Universal

variable {N : Type u} [Field N] [CompatibleRing N]

/-- **The prime model of `Theory.field` over `S` embeds into every field over `S`.** -/
theorem primeField_universal (e : S ↪[Language.ring] M) (f : S ↪[Language.ring] N) :
    ∃ g : primeField e ↪[Language.ring] N, g.comp (primeEmbedding e) = f := by
  have hker : relIdeal e = relIdeal f := ker_lift_eq e f
  -- the map on coordinate rings induced by `f`, well defined because the kernels agree
  let rHom : coordRing e →+* N :=
    Ideal.Quotient.lift (relIdeal e) (FreeCommRing.lift (fun s => f s)) (fun a ha => by
      rw [hker] at ha
      exact RingHom.mem_ker.mp ha)
  have rHom_inj : Function.Injective rHom := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [rHom, Ideal.Quotient.lift_mk] at hxy
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, hker, RingHom.mem_ker, map_sub, hxy, sub_self]
  -- extend it to the fraction field
  let gHom : primeField e →+* N :=
    IsFractionRing.lift (A := coordRing e) (K := primeField e) (L := N) rHom_inj
  have gHom_inj : Function.Injective gHom := by
    intro x y hxy
    have h : gHom (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    by_contra hne
    have hne' : x - y ≠ 0 := sub_ne_zero.mpr hne
    have h1 : gHom (x - y) * gHom ((x - y)⁻¹) = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hne', map_one]
    rw [h, zero_mul] at h1
    exact zero_ne_one h1
  have hgl : ∀ z : coordRing e,
      gHom (algebraMap (coordRing e) (primeField e) z) = rHom z :=
    fun z => IsFractionRing.lift_algebraMap rHom_inj z
  refine ⟨embeddingOfInjectiveRingHom gHom gHom_inj, ?_⟩
  refine FirstOrder.Language.Embedding.ext ?_
  intro s
  simp only [FirstOrder.Language.Embedding.comp_apply]
  have h7 : (embeddingOfInjectiveRingHom gHom gHom_inj : primeField e ↪[Language.ring] N)
      (primeEmbedding e s) = gHom (primeMapFun e s) := rfl
  rw [h7]
  have h4 : rHom (Ideal.Quotient.mk (relIdeal e) (FreeCommRing.of s))
      = FreeCommRing.lift (fun s => f s) (FreeCommRing.of s) := by
    simp only [rHom, Ideal.Quotient.lift_mk]
  rw [primeMapFun_apply, hgl, h4, FreeCommRing.lift_of]

end Universal

end Construction

end PrimeField

/-! ## 5. `HasPrimeModels Theory.field acf` -/

universe u

theorem hasPrimeModels_field_acf :
    JohnsonCriterion.HasPrimeModels.{0, 0, u} Theory.field acf := by
  intro S inst hS
  letI := inst
  obtain ⟨M, _hMacf, ⟨e⟩⟩ := hS
  letI : Field M := FirstOrder.Field.fieldOfModelField M
  letI : CompatibleRing M := FirstOrder.Field.compatibleRingOfModelField M
  refine ⟨Theory.ModelType.of Theory.field (PrimeField.primeField e), PrimeField.primeEmbedding e, ?_⟩
  intro N f
  letI : Field N := FirstOrder.Field.fieldOfModelField N
  letI : CompatibleRing N := FirstOrder.Field.compatibleRingOfModelField N
  exact PrimeField.primeField_universal e f

#print axioms hasPrimeModels_field_acf
#print axioms PrimeField.primeField_universal
#print axioms PrimeField.primeEmbedding
#print axioms PrimeField.mk_of_funMap
#print axioms PrimeField.ker_lift_eq
