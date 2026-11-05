/-
Copyright: none.  This file is evidence for the QE campaign (Johnson, *Fun with Fields*, §2.1).
-/
import Mathlib

/-!
# Prime models over substructures for valued fields

Johnson (*Fun with Fields*, Chapter 2, §2.1) applies his criterion for quantifier elimination
(Lemma 2.1.4) with `T₀` = the theory of valued fields in the one-sorted language `L_val`, whose
non-logical symbols are those of the language of rings together with a binary relation symbol
`v(x) ≤ v(y)`.  Hypothesis (i) of the criterion asks that `T₀` has *prime models over
substructures*, and Johnson discharges it in one sentence:

> If `R` is a substructure of a valued field `K`, the binary predicate uniquely determines the
> valuation structure on `Frac(R)`.  Consequently, the theory of valued fields has prime models
> over substructures.

This file proves exactly that sentence, algebraically.  A substructure of a valued field is a
domain `R` carrying a *faithful* valuation `v` (one with trivial support, i.e. `v r = 0 → r = 0`);
the only part of `v` visible to `L_val` is the binary relation `v x ≤ v y`, and that relation on
`R` is what we assume to be shared between the two valued field extensions.  The two statements
are:

* `vFrac_le_iff_of_le_iff` — **the predicate on `R` determines the predicate on `Frac R`.**
  Two faithful valuations on `R` defining the same relation `x ↦ v x` on `R` induce the same
  relation on `Frac R`.  Hence `Frac(R)` carries a well-defined `L_val`-structure which depends
  only on the `L_val`-structure of `R`.

* `exists_lift` — **the universal (prime model) property.**  Every `L_val`-embedding `R → K` of
  `R` into a valued field `K` extends to an `L_val`-embedding `Frac R → K`, uniquely.  Taking
  `M' = Frac R` in Definition 2.1.1 of the chapter, this is the required factorisation.

The formal predicate "embedding of valued fields" is `IsValEmb`: injectivity together with
preservation (both ways) of `v x ≤ v y`.  This is precisely the notion of embedding of
`L_val`-structures on fields, and it is closed under identity and composition
(`IsValEmb.id`, `IsValEmb.comp`).

Everything is proved for an arbitrary domain `R` with a faithful valuation (not just a subring of a
given field), which is the form in which substructures of valued fields present themselves;
`exists_lift_of_subring` records the case of an actual subring of a valued field, where the
hypotheses are automatic.  The one gap between this and a literal reading of Johnson's
Definition 2.1.1 is that an arbitrary model of `T₀∀` is not shown here to be a domain carrying a
valuation ring (hence a `Valuation`); every substructure of a valued field already is one, and that
is the case used in the proof of Lemma 2.1.4.

The last sections define Johnson's language `L_val` (`Language.val`), its structure on a valued
field (`valStructure`), show that `L_val`-embeddings are exactly the `IsValEmb` maps
(`isValEmb_iff_embedding`), and restate the universal property in that language
(`exists_lift_language`).

No `sorry`, no new axioms: see the `#print axioms` commands at the end.
-/

noncomputable section

namespace FracValued

open Valuation

/-! ## The valuation on the fraction field of a valued domain -/

section Basic

variable {R : Type*} [CommRing R] [IsDomain R]
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- A valuation on a domain is *faithful* if its support is trivial.  This is the condition on a
substructure of a valued field: the valuation of a valued field never takes the value `0` on a
nonzero element. -/
def Faithful (v : Valuation R Γ₀) : Prop := ∀ a : R, v a = 0 → a = 0

variable {v : Valuation R Γ₀}

omit [IsDomain R] in
theorem faithful_iff_supp_eq_bot : Faithful v ↔ v.supp = ⊥ := by
  constructor
  · intro hv
    ext a
    rw [Valuation.mem_supp_iff, Ideal.mem_bot]
    exact ⟨hv a, fun h => by rw [h, map_zero]⟩
  · intro h a ha
    have : a ∈ v.supp := by rw [Valuation.mem_supp_iff]; exact ha
    rw [h] at this
    simpa using this

/-- Nonzero elements of a faithfully valued domain are invertible for the valuation, so that
`Valuation.extendToLocalization` applies to the fraction field. -/
theorem nonZeroDivisors_le_primeCompl (hv : Faithful v) :
    nonZeroDivisors R ≤ v.supp.primeCompl := by
  intro s hs
  rw [Ideal.mem_primeCompl_iff, Valuation.mem_supp_iff]
  exact fun h => (nonZeroDivisors.ne_zero hs) (hv s h)

/-- **The valuation of the fraction field**, extending a faithful valuation `v` on `R`. -/
noncomputable def vFrac (v : Valuation R Γ₀) (hv : Faithful v) :
    Valuation (FractionRing R) Γ₀ :=
  v.extendToLocalization (nonZeroDivisors_le_primeCompl hv) (FractionRing R)

@[simp]
theorem vFrac_algebraMap (v : Valuation R Γ₀) (hv : Faithful v) (a : R) :
    vFrac v hv (algebraMap R (FractionRing R) a) = v a := by
  simp only [vFrac, Valuation.extendToLocalization_apply_map_apply]

theorem vFrac_mk' (v : Valuation R Γ₀) (hv : Faithful v) (a : R) (b : nonZeroDivisors R) :
    vFrac v hv (IsLocalization.mk' (FractionRing R) a b) = v a * (v (b : R))⁻¹ := by
  simp only [vFrac, Valuation.extendToLocalization_mk']

/-- Cross multiplication: in a linearly ordered commutative group with zero, `a/b ≤ c/d` is decided
by `a * d ≤ c * b` as soon as `b` and `d` are nonzero. -/
theorem div_le_div_iff_of_ne {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b c d : Γ}
    (hb : b ≠ 0) (hd : d ≠ 0) : a / b ≤ c / d ↔ a * d ≤ c * b :=
  div_le_div_iff₀ (zero_lt_iff.mpr hb) (zero_lt_iff.mpr hd)

/-- **The predicate on `Frac R` is computed by cross multiplication in `R`.** -/
theorem vFrac_mk'_le_mk'_iff (v : Valuation R Γ₀) (hv : Faithful v) (a c : R)
    (b d : nonZeroDivisors R) :
    vFrac v hv (IsLocalization.mk' (FractionRing R) a b)
        ≤ vFrac v hv (IsLocalization.mk' (FractionRing R) c d) ↔
      v (a * (d : R)) ≤ v (c * (b : R)) := by
  rw [vFrac_mk', vFrac_mk', ← div_eq_mul_inv, ← div_eq_mul_inv,
    div_le_div_iff_of_ne (fun h => (nonZeroDivisors.ne_zero b.2) (hv b h))
      (fun h => (nonZeroDivisors.ne_zero d.2) (hv d h)),
    map_mul, map_mul]

/-- **The `L_val`-predicate on `Frac R` is determined by the predicate on `R`.**  Two faithful
valuations on `R` which induce the same relation `v x ≤ v y` on `R` induce the same relation on
the fraction field.  This is the uniqueness half of "the binary predicate uniquely determines the
valuation structure on `Frac(R)`". -/
theorem vFrac_le_iff_of_le_iff {v₁ : Valuation R Γ₀} {Γ₁ : Type*}
    [LinearOrderedCommGroupWithZero Γ₁] {v₂ : Valuation R Γ₁}
    (h₁ : Faithful v₁) (h₂ : Faithful v₂)
    (h : ∀ a b : R, v₁ a ≤ v₁ b ↔ v₂ a ≤ v₂ b) (x y : FractionRing R) :
    vFrac v₁ h₁ x ≤ vFrac v₁ h₁ y ↔ vFrac v₂ h₂ x ≤ vFrac v₂ h₂ y := by
  obtain ⟨a, b, rfl⟩ := IsLocalization.exists_mk'_eq (M := nonZeroDivisors R) (S := FractionRing R) x
  obtain ⟨c, d, rfl⟩ := IsLocalization.exists_mk'_eq (M := nonZeroDivisors R) (S := FractionRing R) y
  rw [vFrac_mk'_le_mk'_iff, vFrac_mk'_le_mk'_iff, h]

end Basic

/-! ## Embeddings of valued fields -/

section Embeddings

variable {K : Type*} [CommRing K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
variable {L : Type*} [CommRing L] {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']
variable {M : Type*} [CommRing M] {Γ'' : Type*} [LinearOrderedCommGroupWithZero Γ'']

/-- An embedding of valued fields in the sense of the one-sorted language `L_val` of Johnson §2.1:
a ring embedding which preserves the binary relation `v x ≤ v y` in both directions.  (Stated for
commutative rings so that it also applies to a domain and its fraction field.) -/
def IsValEmb (f : K →+* L) (v : Valuation K Γ) (w : Valuation L Γ') : Prop :=
  Function.Injective f ∧ ∀ x y : K, v x ≤ v y ↔ w (f x) ≤ w (f y)

theorem IsValEmb.id (v : Valuation K Γ) : IsValEmb (RingHom.id K) v v :=
  ⟨fun _ _ h => h, fun _ _ => Iff.rfl⟩

theorem IsValEmb.comp {f : K →+* L} {g : L →+* M} {v : Valuation K Γ} {w : Valuation L Γ'}
    {u : Valuation M Γ''} (hf : IsValEmb f v w) (hg : IsValEmb g w u) :
    IsValEmb (g.comp f) v u := by
  refine ⟨hg.1.comp hf.1, fun x y => ?_⟩
  rw [RingHom.comp_apply, RingHom.comp_apply, hf.2, hg.2]

end Embeddings

/-! ## The universal property: `Frac R` is the prime model over `R` -/

section PrimeModel

variable {R : Type*} [CommRing R] [IsDomain R]
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
variable {v : Valuation R Γ₀}

/-- Values of quotients in a faithfully valued field, by cross multiplication. -/
theorem value_div_le_iff {K : Type*} [Field K] {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']
    (w : Valuation K Γ') (hw : Faithful w) {x y b d : K} (hb : b ≠ 0) (hd : d ≠ 0) :
    w (x / b) ≤ w (y / d) ↔ w (x * d) ≤ w (y * b) := by
  rw [map_div₀, map_div₀,
    div_le_div_iff_of_ne (fun h => hb (hw b h)) (fun h => hd (hw d h)), map_mul, map_mul]

/-- **The prime model property for valued fields.**  Every embedding of a valued domain `R` into a
valued field `K` which preserves the relation `v x ≤ v y` extends, uniquely, to an embedding of
valued fields `Frac R → K`.

This is hypothesis (i) of Johnson's Lemma 2.1.4 for the theory of valued fields: `Frac R`, with
the valuation `vFrac v hv`, is the prime model over the substructure `R`. -/
theorem exists_lift {K : Type*} [Field K] {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']
    (v : Valuation R Γ₀) (hv : Faithful v) (w : Valuation K Γ') (hw : Faithful w)
    (f : R →+* K) (hf : Function.Injective f)
    (hord : ∀ a b : R, v a ≤ v b ↔ w (f a) ≤ w (f b)) :
    ∃ g : FractionRing R →+* K,
      (∀ a : R, g (algebraMap R (FractionRing R) a) = f a) ∧
        IsValEmb g (vFrac v hv) w := by
  refine ⟨IsFractionRing.lift hf, fun a => IsFractionRing.lift_algebraMap hf a,
    RingHom.injective _, fun x y => ?_⟩
  obtain ⟨a, b, rfl⟩ := IsLocalization.exists_mk'_eq (M := nonZeroDivisors R) (S := FractionRing R) x
  obtain ⟨c, d, rfl⟩ := IsLocalization.exists_mk'_eq (M := nonZeroDivisors R) (S := FractionRing R) y
  have hb : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hd : (d : R) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hfb : f (b : R) ≠ 0 := by rw [← map_zero f]; exact hf.ne hb
  have hfd : f (d : R) ≠ 0 := by rw [← map_zero f]; exact hf.ne hd
  rw [vFrac_mk'_le_mk'_iff, IsFractionRing.lift_mk', IsFractionRing.lift_mk',
    value_div_le_iff w hw hfb hfd, ← map_mul, ← map_mul, hord]

/-- `R` embeds in its fraction field as a valued field, so the first half of Johnson's
Definition 2.1.1 (`M ↪ M'`) is discharged together with `exists_lift` (the second half). -/
theorem isValEmb_algebraMap (v : Valuation R Γ₀) (hv : Faithful v) :
    IsValEmb (algebraMap R (FractionRing R)) v (vFrac v hv) :=
  ⟨IsFractionRing.injective R (FractionRing R), fun a b => by simp only [vFrac_algebraMap]⟩

/-- **Johnson's Definition 2.1.1 for valued fields**, assembled: `R` embeds in `Frac R` as a
valued field, and `Frac R` embeds in every valued field into which `R` embeds.  Together with the
determination of the predicate on `Frac R` (`vFrac_le_iff_of_le_iff`), this is hypothesis (i) of
Lemma 2.1.4 for the theory of valued fields. -/
theorem prime_models_over_substructures (v : Valuation R Γ₀) (hv : Faithful v) :
    IsValEmb (algebraMap R (FractionRing R)) v (vFrac v hv) ∧
      ∀ {K : Type*} [Field K] {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']
        (w : Valuation K Γ') (hw : Faithful w) (f : R →+* K) (hf : Function.Injective f),
        (∀ a b : R, v a ≤ v b ↔ w (f a) ≤ w (f b)) →
        ∃ g : FractionRing R →+* K,
          (∀ a : R, g (algebraMap R (FractionRing R) a) = f a) ∧ IsValEmb g (vFrac v hv) w :=
  ⟨isValEmb_algebraMap v hv, fun w hw f hf hord => exists_lift v hv w hw f hf hord⟩

/-- Uniqueness of the extension: any ring hom `Frac R → K` agreeing with `f` on `R` is the one
constructed in `exists_lift`.  In particular the prime model is unique up to the identity of
`Frac R`. -/
theorem lift_unique {K : Type*} [Field K] (f : R →+* K) (hf : Function.Injective f)
    (g : FractionRing R →+* K) (hg : ∀ a : R, g (algebraMap R (FractionRing R) a) = f a) :
    g = IsFractionRing.lift hf :=
  (IsFractionRing.lift_unique hf hg).symm

/-- Johnson's Definition 2.1.1, for the theory of valued fields: given two valued field extensions
`K₁` and `K₂` of a valued domain `R`, the fraction field `Frac R` (with its induced valuation)
embeds into both, compatibly with the embeddings of `R`.  This is the "prime model over a
substructure" diagram completion used in the proof of Lemma 2.1.4. -/
theorem prime_model_property {K₁ : Type*} [Field K₁] {Γ₁ : Type*}
    [LinearOrderedCommGroupWithZero Γ₁] {K₂ : Type*} [Field K₂] {Γ₂ : Type*}
    [LinearOrderedCommGroupWithZero Γ₂]
    (v : Valuation R Γ₀) (hv : Faithful v)
    (w₁ : Valuation K₁ Γ₁) (hw₁ : Faithful w₁) (w₂ : Valuation K₂ Γ₂) (hw₂ : Faithful w₂)
    (f₁ : R →+* K₁) (hf₁ : Function.Injective f₁)
    (hord₁ : ∀ a b : R, v a ≤ v b ↔ w₁ (f₁ a) ≤ w₁ (f₁ b))
    (f₂ : R →+* K₂) (hf₂ : Function.Injective f₂)
    (hord₂ : ∀ a b : R, v a ≤ v b ↔ w₂ (f₂ a) ≤ w₂ (f₂ b)) :
    ∃ (g₁ : FractionRing R →+* K₁) (g₂ : FractionRing R →+* K₂),
      (∀ a : R, g₁ (algebraMap R (FractionRing R) a) = f₁ a) ∧
        (∀ a : R, g₂ (algebraMap R (FractionRing R) a) = f₂ a) ∧
          IsValEmb g₁ (vFrac v hv) w₁ ∧ IsValEmb g₂ (vFrac v hv) w₂ := by
  obtain ⟨g₁, hg₁, hve₁⟩ := exists_lift v hv w₁ hw₁ f₁ hf₁ hord₁
  obtain ⟨g₂, hg₂, hve₂⟩ := exists_lift v hv w₂ hw₂ f₂ hf₂ hord₂
  exact ⟨g₁, g₂, hg₁, hg₂, hve₁, hve₂⟩

/-- The case occurring in the criterion: `R` is literally a subring of a valued field `K`.  Then
the valuation on `R` is the restriction of the valuation of `K`, so both hypotheses of
`exists_lift` are automatic. -/
theorem exists_lift_of_subring {K : Type*} [Field K] {Γ' : Type*}
    [LinearOrderedCommGroupWithZero Γ'] (w : Valuation K Γ') (hw : Faithful w) (S : Subring K) :
    ∃ g : FractionRing S →+* K,
      (∀ a : S, g (algebraMap S (FractionRing S) a) = a) ∧
        IsValEmb g (vFrac (w.comap S.subtype) (fun a ha => Subtype.coe_injective (hw a ha))) w := by
  have hcomp : Faithful (w.comap S.subtype) := fun a ha =>
    Subtype.coe_injective (hw (a : K) ha)
  refine exists_lift (w.comap S.subtype) hcomp w hw S.subtype (fun _ _ h => Subtype.coe_injective h)
    (fun a b => ?_)
  rfl

end PrimeModel

/-! ## The one-sorted language `L_val`

Johnson's language is the language of rings together with one binary relation symbol, interpreted
as `v x ≤ v y`.  We define it, the structure on a valued field, and prove that its embeddings are
exactly the `IsValEmb` maps studied above.  This is only packaging: it lets the prime model
property be stated in the form hypothesis (i) of Lemma 2.1.4 is phrased in. -/

section Language

/-- Function symbols of `L_val`: those of the language of rings. -/
inductive ValFunc : ℕ → Type
  | add : ValFunc 2
  | mul : ValFunc 2
  | neg : ValFunc 1
  | zero : ValFunc 0
  | one : ValFunc 0
  deriving DecidableEq

/-- Relation symbols of `L_val`: the single binary predicate `v x ≤ v y`. -/
inductive ValRel : ℕ → Type
  | le : ValRel 2
  deriving DecidableEq

/-- **Johnson's language `L_val`**: the language of rings expanded by a binary predicate for the
relation `v x ≤ v y`. -/
def Language.val : FirstOrder.Language := ⟨ValFunc, ValRel⟩

/-- **The `L_val`-structure of a valued field.** -/
@[instance_reducible]
def valStructure {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) : Language.val.Structure K where
  funMap := fun {_} f x =>
    match f with
    | ValFunc.add => x 0 + x 1
    | ValFunc.mul => x 0 * x 1
    | ValFunc.neg => - x 0
    | ValFunc.zero => 0
    | ValFunc.one => 1
  RelMap := fun {_} r x =>
    match r with
    | ValRel.le => v (x 0) ≤ v (x 1)

section LanguageEmbeddings

variable {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
variable {L : Type*} [Field L] {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']
variable {M : Type*} [Field M] {Γ'' : Type*} [LinearOrderedCommGroupWithZero Γ'']

/-- An `L_val`-embedding is an `IsValEmb` map: this is the direction used to apply the algebraic
results of this file inside the criterion. -/
def embeddingOfIsValEmb (v : Valuation K Γ) (w : Valuation L Γ') (f : K →+* L)
    (h : IsValEmb f v w) :
    @FirstOrder.Language.Embedding Language.val K L (valStructure v) (valStructure w) := by
  letI := valStructure v
  letI := valStructure w
  refine { toFun := f, inj' := h.1, map_fun' := ?_, map_rel' := ?_ }
  · intro _ g x
    cases g with
    | add => exact map_add f (x 0) (x 1)
    | mul => exact map_mul f (x 0) (x 1)
    | neg => exact map_neg f (x 0)
    | zero => exact map_zero f
    | one => exact map_one f
  · intro _ r x
    cases r with
    | le => exact (h.2 (x 0) (x 1)).symm

/-- The ring hom underlying an `L_val`-embedding. -/
def ringHomOfEmbedding (v : Valuation K Γ) (w : Valuation L Γ')
    (F : @FirstOrder.Language.Embedding Language.val K L (valStructure v) (valStructure w)) :
    K →+* L := by
  letI := valStructure v
  letI := valStructure w
  exact { toFun := F
          map_one' := F.map_fun' ValFunc.one (fun i => Fin.elim0 i)
          map_zero' := F.map_fun' ValFunc.zero (fun i => Fin.elim0 i)
          map_mul' := fun x y => F.map_fun' ValFunc.mul ![x, y]
          map_add' := fun x y => F.map_fun' ValFunc.add ![x, y] }

/-- Conversely, an `L_val`-embedding is an `IsValEmb` map, so the two notions of embedding of
valued fields agree. -/
theorem isValEmb_ringHomOfEmbedding (v : Valuation K Γ) (w : Valuation L Γ')
    (F : @FirstOrder.Language.Embedding Language.val K L (valStructure v) (valStructure w)) :
    IsValEmb (ringHomOfEmbedding v w F) v w := by
  letI := valStructure v
  letI := valStructure w
  refine ⟨fun x y hxy => F.inj' hxy, fun x y => ?_⟩
  exact (F.map_rel' ValRel.le ![x, y]).symm

theorem isValEmb_iff_embedding (v : Valuation K Γ) (w : Valuation L Γ') (f : K →+* L) :
    IsValEmb f v w ↔
      ∃ F : @FirstOrder.Language.Embedding Language.val K L (valStructure v) (valStructure w),
        ⇑F = f := by
  constructor
  · intro h
    exact ⟨embeddingOfIsValEmb v w f h, rfl⟩
  · rintro ⟨F, hF⟩
    have h : ringHomOfEmbedding v w F = f := by
      ext x
      exact congrFun hF x
    rw [← h]
    exact isValEmb_ringHomOfEmbedding v w F

end LanguageEmbeddings

end Language

/-! ## The prime model property, stated in `L_val` -/

section LanguagePrimeModel

variable {R : Type*} [CommRing R] [IsDomain R]
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
variable {v : Valuation R Γ₀}

/-- **Johnson Definition 2.1.1 for valued fields, in the language `L_val`.**  Every embedding of
the valued domain `R` into a valued field `K` extends to an embedding of `L_val`-structures
`Frac R → K` carrying `R` into `K` compatibly.  This is the diagram completion
`R ↪ Frac R ↪ K` required of the prime model `Frac R` over the substructure `R`. -/
theorem exists_lift_language {K : Type*} [Field K] {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ']
    (v : Valuation R Γ₀) (hv : Faithful v) (w : Valuation K Γ') (hw : Faithful w)
    (f : R →+* K) (hf : Function.Injective f)
    (hord : ∀ a b : R, v a ≤ v b ↔ w (f a) ≤ w (f b)) :
    ∃ F : @FirstOrder.Language.Embedding Language.val (FractionRing R) K
        (valStructure (vFrac v hv)) (valStructure w),
      ∀ a : R, F (algebraMap R (FractionRing R) a) = f a := by
  obtain ⟨g, hg, hge⟩ := exists_lift v hv w hw f hf hord
  exact ⟨embeddingOfIsValEmb (vFrac v hv) w g hge, hg⟩

end LanguagePrimeModel

end FracValued

/-! ## Axiom check -/

#print axioms FracValued.vFrac_le_iff_of_le_iff
#print axioms FracValued.IsValEmb.comp
#print axioms FracValued.isValEmb_algebraMap
#print axioms FracValued.prime_models_over_substructures
#print axioms FracValued.exists_lift
#print axioms FracValued.lift_unique
#print axioms FracValued.prime_model_property
#print axioms FracValued.exists_lift_of_subring
#print axioms FracValued.isValEmb_iff_embedding
#print axioms FracValued.exists_lift_language
