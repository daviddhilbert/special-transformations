module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Etale.Finite
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Unramified.LocalStructure
public import StacksCore.Tactic.StacksAttribute

/-!
# Étale maps into a henselian local ring (Stacks tag 08HQ)

Let `R → S` be a ring map with `S` henselian local, `p = R ∩ m_S`, `R → A` étale, `q` a prime
of `A` over `p` and `τ : κ(q) → κ(m_S)` a `κ(p)`-algebra map. There is a unique `R`-algebra map
`f : A → S` with `q = f⁻¹(m_S)` inducing `τ` on residue fields. The proof goes through
`S`-algebra retractions of the étale `S`-algebra `S ⊗[R] A`.

## Main results

* `henselian_etale_retraction`, `henselian_etale_retraction_unique`: existence and uniqueness of
  an `S`-algebra retraction with prescribed prime over `m_S`.
* `existsUnique_algHom_henselian_of_residue_datum`: the étale case of Tag 08HQ.
-/

@[expose] public section

open Algebra IsLocalRing Ideal TensorProduct in
/-- Residue data for a localization away from an element outside `𝔫`.

Let `S` be a local ring, `B` an `S`-algebra and `𝔫` a prime of `B` lying over `m_S`
whose residue extension `κ(m_S) → κ(𝔫)` is bijective. Let `f ∉ 𝔫` and let `L` be a
localization of `B` away from `f`, and put `𝔮 := 𝔫·L`. Then `𝔮` is prime, contracts
to `𝔫` along `B → L`, the composite `S → L ⧸ 𝔮` has kernel exactly `m_S` (so an
element of `S` with nonzero image is a unit), and that composite is surjective.

These are precisely the facts about the localization that both halves of the
henselian retraction argument (`henselian_etale_retraction` and
`henselian_etale_retraction_unique`) need before running their respective Hensel
arguments: `B` is presented near `𝔫` as a standard étale `S`-algebra, and the
standard-étale coordinate `P.x` is compared with an element of `S` through
`S ↠ L ⧸ 𝔮`. -/
private theorem localization_away_residue_data
    {S : Type*} [CommRing S] [IsLocalRing S]
    {B : Type*} [CommRing B] [Algebra S B]
    (𝔫 : Ideal B) [𝔫.IsPrime]
    (hlo : 𝔫.comap (algebraMap S B) = maximalIdeal S)
    (hres : Function.Bijective
      (Ideal.ResidueField.map (maximalIdeal S) 𝔫 (algebraMap S B) hlo.symm))
    {f : B} (hf_notin : f ∉ 𝔫)
    (L : Type*) [CommRing L] [Algebra B L] [IsLocalization.Away f L]
    [Algebra S L] [IsScalarTower S B L] :
    (𝔫.map (algebraMap B L)).IsPrime ∧
      (𝔫.map (algebraMap B L)).comap (algebraMap B L) = 𝔫 ∧
      (∀ s : S, algebraMap S (L ⧸ 𝔫.map (algebraMap B L)) s = 0 ↔ s ∈ maximalIdeal S) ∧
      (∀ s : S, algebraMap S (L ⧸ 𝔫.map (algebraMap B L)) s ≠ 0 → IsUnit s) ∧
      Function.Surjective (algebraMap S (L ⧸ 𝔫.map (algebraMap B L))) := by
  -- `S → B ⧸ 𝔫` is surjective, from the bijective residue extension.
  have hsurjB : Function.Surjective (algebraMap S (B ⧸ 𝔫)) := by
    have hSres : Function.Surjective (algebraMap S 𝔫.ResidueField) := by
      have h1 : (algebraMap S 𝔫.ResidueField) =
          (Ideal.ResidueField.map (maximalIdeal S) 𝔫 (algebraMap S B) hlo.symm).comp
            (algebraMap S (maximalIdeal S).ResidueField) := by
        ext s
        simp only [RingHom.coe_comp, Function.comp_apply, Ideal.ResidueField.map_algebraMap]; rfl
      rw [h1, RingHom.coe_comp]
      exact hres.surjective.comp (algebraMap_residueField_surjective (maximalIdeal S))
    intro bb
    obtain ⟨s, hs⟩ := hSres (algebraMap (B ⧸ 𝔫) 𝔫.ResidueField bb)
    exact ⟨s, (injective_algebraMap_quotient_residueField 𝔫)
      (by rw [← hs, ← IsScalarTower.algebraMap_apply S (B ⧸ 𝔫) 𝔫.ResidueField])⟩
  set 𝔮 : Ideal L := 𝔫.map (algebraMap B L) with h𝔮
  have hdisj : Disjoint (↑(Submonoid.powers f) : Set B) ↑𝔫 := by
    rw [Set.disjoint_left]
    rintro x ⟨n, rfl⟩ hx
    exact hf_notin (‹𝔫.IsPrime›.mem_of_pow_mem _ hx)
  have hqprime : 𝔮.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) L 𝔫 ‹_› hdisj
  have hcomapBL : 𝔮.comap (algebraMap B L) = 𝔫 :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f) L ‹𝔫.IsPrime› hdisj
  have htower : (algebraMap S L) = (algebraMap B L).comp (algebraMap S B) :=
    IsScalarTower.algebraMap_eq S B L
  have hlo' : 𝔮.comap (algebraMap S L) = maximalIdeal S := by
    rw [htower, ← Ideal.comap_comap, hcomapBL, hlo]
  have hker : ∀ s : S, algebraMap S (L ⧸ 𝔮) s = 0 ↔ s ∈ maximalIdeal S := by
    intro s
    rw [IsScalarTower.algebraMap_apply S L (L ⧸ 𝔮), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hlo']
  have hunit : ∀ s : S, algebraMap S (L ⧸ 𝔮) s ≠ 0 → IsUnit s := by
    intro s hs0
    exact by_contra fun h =>
      hs0 ((hker s).mpr (by rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]))
  refine ⟨hqprime, hcomapBL, hker, hunit, ?_⟩
  have hBS : ∀ b : B, ∃ s : S, (Ideal.Quotient.mk 𝔮) (algebraMap B L b)
        = algebraMap S (L ⧸ 𝔮) s := by
    intro b
    obtain ⟨s, hs⟩ := hsurjB (Ideal.Quotient.mk 𝔫 b)
    refine ⟨s, ?_⟩
    have hmem : b - algebraMap S B s ∈ 𝔫 := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, ← hs,
        IsScalarTower.algebraMap_apply S B (B ⧸ 𝔫), Ideal.Quotient.algebraMap_eq]
    have hmemq : algebraMap B L b - algebraMap B L (algebraMap S B s) ∈ 𝔮 := by
      rw [← map_sub]
      exact (by rwa [hcomapBL] : b - algebraMap S B s ∈ 𝔮.comap (algebraMap B L))
    have h2 : algebraMap S (L ⧸ 𝔮) s
        = (Ideal.Quotient.mk 𝔮) (algebraMap B L (algebraMap S B s)) := by
      rw [IsScalarTower.algebraMap_apply S L (L ⧸ 𝔮), Ideal.Quotient.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply S B L]
    rw [h2]
    exact Ideal.Quotient.eq.mpr hmemq
  intro y
  obtain ⟨l, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨⟨b, ⟨_, n, rfl⟩⟩, hb⟩ := IsLocalization.surj (Submonoid.powers f) l
  simp only at hb
  obtain ⟨sb, hsb⟩ := hBS b
  obtain ⟨sf, hsf⟩ := hBS (f ^ n)
  have hfunit : IsUnit (algebraMap B L (f ^ n)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit f).pow n
  have hu : IsUnit (algebraMap S (L ⧸ 𝔮) sf) := by
    rw [← hsf]
    exact hfunit.map (Ideal.Quotient.mk 𝔮)
  have hsfunit : IsUnit sf := hunit sf (hu.ne_zero)
  refine ⟨sb * (↑hsfunit.unit⁻¹ : S), ?_⟩
  rw [map_mul]
  have hbq : (Ideal.Quotient.mk 𝔮) l * algebraMap S (L ⧸ 𝔮) sf = algebraMap S (L ⧸ 𝔮) sb := by
    rw [← hsf, ← hsb, ← map_mul, hb]
  have hinv : algebraMap S (L ⧸ 𝔮) sf * algebraMap S (L ⧸ 𝔮) (↑hsfunit.unit⁻¹ : S) = 1 := by
    rw [← map_mul, hsfunit.mul_val_inv, map_one]
  rw [← hbq, mul_assoc, hinv, mul_one]

open Algebra IsLocalRing Ideal TensorProduct in
/-- **Henselian retraction** (heart of Stacks Tag 08HQ; cf. Stacks 04GG/08HR).
Let `S` be a henselian local ring and `B` an étale `S`-algebra. If `𝔫` is a prime
of `B` lying over the maximal ideal `m_S` whose residue field equals `κ(m_S)`
(i.e. the induced residue map `κ(m_S) → κ(𝔫)` is bijective), then there is an
`S`-algebra retraction `σ : B →ₐ[S] S` with `σ⁻¹(m_S) = 𝔫`.

The retraction is built by presenting `B` near `𝔫` as a standard-étale `S`-algebra
`B_𝔫 ≅ (S[T]/(F))_G` (Stacks 00UH). The condition `κ(𝔫) = κ(m_S)` gives a root
`ā₀ ∈ κ(m_S) = S/m_S` of `F̄` at which `F̄'` is a unit, since `B` is étale over `S`.
Hensel's lemma lifts `ā₀` to a root `a ∈ S` of `F` with `IsUnit (F'(a))`, and
sending `T ↦ a` determines an `S`-algebra map `σ : B →ₐ[S] S` with `σ⁻¹(m_S) = 𝔫`.
The Hensel root `a` is unique, which is the source of the uniqueness statement
`henselian_etale_retraction_unique`. -/
@[ega "IV 18.6.2" "partial",
  ega "IV 18.8.1" "(a)⇒(c), special case",
  sga "3 X 4.5" "special case",
  sga "3 XI 1.11" "special case"]
lemma henselian_etale_retraction
    (S : Type*) [CommRing S] [HenselianLocalRing S]
    (B : Type*) [CommRing B] [Algebra S B] [Algebra.Etale S B]
    (𝔫 : Ideal B) [𝔫.IsPrime]
    (hlo : 𝔫.comap (algebraMap S B) = maximalIdeal S)
    (hres : Function.Bijective
      (Ideal.ResidueField.map (maximalIdeal S) 𝔫 (algebraMap S B) hlo.symm)) :
    ∃ σ : B →ₐ[S] S, (maximalIdeal S).comap σ.toRingHom = 𝔫 := by
  -- Step 1: present B near 𝔫 as standard étale (Stacks 00UH) and localize.
  obtain ⟨f, hf_notin, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := S) (S := B) 𝔫
  obtain ⟨P⟩ := hstd.nonempty_standardEtalePresentation
  set L := Localization.Away f with hL
  -- Step 2: S → L/𝔮 is surjective and identifies its kernel with m_S.
  obtain ⟨hqprime, hcomapBL, hker, hunit, hsurjL⟩ :=
    localization_away_residue_data 𝔫 hlo hres hf_notin L
  set 𝔮 : Ideal L := 𝔫.map (algebraMap B L) with h𝔮
  -- Step 3: extract the root data and lift it via Hensel's lemma.
  have h1 : P.P.HasMap P.x := P.hasMap
  rw [StandardEtalePair.HasMap.eq_1] at h1
  obtain ⟨hf0, hgunit⟩ := h1
  have hderiv : IsUnit ((Polynomial.aeval P.x) (Polynomial.derivative P.P.f)) :=
    P.hasMap.isUnit_derivative_f
  obtain ⟨x₀, hx₀⟩ := hsurjL (Ideal.Quotient.mk 𝔮 P.x)
  have hpoly : ∀ p : Polynomial S, (Ideal.Quotient.mk 𝔮) (Polynomial.aeval P.x p)
        = algebraMap S (L ⧸ 𝔮) (Polynomial.aeval x₀ p) := by
    intro p
    have e1 : (Ideal.Quotient.mk 𝔮) (Polynomial.aeval P.x p)
        = Polynomial.aeval (Ideal.Quotient.mk 𝔮 P.x) p := by
      rw [← Ideal.Quotient.algebraMap_eq, Polynomial.aeval_algebraMap_apply]
    rw [e1, ← hx₀, ← Polynomial.aeval_algebraMap_apply]
  have heval_eq : ∀ p : Polynomial S, Polynomial.eval x₀ p = Polynomial.aeval x₀ p := by
    intro p
    simp [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  have heval_mem : Polynomial.eval x₀ P.P.f ∈ maximalIdeal S := by
    rw [← hker, heval_eq, ← hpoly P.P.f, hf0, map_zero]
  have hderiv_unit : IsUnit (Polynomial.eval x₀ (Polynomial.derivative P.P.f)) := by
    rw [heval_eq]
    apply hunit
    rw [← hpoly (Polynomial.derivative P.P.f)]
    exact (hderiv.map (Ideal.Quotient.mk 𝔮)).ne_zero
  obtain ⟨a, ha_root, ha_mem⟩ :=
    HenselianLocalRing.is_henselian P.P.f P.P.monic_f x₀ heval_mem hderiv_unit
  -- Step 4: the Hensel root gives an S-point of the standard-étale pair.
  have hqa : algebraMap S (L ⧸ 𝔮) a = Ideal.Quotient.mk 𝔮 P.x := by
    have : algebraMap S (L ⧸ 𝔮) (a - x₀) = 0 := (hker _).mpr ha_mem
    rw [map_sub, sub_eq_zero] at this
    rw [this, hx₀]
  have hpolyA : ∀ p : Polynomial S, algebraMap S (L ⧸ 𝔮) (Polynomial.aeval a p)
        = (Ideal.Quotient.mk 𝔮) (Polynomial.aeval P.x p) := by
    intro p
    rw [← Polynomial.aeval_algebraMap_apply (L ⧸ 𝔮) a p, hqa,
      ← Ideal.Quotient.algebraMap_eq, Polynomial.aeval_algebraMap_apply]
  have hHasMap : P.P.HasMap a := by
    rw [StandardEtalePair.HasMap.eq_1]
    refine ⟨?_, ?_⟩
    · rw [Polynomial.coe_aeval_eq_eval]
      exact ha_root
    · apply hunit
      rw [hpolyA P.P.g]
      exact (hgunit.map (Ideal.Quotient.mk 𝔮)).ne_zero
  -- Step 5: assemble σ : B → L ≅ P.Ring → S and verify σ⁻¹(m_S) = 𝔫.
  set σ' : P.P.Ring →ₐ[S] S := P.P.lift a hHasMap with hσ'
  set φ : B →ₐ[S] P.P.Ring := (P.equivRing.toAlgHom).comp (IsScalarTower.toAlgHom S B L) with hφ
  set σ : B →ₐ[S] S := σ'.comp φ with hσ
  refine ⟨σ, ?_⟩
  have hcompat : ∀ z : P.P.Ring,
      algebraMap S (L ⧸ 𝔮) (σ' z) = (Ideal.Quotient.mk 𝔮) (P.equivRing.symm z) := by
    let F1 : P.P.Ring →ₐ[S] (L ⧸ 𝔮) := (IsScalarTower.toAlgHom S S (L ⧸ 𝔮)).comp σ'
    let F2 : P.P.Ring →ₐ[S] (L ⧸ 𝔮) :=
      (IsScalarTower.toAlgHom S L (L ⧸ 𝔮)).comp (P.equivRing.symm.toAlgHom)
    have hF : F1 = F2 := by
      apply StandardEtalePair.hom_ext
      show algebraMap S (L ⧸ 𝔮) (σ' P.P.X) = (Ideal.Quotient.mk 𝔮) (P.equivRing.symm P.P.X)
      rw [hσ', StandardEtalePair.lift_X, P.equivRing_symm_X, hqa]
    exact DFunLike.congr_fun hF
  ext b
  rw [Ideal.mem_comap, show σ.toRingHom b = σ b from rfl, ← hker]
  have hcalc : algebraMap S (L ⧸ 𝔮) (σ b) = (Ideal.Quotient.mk 𝔮) (algebraMap B L b) := by
    rw [hσ]
    show algebraMap S (L ⧸ 𝔮) (σ' (φ b)) = _
    rw [hcompat (φ b), hφ]
    show (Ideal.Quotient.mk 𝔮) (P.equivRing.symm (P.equivRing (algebraMap B L b))) = _
    rw [AlgEquiv.symm_apply_apply]
  rw [hcalc, Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hcomapBL]

/-- Composition of induced residue-field maps. -/
lemma residueField_map_comp'
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (I : Ideal R) [I.IsPrime] (J : Ideal S) [J.IsPrime] (K : Ideal T) [K.IsPrime]
    (f : R →+* S) (g : S →+* T) (hf : I = Ideal.comap f J) (hg : J = Ideal.comap g K)
    (hgf : I = Ideal.comap (g.comp f) K) :
    Ideal.ResidueField.map I K (g.comp f) hgf
      = (Ideal.ResidueField.map J K g hg).comp (Ideal.ResidueField.map I J f hf) := by
  ext r
  simp only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]

open IsLocalRing in
/-- An element of a local ring lies in the maximal ideal exactly when it dies in the
residue field. -/
private lemma algebraMap_residueField_eq_zero_iff
    {S : Type*} [CommRing S] [IsLocalRing S] (s : S) :
    algebraMap S (maximalIdeal S).ResidueField s = 0 ↔ s ∈ maximalIdeal S := by
  rw [← RingHom.mem_ker, Ideal.ker_algebraMap_residueField]

open Algebra IsLocalRing Ideal TensorProduct in
/-- The `S`-algebra map cut out by a residue datum.

Given a prime `𝔮` of `A` lying over `p = R ∩ m_S` and a `κ(p)`-algebra map
`τ : κ(𝔮) → κ(m_S)`, there is an `S`-algebra map
`g : S ⊗[R] A → κ(m_S)` which is the residue map on the `S`-factor and `τ ∘ (A → κ(𝔮))`
on the `A`-factor. Its kernel `𝔫` is a prime of `S ⊗[R] A` lying over `m_S` whose
residue extension `κ(m_S) → κ(𝔫)` is bijective, i.e. `κ(𝔫) = κ(m_S)`.

This is the prime `𝔫` that both halves of Stacks 08HQ feed to the henselian
retraction, and both halves also need `g` itself together with its two defining
properties afterwards — `exists_algHom_henselian_of_residue_datum` to identify `𝔫 ∩ A` with `𝔮` and
compute the residue map of `includeRight`, `algHom_henselian_unique_of_residue_datum` to recognise
`𝔫` as the contraction of `m_S` along each transported retraction. -/
private theorem exists_algHom_residueField_of_residue_datum
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing S]
    (A : Type*) [CommRing A] [Algebra R A]
    (𝔮 : Ideal A) [𝔮.IsPrime]
    (hlo : 𝔮.comap (algebraMap R A) = (maximalIdeal S).comap (algebraMap R S))
    (τ : 𝔮.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ : τ.comp (Ideal.ResidueField.map _ 𝔮 (algebraMap R A) hlo.symm)
        = Ideal.ResidueField.map _ (maximalIdeal S) (algebraMap R S) rfl) :
    ∃ (g : (S ⊗[R] A) →ₐ[S] (maximalIdeal S).ResidueField)
        (_ : (RingHom.ker g.toRingHom).IsPrime)
        (hn_lo : (RingHom.ker g.toRingHom).comap (algebraMap S (S ⊗[R] A)) = maximalIdeal S),
      (∀ s : S, g (algebraMap S (S ⊗[R] A) s) = algebraMap S (maximalIdeal S).ResidueField s) ∧
      (∀ a : A, g (Algebra.TensorProduct.includeRight a) = τ (algebraMap A 𝔮.ResidueField a)) ∧
      Function.Bijective (Ideal.ResidueField.map (maximalIdeal S) (RingHom.ker g.toRingHom)
        (algebraMap S (S ⊗[R] A)) hn_lo.symm) := by
  -- The S-algebra map g : S ⊗[R] A → κ(m_S) determined by the residue datum (𝔮, τ):
  -- on S it is the residue map, on A it is τ ∘ (A → κ(𝔮)). These agree on R by hlo + hτ.
  let tower : IsScalarTower R S (maximalIdeal S).ResidueField :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hp : ((maximalIdeal S).comap (algebraMap R S)).IsPrime := inferInstance
  -- The A-component as an R-algebra map: τ ∘ (residue A → κ(𝔮)) commutes with R.
  have hcommA : ∀ r : R,
      τ ((algebraMap A 𝔮.ResidueField) ((algebraMap R A) r))
        = algebraMap R (maximalIdeal S).ResidueField r := by
    intro r
    have e1 : (algebraMap A 𝔮.ResidueField) ((algebraMap R A) r)
        = (Ideal.ResidueField.map ((maximalIdeal S).comap (algebraMap R S)) 𝔮 (algebraMap R A)
            hlo.symm)
            ((algebraMap R ((maximalIdeal S).comap (algebraMap R S)).ResidueField) r) := by
      rw [Ideal.ResidueField.map_algebraMap]
    rw [e1]
    have e2 := DFunLike.congr_fun hτ ((algebraMap R ((maximalIdeal S).comap (algebraMap R
        S)).ResidueField) r)
    simp only [RingHom.coe_comp, Function.comp_apply] at e2
    rw [e2, Ideal.ResidueField.map_algebraMap]
    rw [IsScalarTower.algebraMap_apply R S (maximalIdeal S).ResidueField]
  let gAalg : A →ₐ[R] (maximalIdeal S).ResidueField :=
    { (τ.comp (algebraMap A 𝔮.ResidueField)) with commutes' := hcommA }
  let fS : S →ₐ[S] (maximalIdeal S).ResidueField := Algebra.ofId S _
  let g : (S ⊗[R] A) →ₐ[S] (maximalIdeal S).ResidueField :=
    Algebra.TensorProduct.lift fS gAalg (fun x y => Commute.all _ _)
  -- g restricted to the S-factor is the residue map S → κ(m_S).
  have hgleft : ∀ s : S, g (algebraMap S (S ⊗[R] A) s)
      = algebraMap S (maximalIdeal S).ResidueField s := by
    intro s
    have hgl : g (algebraMap S (S ⊗[R] A) s) = fS s := by
      have hh := Algebra.TensorProduct.lift_comp_includeLeft fS gAalg (fun x y => Commute.all _ _)
      calc g (algebraMap S (S ⊗[R] A) s)
          = (g.comp Algebra.TensorProduct.includeLeft) s := rfl
        _ = fS s := by rw [hh]
    rw [hgl]; rfl
  -- g restricted to the A-factor is τ ∘ (A → κ(𝔮)).
  have hgright : ∀ a : A, g (Algebra.TensorProduct.includeRight a)
      = τ (algebraMap A 𝔮.ResidueField a) := by
    intro a
    have hh := Algebra.TensorProduct.lift_comp_includeRight fS gAalg (fun x y => Commute.all _ _)
    have : (AlgHom.restrictScalars R g).comp Algebra.TensorProduct.includeRight = gAalg := hh
    have := DFunLike.congr_fun this a
    exact this
  -- g is surjective, since its S-restriction (the residue map) already is.
  have hgsurj : Function.Surjective g := by
    intro y
    obtain ⟨s, hs⟩ := Ideal.algebraMap_residueField_surjective (maximalIdeal S) y
    exact ⟨algebraMap S (S ⊗[R] A) s, by rw [hgleft]; exact hs⟩
  -- 𝔫 := ker g; prime (codomain is a field), and B/𝔫 ≅ κ(m_S) is a field so 𝔫 is maximal.
  set 𝔫 : Ideal (S ⊗[R] A) := RingHom.ker g.toRingHom with h𝔫
  have hnprime : 𝔫.IsPrime := RingHom.ker_isPrime g.toRingHom
  let e : (S ⊗[R] A) ⧸ 𝔫 ≃+* (maximalIdeal S).ResidueField :=
    RingHom.quotientKerEquivOfSurjective hgsurj
  have hnmax : 𝔫.IsMaximal := Ideal.Quotient.maximal_of_isField 𝔫
    (MulEquiv.isField (Field.toIsField _) e.toMulEquiv)
  -- Lying over: comap of 𝔫 along S → B is m_S.
  have hn_lo : 𝔫.comap (algebraMap S (S ⊗[R] A)) = maximalIdeal S := by
    apply Ideal.ext
    intro s
    rw [Ideal.mem_comap, h𝔫, RingHom.mem_ker]
    show g (algebraMap S (S ⊗[R] A) s) = 0 ↔ _
    rw [hgleft, algebraMap_residueField_eq_zero_iff]
  -- The residue map κ(m_S) → κ(𝔫) is bijective: injective (field hom) + surjective.
  have hn_res : Function.Bijective
      (Ideal.ResidueField.map (maximalIdeal S) 𝔫 (algebraMap S (S ⊗[R] A)) hn_lo.symm) := by
    set m := Ideal.ResidueField.map (maximalIdeal S) 𝔫 (algebraMap S (S ⊗[R] A)) hn_lo.symm with hm
    refine ⟨m.injective, ?_⟩
    -- Surjectivity: S → B/𝔫 is surjective (g surjective), so S → κ(𝔫) is surjective.
    have hSBsurj : Function.Surjective (algebraMap S ((S ⊗[R] A) ⧸ 𝔫)) := by
      intro y
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨s, hs⟩ := Ideal.algebraMap_residueField_surjective (maximalIdeal S) (g b)
      refine ⟨s, ?_⟩
      rw [IsScalarTower.algebraMap_apply S (S ⊗[R] A) ((S ⊗[R] A) ⧸ 𝔫),
        Ideal.Quotient.algebraMap_eq]
      apply Ideal.Quotient.eq.mpr
      rw [h𝔫, RingHom.mem_ker]
      show g (algebraMap S (S ⊗[R] A) s - b) = 0
      rw [map_sub, hgleft, hs, sub_self]
    have hSresSurj : Function.Surjective (algebraMap S 𝔫.ResidueField) := by
      rw [IsScalarTower.algebraMap_eq S ((S ⊗[R] A) ⧸ 𝔫) 𝔫.ResidueField, RingHom.coe_comp]
      exact (Ideal.bijective_algebraMap_quotient_residueField 𝔫).surjective.comp hSBsurj
    intro z
    obtain ⟨s, hs⟩ := hSresSurj z
    refine ⟨algebraMap S (maximalIdeal S).ResidueField s, ?_⟩
    rw [hm, Ideal.ResidueField.map_algebraMap,
      ← IsScalarTower.algebraMap_apply S (S ⊗[R] A) 𝔫.ResidueField, hs]
  exact ⟨g, hnprime, hn_lo, hgleft, hgright, hn_res⟩

open Algebra IsLocalRing Ideal TensorProduct in
/-- **Existence half of Stacks Tag 08HQ.** Same data as
`existsUnique_algHom_henselian_of_residue_datum`; produces an `R`-algebra map `f : A → S` with
`𝔮 = f⁻¹(m_S)` inducing `τ`.

The proof runs in four steps.
1. Base change `B := S ⊗[R] A` is étale over `S` (`Algebra.Etale.baseChange`).
2. The residue datum `(𝔮, τ)` cuts out a prime `𝔫` of `B` over `m_S` with
   `κ(𝔫) = κ(m_S)`: it is the kernel of the `S`-algebra map
   `B = S ⊗[R] A → κ(𝔮) ⊗_{κ(p)} κ(m_S) --(mult ∘ (1 ⊗ τ))--> κ(m_S)`.
   The lying-over `hlo` and the `κ(p)`-compatibility `hτ` make this well defined
   and force the residue field at `𝔫` to be exactly `κ(m_S)`.
3. `henselian_etale_retraction` supplies `σ : B →ₐ[S] S` with `σ⁻¹(m_S) = 𝔫`.
4. `f := (σ.restrictScalars R).comp includeRight`; the conditions on `σ` (prime
   `𝔫`, induced `id` on `κ(m_S)`) transport back across the base-change bijection
   `Hom_R(A, S) ≃ Hom_S(S ⊗[R] A, S)` to give `𝔮 = f⁻¹(m_S)` and that `f` induces
   `τ`. -/
lemma exists_algHom_henselian_of_residue_datum
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [HenselianLocalRing S]
    (A : Type*) [CommRing A] [Algebra R A] [Algebra.Etale R A]
    (𝔮 : Ideal A) [𝔮.IsPrime]
    (hlo : 𝔮.comap (algebraMap R A) = (maximalIdeal S).comap (algebraMap R S))
    (τ : 𝔮.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ : τ.comp (Ideal.ResidueField.map _ 𝔮 (algebraMap R A) hlo.symm)
        = Ideal.ResidueField.map _ (maximalIdeal S) (algebraMap R S) rfl) :
    ∃ f : A →ₐ[R] S,
      ∃ (h : (maximalIdeal S).comap f.toRingHom = 𝔮),
        Ideal.ResidueField.map 𝔮 (maximalIdeal S) f.toRingHom h.symm = τ := by
  -- Base change: B := S ⊗[R] A is étale over S.
  have hBet : Algebra.Etale S (TensorProduct R S A) := Algebra.Etale.baseChange R A S
  -- The residue datum (𝔮, τ) cuts out a prime 𝔫 of B = S ⊗[R] A over m_S with
  -- κ(𝔫) = κ(m_S): it is the kernel of the S-algebra map
  --   S ⊗[R] A → κ(𝔮) ⊗_{κ(p)} κ(m_S) --(τ ⊗ 1, then multiply)--> κ(m_S).
  obtain ⟨g, hnprime, hn_lo, hgleft, hgright, hn_res⟩ :=
    exists_algHom_residueField_of_residue_datum R S A 𝔮 hlo τ hτ
  set 𝔫 : Ideal (S ⊗[R] A) := RingHom.ker g.toRingHom with h𝔫
  -- (Cnj-A) comap of 𝔫 along includeRight is 𝔮.
  have hnA : 𝔫.comap (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A)).toRingHom
      = 𝔮 := by
    apply Ideal.ext
    intro a
    rw [Ideal.mem_comap]
    show Algebra.TensorProduct.includeRight a ∈ 𝔫 ↔ a ∈ 𝔮
    rw [h𝔫, RingHom.mem_ker]
    show g (Algebra.TensorProduct.includeRight a) = 0 ↔ a ∈ 𝔮
    rw [hgright a, map_eq_zero_iff τ τ.injective,
      ← RingHom.mem_ker, Ideal.ker_algebraMap_residueField]
  -- (Cnj-B) the residue map of includeRight, κ(𝔮) → κ(𝔫), equals (κ(m_S) → κ(𝔫)) ∘ τ.
  -- Prove this ring-hom equality via IsFractionRing.ringHom_ext.
  have hnB : Ideal.ResidueField.map 𝔮 𝔫
        (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A)).toRingHom hnA.symm
      = (Ideal.ResidueField.map (maximalIdeal S) 𝔫
          (algebraMap S (S ⊗[R] A)) hn_lo.symm).comp τ := by
    ext a
    rw [RingHom.comp_apply, RingHom.comp_apply, Ideal.ResidueField.map_algebraMap,
      RingHom.comp_apply]
    -- The class of (includeRight a) in B/𝔫 equals the class of algebraMap S (S⊗A) s,
    -- where s : S with algebraMap S κ(m_S) s = τ (algebraMap A κ(𝔮) a); the two agree
    -- because g (includeRight a) = τ (algebraMap A κ(𝔮) a) and g is the residue map on S.
    obtain ⟨s, hs⟩ := Ideal.algebraMap_residueField_surjective (maximalIdeal S)
      (τ (algebraMap A 𝔮.ResidueField a))
    have hclass : algebraMap (S ⊗[R] A) 𝔫.ResidueField (Algebra.TensorProduct.includeRight a)
        = algebraMap (S ⊗[R] A) 𝔫.ResidueField (algebraMap S (S ⊗[R] A) s) := by
      rw [IsScalarTower.algebraMap_apply (S ⊗[R] A) ((S ⊗[R] A) ⧸ 𝔫) 𝔫.ResidueField,
        IsScalarTower.algebraMap_apply (S ⊗[R] A) ((S ⊗[R] A) ⧸ 𝔫) 𝔫.ResidueField]
      congr 1
      apply Ideal.Quotient.eq.mpr
      rw [h𝔫, RingHom.mem_ker, map_sub]
      show g (Algebra.TensorProduct.includeRight a) - g (algebraMap S (S ⊗[R] A) s) = 0
      rw [hgright a, hgleft, hs, sub_self]
    show algebraMap (S ⊗[R] A) 𝔫.ResidueField (Algebra.TensorProduct.includeRight a) = _
    rw [hclass, ← hs, Ideal.ResidueField.map_algebraMap]
  -- Henselian retraction: there is σ : B →ₐ[S] S with σ⁻¹(m_S) = 𝔫.
  obtain ⟨σ, hσ⟩ := henselian_etale_retraction S (TensorProduct R S A) 𝔫 hn_lo hn_res
  -- Set f := σ ∘ includeRight (restricting scalars to R). Verify P f.
  refine ⟨(σ.restrictScalars R).comp Algebra.TensorProduct.includeRight, ?_, ?_⟩
  · -- 𝔮 = f⁻¹(m_S): comap of f equals comap of includeRight of σ⁻¹(m_S) = 𝔫,
    -- and 𝔫 ∩ A = 𝔮 by the way 𝔫 was constructed (kernel hitting κ(𝔮)).
    show (maximalIdeal S).comap
      ((σ.toRingHom).comp (Algebra.TensorProduct.includeRight (R := R) (A := S) (B :=
          A)).toRingHom) = 𝔮
    rw [← Ideal.comap_comap, hσ, hnA]
  · -- f induces τ on residue fields: the residue map of σ at 𝔫 is the inverse of
    -- hn_res (the iso κ(m_S) ≅ κ(𝔫)); precomposed with includeRight's residue map
    -- κ(𝔮) → κ(𝔫) this is exactly τ, by construction of 𝔫 from (𝔮, τ).
    -- σ̄ ∘ mn = id on κ(m_S) (σ is an S-algebra retraction): proven pointwise.
    have hσmn : ∀ z : (maximalIdeal S).ResidueField,
        (Ideal.ResidueField.map 𝔫 (maximalIdeal S) σ.toRingHom hσ.symm)
          ((Ideal.ResidueField.map (maximalIdeal S) 𝔫
              (algebraMap S (TensorProduct R S A)) hn_lo.symm) z) = z := by
      intro z
      obtain ⟨s, rfl⟩ := Ideal.algebraMap_residueField_surjective (maximalIdeal S) z
      rw [Ideal.ResidueField.map_algebraMap, Ideal.ResidueField.map_algebraMap]
      congr 1
      exact σ.commutes s
    -- The goal: map 𝔮 m_S f.toRingHom _ = τ.  Prove via IsFractionRing.ringHom_ext.
    ext a
    rw [RingHom.comp_apply, RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]
    -- LHS now: algebraMap S κ(m_S) (f a) = algebraMap S κ(m_S) (σ (includeRight a)).
    show algebraMap S (maximalIdeal S).ResidueField (σ (Algebra.TensorProduct.includeRight a)) = _
    -- Rewrite via σ̄ and incR̄ = mn ∘ τ, then σ̄ ∘ mn = id.
    have hstep :
        algebraMap S (maximalIdeal S).ResidueField (σ (Algebra.TensorProduct.includeRight a))
          = (Ideal.ResidueField.map 𝔫 (maximalIdeal S) σ.toRingHom hσ.symm)
              (algebraMap (TensorProduct R S A) 𝔫.ResidueField
                (Algebra.TensorProduct.includeRight a)) := by
      rw [Ideal.ResidueField.map_algebraMap]; rfl
    rw [hstep]
    -- algebraMap B κ(𝔫) (includeRight a) = incR̄ (algebraMap A κ(𝔮) a).
    have hincR :
        algebraMap (TensorProduct R S A) 𝔫.ResidueField (Algebra.TensorProduct.includeRight a)
          = (Ideal.ResidueField.map 𝔮 𝔫
              (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A)).toRingHom hnA.symm)
              (algebraMap A 𝔮.ResidueField a) := by
      rw [Ideal.ResidueField.map_algebraMap]; rfl
    rw [hincR, hnB, RingHom.comp_apply, hσmn]

open IsLocalRing in
/-- Extension of an `S`-algebra map `σ : B →ₐ[S] S` to the localization of `B` away
from an element `f` whose image `σ f` is a unit: every power of `f` is then sent to
a unit, so `σ` factors through `Localization.Away f`. -/
noncomputable def awayLiftAlgHom
    {S B : Type*} [CommRing S] [CommRing B] [Algebra S B]
    (f : B) (σ : B →ₐ[S] S) (hf : IsUnit (σ f)) :
    Localization.Away f →ₐ[S] S :=
  haveI hfu : ∀ y : Submonoid.powers f, IsUnit (σ.toRingHom (y : B)) := by
    rintro ⟨_, n, rfl⟩
    simp only [map_pow]
    exact hf.pow n
  { IsLocalization.lift (g := σ.toRingHom) hfu with
    commutes' := by
      intro s
      change IsLocalization.lift hfu (algebraMap S (Localization.Away f) s) = s
      rw [IsScalarTower.algebraMap_apply S B (Localization.Away f), IsLocalization.lift_eq]
      change σ (algebraMap S B s) = s
      rw [AlgHom.commutes]; rfl }

/-- `awayLiftAlgHom f σ hf` really does extend `σ`: it agrees with `σ` on the image
of `B` in `Localization.Away f`. -/
lemma awayLiftAlgHom_apply
    {S B : Type*} [CommRing S] [CommRing B] [Algebra S B]
    (f : B) (σ : B →ₐ[S] S) (hf : IsUnit (σ f)) (b : B) :
    awayLiftAlgHom f σ hf (algebraMap B (Localization.Away f) b) = σ b := by
  show IsLocalization.lift _ (algebraMap B (Localization.Away f) b) = σ b
  rw [IsLocalization.lift_eq]; rfl

open IsLocalRing in
/-- Uniqueness of the Hensel root: in a local ring, a root `a` of `f` at which the
derivative of `f` is a unit is the only root of `f` in its residue class modulo the
maximal ideal. -/
@[sga "3 VIIB 1.6" "partial"]
lemma hensel_root_unique
    {R : Type*} [CommRing R] [IsLocalRing R]
    (f : Polynomial R) (a b : R)
    (ha : Polynomial.eval a f = 0) (hb : Polynomial.eval b f = 0)
    (hua : IsUnit (Polynomial.eval a (Polynomial.derivative f)))
    (hab : b - a ∈ maximalIdeal R) : a = b := by
  obtain ⟨k, hk⟩ := f.binomExpansion a (b - a)
  rw [add_sub_cancel] at hk
  rw [hb, ha, zero_add] at hk
  have hk2 : 0 = (b - a) * (Polynomial.eval a (Polynomial.derivative f) + k * (b - a)) := by
    rw [hk]; ring
  set y := b - a with hy
  have hunit : IsUnit (Polynomial.eval a (Polynomial.derivative f) + k * y) := by
    have hky : k * y ∈ maximalIdeal R := Ideal.mul_mem_left _ _ hab
    rw [← notMem_maximalIdeal] at hua ⊢
    intro hmem
    exact hua (by simpa using Ideal.sub_mem _ hmem hky)
  have hy0 : y = 0 := hunit.mul_left_eq_zero.mp hk2.symm
  rw [hy, sub_eq_zero] at hy0
  exact hy0.symm

open Algebra IsLocalRing Ideal TensorProduct in
/-- Uniqueness half of `henselian_etale_retraction`: an `S`-algebra retraction
`σ : B →ₐ[S] S` of an étale `S`-algebra `B` is determined by the prime `σ⁻¹(m_S)`,
when that prime lies over `m_S` with residue field equal to `κ(m_S)`. Uniqueness
comes from the uniqueness of the Hensel root in the standard-étale presentation of
`B` near `𝔫`. -/
@[ega "IV 18.6.2" "partial", sga "3 XI 1.11" "special case", sga "4 XII 6.13" "partial"]
lemma henselian_etale_retraction_unique
    (S : Type*) [CommRing S] [HenselianLocalRing S]
    (B : Type*) [CommRing B] [Algebra S B] [Algebra.Etale S B]
    (𝔫 : Ideal B) [𝔫.IsPrime]
    (hlo : 𝔫.comap (algebraMap S B) = maximalIdeal S)
    (hres : Function.Bijective
      (Ideal.ResidueField.map (maximalIdeal S) 𝔫 (algebraMap S B) hlo.symm))
    (σ₁ σ₂ : B →ₐ[S] S)
    (hσ₁ : (maximalIdeal S).comap σ₁.toRingHom = 𝔫)
    (hσ₂ : (maximalIdeal S).comap σ₂.toRingHom = 𝔫) :
    σ₁ = σ₂ := by
  -- Localization setup, exactly as in `henselian_etale_retraction`.
  obtain ⟨f, hf_notin, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := S) (S := B) 𝔫
  obtain ⟨P⟩ := hstd.nonempty_standardEtalePresentation
  set L := Localization.Away f with hL
  obtain ⟨-, -, -, -, hsurjL⟩ := localization_away_residue_data 𝔫 hlo hres hf_notin L
  set 𝔮 : Ideal L := 𝔫.map (algebraMap B L) with h𝔮
  -- root data
  have h1 : P.P.HasMap P.x := P.hasMap
  rw [StandardEtalePair.HasMap.eq_1] at h1
  obtain ⟨hf0, -⟩ := h1
  obtain ⟨x₀, hx₀⟩ := hsurjL (Ideal.Quotient.mk 𝔮 P.x)
  -- f ∉ 𝔫, so σᵢ f is a unit.
  have hσf : ∀ σ : B →ₐ[S] S, (maximalIdeal S).comap σ.toRingHom = 𝔫 → IsUnit (σ f) := by
    intro σ hσ
    rw [← notMem_maximalIdeal]
    intro hmem
    have : f ∈ (maximalIdeal S).comap σ.toRingHom := hmem
    rw [hσ] at this
    exact hf_notin this
  -- Generic: from σ with σ⁻¹m = 𝔫, the value c = (lift σ)(P.x) is a root of P.P.f
  -- with c - x₀ ∈ m and unit derivative.
  have hgen : ∀ σ : B →ₐ[S] S, ∀ hσ : (maximalIdeal S).comap σ.toRingHom = 𝔫,
      let c := awayLiftAlgHom f σ (hσf σ hσ) P.x
      Polynomial.eval c P.P.f = 0 ∧ c - x₀ ∈ maximalIdeal S ∧
        IsUnit (Polynomial.eval c (Polynomial.derivative P.P.f)) := by
    intro σ hσ
    set t := awayLiftAlgHom f σ (hσf σ hσ) with ht
    set c := t P.x with hc
    have hev : ∀ p : Polynomial S, Polynomial.eval c p = t (Polynomial.aeval P.x p) := by
      intro p
      rw [hc, ← Polynomial.aeval_algHom_apply, Polynomial.coe_aeval_eq_eval]
    have hroot : Polynomial.eval c P.P.f = 0 := by rw [hev, hf0, map_zero]
    have hderiv : IsUnit (Polynomial.eval c (Polynomial.derivative P.P.f)) := by
      rw [hev]
      exact P.hasMap.isUnit_derivative_f.map t
    -- residue: c - x₀ ∈ m. Build Q : L/𝔮 →+* S/m from t.
    have hmemq : ∀ x ∈ 𝔮, (Ideal.Quotient.mk (maximalIdeal S)) (t x) = 0 := by
      intro x hx
      rw [h𝔮] at hx
      -- x ∈ 𝔫.map (B→L). Use induction on membership.
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨b, hb, rfl⟩
        rw [awayLiftAlgHom_apply]
        rw [Ideal.Quotient.eq_zero_iff_mem]
        have : b ∈ (maximalIdeal S).comap σ.toRingHom := by rw [hσ]; exact hb
        exact this
      · simp
      · intro a b _ _ ha hb; simp only [map_add, ha, hb, add_zero]
      · intro a x _ hx2
        simp only [smul_eq_mul, map_mul, hx2, mul_zero]
    let Q : L ⧸ 𝔮 →+* S ⧸ maximalIdeal S :=
      Ideal.Quotient.lift 𝔮 ((Ideal.Quotient.mk (maximalIdeal S)).comp t.toRingHom)
        (by intro x hx; simp only [RingHom.comp_apply]; exact hmemq x hx)
    have hQmk : ∀ x : L, Q (Ideal.Quotient.mk 𝔮 x) = Ideal.Quotient.mk (maximalIdeal S) (t x) := by
      intro x; rfl
    have hQalg : ∀ s : S, Q (algebraMap S (L ⧸ 𝔮) s) = Ideal.Quotient.mk (maximalIdeal S) s := by
      intro s
      rw [IsScalarTower.algebraMap_apply S L (L ⧸ 𝔮), Ideal.Quotient.algebraMap_eq, hQmk]
      congr 1
      show t (algebraMap S L s) = s
      rw [AlgHom.commutes]; rfl
    -- mk m c = Q (mk 𝔮 P.x); mk m x₀ = Q (algebraMap S (L/𝔮) x₀) = Q (mk 𝔮 P.x).
    have hcx0 : Ideal.Quotient.mk (maximalIdeal S) c = Ideal.Quotient.mk (maximalIdeal S) x₀ := by
      have e1 : Ideal.Quotient.mk (maximalIdeal S) c = Q (Ideal.Quotient.mk 𝔮 P.x) := by
        rw [hQmk]
      have e2 : Ideal.Quotient.mk (maximalIdeal S) x₀ = Q (Ideal.Quotient.mk 𝔮 P.x) := by
        rw [← hx₀, hQalg]
      rw [e1, e2]
    have hmem : c - x₀ ∈ maximalIdeal S := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, hcx0]
    exact ⟨hroot, hmem, hderiv⟩
  -- Apply to both σ₁, σ₂; get c₁ = c₂.
  obtain ⟨hroot1, hmem1, hderiv1⟩ := hgen σ₁ hσ₁
  obtain ⟨hroot2, hmem2, hderiv2⟩ := hgen σ₂ hσ₂
  set c₁ := awayLiftAlgHom f σ₁ (hσf σ₁ hσ₁) P.x with hc1
  set c₂ := awayLiftAlgHom f σ₂ (hσf σ₂ hσ₂) P.x with hc2
  have hc12 : c₁ = c₂ := by
    refine (hensel_root_unique P.P.f c₂ c₁ hroot2 hroot1 hderiv2 ?_).symm
    rw [← sub_sub_sub_cancel_right c₁ c₂ x₀]
    exact Ideal.sub_mem _ hmem1 hmem2
  -- Now conclude σ₁ = σ₂. Build tᵢ, and ρᵢ := tᵢ ∘ equivRing.symm : P.Ring → S.
  set t₁ := awayLiftAlgHom f σ₁ (hσf σ₁ hσ₁) with ht1
  set t₂ := awayLiftAlgHom f σ₂ (hσf σ₂ hσ₂) with ht2
  -- t₁ = t₂ via StandardEtalePair.hom_ext on ρᵢ = tᵢ.comp equivRing.symm.
  have hteq : t₁ = t₂ := by
    let ρ₁ : P.P.Ring →ₐ[S] S := t₁.comp P.equivRing.symm.toAlgHom
    let ρ₂ : P.P.Ring →ₐ[S] S := t₂.comp P.equivRing.symm.toAlgHom
    have hρ : ρ₁ = ρ₂ := by
      apply StandardEtalePair.hom_ext
      show t₁ (P.equivRing.symm P.P.X) = t₂ (P.equivRing.symm P.P.X)
      rw [P.equivRing_symm_X]
      exact hc12
    refine AlgHom.ext fun l => ?_
    simpa [ρ₁, ρ₂] using DFunLike.congr_fun hρ (P.equivRing l)
  -- σᵢ = tᵢ ∘ (B → L). So σ₁ = σ₂.
  ext b
  have e1 : σ₁ b = t₁ (algebraMap B L b) := (awayLiftAlgHom_apply f σ₁ (hσf σ₁ hσ₁) b).symm
  have e2 : σ₂ b = t₂ (algebraMap B L b) := (awayLiftAlgHom_apply f σ₂ (hσf σ₂ hσ₂) b).symm
  rw [e1, e2, hteq]

open Algebra IsLocalRing Ideal TensorProduct in
/-- **Uniqueness half of Stacks tag 08HQ.** Same data as
`existsUnique_algHom_henselian_of_residue_datum`: at most one `R`-algebra map `f : A → S` satisfies
`𝔮 = f⁻¹(m_S)` and induces `τ` on residue fields. Both candidates transport to `S`-algebra
retractions of `S ⊗[R] A` cutting out the same prime, so `henselian_etale_retraction_unique`
identifies them. -/
lemma algHom_henselian_unique_of_residue_datum
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [HenselianLocalRing S]
    (A : Type*) [CommRing A] [Algebra R A] [Algebra.Etale R A]
    (𝔮 : Ideal A) [𝔮.IsPrime]
    (hlo : 𝔮.comap (algebraMap R A) = (maximalIdeal S).comap (algebraMap R S))
    (τ : 𝔮.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ : τ.comp (Ideal.ResidueField.map _ 𝔮 (algebraMap R A) hlo.symm)
        = Ideal.ResidueField.map _ (maximalIdeal S) (algebraMap R S) rfl) :
    ∀ f₁ f₂ : A →ₐ[R] S,
      (∃ (h : (maximalIdeal S).comap f₁.toRingHom = 𝔮),
        Ideal.ResidueField.map 𝔮 (maximalIdeal S) f₁.toRingHom h.symm = τ) →
      (∃ (h : (maximalIdeal S).comap f₂.toRingHom = 𝔮),
        Ideal.ResidueField.map 𝔮 (maximalIdeal S) f₂.toRingHom h.symm = τ) →
      f₁ = f₂ := by
  have hBet : Algebra.Etale S (TensorProduct R S A) := Algebra.Etale.baseChange R A S
  -- reconstruct g and 𝔫 = ker g
  obtain ⟨g, hnprime, hn_lo, hgleft, hgright, hn_res⟩ :=
    exists_algHom_residueField_of_residue_datum R S A 𝔮 hlo τ hτ
  set 𝔫 : Ideal (S ⊗[R] A) := RingHom.ker g.toRingHom with h𝔫
  -- transport: each f with P f gives σ_f with σ_f⁻¹(m) = 𝔫.
  have htrans : ∀ f : A →ₐ[R] S, ∀ hf : (maximalIdeal S).comap f.toRingHom = 𝔮,
      Ideal.ResidueField.map 𝔮 (maximalIdeal S) f.toRingHom hf.symm = τ →
      let σ := Algebra.TensorProduct.lift (AlgHom.id S S) f (fun x y => Commute.all _ _)
      (maximalIdeal S).comap σ.toRingHom = 𝔫 := by
    intro f hf hfτ
    set σ := Algebra.TensorProduct.lift (AlgHom.id S S) f (fun x y => Commute.all _ _) with hσ
    -- gσ := ofId ∘ σ equals g.
    have hgσ : (Algebra.ofId S (maximalIdeal S).ResidueField).comp σ = g := by
      apply Algebra.TensorProduct.ext'
      intro s a
      -- both sides on s ⊗ₜ a
      show (Algebra.ofId S (maximalIdeal S).ResidueField) (σ (s ⊗ₜ[R] a)) = g (s ⊗ₜ[R] a)
      have hσsa : σ (s ⊗ₜ[R] a) = s * f a := by
        rw [hσ, Algebra.TensorProduct.lift_tmul]; simp
      have hgsa : g (s ⊗ₜ[R] a)
          = algebraMap S (maximalIdeal S).ResidueField s * τ (algebraMap A 𝔮.ResidueField a) := by
        have : s ⊗ₜ[R] a = algebraMap S (S ⊗[R] A) s * Algebra.TensorProduct.includeRight a := by
          rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.includeRight_apply,
            Algebra.TensorProduct.tmul_mul_tmul]; simp
        rw [this, map_mul, hgleft, hgright]
      rw [hσsa, hgsa, map_mul]
      congr 1
      -- (ofId) (f a) = τ (algebraMap A κ(𝔮) a)
      have key : algebraMap A 𝔮.ResidueField a
          = (algebraMap (A ⧸ 𝔮) 𝔮.ResidueField) ((Ideal.Quotient.mk 𝔮) a) := by
        rw [IsScalarTower.algebraMap_apply A (A ⧸ 𝔮) 𝔮.ResidueField, Ideal.Quotient.algebraMap_eq]
      rw [key]
      have hmap := DFunLike.congr_fun hfτ ((algebraMap (A ⧸ 𝔮) 𝔮.ResidueField) ((Ideal.Quotient.mk
          𝔮) a))
      rw [← hmap]
      rw [show (algebraMap (A ⧸ 𝔮) 𝔮.ResidueField) ((Ideal.Quotient.mk 𝔮) a) = algebraMap A
          𝔮.ResidueField a from key.symm]
      rw [Ideal.ResidueField.map_algebraMap]
      show (Algebra.ofId S (maximalIdeal S).ResidueField) (f a) = algebraMap S (maximalIdeal
          S).ResidueField (f a)
      rfl
    apply Ideal.ext
    intro x
    rw [Ideal.mem_comap, h𝔫, RingHom.mem_ker]
    show σ x ∈ maximalIdeal S ↔ g x = 0
    rw [← algebraMap_residueField_eq_zero_iff, ← hgσ]
    show algebraMap S (maximalIdeal S).ResidueField (σ x) = 0 ↔ _
    rfl
  -- main: f₁ = f₂
  rintro f₁ f₂ ⟨hf1, hf1τ⟩ ⟨hf2, hf2τ⟩
  set σ₁ := Algebra.TensorProduct.lift (AlgHom.id S S) f₁ (fun x y => Commute.all _ _) with hs1
  set σ₂ := Algebra.TensorProduct.lift (AlgHom.id S S) f₂ (fun x y => Commute.all _ _) with hs2
  have hσ₁ : (maximalIdeal S).comap σ₁.toRingHom = 𝔫 := htrans f₁ hf1 hf1τ
  have hσ₂ : (maximalIdeal S).comap σ₂.toRingHom = 𝔫 := htrans f₂ hf2 hf2τ
  have heq : σ₁ = σ₂ :=
    henselian_etale_retraction_unique S (TensorProduct R S A) 𝔫 hn_lo hn_res σ₁ σ₂ hσ₁ hσ₂
  -- f₁ = σ₁ ∘ includeRight, f₂ = σ₂ ∘ includeRight
  have e1 : f₁ = (σ₁.restrictScalars R).comp Algebra.TensorProduct.includeRight :=
    (Algebra.TensorProduct.lift_comp_includeRight (AlgHom.id S S) f₁
      (fun x y => Commute.all _ _)).symm
  have e2 : f₂ = (σ₂.restrictScalars R).comp Algebra.TensorProduct.includeRight :=
    (Algebra.TensorProduct.lift_comp_includeRight (AlgHom.id S S) f₂
      (fun x y => Commute.all _ _)).symm
  rw [e1, e2, heq]

open IsLocalRing Ideal in
/-- **Stacks Tag 08HQ** (map into henselian). Let `R → S` be a ring map with `S`
henselian local, `p = R ∩ m_S` the contraction of the maximal ideal. Given an
etale `R`-algebra `A`, a prime `q` of `A` lying over `p`, and a
`κ(p)`-algebra map `τ : κ(q) → κ(m_S)`, there is a unique `R`-algebra map
`f : A → S` with `q = f⁻¹(m_S)` inducing `τ` on residue fields. -/
@[stacks 08HQ]
theorem existsUnique_algHom_henselian_of_residue_datum
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [HenselianLocalRing S]
    (A : Type*) [CommRing A] [Algebra R A] [Algebra.Etale R A]
    -- `q` is a prime of `A` lying over `p = R ∩ m_S`.
    (𝔮 : Ideal A) [𝔮.IsPrime]
    (hlo : 𝔮.comap (algebraMap R A) = (maximalIdeal S).comap (algebraMap R S))
    -- `τ : κ(q) → κ(m_S)` is a `κ(p)`-algebra map: the triangle over `κ(p)` commutes.
    (τ : 𝔮.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ : τ.comp (Ideal.ResidueField.map _ 𝔮 (algebraMap R A) hlo.symm)
        = Ideal.ResidueField.map _ (maximalIdeal S) (algebraMap R S) rfl) :
    -- There is a unique `R`-algebra map `f : A → S` with `q = f⁻¹(m_S)` inducing `τ`.
    ∃! f : A →ₐ[R] S,
      ∃ (h : (maximalIdeal S).comap f.toRingHom = 𝔮),
        Ideal.ResidueField.map 𝔮 (maximalIdeal S) f.toRingHom h.symm = τ := by
  -- ## Proof of Stacks Tag 08HQ (map into henselian)
  --
  -- We abbreviate by `P f` the conjunction of the two required properties of an
  -- `R`-algebra map `f : A →ₐ[R] S`:
  --   (i)  `q = f⁻¹(m_S)`  (i.e. `(maximalIdeal S).comap f.toRingHom = 𝔮`), and
  --   (ii) `f` induces `τ` on residue fields.
  -- The goal `∃! f, P f` is `(∃ f, P f) ∧ (∀ f₁ f₂, P f₁ → P f₂ → f₁ = f₂)` up to
  -- the standard `ExistsUnique` unfolding. We establish existence and uniqueness
  -- separately; both come from the henselian retraction applied to the étale
  -- base change `B := A ⊗[R] S`.
  --
  -- The argument, following the Stacks proof.
  -- Form the étale `S`-algebra `B := A ⊗[R] S` (étale by base change of the
  -- étale `R → A`). The universal property of the tensor product gives a
  -- bijection between `R`-algebra maps `f : A →ₐ[R] S` and `S`-algebra
  -- retractions `σ : B →ₐ[S] S` (a map `f` corresponds to `σ = lift f id`, and
  -- `f = σ ∘ includeLeft`). Under this bijection, property (i)+(ii) for `f`
  -- correspond to: `σ⁻¹(m_S) = 𝔫` and `σ` induces the identity on `κ(m_S)`,
  -- where `𝔫` is the distinguished prime of `B` over `m_S` cut out by the
  -- residue datum `(𝔮, τ)` (the kernel of `B → κ(𝔮) ⊗_{κ(p)} κ(m_S) → κ(m_S)`,
  -- the second map being `τ ⊗ 1` followed by multiplication). The henselian
  -- retraction lemma supplies a UNIQUE such `σ`, hence a unique such `f`.
  --
  -- The two halves are packaged as `have`s; the heart of both is
  -- `henselian_etale_retraction` above, which is in turn the standard-étale plus
  -- Hensel root-lifting argument.
  --
  -- For readability set `P` to be the target predicate.
  set P : (A →ₐ[R] S) → Prop := fun f =>
      ∃ (h : (maximalIdeal S).comap f.toRingHom = 𝔮),
        Ideal.ResidueField.map 𝔮 (maximalIdeal S) f.toRingHom h.symm = τ with hP
  -- EXISTENCE.
  -- Build `B := A ⊗[R] S`, étale over `S`. The residue datum `(𝔮, τ)` determines
  -- a prime `𝔫 ⊂ B` over `m_S` with `κ(𝔫) = κ(m_S)` (residue field equal to the
  -- base, not merely an extension). By `henselian_retraction` there is a unique
  -- `S`-algebra retraction `σ : B →ₐ[S] S` with `σ⁻¹(m_S) = 𝔫` inducing `id` on
  -- `κ(m_S)`. Set `f := σ.restrictScalars R ∘ includeLeft`; then `f` is an
  -- `R`-algebra map and a residue-field/prime computation (transporting the
  -- conditions on `σ` across the base-change bijection) gives `P f`.
  have hex : ∃ f : A →ₐ[R] S, P f :=
    exists_algHom_henselian_of_residue_datum R S A 𝔮 hlo τ hτ
  -- UNIQUENESS.
  -- If `P f₁` and `P f₂`, transport each `fᵢ` to a retraction `σᵢ : B →ₐ[S] S`
  -- via `σᵢ = TensorProduct.lift fᵢ id`. Properties (i)+(ii) for `fᵢ` give that
  -- both `σᵢ` satisfy the conditions (`σᵢ⁻¹(m_S) = 𝔫`, `σᵢ` induces `id`) of the
  -- henselian retraction. Its uniqueness clause forces `σ₁ = σ₂`, and since
  -- `fᵢ = σᵢ ∘ includeLeft` (the inverse direction of the bijection) we get
  -- `f₁ = f₂`.
  have huniq : ∀ f₁ f₂ : A →ₐ[R] S, P f₁ → P f₂ → f₁ = f₂ :=
    algHom_henselian_unique_of_residue_datum R S A 𝔮 hlo τ hτ
  -- Combine existence and uniqueness into the `∃!` goal.
  obtain ⟨f, hf⟩ := hex
  exact ⟨f, hf, fun g hg => huniq g f hg hf⟩

end
