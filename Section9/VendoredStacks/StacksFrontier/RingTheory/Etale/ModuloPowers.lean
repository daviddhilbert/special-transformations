module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

@[expose] public section

universe u v w

/-!
# An étale local homomorphism is an isomorphism modulo powers of a principal ideal

Let `(R, m_R) → (S, m_S)` be a local homomorphism of local rings, with `S` the localization at a
prime `q` of an étale `R`-algebra `T`, and assume the residue field extension `κ(m_R) → κ(m_S)`
is surjective. This file proves Stacks 0GSD: there is a `t ∈ m_R` with `R/tⁿR → S/tⁿS` bijective
for every `n`.

The witness is produced by Newton's method. Shrinking `T` to a principal localization that is
*standard étale* over `R` (Proposition 00UE) presents `S` as a ring of fractions of polynomials
in one element: there are a monic `f ∈ R[X]` and a `ξ₀ ∈ S` with `f(ξ₀) = 0` and `f'(ξ₀)` a unit,
such that every `z ∈ S` satisfies `z·Q₁(ξ₀) = Q₂(ξ₀)` with `Q₁(ξ₀)` a unit. The residue field
hypothesis provides an `a ∈ R` with `ξ := ξ₀ - a ∈ m_S`. Writing `f(X + a) = X·h + t` with `t` its
constant term gives `t = -ξ·h(ξ) ∈ m_R`, and `h(ξ)` is a unit because it agrees with the unit
`f'(ξ)` modulo `m_S`. The recursion `ξ = -t·h(ξ)⁻¹` then produces, for every `n`, an `r ∈ m_R`
with `tⁿ ∣ ξ - r` in `S`; lifting along the principal ideal `tⁿ` rather than along `m_R` is what
makes a single element `t` work for all `n` at once.

Surjectivity of `R/tⁿR → S/tⁿS` follows: in `z·Q₁(ξ₀) = Q₂(ξ₀)` both sides are congruent modulo
`tⁿ` to images of elements of `R`, and the one coming from `Q₁` is a unit of `R` because it is a
unit of `S` and `R → S` is local. Injectivity is faithful flatness: `R → S` is flat, being a
localization of an étale algebra, and a flat local homomorphism of local rings is faithfully flat
(Lemmas 00HR, 05CK), so `tⁿS ∩ R = tⁿR`.

## Main results

* `Stacks.Etale.PrincipalPowerIso.solution`: the statement of
  `IsLocalRing.exists_mem_maximalIdeal_bijective_algebraMap_quotient_span_pow`, Lemma 0GSD.

## Implementation notes

The source reaches surjectivity by a second shrinking of `T`, to `R[x]_{hg}/(f)`, in which
`T/tT` is a quotient of `R/tR`, lifts that to `tⁿ` with Lemma 07RD, and then transfers from `T`
to `S`. The route taken here does the lifting in `S` directly, by the Newton recursion above, so
neither the second localization of `T` nor Lemma 07RD is needed; the finiteness of `T` over `R`
that 07RD consumes enters instead as the presentation of `S` by one simple root with polynomial
denominators, `exists_hasMap_forall_exists_mul_aeval_eq`.

## References

* [StacksProject 0GSD](https://stacks.math.columbia.edu/tag/0GSD), Lemma 10.153.1.
* [Lindel], the Lemma on page 321.
* [KC], Lemma 4.1.5.
-/

open Polynomial IsLocalRing

namespace Stacks.Etale.PrincipalPowerIso



section Polynomials

variable {R : Type*} [CommRing R]

/-- The derivative of `p = X * divX p + C (p.coeff 0)`. -/
private lemma derivative_eq_divX_add_X_mul_derivative_divX (p : R[X]) :
    derivative p = p.divX + X * derivative p.divX := by
  conv_lhs => rw [← X_mul_divX_add p]
  simp only [derivative_add, derivative_mul, derivative_X, derivative_C, one_mul, add_zero]

end Polynomials

section LocalRing

variable {S : Type*} [CommRing S] [IsLocalRing S]

/-- Two elements of a local ring congruent modulo the maximal ideal are units together. -/
private lemma isUnit_of_sub_mem_maximalIdeal {x y : S} (h : x - y ∈ maximalIdeal S)
    (hy : IsUnit y) : IsUnit x :=
  notMem_maximalIdeal.mp fun hx => notMem_maximalIdeal.mpr hy (by simpa using sub_mem hx h)

end LocalRing

section Newton

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The values of a polynomial at `ξ` and at (the image of) a scalar `ρ` are congruent modulo any
divisor of `ξ - ρ`. -/
private lemma dvd_aeval_sub_eval {d ξ : S} {ρ : R} (hd : d ∣ ξ - algebraMap R S ρ) (p : R[X]) :
    d ∣ aeval ξ p - algebraMap R S (p.eval ρ) :=
  hd.trans <| by
    rw [← aeval_algebraMap_apply_eq_algebraMap_eval, aeval_def, aeval_def, eval₂_eq_eval_map,
      eval₂_eq_eval_map]
    exact sub_dvd_eval_sub _ _ _

variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]

omit [IsLocalRing R] in
/-- A unit of `S` of the form `p(ξ)`, with `ξ` congruent to a scalar `ρ` modulo `m_S`, gives a
scalar `w` with `p(ρ)·w = 1` in `S`. -/
private lemma exists_algebraMap_eval_mul_eq_one {ξ : S} {ρ : R}
    (hρ : ξ - algebraMap R S ρ ∈ maximalIdeal S) {p : R[X]} (hp : IsUnit (aeval ξ p)) :
    ∃ w : R, algebraMap R S (p.eval ρ) * algebraMap R S w = 1 := by
  obtain ⟨w, hw⟩ := (IsLocalHom.map_nonunit (f := algebraMap R S) _ <|
    isUnit_of_sub_mem_maximalIdeal
      (by simpa using neg_mem (Ideal.mem_of_dvd _ (dvd_aeval_sub_eval dvd_rfl p) hρ))
      hp).exists_right_inv
  exact ⟨w, by rw [← map_mul, hw, map_one]⟩

/-- **Every element of a local ring is congruent modulo the maximal ideal to one in the image of
a ring homomorphism whose composite with the residue map is surjective.**

Only the target need be local, and the homomorphism need not be local: the hypothesis is
surjectivity of `residue B ∘ F` itself, which is what the proof uses. -/
public theorem exists_sub_mem_maximalIdeal_of_surjective_residue_comp {A B : Type*}
    [CommRing A] [CommRing B] [IsLocalRing B] (F : A →+* B)
    (hres : Function.Surjective ((residue B).comp F)) (b : B) :
    ∃ a : A, b - F a ∈ maximalIdeal B := by
  obtain ⟨a, ha⟩ := hres (residue B b)
  exact ⟨a, Ideal.Quotient.eq.1 ha.symm⟩

/-- **Surjectivity of the residue field extension says that every element of `B` is congruent
modulo `m_B` to the image of an element of `A`.** The hypothesis of
`Stacks.Etale.PrincipalPowerIso.exists_sub_mem_maximalIdeal_of_surjective_residue_comp` in the
form it is usually available: `ResidueField.map F` surjective, which gives the composite because
`residue A` is surjective and `ResidueField.map F` commutes with the residue maps. -/
public theorem exists_sub_mem_maximalIdeal_of_surjective_residueFieldMap {A B : Type*}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (F : A →+* B) [IsLocalHom F]
    (hres : Function.Surjective (ResidueField.map F)) (b : B) :
    ∃ a : A, b - F a ∈ maximalIdeal B :=
  exists_sub_mem_maximalIdeal_of_surjective_residue_comp F
    (fun y => by
      obtain ⟨x, hx⟩ := hres y
      obtain ⟨a, rfl⟩ := residue_surjective (R := A) x
      exact ⟨a, by rw [← hx, ResidueField.map_residue]; rfl⟩) b

/-- A scalar that becomes a multiple of an element of `m_S` lies in `m_R`. -/
private lemma mem_maximalIdeal_of_add_mul_eq_zero {t : R} {ξ u : S} (hξ : ξ ∈ maximalIdeal S)
    (heq : algebraMap R S t + ξ * u = 0) : t ∈ maximalIdeal R := by
  rw [← IsLocalRing.maximalIdeal_comap (algebraMap R S)]
  show algebraMap R S t ∈ maximalIdeal S
  rw [show algebraMap R S t = -(ξ * u) by linear_combination heq]
  exact neg_mem ((maximalIdeal S).mul_mem_right _ hξ)

/-- **Newton's method along a principal ideal.** If `t + ξ·h(ξ) = 0` with `ξ` in the maximal ideal
of `S` and `h(ξ)` a unit, then `ξ` is congruent modulo `tⁿ` to the image of an element of `m_R`,
for every `n`. The recursion is `ξ ↦ -t·h(r)⁻¹`, whose error is divisible by one more power of
`t` because `h(ξ) - h(r)` is. -/
private lemma exists_mem_maximalIdeal_dvd_sub {t : R} {h : R[X]} {ξ : S}
    (hξ : ξ ∈ maximalIdeal S) (hu : IsUnit (aeval ξ h))
    (heq : algebraMap R S t + ξ * aeval ξ h = 0) (n : ℕ) :
    ∃ r ∈ maximalIdeal R, algebraMap R S t ^ n ∣ ξ - algebraMap R S r := by
  have htR : t ∈ maximalIdeal R := mem_maximalIdeal_of_add_mul_eq_zero hξ heq
  induction n with
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | succ n ih =>
    obtain ⟨r, hr, hdvd⟩ := ih
    obtain ⟨w, hw'⟩ := exists_algebraMap_eval_mul_eq_one (sub_mem hξ (map_nonunit _ r hr)) hu
    refine ⟨-(t * w), neg_mem ((maximalIdeal R).mul_mem_right _ htR), ?_⟩
    have key : aeval ξ h * (ξ - algebraMap R S (-(t * w)))
        = algebraMap R S t * algebraMap R S w * (aeval ξ h - algebraMap R S (h.eval r)) := by
      simp only [map_neg, map_mul]
      linear_combination heq + algebraMap R S t * hw'
    refine (IsUnit.dvd_mul_left hu).mp ?_
    rw [key, pow_succ, mul_comm (algebraMap R S t ^ n), mul_assoc]
    exact mul_dvd_mul_left _ ((dvd_aeval_sub_eval hdvd h).mul_left _)

/-- **The witness `t`.** If `ξ₀` is a simple root of `f` congruent to the scalar `a` modulo `m_S`,
then the constant term `t` of the translate `f(X + a)` lies in `m_R`, and `ξ₀` is congruent to a
scalar modulo every power of `t`. -/
private lemma exists_mem_maximalIdeal_forall_exists_dvd_sub {f : R[X]} {ξ₀ : S} {a : R}
    (hzero : aeval ξ₀ f = 0) (hder : IsUnit (aeval ξ₀ (derivative f)))
    (ha : ξ₀ - algebraMap R S a ∈ maximalIdeal S) :
    ∃ t ∈ maximalIdeal R, ∀ n : ℕ, ∃ ρ : R, algebraMap R S t ^ n ∣ ξ₀ - algebraMap R S ρ := by
  set ξ := ξ₀ - algebraMap R S a with hξdef
  set F := f.comp (X + C a) with hF
  have hξ₀ : ξ + algebraMap R S a = ξ₀ := by rw [hξdef]; ring
  have hFξ : aeval ξ F = 0 := by rw [hF, aeval_comp]; simpa [hξ₀] using hzero
  have heq : algebraMap R S (F.coeff 0) + ξ * aeval ξ F.divX = 0 := by
    rw [← X_mul_divX_add F] at hFξ
    simp only [map_add, map_mul, aeval_X, aeval_C] at hFξ
    linear_combination hFξ
  have hderF : IsUnit (aeval ξ (derivative F)) := by
    have hcomp : derivative F = (derivative f).comp (X + C a) := by rw [hF, derivative_comp]; simp
    rw [hcomp, aeval_comp]
    simpa [hξ₀] using hder
  have hu : IsUnit (aeval ξ F.divX) := by
    refine isUnit_of_sub_mem_maximalIdeal ?_ hderF
    have hsub : aeval ξ F.divX - aeval ξ (derivative F)
        = -(ξ * aeval ξ (derivative F.divX)) := by
      rw [derivative_eq_divX_add_X_mul_derivative_divX F]
      simp only [map_add, map_mul, aeval_X]
      ring
    rw [hsub]
    exact neg_mem ((maximalIdeal S).mul_mem_right _ ha)
  refine ⟨F.coeff 0, mem_maximalIdeal_of_add_mul_eq_zero ha heq, fun n => ?_⟩
  obtain ⟨r, -, hdvd⟩ := exists_mem_maximalIdeal_dvd_sub ha hu heq n
  refine ⟨r + a, ?_⟩
  rwa [map_add, show ξ₀ - (algebraMap R S r + algebraMap R S a) = ξ - algebraMap R S r from by
    rw [hξdef]; ring]

/-- If `z·Q₁(ξ) = Q₂(ξ)` with `Q₁(ξ)` a unit and `ξ` congruent to a scalar modulo `tⁿ`, then `z`
too is congruent to a scalar modulo `tⁿ`. -/
private lemma exists_dvd_sub_of_mul_aeval_eq {t : R} (ht : t ∈ maximalIdeal R) {n : ℕ} {ξ : S}
    {ρ : R} (hρ : algebraMap R S t ^ n ∣ ξ - algebraMap R S ρ) {z : S} {Q₁ Q₂ : R[X]}
    (hQ : IsUnit (aeval ξ Q₁)) (hz : z * aeval ξ Q₁ = aeval ξ Q₂) :
    ∃ r : R, algebraMap R S t ^ n ∣ z - algebraMap R S r := by
  rcases n with _ | n
  · exact ⟨0, by simp⟩
  obtain ⟨w, hw'⟩ := exists_algebraMap_eval_mul_eq_one (Ideal.mem_of_dvd _ hρ
    (Ideal.pow_mem_of_mem _ (map_nonunit _ t ht) _ n.succ_pos)) hQ
  refine ⟨Q₂.eval ρ * w, ?_⟩
  have key : z - algebraMap R S (Q₂.eval ρ * w) = algebraMap R S w *
      (-(z * (aeval ξ Q₁ - algebraMap R S (Q₁.eval ρ)))
        + (aeval ξ Q₂ - algebraMap R S (Q₂.eval ρ))) := by
    simp only [map_mul]
    linear_combination algebraMap R S w * hz - z * hw'
  rw [key]
  exact (dvd_add (dvd_neg.mpr ((dvd_aeval_sub_eval hρ Q₁).mul_left z))
    (dvd_aeval_sub_eval hρ Q₂)).mul_left _

end Newton

section FaithfullyFlat

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]

/-- **A faithfully flat algebra does not enlarge the quotient by an ideal.** Since `IS ∩ R = I`,
the map `R/I → S/IS` is injective. -/
private lemma injective_algebraMap_quotient (I : Ideal R) :
    Function.Injective (algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S))) := by
  intro u v huv
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective u
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective v
  have h1 : Ideal.Quotient.mk (I.map (algebraMap R S)) (algebraMap R S u)
      = Ideal.Quotient.mk _ (algebraMap R S v) := huv
  rw [Ideal.Quotient.eq] at h1 ⊢
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) I, Ideal.mem_comap, map_sub]
  exact h1

end FaithfullyFlat

section Presentation

/-- **A localization of an étale algebra at a prime is a ring of fractions of polynomials in one
simple root** (Proposition 00UE). If `S` is the localization at a prime `q` of an étale
`R`-algebra `T`, there are a standard étale pair `P` over `R` and a `ξ : S` with `P.HasMap ξ` —
that is, `P.f(ξ) = 0` and `P.g(ξ)` a unit — such that every element of `S` becomes a value at `ξ`
of a polynomial over `R` after multiplication by such a value that is a unit. -/
private lemma exists_hasMap_forall_exists_mul_aeval_eq (R : Type u) [CommRing R] (S : Type v)
    [CommRing S] [Algebra R S] (T : Type w) [CommRing T] [Algebra R T] [Algebra.Etale R T]
    [Algebra T S] [IsScalarTower R T S] (q : Ideal T) [q.IsPrime] [IsLocalization.AtPrime S q] :
    ∃ (P : StandardEtalePair R) (ξ : S), P.HasMap ξ ∧
      ∀ z : S, ∃ Q₁ Q₂ : R[X], IsUnit (aeval ξ Q₁) ∧ z * aeval ξ Q₁ = aeval ξ Q₂ := by
  obtain ⟨f₀, hf₀, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) q
  have := hstd
  have hf₀' : IsUnit (algebraMap T S f₀) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff S q f₀).mpr hf₀
  let φ : Localization.Away f₀ →ₐ[R] S :=
    IsLocalization.Away.liftAlgHom f₀ (f := IsScalarTower.toAlgHom R T S) hf₀'
  have hφ : ∀ x : T, φ (algebraMap T (Localization.Away f₀) x) = algebraMap T S x :=
    fun x => IsLocalization.Away.lift_eq f₀ hf₀' x
  let P : StandardEtalePresentation R (Localization.Away f₀) :=
    Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some
  have hmap : P.P.HasMap (φ P.x) := P.hasMap.map φ
  refine ⟨P.P, φ P.x, hmap, fun z => ?_⟩
  have himg : ∀ {x : T} {p : R[X]} {k : ℕ},
      algebraMap T (Localization.Away f₀) x * aeval P.x P.P.g ^ k = aeval P.x p →
      algebraMap T S x * aeval (φ P.x) P.P.g ^ k = aeval (φ P.x) p := fun h => by
    simpa [hφ, aeval_algHom_apply] using congrArg φ h
  obtain ⟨⟨y, s⟩, hy⟩ := IsLocalization.surj (M := q.primeCompl) (S := S) z
  obtain ⟨p₁, k, hp₁⟩ := P.exists_mul_aeval_x_g_pow_eq_aeval_x
    (algebraMap T (Localization.Away f₀) (s : T))
  obtain ⟨p₂, m, hp₂⟩ := P.exists_mul_aeval_x_g_pow_eq_aeval_x
    (algebraMap T (Localization.Away f₀) y)
  refine ⟨p₁ * P.P.g ^ m, p₂ * P.P.g ^ k, ?_, ?_⟩
  · rw [map_mul, map_pow, ← himg hp₁]
    exact (((IsLocalization.AtPrime.isUnit_to_map_iff S q (s : T)).mpr s.2).mul
      (hmap.2.pow k)).mul (hmap.2.pow m)
  · rw [map_mul, map_mul, map_pow, map_pow, ← himg hp₁, ← himg hp₂, ← hy]
    ring

end Presentation

/-- **An étale local homomorphism is an isomorphism modulo powers of a principal ideal.** Let
`(R, m_R) → (S, m_S)` be a local homomorphism of local rings such that `S` is the localization
of an étale `R`-algebra `T` at a prime `q`, and such that the residue field extension
`κ(m_R) → κ(m_S)` is surjective, hence an isomorphism. Then there is `t ∈ m_R` such that
`R/tⁿR → S/tⁿS` is an isomorphism for every `n`. -/
public theorem solution
    (R : Type u) [CommRing R] [IsLocalRing R] (S : Type v) [CommRing S] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] (T : Type w) [CommRing T] [Algebra R T]
    [Algebra.Etale R T] [Algebra T S] [IsScalarTower R T S] (q : Ideal T) [q.IsPrime]
    [IsLocalization.AtPrime S q]
    (hres : Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R S))) :
    ∃ t ∈ IsLocalRing.maximalIdeal R, ∀ n : ℕ, Function.Bijective
      (algebraMap (R ⧸ Ideal.span {t ^ n}) (S ⧸ (Ideal.span {t ^ n}).map (algebraMap R S))) := by
  -- `R → S` is faithfully flat, being flat and local (Lemmas 00HR, 05CK).
  have : Module.Flat T S := IsLocalization.flat S q.primeCompl
  have : Module.Flat R S := Module.Flat.trans R T S
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  obtain ⟨P, ξ₀, hmap, hden⟩ := exists_hasMap_forall_exists_mul_aeval_eq R S T q
  obtain ⟨a, ha⟩ :=
    exists_sub_mem_maximalIdeal_of_surjective_residueFieldMap (algebraMap R S) hres ξ₀
  obtain ⟨t, htR, hcong⟩ :=
    exists_mem_maximalIdeal_forall_exists_dvd_sub hmap.1 hmap.isUnit_derivative_f ha
  refine ⟨t, htR, fun n => ⟨injective_algebraMap_quotient _, fun u => ?_⟩⟩
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective u
  obtain ⟨ρ, hρ⟩ := hcong n
  obtain ⟨Q₁, Q₂, hQ, hzz⟩ := hden z
  obtain ⟨r, hr⟩ := exists_dvd_sub_of_mul_aeval_eq htR hρ hQ hzz
  refine ⟨Ideal.Quotient.mk _ r, ?_⟩
  show Ideal.Quotient.mk ((Ideal.span {t ^ n}).map (algebraMap R S)) (algebraMap R S r)
    = Ideal.Quotient.mk _ z
  rw [Ideal.Quotient.eq, Ideal.map_span, Set.image_singleton, map_pow, Ideal.mem_span_singleton]
  exact dvd_sub_comm.mp hr

end Stacks.Etale.PrincipalPowerIso

/-!
# An étale local homomorphism is an isomorphism modulo powers of a principal ideal

Let `(R, m_R) → (S, m_S)` be a local homomorphism of local rings and assume that `S` is the
localization at a prime `q` of an étale `R`-algebra `T`, and that the induced extension of
residue fields `κ(m_R) → κ(m_S)` is an isomorphism. Then `R → S` is an isomorphism after
reduction modulo all powers of a suitable nonunit: there is `t ∈ m_R` with
`R/tⁿR → S/tⁿS` bijective for every `n`.

The witness is not an arbitrary element of `m_R`. In the source's proof `R → T` is reduced to a
*standard étale* map `T = R[x]_g/(f)` (Proposition 00UE, Definition 00UB); the residue field
hypothesis allows `x` to be translated so that `q = (m_R, x)`, and then
`f = xᵈ + a_{d-1}x^{d-1} + ⋯ + a₁x + t` with `t = f(0)`, which lies in `m_R` precisely because
`x ∈ q`. Writing `f = t + x h` with `h = a₁ + a₂x + ⋯ + x^{d-1}`, invertibility of `f'` on `T`
forces `a₁`, hence `h`, to be a unit at `q`, so `T` may be shrunk to `R[x]_{hg}/(f)` and then
`T/tT = (R/tR)[x]_{hg}/(x)` is a quotient of `R/tR`. Lemma 07RD upgrades this to surjectivity of
`R/tⁿR → T/tⁿT` for all `n`, injectivity comes from faithful flatness of the flat local map
`R/tⁿR → S/tⁿS` (Lemmas 00HR, 05CK), and finally `S/tⁿS` is a localization of the local ring
`T/tⁿT = R/tⁿR` at a prime containing its maximal ideal, hence equal to it.

The typical instance: `R = ℤ_(5)`, `T = R[x]/(x² - x + 5)`, `q = (5, x)`. Here `T` is the ring of
integers of `ℚ(√-19)` localized at `5`, in which `5` splits, `S = T_q` is a discrete valuation
ring strictly larger than `R`, the residue fields are both `𝔽₅`, and `t = f(0) = 5` gives
`R/5ⁿ ≅ S/5ⁿ ≅ ℤ/5ⁿ`.

## Main results

* `IsLocalRing.exists_mem_maximalIdeal_bijective_algebraMap_quotient_span_pow`: Lemma 0GSD.

## Implementation notes

The quotient map `R/tⁿR → S/tⁿS` is the `algebraMap` of the canonical algebra structure
`Ideal.Quotient.algebraQuotientMapQuotient` on `S ⧸ (Ideal.span {t ^ n}).map (algebraMap R S)`
over `R ⧸ Ideal.span {t ^ n}`; it is characterized by
`algebraMap _ _ (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (algebraMap R S r)`, which holds by
`rfl`. Stating bijectivity of this map, rather than the existence of some isomorphism between the
two quotients, is what pins the source's map.

Three departures from the source's form, none of them weakening it.

The hypothesis "`S` is the localization of an étale ring extension of `R`" is carried by an
ambient `R`-algebra `T` with `[Algebra.Etale R T]` and a prime `q` of `T` with
`[IsLocalization.AtPrime S q]`, rather than by an existential inside the statement; the
statement is thereby universally quantified over the presentation of `S`, which is how a user
supplies one. The source's further condition that `q` lies over `m_R` is omitted because it is
implied: `q = m_S.comap (algebraMap T S)` for a localization at a prime, so its contraction to
`R` is `m_S.comap (algebraMap R S) = m_R` by `[IsLocalHom (algebraMap R S)]`.

The conclusion is stated for every `n : ℕ` rather than for `n ≥ 1`. For `n = 0` both quotients are
the zero ring, so that case is true and carrying `1 ≤ n` would leave a hypothesis the conclusion
does not use.

The residue field hypothesis asks only that `κ(m_R) → κ(m_S)` be surjective. It is automatically
injective, being a ring homomorphism out of a field into a nontrivial ring, so this is the same
condition as the source's "is an isomorphism", stated with the weaker of the two hypotheses.

Faithfulness to [StacksProject 0GSD]:

1. No dead hypothesis. `t ∈ IsLocalRing.maximalIdeal R` is load-bearing in the conclusion:
   without it `t = 1` makes both quotients zero and the statement vacuous. The residue field
   surjectivity is used and not implied by the rest: `R = ℤ_(5)`, `T = R[x]/(x² + x + 1)`,
   `q = (5, x)` is étale with `κ(q) = 𝔽_25`, and no `t ∈ 5R` can give `R/tR ≅ S/tS`, since
   `S/5S = 𝔽_25` is not a quotient of `R/5R = 𝔽₅`, while every other hypothesis holds.
   `[IsLocalHom (algebraMap R S)]` is used twice over: it is what makes `κ(m_R) → κ(m_S)` exist
   at all, and it is load-bearing on its own — for `R = ℤ_(5)`, `T = R[1/5] = ℚ`, which is étale
   over `R` as a localization away from `5`, and `q = 0`, we get `S = ℚ`, all the remaining
   hypotheses hold (the residue field condition cannot even be formulated), and every `t ∈ m_R`
   fails, since `S/tⁿS = 0` while `R/tⁿR ≠ 0`. `[Algebra.Etale R T]` is used: for `T = R[x]` and
   `q = (5, x)` all other hypotheses hold, `κ(m_S) = 𝔽₅`, and `R/tⁿR → S/tⁿS` fails to be
   bijective for every `t ∈ 5R`, since `S/5S = 𝔽₅[x]_(x)` is not a quotient of `𝔽₅`.
2. The scalars and the base are the source's. Both quotients are taken of `R` and of `S`
   themselves by the ideals generated by `tⁿ` and by its image, and the map compared is the one
   induced by the given `R → S`; no localization of `R` intervenes, and the ideal in `S` is
   `tⁿS`, the ideal generated by the image of `tⁿ`, not the contraction or an abstract ideal.
3. What the source names is pinned. The residue field extension `κ(m_R) → κ(m_S)` is
   `IsLocalRing.ResidueField.map (algebraMap R S)`, the map induced by the given local
   homomorphism, and the comparison map `R/tⁿR → S/tⁿS` is the canonical `algebraMap` described
   above; neither is merely asserted to exist.
4. The instantiation is not degenerate. The witness `R = ℤ_(5)`, `T = R[x]/(x² - x + 5)`,
   `q = (5, x)`, `t = 5` recorded above has `S ≠ R` — `S` is a localization of a rank two
   `R`-algebra, with fraction field `ℚ(√-19)` — so the conclusion is not the tautology obtained
   when `T = R`, and `t = 5` is a nonzero nonunit, so no `tⁿR` is `0` or `R`.

## References

* [StacksProject 0GSD](https://stacks.math.columbia.edu/tag/0GSD), Lemma 10.153.1, in
  Section 10.153 "Local homomorphisms".
* [Lindel], the Lemma on page 321.
* [KC], Lemma 4.1.5.
-/

@[expose] public section



/-- **An étale local homomorphism is an isomorphism modulo powers of a principal ideal.** Let
`(R, m_R) → (S, m_S)` be a local homomorphism of local rings such that `S` is the localization
of an étale `R`-algebra `T` at a prime `q`, and such that the residue field extension
`κ(m_R) → κ(m_S)` is surjective, hence an isomorphism. Then there is `t ∈ m_R` such that
`R/tⁿR → S/tⁿS` is an isomorphism for every `n`. -/
@[stacks 0GSD "The hypothesis `t ∈ m_R` and the conclusion are the source's; the map shown
bijective is the canonical `R/tⁿR → S/tⁿS`. Stated for all `n : ℕ` (the case `n = 0` is the zero
ring), with `κ(m_R) → κ(m_S)` merely surjective (equivalent, as it is injective automatically),
and with the étale algebra `T` and the prime `q` as hypotheses rather than an existential."]
public theorem IsLocalRing.exists_mem_maximalIdeal_bijective_algebraMap_quotient_span_pow
    (R : Type u) [CommRing R] [IsLocalRing R] (S : Type v) [CommRing S] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] (T : Type w) [CommRing T] [Algebra R T]
    [Algebra.Etale R T] [Algebra T S] [IsScalarTower R T S] (q : Ideal T) [q.IsPrime]
    [IsLocalization.AtPrime S q]
    (hres : Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R S))) :
    ∃ t ∈ IsLocalRing.maximalIdeal R, ∀ n : ℕ, Function.Bijective
      (algebraMap (R ⧸ Ideal.span {t ^ n}) (S ⧸ (Ideal.span {t ^ n}).map (algebraMap R S))) :=
    by exact Stacks.Etale.PrincipalPowerIso.solution R S T q hres

end
