module

public import StacksFrontier.RingTheory.Henselian.EtaleLifting.HenselianRetraction
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
# Lifting a residue-field map to a henselian local ring (Stacks tag 08HR)

The ind-étale version of Tag 08HQ: for `S` henselian local over `R` and `A` ind-étale over `R`,
a residue datum `(q, τ)` on `A` lifts to a unique `R`-algebra map `f : A → S`.

## Main results

* `Stacks.Henselian.EtaleLifting.henselian_Spoint_lift`: `S`-points of an étale `S`-algebra lift
  uniquely from residue-field points.
* `Stacks.Henselian.EtaleLifting.exists_unique_algHom_etale`: the étale case, in terms of
  `residueFieldMapBase`, `residueFieldMapFib` and `InducesResidueMap`.
* `Stacks.Henselian.EtaleLifting.algHom`, `algHom_spec`, `algHom_unique`: the ind-étale case.
* `HenselianLocalRing.existsUnique_algHom_residue_of_etale`: residue-field points of an étale
  algebra lift uniquely to a henselian local ring.
-/

@[expose] public section

open CategoryTheory Limits IsLocalRing
open scoped TensorProduct

universe u v w

namespace Stacks.Henselian.EtaleLifting

variable {R A : Type u} {S : Type v} [CommRing R] [CommRing S] [CommRing A]
variable [Algebra R S] [Algebra R A]

/-- The canonical map `κ(p) → S/m_S` induced by `R → S`, where `p = R ∩ m_S` is the
contraction of `m_S` along `R → S`.  It is well defined precisely because
`p = m_S.comap (R → S)`. -/
noncomputable def residueFieldMapBase [IsLocalRing S] (p : Ideal R) [p.IsPrime]
    (hp : p = (maximalIdeal S).comap (algebraMap R S)) :
    p.ResidueField →+* ResidueField S :=
  Ideal.ResidueField.lift p ((residue S).comp (algebraMap R S))
    (by
      intro a ha
      rw [hp] at ha
      simp only [RingHom.mem_ker, RingHom.comp_apply]
      exact (residue_eq_zero_iff _).mpr ha)
    (by
      intro r hr
      simp only [Submonoid.mem_comap, RingHom.comp_apply, IsUnit.mem_submonoid_iff]
      have hrp : r ∉ p := hr
      have hr' : algebraMap R S r ∉ maximalIdeal S := by
        intro hmem
        exact hrp (by rw [hp]; exact hmem)
      have : residue S (algebraMap R S r) ≠ 0 :=
        (residue_ne_zero_iff_isUnit _).mpr ((notMem_maximalIdeal).mp hr')
      exact isUnit_iff_ne_zero.mpr this)

/-- `residueFieldMapBase` is the residue map of `S`, read along `R → S`: the class of `r : R` in
`κ(p)` goes to the class of `φ r` in `S/m_S`. -/
@[simp]
lemma residueFieldMapBase_algebraMap [IsLocalRing S] (p : Ideal R) [p.IsPrime]
    (hp : p = (maximalIdeal S).comap (algebraMap R S)) (r : R) :
    residueFieldMapBase p hp (algebraMap R p.ResidueField r) = residue S (algebraMap R S r) :=
  Ideal.ResidueField.lift_algebraMap _ _ _ _ r

/-- The canonical map `κ(p) → κ(q)` induced by `R → A`, where `q` lies over `p`
(i.e. `p = q.comap (R → A)`). -/
noncomputable def residueFieldMapFib {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    (p : Ideal R) [p.IsPrime] (q : Ideal A) [q.IsPrime]
    (hpq : p = q.comap (algebraMap R A)) :
    p.ResidueField →+* q.ResidueField :=
  Ideal.ResidueField.map p q (algebraMap R A) hpq

/-- `residueFieldMapFib` is the canonical map `A → κ(q)`, read along `R → A`: the class of `r : R`
in `κ(p)` goes to the class of its image in `κ(q)`. -/
@[simp]
lemma residueFieldMapFib_algebraMap {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    (p : Ideal R) [p.IsPrime] (q : Ideal A) [q.IsPrime]
    (hpq : p = q.comap (algebraMap R A)) (r : R) :
    residueFieldMapFib p q hpq (algebraMap R p.ResidueField r)
      = algebraMap A q.ResidueField (algebraMap R A r) :=
  Ideal.ResidueField.map_algebraMap _ _ _ _ r

/-- The residue field map `κ(q) → S/m_S` induced by an `R`-algebra (or ring) homomorphism
`f : A → S` satisfying `q = f⁻¹(m_S)`. We package the defining property as the commuting
square `τ ∘ (A → κ(q)) = (S → S/m_S) ∘ f`, which is the meaning of "`f mod q = τ`". -/
def InducesResidueMap {A : Type u} {S : Type v} [CommRing A] [CommRing S]
    [IsLocalRing S] (q : Ideal A) [q.IsPrime] (f : A →+* S)
    (τ : q.ResidueField →+* ResidueField S) : Prop :=
  τ.comp (algebraMap A q.ResidueField) = (residue S).comp f

private lemma ideal_eq_comap_of_inducesResidueMap {A : Type u} {S : Type v}
    [CommRing A] [CommRing S] [IsLocalRing S] (q : Ideal A) [q.IsPrime]
    (g : A →+* S) (τ : q.ResidueField →+* ResidueField S)
    (h : InducesResidueMap q g τ) : q = (maximalIdeal S).comap g := by
  calc q = RingHom.ker (algebraMap A q.ResidueField) :=
          (Ideal.ker_algebraMap_residueField q).symm
    _ = RingHom.ker (τ.comp (algebraMap A q.ResidueField)) :=
        (RingHom.ker_comp_of_injective _ τ.injective).symm
    _ = RingHom.ker ((residue S).comp g) := by rw [h]
    _ = (RingHom.ker (residue S)).comap g := (RingHom.comap_ker _ _).symm
    _ = (maximalIdeal S).comap g := by rw [IsLocalRing.ker_residue]

/-- A residue datum `τ` over `κ(p)` makes `τ ∘ (A → κ(q))` into an `R`-algebra map `A → κ(S)`. -/
private lemma exists_algHom_eq_comp_residueField {R : Type u} {A : Type v} {S : Type w}
    [CommRing R] [CommRing A] [CommRing S] [Algebra R A] [Algebra R S] [IsLocalRing S]
    (p : Ideal R) [p.IsPrime] (hp : p = (maximalIdeal S).comap (algebraMap R S))
    (q : Ideal A) [q.IsPrime] (hpq : p = q.comap (algebraMap R A))
    (τ : q.ResidueField →+* ResidueField S)
    (hτ : τ.comp (residueFieldMapFib p q hpq) = residueFieldMapBase p hp) :
    ∃ ψ : A →ₐ[R] ResidueField S,
      (ψ : A →+* ResidueField S) = τ.comp (algebraMap A q.ResidueField) := by
  refine ⟨AlgHom.mk' (τ.comp (algebraMap A q.ResidueField)) fun c x => ?_, rfl⟩
  rw [Algebra.smul_def, Algebra.smul_def]
  simp only [RingHom.comp_apply, map_mul]
  congr 1
  show τ (algebraMap A q.ResidueField (algebraMap R A c)) = algebraMap R (ResidueField S) c
  rw [← residueFieldMapFib_algebraMap p q hpq c, ← RingHom.comp_apply, hτ,
    residueFieldMapBase_algebraMap, IsScalarTower.algebraMap_apply R S (ResidueField S) c,
    ResidueField.algebraMap_eq]

/-- **Henselian `S`-point lifting (the analytic kernel of Tag 08HQ).**
Let `S` be henselian local with residue field `κ = ResidueField S`, and let `C` be an étale
`S`-algebra.  Then every `S`-algebra map `φ : C → κ` lifts UNIQUELY through `residue S : S → κ`
to an `S`-algebra map `σ : C → S` (i.e. `(residue S) ∘ σ = φ`).

INFORMAL PROOF (Tag 08HQ kernel).  Let `Q = ker φ`, a prime of `C` over `m_S` with `C/Q ≅ κ`
(residue degree 1, since `φ ∘ ιₛ = residue S` is surjective).  As `C` is étale (hence finitely
presented) at `Q`, by `Algebra.IsEtaleAt.exists_isStandardEtale` there is `h ∉ Q` with `C_h`
standard étale over `S`, presented by a `StandardEtalePair` `P` with monic `P.f` and universal
element `P.X`.  Set `a₀ = φ̄(P.X) ∈ κ`.  Then `a₀` is a SIMPLE root of `P.f mod m_S`: it is a root
since `P.f(P.X) = 0`, and simple since `P.f'(P.X)` is a unit in `C_h` (standard étale) so its
`φ̄`-image is nonzero.  Henselian `S` (Stacks 04GG, `HenselianLocalRing.TFAE` simple-root lifting)
lifts `a₀` to a unique `x ∈ S` with `P.f(x) = 0`, `residue S x = a₀`; `P.HasMap x` holds (the
localization element `P.g(P.X)` is a unit ⇒ `P.g(x) ∉ m_S` ⇒ unit), giving `σ = P.lift x`
(globalised through `C → C_h`).  `(residue S) ∘ σ = φ` since both agree on `P.X` (`hom_ext`).
Uniqueness: any two lifts have `σᵢ(P.X) = xᵢ` two roots of `P.f` over `S` with the same simple
reduction `a₀`; the divided-difference factorisation `P.f(x₁) - P.f(x₂) = (x₁-x₂)·H` with
`H ≡ P.f'(a₀) ≢ 0 (mod m_S)` a unit forces `x₁ = x₂`, hence `σ₁ = σ₂`
(`StandardEtalePair.hom_ext`).

This is the analytic content of Tags 08HQ and 08HR; the building blocks 00UE, 04GG and
`StandardEtalePair` are in Mathlib. -/
theorem henselian_Spoint_lift
    (S : Type v) [CommRing S] [HenselianLocalRing S]
    (C : Type w) [CommRing C] [Algebra S C] [Algebra.Etale S C]
    (φ : C →ₐ[S] ResidueField S) :
    ∃! σ : C →ₐ[S] S, (residue S).comp (σ : C →+* S) = (φ : C →+* ResidueField S) := by
  -- (1) Standard-étale chart at Q = ker φ.
  set Q : Ideal C := RingHom.ker (φ : C →+* ResidueField S) with hQdef
  have hQp : Q.IsPrime := RingHom.ker_isPrime _
  have hetaleAt : Algebra.IsEtaleAt S Q := Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat Q
  obtain ⟨h, hhQ, hStd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := S) (S := C) Q
  obtain ⟨pres⟩ := hStd.nonempty_standardEtalePresentation
  have hQ : h ∉ RingHom.ker (φ : C →+* ResidueField S) := hhQ
  have hφh : IsUnit (φ h) := by
    rw [RingHom.mem_ker] at hQ
    exact isUnit_iff_ne_zero.mpr (by simpa using hQ)
  let ℓ : C →ₐ[S] Localization.Away h := IsScalarTower.toAlgHom S C (Localization.Away h)
  -- Any `S`-algebra map out of `C` sending `h` to a unit extends along `ℓ`.
  have hlift : ∀ (T : Type v) [CommRing T] [Algebra S T] (g : C →ₐ[S] T), IsUnit (g h) →
      ∃ gₕ : Localization.Away h →ₐ[S] T, ∀ c : C, gₕ (ℓ c) = g c := by
    intro T _ _ g hg
    have hu : ∀ (y : Submonoid.powers h), IsUnit (g ↑y) := by
      rintro ⟨y, n, rfl⟩; simpa using hg.pow n
    refine ⟨IsLocalization.liftAlgHom (M := Submonoid.powers h) (f := g) hu, fun c => ?_⟩
    show IsLocalization.liftAlgHom hu (algebraMap C (Localization.Away h) c) = g c
    rw [IsLocalization.coe_liftAlgHom, IsLocalization.lift_eq]; rfl
  obtain ⟨φh, hℓφ⟩ := hlift _ φ hφh
  set a₀ : ResidueField S := φh pres.x with ha₀
  have hmap := pres.hasMap
  rw [StandardEtalePair.HasMap.eq_1] at hmap
  -- (2) Existence: lift the simple root a₀ to x ∈ S and build σ₀ = lift x ∘ chart ∘ localization.
  have hroot : Polynomial.aeval a₀ pres.P.f = 0 := by
    rw [ha₀, Polynomial.aeval_algHom_apply, hmap.left, map_zero]
  have hsimple : Polynomial.aeval a₀ (Polynomial.derivative pres.P.f) ≠ 0 := by
    have hu : IsUnit (Polynomial.aeval pres.x (Polynomial.derivative pres.P.f)) :=
      StandardEtalePair.HasMap.isUnit_derivative_f pres.P pres.hasMap
    rw [ha₀, Polynomial.aeval_algHom_apply]
    exact (hu.map φh).ne_zero
  have hTFAE := (HenselianLocalRing.TFAE S).out 1 2
  obtain ⟨x, hxroot, hxres⟩ :=
    (hTFAE.mp ‹HenselianLocalRing S›) pres.P.f pres.P.monic_f a₀ hroot hsimple
  have hHasMapx : pres.P.HasMap x := by
    rw [StandardEtalePair.HasMap.eq_1]
    refine ⟨?_, ?_⟩
    · rw [Polynomial.coe_aeval_eq_eval]; exact hxroot
    · rw [← notMem_maximalIdeal]
      intro hcon
      have hz : residue S (Polynomial.aeval x pres.P.g) = 0 := (residue_eq_zero_iff _).mpr hcon
      have hz2 : Polynomial.aeval a₀ pres.P.g = 0 := by
        have e1 : residue S (Polynomial.aeval x pres.P.g)
            = Polynomial.aeval ((Algebra.ofId S (ResidueField S)) x) pres.P.g := by
          rw [Polynomial.aeval_algHom_apply]; rfl
        rw [e1] at hz
        have he : (Algebra.ofId S (ResidueField S)) x = a₀ := hxres
        rwa [he] at hz
      rw [ha₀, Polynomial.aeval_algHom_apply] at hz2
      exact (hmap.right.map φh).ne_zero hz2
  let σ₀ₕ : Localization.Away h →ₐ[S] S := (pres.P.lift x hHasMapx).comp pres.equivRing.toAlgHom
  let σ₀ : C →ₐ[S] S := σ₀ₕ.comp ℓ
  have hσ₀ₕx : σ₀ₕ pres.x = x := by
    show (pres.P.lift x hHasMapx) (pres.equivRing pres.x) = x
    rw [pres.equivRing_x, pres.P.lift_X]
  have hσ₀ : (residue S).comp (σ₀ : C →+* S) = (φ : C →+* ResidueField S) := by
    have keyAlg : (Algebra.ofId S (ResidueField S)).comp σ₀ₕ = φh := by
      apply pres.hom_ext
      show (Algebra.ofId S (ResidueField S)) (σ₀ₕ pres.x) = φh pres.x
      rw [hσ₀ₕx]
      exact hxres
    ext c
    show (residue S) (σ₀ c) = φ c
    exact (DFunLike.congr_fun keyAlg (ℓ c)).trans (hℓφ c)
  -- (3) Uniqueness: every lift σ factors through the chart and its value at pres.x is the
  --     unique simple-root lift x, hence equals σ₀ by `StandardEtalePresentation.hom_ext`.
  have hgen : ∀ (σ : C →ₐ[S] S), (residue S).comp (σ : C →+* S) = (φ : C →+* ResidueField S) →
      ∃ σₕ : Localization.Away h →ₐ[S] S, σₕ.comp ℓ = σ ∧
        (pres.P.f).IsRoot (σₕ pres.x) ∧ residue S (σₕ pres.x) = a₀ ∧
        IsUnit ((pres.P.f).derivative.eval (σₕ pres.x)) := by
    intro σ hσ
    have hσh : IsUnit (σ h) := by
      rw [← notMem_maximalIdeal]
      have hres : residue S (σ h) = φ h := congrFun (congrArg DFunLike.coe hσ) h
      intro hm
      exact hφh.ne_zero (by rw [← hres]; exact (residue_eq_zero_iff _).mpr hm)
    obtain ⟨σₕ, hℓσ⟩ := hlift S σ hσh
    refine ⟨σₕ, AlgHom.ext hℓσ, ?_, ?_, ?_⟩
    · have hHM : pres.P.HasMap (σₕ pres.x) := pres.hasMap.map σₕ
      rw [StandardEtalePair.HasMap.eq_1] at hHM
      rw [Polynomial.IsRoot, ← Polynomial.coe_aeval_eq_eval]
      exact hHM.left
    · have hcomp : (Algebra.ofId S (ResidueField S)).comp σₕ = φh := by
        apply IsLocalization.algHom_ext (Submonoid.powers h)
        ext c
        show residue S (σₕ (ℓ c)) = φh (ℓ c)
        rw [hℓσ, hℓφ]
        exact congrFun (congrArg DFunLike.coe hσ) c
      rw [ha₀]
      exact congrFun (congrArg DFunLike.coe hcomp) pres.x
    · have hHM : pres.P.HasMap (σₕ pres.x) := pres.hasMap.map σₕ
      have := StandardEtalePair.HasMap.isUnit_derivative_f pres.P hHM
      rwa [Polynomial.coe_aeval_eq_eval] at this
  refine ⟨σ₀, hσ₀, ?_⟩
  intro σ' hσ'
  obtain ⟨σ'ₕ, e', hr', hres', hsi'⟩ := hgen σ' hσ'
  obtain ⟨σ₀ₕ', e0, hr0, hres0, _⟩ := hgen σ₀ hσ₀
  have hxeq : σ'ₕ pres.x = σ₀ₕ' pres.x :=
    hensel_root_unique pres.P.f _ _ hr' hr0 hsi'
      ((residue_eq_zero_iff _).mp (by rw [map_sub, hres0, hres', sub_self]))
  have heqₕ : σ'ₕ = σ₀ₕ' := pres.hom_ext hxeq
  rw [← e', ← e0, heqₕ]

/-- **Étale case — Stacks Tag 08HQ (Lemma 10.154.5).**
The henselian/étale lifting heart of Tag 08HR.  Let `R → S` be a ring map with `S` henselian
local, let `B` be an *étale* `R`-algebra, `qB` a prime of `B` lying over `p = R ∩ m_S`, and
`τ : κ(qB) → S/m_S` a `κ(p)`-algebra map.  Then there is a UNIQUE `R`-algebra homomorphism
`f : B → S` with `qB = f⁻¹(m_S)` and `f mod qB = τ`.

INFORMAL PROOF (Stacks Tag 08HQ).  Base change: `B ⊗_R S` is étale over `S` (étale is stable
under base change, `Algebra.Etale.baseChange`).  The residue datum `(qB, τ)` corresponds, via
`p = R ∩ m_S` and the universal property of base change, to a prime `Q` of `B ⊗_R S` lying over
`m_S` together with a `κ(m_S) = S/m_S`-point of the (separable, since étale) residue field
extension `κ(Q)/κ(m_S)`; concretely `τ : κ(qB) → S/m_S` packages a maximal ideal `Q ⊃ m_S·(B⊗_R S)`
whose residue field equals `S/m_S` (i.e. `Q` has residue degree `1` and `(B⊗_R S)/Q = S/m_S`).
Localising/standard-étale-presenting `B ⊗_R S` at `Q`, the henselian property of `S` (Stacks
Tag 04GG, `HenselianLocalRing.TFAE`: simple roots of monic polynomials over `S` lift uniquely from
`S/m_S`) produces a unique `S`-algebra retraction `σ : B ⊗_R S → S` with `σ⁻¹(m_S) = Q`.  Composing
the coprojection `B → B ⊗_R S` with `σ` yields the desired `f : B → S`; the two conditions
`qB = f⁻¹(m_S)` and `f mod qB = τ` translate exactly into `σ⁻¹(m_S) = Q` and the residue-field
identity, and uniqueness of `f` follows from uniqueness of the henselian splitting `σ`.

This is the irreducible analytic kernel of the lemma. -/
@[ega "IV 18.6.2" "more general"]
theorem exists_unique_algHom_etale
    {B : Type w} [CommRing B] [Algebra R B] [Algebra.Etale R B]
    [HenselianLocalRing S]
    (p : Ideal R) [p.IsPrime]
    (hp : p = (maximalIdeal S).comap (algebraMap R S))
    (qB : Ideal B) [qB.IsPrime]
    (hpqB : p = qB.comap (algebraMap R B))
    (τ : qB.ResidueField →+* ResidueField S)
    (hτ : τ.comp (residueFieldMapFib p qB hpqB) = residueFieldMapBase p hp) :
    ∃! f : B →ₐ[R] S,
      qB = (maximalIdeal S).comap (f : B →+* S) ∧
      InducesResidueMap qB (f : B →+* S) τ := by
  -- Proof of Tag 08HQ via base change `C := S ⊗[R] B` (étale over `S`,
  -- `Algebra.Etale.baseChange`) and the henselian kernel `henselian_Spoint_lift`.
  --
  -- ψ : B →ₐ[R] κ(S) realizing τ; its underlying ring hom is `τ ∘ (B → κ(qB))`.
  --   Existence as an *R-algebra* map needs the κ(p)-compatibility `commutes'`, which is exactly
  --   `hτ` transported through `hp`, `hpqB`, the definitions of `residueFieldMapBase`/`Fib`, and
  --   the fact that `B → κ(qB)` over `R` factors through `κ(p)` (residueFieldMapFib).
  obtain ⟨ψ, hψ⟩ := exists_algHom_eq_comp_residueField p hp qB hpqB τ hτ
  -- φ : S ⊗[R] B →ₐ[S] κ(S) is the base-change extension of ψ (`AlgHom.liftEquiv`).
  let φ : (S ⊗[R] B) →ₐ[S] ResidueField S := AlgHom.liftEquiv R S B (ResidueField S) ψ
  -- transport_iff: across the base-change adjunction equiv `e := AlgHom.liftEquiv R S B S`, the
  -- residue datum on `σ : S⊗B →ₐ[S] S` matches the two conditions on `f := e.symm σ : B →ₐ[R] S`.
  -- Both `(residue S)∘σ` and `φ` are S-alg maps `S⊗B → κ(S)`; by `Algebra.TensorProduct.hom_ext`
  -- equality ⟺ agreement on `includeLeft` (both `residue S`, automatic) and on `includeRight`
  -- (`(residue S)∘f` resp. `ψ = τ∘(B→κ(qB))`), i.e. exactly `InducesResidueMap qB f τ` (via `hψ`).
  -- And `qB = f⁻¹(m_S)` is automatic from `InducesResidueMap` (τ injective field map,
  -- `ker (B → κ(qB)) = qB`).
  have hcong : ∀ σ : (S ⊗[R] B) →ₐ[S] S,
      (qB = (maximalIdeal S).comap (((AlgHom.liftEquiv R S B S).symm σ : B →ₐ[R] S) : B →+* S) ∧
        InducesResidueMap qB (((AlgHom.liftEquiv R S B S).symm σ : B →ₐ[R] S) : B →+* S) τ)
      ↔ (residue S).comp (σ : (S ⊗[R] B) →+* S) = (φ : (S ⊗[R] B) →+* ResidueField S) := by
    have hφ : φ = AlgHom.liftEquiv R S B (ResidueField S) ψ := rfl
    have hψb : ∀ b : B, ψ b = τ (algebraMap B qB.ResidueField b) := fun b =>
      congrFun (congrArg DFunLike.coe hψ) b
    intro σ
    set f : B →+* S := (((AlgHom.liftEquiv R S B S).symm σ : B →ₐ[R] S) : B →+* S) with hf
    have key : ∀ b : B, f b = σ (1 ⊗ₜ[R] b) := fun b =>
      AlgHom.liftEquiv_symm_apply σ b
    have keyφ : ∀ b : B,
        (φ : (S ⊗[R] B) →+* ResidueField S) (1 ⊗ₜ[R] b)
          = τ (algebraMap B qB.ResidueField b) := by
      intro b
      show φ (1 ⊗ₜ[R] b) = _
      rw [hφ, AlgHom.liftEquiv_tmul, one_smul]
      exact hψb b
    have keyσ : ∀ b : B, ((residue S).comp (σ : (S ⊗[R] B) →+* S)) (1 ⊗ₜ[R] b)
        = (residue S) (σ (1 ⊗ₜ[R] b)) := fun b => rfl
    -- fact (A): the core transport equivalence (eq. 5.1).
    have factA : ((residue S).comp (σ : (S ⊗[R] B) →+* S)
          = (φ : (S ⊗[R] B) →+* ResidueField S))
        ↔ ((residue S).comp f = τ.comp (algebraMap B qB.ResidueField)) := by
      constructor
      · intro h
        ext b
        have hb := congrFun (congrArg DFunLike.coe h) (1 ⊗ₜ[R] b)
        rw [keyσ b, keyφ b] at hb
        simp only [RingHom.comp_apply]
        rw [key b]
        exact hb
      · intro h
        apply Algebra.TensorProduct.ringHom_ext
        · ext s
          simp only [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply]
          have hsl : (s ⊗ₜ[R] (1 : B)) = algebraMap S (S ⊗[R] B) s := by
            rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
          rw [hsl]
          show (residue S) (σ (algebraMap S (S ⊗[R] B) s)) = φ (algebraMap S (S ⊗[R] B) s)
          rw [AlgHom.commutes, AlgHom.commutes, Algebra.algebraMap_self_apply]
          rfl
        · ext b
          have hb := congrFun (congrArg DFunLike.coe h) b
          simp only [RingHom.comp_apply] at hb
          rw [key b] at hb
          show ((residue S).comp (σ : (S ⊗[R] B) →+* S)) (1 ⊗ₜ[R] b)
              = (φ : (S ⊗[R] B) →+* ResidueField S) (1 ⊗ₜ[R] b)
          rw [keyσ b, keyφ b]
          exact hb
    refine ⟨fun ⟨_, hind⟩ => factA.mpr hind.symm, fun hres => ?_⟩
    have hAf : (residue S).comp f = τ.comp (algebraMap B qB.ResidueField) := factA.mp hres
    exact ⟨ideal_eq_comap_of_inducesResidueMap qB f τ hAf.symm, hAf.symm⟩
  -- Glue: transport the kernel's `∃! σ` to the goal `∃! f` via `Equiv.existsUnique_congr'`.
  exact (Equiv.existsUnique_congr' (e := AlgHom.liftEquiv R S B S) hcong).mpr
    (henselian_Spoint_lift S (S ⊗[R] B) φ)

/-- The coprojections of a colimit presentation of `A` in `CommAlgCat R` are jointly epimorphic
against `R`-algebras in *any* universe.

The universal property of the colimit only produces maps into objects of `CommAlgCat.{u} R`, so it
says nothing directly about a target `T` in another universe.  It does apply to the equalizer of
`g₁` and `g₂`, which is a subalgebra of `A`, hence again an object of `CommAlgCat.{u} R`:
descending along the presentation exhibits the inclusion `equalizer g₁ g₂ → A` as a retraction, so
every element of `A` lies in the equalizer. -/
private lemma algHom_eq_of_comp_ι_eq {R : Type u} {A J : Type v}
    [CommRing R] [CommRing A] [Algebra R A] [SmallCategory J]
    (pres : ColimitPresentation J (CommAlgCat.of R A))
    {T : Type w} [CommRing T] [Algebra R T] (g₁ g₂ : A →ₐ[R] T)
    (h : ∀ j, g₁.comp (pres.ι.app j).hom = g₂.comp (pres.ι.app j).hom) :
    g₁ = g₂ := by
  set E := AlgHom.equalizer g₁ g₂ with hE
  have hmem : ∀ (j : J) (x : pres.diag.obj j), (pres.ι.app j).hom x ∈ E := fun j x =>
    congrFun (congrArg DFunLike.coe (h j)) x
  let c : Cocone pres.diag :=
    { pt := CommAlgCat.of R E
      ι :=
        { app := fun j => CommAlgCat.ofHom (((pres.ι.app j).hom).codRestrict E (hmem j))
          naturality := fun j k φ => by
            apply CommAlgCat.hom_ext
            ext x
            exact Subtype.ext (by simp) } }
  have hretr : ∀ a : A, ((pres.isColimit.desc c).hom a : A) = a := by
    have hid : pres.isColimit.desc c ≫ CommAlgCat.ofHom E.val = 𝟙 _ := by
      apply pres.isColimit.hom_ext
      intro j
      rw [← Category.assoc, pres.isColimit.fac, Category.comp_id]
      apply CommAlgCat.hom_ext
      rfl
    intro a
    exact congrFun (congrArg DFunLike.coe (congrArg CommAlgCat.Hom.hom hid)) a
  ext a
  have hm : ((pres.isColimit.desc c).hom a : A) ∈ E := ((pres.isColimit.desc c).hom a).2
  rwa [hretr a] at hm

/-- A compatible family of `R`-algebra maps out of a colimit presentation of `A` in `CommAlgCat R`
descends to `A`, whatever the universe of the target `T`.

Again the universal property is only available for targets in `CommAlgCat.{u} R`, so the family is
descended into a `Type u` model of the subalgebra of `T` it generates: that subalgebra is the range
of `β : MvPolynomial (Σ j, Aⱼ) R →ₐ[R] T`, hence a quotient of a polynomial algebra on a type in
`Type u`.  The descended map is the composite of that model's embedding into `T` with the map the
universal property provides. -/
private lemma exists_algHom_comp_ι_eq {R : Type u} {A J : Type (max u v)}
    [CommRing R] [CommRing A] [Algebra R A] [SmallCategory J]
    (pres : ColimitPresentation J (CommAlgCat.of R A))
    {T : Type w} [CommRing T] [Algebra R T] (g : ∀ j, pres.diag.obj j →ₐ[R] T)
    (hg : ∀ {j k : J} (φ : j ⟶ k), (g k).comp (pres.diag.map φ).hom = g j) :
    ∃ f : A →ₐ[R] T, ∀ j, f.comp (pres.ι.app j).hom = g j := by
  set β : MvPolynomial (Σ j, pres.diag.obj j) R →ₐ[R] T :=
    MvPolynomial.aeval (fun p => g p.1 p.2) with hβ
  set e := Ideal.quotientKerEquivRange β with he
  set emb := β.range.val.comp e.toAlgHom with hemb
  have hembinj : Function.Injective emb := by
    rw [hemb]; exact Subtype.val_injective.comp e.injective
  have hrange : ∀ (j : J) (x : pres.diag.obj j), g j x ∈ β.range := fun j x =>
    ⟨MvPolynomial.X ⟨j, x⟩, by simp [hβ]⟩
  set g₀ : ∀ j, pres.diag.obj j →ₐ[R] _ := fun j =>
    e.symm.toAlgHom.comp ((g j).codRestrict β.range (hrange j)) with hg₀
  have hembg : ∀ j, emb.comp (g₀ j) = g j := by
    intro j; ext x; simp [hemb, hg₀]
  let c : Cocone pres.diag :=
    { pt := CommAlgCat.of R _
      ι :=
        { app := fun j => CommAlgCat.ofHom (g₀ j)
          naturality := fun j k φ => by
            apply CommAlgCat.hom_ext
            simp only [CommAlgCat.hom_comp, CommAlgCat.hom_ofHom, Functor.const_obj_obj,
              Functor.const_obj_map, Category.comp_id]
            refine AlgHom.ext fun x => hembinj ?_
            show emb ((g₀ k) ((pres.diag.map φ).hom x)) = emb ((g₀ j) x)
            rw [← AlgHom.comp_apply emb (g₀ k), ← AlgHom.comp_apply emb (g₀ j),
              hembg k, hembg j]
            exact congrFun (congrArg DFunLike.coe (hg φ)) x } }
  refine ⟨emb.comp (pres.isColimit.desc c).hom, fun j => ?_⟩
  rw [AlgHom.comp_assoc, show (pres.isColimit.desc c).hom.comp (pres.ι.app j).hom = g₀ j from
    congrArg CommAlgCat.Hom.hom (pres.isColimit.fac c j), hembg j]

/-- **Theorem (Stacks Tag 08HR, Lemma 10.154.6).**
Let `R → S` be a ring map with `S` henselian local. Let `A` be ind-étale over `R`, i.e. a
filtered colimit of étale `R`-algebras, `q` a prime of `A` lying over `p = R ∩ m_S`, and
`τ : κ(q) → S/m_S` a `κ(p)`-algebra map. Then there is a unique `R`-algebra homomorphism `f : A →
S` with
`q = f⁻¹(m_S)` and `f mod q = τ`.

INFORMAL PROOF (Stacks Tag 08HR).  Write `A = colim_{j∈J} A_j` as a filtered colimit of étale
`R`-algebras `A_j = F.obj j`, with coprojections `ιⱼ : A_j → A`.  For each `j` set
`qⱼ = ιⱼ⁻¹(q)`, a prime of `A_j` lying over `p` (contracting `q` to `A_j`), and let `τⱼ : κ(qⱼ) →
S/m_S` be the composite `κ(qⱼ) → κ(q) →[τ] S/m_S` (the residue
map of `ιⱼ` followed by `τ`); each `τⱼ` is a `κ(p)`-algebra map because `τ` is.  By the étale case
(`exists_unique_algHom_etale`, Tag 08HQ) there is a UNIQUE `R`-algebra map `fⱼ : A_j → S` with
`qⱼ = fⱼ⁻¹(m_S)` and `fⱼ mod qⱼ = τⱼ`.  Uniqueness makes the `fⱼ` compatible: for `φ : j ⟶ k`,
both `f_k ∘ F.map φ` and `fⱼ` solve the étale problem for `A_j` (same `qⱼ`, same `τⱼ`), so they
agree; hence `(fⱼ)` is a cocone `F ⟶ (const S)`.  The colimit universal property gives a unique
`R`-algebra map `f : A → S` with `f ∘ ιⱼ = fⱼ`.  Then `f⁻¹(m_S) = q` and `f mod q = τ` hold:
each is checked after precomposing with the (jointly surjective on the colimit) `ιⱼ`, where they
reduce to the corresponding properties of `fⱼ`.  Uniqueness of `f`: any solution `g` restricts to
`g ∘ ιⱼ`, which solves the étale problem for `A_j`, hence equals `fⱼ` by Tag 08HQ uniqueness; as
the `ιⱼ` are jointly epic into the colimit, `g = f`. -/
private theorem existsUnique_algHom_aux
    {R : Type u} {A : Type v} {S : Type w}
    [CommRing R] [CommRing A] [CommRing S] [Algebra R A] [Algebra R S]
    [HenselianLocalRing S]
    (hA : (CommAlgCat.etale.{max u v} R).ind.{max u v}
      (CommAlgCat.of R (ULift.{u} A)))
    (p : Ideal R) [p.IsPrime]
    (hp : p = (maximalIdeal S).comap (algebraMap R S))
    (q : Ideal A) [q.IsPrime]
    (hpq : p = q.comap (algebraMap R A))
    (τ : q.ResidueField →+* ResidueField S)
    -- `τ` is a `κ(p)`-algebra map: it is compatible with `κ(p) → κ(q)` and `κ(p) → S/m_S`.
    (hτ : τ.comp (residueFieldMapFib p q hpq) = residueFieldMapBase p hp) :
    ∃! f : A →ₐ[R] S,
      q = (maximalIdeal S).comap (f : A →+* S) ∧
      InducesResidueMap q (f : A →+* S) τ := by
  -- Unpack the filtered-colimit presentation of `A`, and abbreviate its diagram by `F`.
  obtain ⟨J, instSC, instFilt, pres, hetale⟩ := hA
  set F : J ⥤ CommAlgCat.{max u v} R := pres.diag with hF
  -- The whole content now reduces, stage by stage, to the étale case `exists_unique_algHom_etale`
  -- (Tag 08HQ, the named hard kernel decomposed above), glued through the colimit `c`.
  -- Concretely:
  --
  -- D1 (per-stage data).  For each `j` form the coprojection `ιⱼ := (pres.ι.app j).hom`,
  --   the contracted prime `qⱼ := q.comap ιⱼ` (prime, lying over `p` since `q` does and
  --   `R → A_j → A = R → A`), and the residue datum `τⱼ := τ ∘ (κ(qⱼ) → κ(q))`.  Each `τⱼ` is a
  --   `κ(p)`-algebra map because `τ` is and the `κ(p)→κ(qⱼ)→κ(q)` triangle commutes.
  -- D2 (étale lift).  `exists_unique_algHom_etale` applied to `(F.obj j, qⱼ, τⱼ)` gives a unique
  --   `R`-algebra map `fⱼ : F.obj j → S` with `qⱼ = fⱼ⁻¹(m_S)` and `InducesResidueMap qⱼ fⱼ τⱼ`.
  -- D3 (cocone).  For `φ : j ⟶ k`, `f_k ∘ F.map φ` and `fⱼ` both solve the étale problem at `j`
  --   (`F.map φ` pulls `q_k` back to `qⱼ` and `τ_k` back to `τⱼ`), so they coincide by D2's
  --   uniqueness; hence `(fⱼ)` defines a cocone `F ⟶ (Functor.const J).obj (CommAlgCat.of R S)`.
  -- D4 (glue + verify + uniqueness).  `exists_algHom_comp_ι_eq` descends that family to
  --   `f : A → S`; both `q = f⁻¹(m_S)` and `InducesResidueMap q f τ` are checked after composing
  --   with the `ιⱼ`, which are jointly epimorphic by `algHom_eq_of_comp_ι_eq` (where they are
  --   exactly the `fⱼ` properties).  Any other solution `g` restricts to a stagewise solution,
  --   equal to `fⱼ` by D2, so `g = f` by joint epimorphy again.
  --
  -- The descent bookkeeping (D1, D3, D4) is routine `CommAlgCat` manipulation; the genuine
  -- mathematics is the étale kernel D2, isolated as `exists_unique_algHom_etale`.
  -- D1: coprojections, contracted primes, residue data.
  let e : ULift.{u} A ≃ₐ[R] A := ULift.algEquiv
  set ι : ∀ j, F.obj j →ₐ[R] A := fun j => e.toAlgHom.comp (pres.ι.app j).hom with hι
  -- ι is natural: precomposing ι_k by F.map φ recovers ι_j.
  have hιnat : ∀ {j k : J} (φ : j ⟶ k), (ι k).comp (F.map φ).hom = ι j := by
    intro j k φ
    simp only [hι, AlgHom.comp_assoc]
    congr 1
    exact congrArg CommAlgCat.Hom.hom (pres.w φ)
  -- ring-hom version of naturality
  have hιnatR : ∀ {j k : J} (φ : j ⟶ k),
      (ι k : F.obj k →+* A).comp ((F.map φ).hom : F.obj j →+* F.obj k) = (ι j : F.obj j →+* A) := by
    intro j k φ
    exact congrArg (fun (g : F.obj j →ₐ[R] A) => (g : F.obj j →+* A)) (hιnat φ)
  set Φ : A →+* ResidueField S := τ.comp (algebraMap A q.ResidueField) with hΦ
  -- the contracted prime at stage j
  set qj : ∀ j, Ideal (F.obj j) := fun j => q.comap (ι j : F.obj j →+* A) with hqj
  have qjPrime : ∀ j, (qj j).IsPrime := fun j => Ideal.IsPrime.comap _
  have hpqj : ∀ j, p = (qj j).comap (algebraMap R (F.obj j)) := by
    intro j
    rw [hqj]
    simp only
    rw [Ideal.comap_comap, (ι j).comp_algebraMap]
    exact hpq
  -- the residue datum at stage j: τj := τ ∘ (κ(qj) → κ(q)) where the residue map comes from ι j.
  set τj : ∀ j, (qj j).ResidueField →+* ResidueField S :=
    fun j => τ.comp (Ideal.ResidueField.map (qj j) q (ι j : F.obj j →+* A) rfl) with hτj
  -- κ(p)-compatibility of τj (inherited from hτ via functoriality of residue field maps).
  have hτjcompat : ∀ j, (τj j).comp (residueFieldMapFib p (qj j) (hpqj j))
      = residueFieldMapBase p hp := by
    intro j
    refine Ideal.ResidueField.ringHom_ext (RingHom.ext fun r => ?_)
    have hτr := RingHom.congr_fun hτ (algebraMap R p.ResidueField r)
    simp only [hτj, RingHom.comp_apply, residueFieldMapFib_algebraMap,
      Ideal.ResidueField.map_algebraMap, AlgHom.coe_toRingHom, AlgHom.commutes,
      residueFieldMapBase_algebraMap] at hτr ⊢
    exact hτr
  -- Translation: the residue map of τj at stage j composed with the canonical A_j → κ(qj)
  -- equals Φ ∘ ι_j, where Φ = τ ∘ (A → κ(q)).
  have hΦιj : ∀ j, (τj j).comp (algebraMap (F.obj j) (qj j).ResidueField)
      = Φ.comp (ι j : F.obj j →+* A) := by
    intro j
    rw [hτj, hΦ]
    simp only
    ext a
    simp only [RingHom.comp_apply]
    rw [Ideal.ResidueField.map_algebraMap]
  -- D2: the étale lift at each stage.
  have hstage : ∀ j, ∃! fj : F.obj j →ₐ[R] S,
      qj j = (maximalIdeal S).comap (fj : F.obj j →+* S) ∧
      InducesResidueMap (qj j) (fj : F.obj j →+* S) (τj j) := by
    intro j
    have := qjPrime j
    have := hetale j
    exact exists_unique_algHom_etale p hp (qj j) (hpqj j) (τj j) (hτjcompat j)
  -- f j : the chosen stagewise solution; its two properties; and stagewise uniqueness.
  set f : ∀ j, F.obj j →ₐ[R] S := fun j => (hstage j).exists.choose with hf
  have hfspec : ∀ j, qj j = (maximalIdeal S).comap (f j : F.obj j →+* S) ∧
      InducesResidueMap (qj j) (f j : F.obj j →+* S) (τj j) :=
    fun j => (hstage j).exists.choose_spec
  have hfuniq : ∀ j (g : F.obj j →ₐ[R] S),
      (qj j = (maximalIdeal S).comap (g : F.obj j →+* S) ∧
        InducesResidueMap (qj j) (g : F.obj j →+* S) (τj j)) → g = f j := by
    intro j g hg
    exact (hstage j).unique hg (hfspec j)
  -- Each f j satisfies Φ ∘ ι_j = (residue S) ∘ f_j.
  have hfΦ : ∀ j, Φ.comp (ι j : F.obj j →+* A) = (residue S).comp (f j : F.obj j →+* S) := by
    intro j
    rw [← hΦιj j]
    exact (hfspec j).right
  -- A stagewise map `g` with `Φ ∘ ι_j = (residue S) ∘ g` solves the étale problem at stage j.
  have hsolve : ∀ j (g : F.obj j →ₐ[R] S), (∀ x, Φ (ι j x) = residue S (g x)) →
      qj j = (maximalIdeal S).comap (g : F.obj j →+* S) ∧
        InducesResidueMap (qj j) (g : F.obj j →+* S) (τj j) := by
    intro j g hg
    have hind : InducesResidueMap (qj j) (g : F.obj j →+* S) (τj j) :=
      RingHom.ext fun x => (RingHom.congr_fun (hΦιj j) x).trans (hg x)
    exact ⟨ideal_eq_comap_of_inducesResidueMap (qj j) _ (τj j) hind, hind⟩
  -- D3: compatibility. For φ : j ⟶ k, (f k) ∘ (F.map φ) solves stage j, hence equals f j.
  have hcompat : ∀ {j k : J} (φ : j ⟶ k), (f k).comp (F.map φ).hom = f j := by
    intro j k φ
    refine hfuniq j _ (hsolve j _ fun x => ?_)
    rw [← hιnat φ]
    exact RingHom.congr_fun (hfΦ k) _
  -- D4: descend the compatible family, and record that the ι_j are jointly epimorphic.
  obtain ⟨fglueU, hfacU⟩ := exists_algHom_comp_ι_eq (R := R)
    (A := ULift.{u} A) pres f fun φ => hcompat φ
  let fglue : A →ₐ[R] S := fglueU.comp e.symm.toAlgHom
  have hfac : ∀ j, fglue.comp (ι j) = f j := by
    intro j
    ext x
    have hx := congrFun (congrArg DFunLike.coe (hfacU j)) x
    simpa [fglue, hι] using hx
  have hjointepiT : ∀ (T : Type w) [CommRing T] [Algebra R T] (g₁ g₂ : A →ₐ[R] T),
      (∀ j, g₁.comp (ι j) = g₂.comp (ι j)) → g₁ = g₂ :=
    fun T _ _ g₁ g₂ hgg => by
      have hu : g₁.comp e.toAlgHom = g₂.comp e.toAlgHom := by
        apply algHom_eq_of_comp_ι_eq pres
        intro j
        simpa only [hι, AlgHom.comp_assoc] using hgg j
      ext a
      have ha := congrFun (congrArg DFunLike.coe hu) (e.symm a)
      simpa using ha
  -- Φ is R-linear: package it as an R-algebra hom A → κ(S).
  obtain ⟨Φₐ, hΦₐ⟩ := exists_algHom_eq_comp_residueField p hp q hpq τ hτ
  -- Verify fglue: InducesResidueMap q fglue τ, i.e. Φ = (residue S) ∘ fglue.
  have hglueInduces : InducesResidueMap q (fglue : A →+* S) τ := by
    show Φ = (residue S).comp (fglue : A →+* S)
    -- as R-algebra homs A → κ(S): Φₐ vs (S → κ(S) as R-alg) ∘ fglue.
    let Rfglue : A →ₐ[R] ResidueField S :=
      (IsScalarTower.toAlgHom R S (ResidueField S)).comp fglue
    have hRf : (Rfglue : A →+* ResidueField S) = (residue S).comp (fglue : A →+* S) := by
      ext a
      show (IsScalarTower.toAlgHom R S (ResidueField S)) (fglue a) = (residue S) (fglue a)
      show algebraMap S (ResidueField S) (fglue a) = (residue S) (fglue a)
      rw [ResidueField.algebraMap_eq]
    have heq : Φₐ = Rfglue := by
      apply hjointepiT (ResidueField S) Φₐ Rfglue
      intro j
      ext x
      show Φₐ (ι j x) = (residue S) (fglue (ι j x))
      rw [show Φₐ (ι j x) = Φ (ι j x) from RingHom.congr_fun hΦₐ _,
        ← AlgHom.comp_apply fglue (ι j) x, hfac j]
      exact RingHom.congr_fun (hfΦ j) x
    calc Φ = (Φₐ : A →+* ResidueField S) := hΦₐ.symm
      _ = (Rfglue : A →+* ResidueField S) := by rw [heq]
      _ = (residue S).comp (fglue : A →+* S) := hRf
  -- comap conjunct follows from InducesResidueMap by factB.
  have hgluecomap : q = (maximalIdeal S).comap (fglue : A →+* S) :=
    ideal_eq_comap_of_inducesResidueMap q (fglue : A →+* S) τ hglueInduces
  refine ⟨fglue, ⟨hgluecomap, hglueInduces⟩, ?_⟩
  -- Uniqueness.
  rintro g ⟨hgcomap, hgInduces⟩
  -- g.comp (ι j) solves stage j, hence equals f j = fglue.comp (ι j); joint epi gives g = fglue.
  apply hjointepiT S g fglue
  intro j
  have hgInd' : Φ = (residue S).comp (g : A →+* S) := hgInduces
  have hgj : (g.comp (ι j)) = f j :=
    hfuniq j _ (hsolve j _ fun x => RingHom.congr_fun hgInd' (ι j x))
  -- fglue.comp (ι j) = f j as alg homs.
  rw [hgj, hfac j]

/-- **The lift of a residue datum along an ind-étale algebra into a henselian local ring**
(Stacks Tag 08HR, Lemma 10.154.6). Let `R → S` be a ring map with `S` henselian local, let `A` be
ind-étale over `R`, let `q` be a prime of `A` lying over `p = R ∩ 𝔪 S`, and let
`τ : κ(q) → κ(S)` be a `κ(p)`-algebra map. This is the `R`-algebra map `A → S` with
`q = f⁻¹(𝔪 S)` inducing `τ` on residue fields; `algHom_spec` is those two properties and
`algHom_unique` says it is the only such map. -/
@[stacks 08HR "the map itself; `algHom_spec` is its two defining properties and `algHom_unique`
its uniqueness", no_expose]
noncomputable def algHom
    {R : Type u} {A : Type v} {S : Type w}
    [CommRing R] [CommRing A] [CommRing S] [Algebra R A] [Algebra R S]
    [HenselianLocalRing S]
    (hA : (CommAlgCat.etale.{max u v} R).ind.{max u v}
      (CommAlgCat.of R (ULift.{u} A)))
    (p : Ideal R) [p.IsPrime]
    (hp : p = (maximalIdeal S).comap (algebraMap R S))
    (q : Ideal A) [q.IsPrime]
    (hpq : p = q.comap (algebraMap R A))
    (τ : q.ResidueField →+* ResidueField S)
    (hτ : τ.comp (residueFieldMapFib p q hpq) = residueFieldMapBase p hp) :
    A →ₐ[R] S :=
  (existsUnique_algHom_aux hA p hp q hpq τ hτ).exists.choose

/-- `algHom` pulls the maximal ideal of `S` back to `q` and induces `τ` on residue fields. -/
@[stacks 08HR "the two defining properties of `algHom`"]
theorem algHom_spec
    {R : Type u} {A : Type v} {S : Type w}
    [CommRing R] [CommRing A] [CommRing S] [Algebra R A] [Algebra R S]
    [HenselianLocalRing S]
    (hA : (CommAlgCat.etale.{max u v} R).ind.{max u v}
      (CommAlgCat.of R (ULift.{u} A)))
    (p : Ideal R) [p.IsPrime]
    (hp : p = (maximalIdeal S).comap (algebraMap R S))
    (q : Ideal A) [q.IsPrime]
    (hpq : p = q.comap (algebraMap R A))
    (τ : q.ResidueField →+* ResidueField S)
    (hτ : τ.comp (residueFieldMapFib p q hpq) = residueFieldMapBase p hp) :
    q = (maximalIdeal S).comap (algHom hA p hp q hpq τ hτ : A →+* S) ∧
      InducesResidueMap q (algHom hA p hp q hpq τ hτ : A →+* S) τ :=
  (existsUnique_algHom_aux hA p hp q hpq τ hτ).exists.choose_spec

/-- `algHom` pulls the maximal ideal of `S` back to `q`. -/
theorem comap_maximalIdeal_algHom
    {R : Type u} {A : Type v} {S : Type w}
    [CommRing R] [CommRing A] [CommRing S] [Algebra R A] [Algebra R S]
    [HenselianLocalRing S]
    (hA : (CommAlgCat.etale.{max u v} R).ind.{max u v}
      (CommAlgCat.of R (ULift.{u} A)))
    (p : Ideal R) [p.IsPrime]
    (hp : p = (maximalIdeal S).comap (algebraMap R S))
    (q : Ideal A) [q.IsPrime]
    (hpq : p = q.comap (algebraMap R A))
    (τ : q.ResidueField →+* ResidueField S)
    (hτ : τ.comp (residueFieldMapFib p q hpq) = residueFieldMapBase p hp) :
    q = (maximalIdeal S).comap (algHom hA p hp q hpq τ hτ : A →+* S) :=
  (algHom_spec hA p hp q hpq τ hτ).1

/-- `algHom` induces the prescribed map `τ` on residue fields. -/
theorem inducesResidueMap_algHom
    {R : Type u} {A : Type v} {S : Type w}
    [CommRing R] [CommRing A] [CommRing S] [Algebra R A] [Algebra R S]
    [HenselianLocalRing S]
    (hA : (CommAlgCat.etale.{max u v} R).ind.{max u v}
      (CommAlgCat.of R (ULift.{u} A)))
    (p : Ideal R) [p.IsPrime]
    (hp : p = (maximalIdeal S).comap (algebraMap R S))
    (q : Ideal A) [q.IsPrime]
    (hpq : p = q.comap (algebraMap R A))
    (τ : q.ResidueField →+* ResidueField S)
    (hτ : τ.comp (residueFieldMapFib p q hpq) = residueFieldMapBase p hp) :
    InducesResidueMap q (algHom hA p hp q hpq τ hτ : A →+* S) τ :=
  (algHom_spec hA p hp q hpq τ hτ).2

/-- `algHom` is the only `R`-algebra map `A → S` pulling `𝔪 S` back to `q` and inducing `τ` on
residue fields. -/
@[stacks 08HR "uniqueness of `algHom`"]
theorem algHom_unique
    {R : Type u} {A : Type v} {S : Type w}
    [CommRing R] [CommRing A] [CommRing S] [Algebra R A] [Algebra R S]
    [HenselianLocalRing S]
    (hA : (CommAlgCat.etale.{max u v} R).ind.{max u v}
      (CommAlgCat.of R (ULift.{u} A)))
    (p : Ideal R) [p.IsPrime]
    (hp : p = (maximalIdeal S).comap (algebraMap R S))
    (q : Ideal A) [q.IsPrime]
    (hpq : p = q.comap (algebraMap R A))
    (τ : q.ResidueField →+* ResidueField S)
    (hτ : τ.comp (residueFieldMapFib p q hpq) = residueFieldMapBase p hp)
    (f : A →ₐ[R] S)
    (hf : q = (maximalIdeal S).comap (f : A →+* S) ∧
      InducesResidueMap q (f : A →+* S) τ) :
    f = algHom hA p hp q hpq τ hτ :=
  (existsUnique_algHom_aux hA p hp q hpq τ hτ).unique hf (algHom_spec hA p hp q hpq τ hτ)

end Stacks.Henselian.EtaleLifting

open IsLocalRing in
/-- **Residue-field points of an étale algebra lift uniquely to a henselian local ring.** Let `S`
be a henselian local `R`-algebra and let `A` be an étale `R`-algebra. Every `R`-algebra map
`ψ : A → κ(S)` is the reduction of exactly one `R`-algebra map `f : A → S`. This is
`Stacks.Henselian.EtaleLifting.henselian_Spoint_lift` for the étale `S`-algebra `S ⊗[R] A`, read
through the universal property of the base change. -/
@[ega "IV 18.6.2" "special case", sga "4 VIII 4.1" "partial"]
theorem HenselianLocalRing.existsUnique_algHom_residue_of_etale {R : Type u} {A : Type w}
    {S : Type v} [CommRing R] [CommRing A] [CommRing S] [Algebra R A] [Algebra R S]
    [Algebra.Etale R A] [HenselianLocalRing S] (ψ : A →ₐ[R] ResidueField S) :
    ∃! f : A →ₐ[R] S, ∀ a, residue S (f a) = ψ a := by
  obtain ⟨σ, hσ, huniq⟩ :=
    Stacks.Henselian.EtaleLifting.henselian_Spoint_lift S (S ⊗[R] A) (AlgHom.liftEquiv R S A _ ψ)
  refine ⟨(AlgHom.liftEquiv R S A S).symm σ, fun a => ?_, fun f hf => ?_⟩
  · simpa using RingHom.congr_fun hσ (1 ⊗ₜ[R] a)
  · refine ((AlgHom.liftEquiv R S A S).symm_apply_eq.mpr (huniq _ ?_).symm).symm
    ext s <;> simp [Algebra.smul_def, hf]

end
