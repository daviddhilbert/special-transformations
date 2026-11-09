module

import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Etale.Finite
import Mathlib.Order.CompletePartialOrder
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.Parity
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Data.NNRat.Floor
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.CategoryTheory.ObjectProperty.Ind
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
import Mathlib.Algebra.Category.CommAlgCat.FiniteType
import Mathlib.CategoryTheory.Monoidal.Mon
public import StacksFrontier.Algebra.Category.CommAlgCat.FilteredColimits
import StacksCore.Tactic.EgaSgaAttribute


@[expose] public section

universe u v w

namespace Stacks.Henselization.EtaleColimit

/-!
# Existence of the henselization of a local ring

Let `(R, 𝔪, κ)` be a local ring. The henselization is built as the colimit of the *category of
pairs*: an object is an étale `R`-algebra `S` together with a prime `𝔮` of `S` lying over `𝔪`
with `κ(𝔮) = κ`, and a morphism `(S, 𝔮) → (S', 𝔮')` is an `R`-algebra map `φ` with
`φ⁻¹(𝔮') = 𝔮`.

## Implementation notes

*Pairs are augmentations to the residue field.* A prime `𝔮` of an `R`-algebra `S` lying over `𝔪`
with `κ = κ(𝔮)` is the same datum as an `R`-algebra map `α : S → κ`: given `α`, its kernel is
such a prime (it is automatically surjective, because `R → κ` already is), and given `𝔮`, the
composite `S → S/𝔮 ≃ κ` is such an `α`. Under this dictionary a morphism of pairs is exactly a
morphism of `R`-algebras over `κ`, because the only `R`-algebra endomorphism of `κ` is the
identity. So the category of pairs is `CategoryTheory.CostructuredArrow` of the inclusion of the
étale `R`-algebras into `CommAlgCat R` over the object `κ`, which is how it is spelled here; the
prime ideals never have to be carried around.

*Smallness.* An étale algebra is of finite presentation, hence of finite type, so the étale
objects of `CommAlgCat R` form an essentially `u`-small object property
(`etale_essentiallySmall`, via `FGAlgCatSkeleton`). Since `CommAlgCat.{u} R` is locally `u`-small,
the category of pairs is then essentially `u`-small, and the colimit may be taken over its small
model, which is what `ObjectProperty.ind.{u}` asks for.

*Elements of the colimit.* Items (1), (3) and (4) all need that an element of `R^h`, and indeed
any finite set of elements, already lives on a single pair. Mathlib computes filtered colimits of
rings and of modules concretely, but not of `CommAlgCat R`, so
`CategoryTheory.Limits.Concrete.isColimit_exists_rep` cannot be applied here. Instead
`CommAlgCat.iSup_range_eq_top` shows that the images of the structure maps of any colimit cocone
of `R`-algebras generate its vertex — the vertex retracts onto the subalgebra they span — and over
a filtered index category those images form a directed family, so their union is already the whole
vertex.
-/

open CategoryTheory CategoryTheory.Limits IsLocalRing



/-! ### Preliminaries on filtered colimits of algebras -/

section

variable (R : Type u) [CommRing R]

/-- Finitely many elements of a filtered colimit of commutative `R`-algebras are all images from
one and the same object of the index category. -/
theorem exists_app_eq_finset {J : Type v} [Category.{w} J] [IsFiltered J]
    {F : J ⥤ CommAlgCat.{u} R} (c : Cocone F) (hc : IsColimit c)
    (s : Finset ((c.pt : CommAlgCat.{u} R) : Type u)) :
    ∃ j : J, ∀ x ∈ s, ∃ y : ((F.obj j : CommAlgCat.{u} R) : Type u), (c.ι.app j).hom y = x := by
  classical
  have : Nonempty J := IsFiltered.nonempty
  choose j y hy using fun x => CommAlgCat.exists_app_eq hc x
  obtain ⟨k, hk⟩ := (CommAlgCat.directed_range c).finset_le (s.image j)
  exact ⟨k, fun x hx => hk (j x) (Finset.mem_image_of_mem _ hx) ⟨y x, hy x⟩⟩

/-- The image of the ideal generated by `I` under an `R`-algebra map lies in the ideal generated
by `I` in the target. -/
theorem mem_map_of_algHom {A : Type v} {B : Type w} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : A →ₐ[R] B) {I : Ideal R} {z : A} (hz : z ∈ I.map (algebraMap R A)) :
    f z ∈ I.map (algebraMap R B) := by
  have h : Ideal.map (f : A →+* B) (I.map (algebraMap R A)) = I.map (algebraMap R B) := by
    rw [Ideal.map_map, AlgHom.comp_algebraMap]
  exact h ▸ Ideal.mem_map_of_mem _ hz

/-- Evaluating the image of a polynomial at the image of a point: `Polynomial.eval_map_apply`
for an `R`-algebra map applied through its own coercion. -/
public theorem eval_map_toRingHom {A B : Type u} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : A →ₐ[R] B) (T : Polynomial A) (y : A) :
    (T.map f.toRingHom).eval (f y) = f (T.eval y) :=
  Polynomial.eval_map_apply f.toRingHom y

end

section

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-! ### The index category of pairs -/

omit [IsLocalRing R] in
/-- The étale objects of `CommAlgCat.{u} R` form an essentially `u`-small object property:
an étale algebra is of finite type, hence a quotient of a polynomial ring on finitely many
variables. -/
public theorem etale_essentiallySmall :
    ObjectProperty.EssentiallySmall.{u} (CommAlgCat.etale.{u} R) := by
  refine ⟨⟨ObjectProperty.ofObj (fun P : FGAlgCatSkeleton R ↦ (P.eval).obj), inferInstance, ?_⟩⟩
  intro A hA
  have : Algebra.Etale R A := hA
  have : Algebra.FiniteType R A := inferInstance
  obtain ⟨P, ⟨e⟩⟩ := Algebra.FiniteType.exists_fgAlgCatSkeleton R (A : Type u)
  exact ⟨(P.eval).obj, ObjectProperty.ofObj_apply _ P, ⟨CommAlgCat.isoMk e⟩⟩

attribute [local instance] etale_essentiallySmall

/-- The **category of pairs** of Stacks 04GN: an étale `R`-algebra together with an augmentation
to the residue field `κ` of `R`. See the module docstring for why this is the same as the
source's category of pairs `(S, 𝔮)`. -/
private abbrev Pairs : Type (u + 1) :=
  CostructuredArrow (CommAlgCat.etale.{u} R).ι (CommAlgCat.of R (ResidueField R))

/-- The algebra underlying a pair is étale over `R`. -/
private theorem Pairs.etale (A : Pairs R) : Algebra.Etale R (A.left.obj : Type u) :=
  A.left.property

attribute [local instance] Pairs.etale

/-- The category of pairs is essentially `u`-small. -/
private theorem essentiallySmall_pairs : EssentiallySmall.{u} (Pairs R) := inferInstance

attribute [local instance] essentiallySmall_pairs

/-- The pair `(R, 𝔪)`, i.e. `R` itself augmented by the residue map. -/
private noncomputable def Pairs.unit : Pairs R :=
  CostructuredArrow.mk (Y := ⟨CommAlgCat.of R R, inferInstance⟩)
    (CommAlgCat.ofHom (Algebra.ofId R (ResidueField R)))

/-- The `R`-algebra map underlying a morphism of pairs. -/
private noncomputable abbrev Pairs.map {A B : Pairs R} (h : A ⟶ B) :
    (A.left.obj : Type u) →ₐ[R] (B.left.obj : Type u) :=
  ((CommAlgCat.etale.{u} R).ι.map h.left).hom

/-- A morphism of pairs is determined by its underlying algebra map. -/
private theorem Pairs.hom_ext {A B : Pairs R} (u v : A ⟶ B)
    (h : Pairs.map R u = Pairs.map R v) : u = v := by
  have h' : (CommAlgCat.etale.{u} R).ι.map u.left = (CommAlgCat.etale.{u} R).ι.map v.left :=
    CommAlgCat.hom_ext h
  exact CostructuredArrow.hom_ext _ _ ((CommAlgCat.etale.{u} R).ι.map_injective h')

/-- Underlying algebra maps compose. -/
private theorem Pairs.map_comp {A B C : Pairs R} (u : A ⟶ B) (v : B ⟶ C)
    (x : (A.left.obj : Type u)) :
    Pairs.map R (u ≫ v) x = Pairs.map R v (Pairs.map R u x) :=
  ConcreteCategory.congr_hom ((CommAlgCat.etale.{u} R).ι.map_comp u.left v.left) x

/-- A morphism of pairs is compatible with the augmentations. -/
private theorem Pairs.aug_map {A B : Pairs R} (u : A ⟶ B) (x : (A.left.obj : Type u)) :
    B.hom.hom (Pairs.map R u x) = A.hom.hom x :=
  ConcreteCategory.congr_hom (CostructuredArrow.w u) x

/-- The pair given by an étale `R`-algebra `S` and an augmentation `S → κ`. -/
private noncomputable abbrev Pairs.ofAug {S : Type u} [CommRing S] [Algebra R S]
    (hS : Algebra.Etale R S) (α : S →ₐ[R] ResidueField R) : Pairs R :=
  CostructuredArrow.mk (Y := ⟨CommAlgCat.of R S, hS⟩) (CommAlgCat.ofHom α)

/-- A morphism of pairs from an algebra map compatible with the augmentations. -/
private noncomputable abbrev Pairs.homOfAlgHom {A B : Pairs R}
    (φ : (A.left.obj : Type u) →ₐ[R] (B.left.obj : Type u)) (h : B.hom.hom.comp φ = A.hom.hom) :
    A ⟶ B :=
  CostructuredArrow.homMk (ObjectProperty.homMk (CommAlgCat.ofHom φ)) (CommAlgCat.hom_ext h)

/-- **Localizing a pair.** If the augmentation of `g` is nonzero in the pair `A`, then `A` has a
morphism to the pair `(S[1/g], α)`: the localization is again étale over `R`, and the augmentation
extends to it because it sends `g` to a unit. In the new pair `g` becomes invertible. -/
private theorem Pairs.exists_away (A : Pairs R) (g : (A.left.obj : Type u))
    (hg : A.hom.hom g ≠ 0) :
    ∃ (C : Pairs R) (h : A ⟶ C), IsUnit (Pairs.map R h g) := by
  have hEt' : Algebra.Etale R (Localization.Away g) :=
    Algebra.Etale.comp R (A.left.obj : Type u) (Localization.Away g)
  have hunits : ∀ y : Submonoid.powers g, IsUnit (A.hom.hom (y : (A.left.obj : Type u))) := by
    intro y
    obtain ⟨n, hn⟩ := y.2
    simp only [← hn, map_pow]
    exact (isUnit_iff_ne_zero.2 hg).pow n
  obtain ⟨aug, haug⟩ : ∃ aug : Localization.Away g →ₐ[R] ResidueField R,
      ∀ x : (A.left.obj : Type u),
        aug (algebraMap (A.left.obj : Type u) (Localization.Away g) x) = A.hom.hom x :=
    ⟨IsLocalization.liftAlgHom (M := Submonoid.powers g) (S := Localization.Away g)
      (f := A.hom.hom) hunits, fun x => IsLocalization.lift_eq hunits x⟩
  refine ⟨Pairs.ofAug R hEt' aug, Pairs.homOfAlgHom R
    (IsScalarTower.toAlgHom R (A.left.obj : Type u) (Localization.Away g))
    (AlgHom.ext haug), ?_⟩
  show IsUnit ((IsScalarTower.toAlgHom R (A.left.obj : Type u) (Localization.Away g)) g)
  exact IsLocalization.map_units (M := Submonoid.powers g) (Localization.Away g)
    ⟨g, Submonoid.mem_powers g⟩

/-- Part (2) of filteredness: any two pairs map to a common pair, namely their tensor product
over `R` augmented by the product of the two augmentations. -/
private theorem Pairs.cocone_objs (A B : Pairs R) :
    ∃ (C : Pairs R) (_ : A ⟶ C) (_ : B ⟶ C), True := by
  have hT : Algebra.Etale R (TensorProduct R (A.left.obj : Type u) (B.left.obj : Type u)) :=
    Algebra.Etale.comp R (A.left.obj : Type u)
      (TensorProduct R (A.left.obj : Type u) (B.left.obj : Type u))
  refine ⟨Pairs.ofAug R hT (Algebra.TensorProduct.lift A.hom.hom B.hom.hom
        fun _ _ ↦ Commute.all _ _),
    Pairs.homOfAlgHom R (Algebra.TensorProduct.includeLeft (R := R) (S := R)) ?_,
    Pairs.homOfAlgHom R (Algebra.TensorProduct.includeRight (R := R)) ?_, trivial⟩
  all_goals ext x; simp

/-- Part (3) of filteredness: any two parallel morphisms of pairs are equalized after a further
morphism.

Both morphisms `φ, ψ : S → S'` assemble into `θ : S ⊗[R] S → S'`. Because `S` is étale over `R`,
hence unramified and essentially of finite type, `S ⊗[R] S` carries Mathlib's element
`Algebra.FormallyUnramified.elem R S`, which multiplies the two inclusions of `S` together
(`one_tmul_mul_elem`) and is sent to `1` by the multiplication map (`lmul_elem`). Its image
`ε = θ e` therefore satisfies `φ s * ε = ψ s * ε` for every `s`, while the augmentation of `S'`
sends `ε` to `1`, because `α' ∘ θ` and `α ∘ lmul'` agree on tensors. Localizing `S'` away from `ε`
is thus a morphism of pairs after which `φ` and `ψ` coincide. -/
private theorem Pairs.cocone_maps {A B : Pairs R} (f g : A ⟶ B) :
    ∃ (C : Pairs R) (h : B ⟶ C), f ≫ h = g ≫ h := by
  set θ := Algebra.TensorProduct.lift (Pairs.map R f) (Pairs.map R g)
    (fun _ _ => Commute.all _ _) with hθ
  set e := Algebra.FormallyUnramified.elem R (A.left.obj : Type u) with he
  have hcomm : B.hom.hom.comp θ = A.hom.hom.comp (Algebra.TensorProduct.lmul' R) := by
    refine Algebra.TensorProduct.ext' fun x y => ?_
    simp only [AlgHom.coe_comp, Function.comp_apply, hθ, Algebra.TensorProduct.lift_tmul,
      Algebra.TensorProduct.lmul'_apply_tmul, map_mul, Pairs.aug_map R f x, Pairs.aug_map R g y]
  have haug : B.hom.hom (θ e) = 1 := by
    simpa [he, Algebra.FormallyUnramified.lmul_elem] using DFunLike.congr_fun hcomm e
  obtain ⟨C, h, hu⟩ := Pairs.exists_away R B (θ e) (by simp [haug])
  refine ⟨C, h, Pairs.hom_ext R _ _ (AlgHom.ext fun x => ?_)⟩
  have key : Pairs.map R f x * θ e = Pairs.map R g x * θ e := by
    simpa [hθ, he, Algebra.TensorProduct.lift_tmul] using (congrArg θ
      (Algebra.FormallyUnramified.one_tmul_mul_elem (R := R) (S := (A.left.obj : Type u)) x)).symm
  rw [Pairs.map_comp, Pairs.map_comp]
  refine hu.mul_right_cancel ?_
  rw [← map_mul, ← map_mul, key]

/-- The category of pairs is filtered. -/
@[sga "4 VIII 4.1" "partial"]
private theorem isFiltered_pairs : IsFiltered (Pairs R) :=
  have : IsFilteredOrEmpty (Pairs R) :=
    { cocone_objs := fun A B ↦ Pairs.cocone_objs R A B
      cocone_maps := fun {_ _} f g ↦ Pairs.cocone_maps R f g }
  { nonempty := ⟨Pairs.unit R⟩ }

attribute [local instance] isFiltered_pairs

/-! ### The colimit -/

/-- A `u`-small model of the category of pairs. -/
private abbrev Index : Type u := SmallModel (Pairs R)

/-- The diagram of étale `R`-algebras indexed by the small model of the category of pairs. -/
private noncomputable def diagram : Index R ⥤ CommAlgCat.{u} R :=
  (equivSmallModel (Pairs R)).inverse ⋙
    CostructuredArrow.proj (CommAlgCat.etale.{u} R).ι (CommAlgCat.of R (ResidueField R)) ⋙
      (CommAlgCat.etale.{u} R).ι

/-- The **henselization** of `R`: the colimit of the diagram of pairs. -/
private noncomputable abbrev henselization : CommAlgCat.{u} R := colimit (diagram R)

/-- Item (2): the henselization is a filtered colimit of étale `R`-algebras. -/
@[sga "4 VIII 4.1" "partial"]
private theorem ind_henselization :
    (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R (henselization R : Type u)) :=
  ⟨Index R, inferInstance, IsFiltered.of_equivalence (equivSmallModel (Pairs R)),
    { diag := diagram R
      ι := (colimit.cocone (diagram R)).ι
      isColimit := colimit.isColimit _ },
    fun i ↦ Pairs.etale R ((equivSmallModel (Pairs R)).inverse.obj i)⟩

/-! ### Elements of the henselization -/

/-- The functor `(S, α) ↦ S` from pairs to `R`-algebras. -/
private abbrev pairsFunctor : Pairs R ⥤ CommAlgCat.{u} R :=
  CostructuredArrow.proj (CommAlgCat.etale.{u} R).ι (CommAlgCat.of R (ResidueField R)) ⋙
    (CommAlgCat.etale.{u} R).ι

/-- Reindexing the diagram along the equivalence with the small model identifies `pairsFunctor`
with the diagram, up to the unit of the equivalence. -/
private noncomputable def pairsIsoDiagram :
    pairsFunctor R ≅ (equivSmallModel (Pairs R)).functor ⋙ diagram R :=
  (Functor.leftUnitor (pairsFunctor R)).symm ≪≫
    Functor.isoWhiskerRight (equivSmallModel (Pairs R)).unitIso (pairsFunctor R) ≪≫
      Functor.associator _ _ _

/-- The colimit cocone of the henselization, indexed by the category of pairs itself rather than
by its small model. -/
private noncomputable def pairsCocone : Cocone (pairsFunctor R) :=
  (Cocone.precompose (pairsIsoDiagram R).hom).obj
    (Cocone.whisker (equivSmallModel (Pairs R)).functor (colimit.cocone (diagram R)))

/-- The cocone over the category of pairs is a colimit cocone. -/
private noncomputable def pairsCoconeIsColimit : IsColimit (pairsCocone R) :=
  (IsColimit.precomposeHomEquiv (pairsIsoDiagram R) _).symm
    (IsColimit.whiskerEquivalence (colimit.isColimit (diagram R)) (equivSmallModel (Pairs R)))

/-- The `R`-algebra map from a pair into `R^h`, i.e. the structure map of the colimit cocone. -/
private noncomputable abbrev stageHom (A : Pairs R) :
    (A.left.obj : Type u) →ₐ[R] (henselization R : Type u) := ((pairsCocone R).ι.app A).hom

/-- A morphism of pairs does not change the element of `R^h` that a point of a pair determines. -/
private theorem stageHom_map {A B : Pairs R} (u : A ⟶ B) (y : (A.left.obj : Type u)) :
    stageHom R B (Pairs.map R u y) = stageHom R A y :=
  ConcreteCategory.congr_hom ((pairsCocone R).w u) y

/-- Every element of `R^h` comes from a pair. -/
private theorem exists_stage (x : (henselization R : Type u)) :
    ∃ (A : Pairs R) (y : (A.left.obj : Type u)), stageHom R A y = x :=
  CommAlgCat.exists_app_eq (pairsCoconeIsColimit R) x

/-- The cocone of augmentations: every pair comes with an `R`-algebra map to `κ`, compatibly with
morphisms of pairs. -/
private noncomputable def augPairsCocone : Cocone (pairsFunctor R) where
  pt := CommAlgCat.of R (ResidueField R)
  ι := { app := fun A => A.hom
         naturality := fun A B u => by
           change u.left.hom ≫ B.hom = A.hom ≫ 𝟙 _
           rw [Category.comp_id]
           exact CostructuredArrow.w u }

/-- The **augmentation** `R^h → κ`, induced by the augmentations of the pairs. -/
private noncomputable def aug : (henselization R : Type u) →ₐ[R] ResidueField R :=
  ((pairsCoconeIsColimit R).desc (augPairsCocone R)).hom

/-- The augmentation of `R^h` restricts on each stage to the augmentation of that pair. -/
private theorem aug_stageHom (A : Pairs R) (y : (A.left.obj : Type u)) :
    aug R (stageHom R A y) = A.hom.hom y :=
  ConcreteCategory.congr_hom ((pairsCoconeIsColimit R).fac (augPairsCocone R) A) y

/-- The augmentation composed with `R → R^h` is the residue map of `R`. -/
private theorem aug_algebraMap (r : R) :
    aug R (algebraMap R (henselization R : Type u) r) = residue R r := by
  rw [AlgHom.commutes, ResidueField.algebraMap_eq]

/-- **An element of `R^h` is a unit exactly when its augmentation is nonzero.** If `aug x ≠ 0`
then `x` comes from a triple `(S, α, f)` with `α f ≠ 0`, and `f` becomes invertible in the
localization `S[1/f]`, which is again a pair. -/
private theorem isUnit_iff_aug_ne_zero (x : (henselization R : Type u)) :
    IsUnit x ↔ aug R x ≠ 0 := by
  refine ⟨fun hx => (hx.map (aug R)).ne_zero, fun hx => ?_⟩
  obtain ⟨A, y, rfl⟩ := exists_stage R x
  rw [aug_stageHom] at hx
  obtain ⟨C, h, hu⟩ := Pairs.exists_away R A y hx
  rw [← stageHom_map R h y]
  exact hu.map (stageHom R C)

/-- `R^h` is nontrivial, since it surjects onto the field `κ`. -/
private theorem nontrivial_henselization : Nontrivial (henselization R : Type u) :=
  (aug R).toRingHom.domain_nontrivial

attribute [local instance] nontrivial_henselization

/-! ### The henselization is local with maximal ideal `𝔪 R^h` and residue field `κ` -/

/-- The henselization is a local ring: a triple `(S, 𝔮, f)` with `𝔪 S = 𝔮` and `f ∉ 𝔮` becomes
invertible in the pair `(S_f, 𝔮 S_f)`. -/
private theorem isLocalRing_henselization : IsLocalRing (henselization R : Type u) := by
  refine IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add fun a b hab => ?_
  rw [isUnit_iff_aug_ne_zero, map_add] at hab
  rw [isUnit_iff_aug_ne_zero, isUnit_iff_aug_ne_zero]
  contrapose! hab
  rw [hab.1, hab.2, add_zero]

attribute [local instance] isLocalRing_henselization

/-- The structural map `R → R^h` is local. -/
private theorem isLocalHom_algebraMap_henselization :
    IsLocalHom (algebraMap R (henselization R : Type u)) := by
  refine ⟨fun r hr => ?_⟩
  rw [isUnit_iff_aug_ne_zero, aug_algebraMap] at hr
  by_contra hnu
  exact hr ((residue_eq_zero_iff r).2 ((mem_maximalIdeal r).2 (mem_nonunits_iff.2 hnu)))

/-- The maximal ideal of `R^h` is the kernel of the augmentation. -/
private theorem mem_maximalIdeal_iff_aug_eq_zero (x : (henselization R : Type u)) :
    x ∈ maximalIdeal (henselization R : Type u) ↔ aug R x = 0 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_aug_ne_zero, not_not]

attribute [local instance] isLocalHom_algebraMap_henselization

/-! ### Item (3): the maximal ideal is generated by `𝔪` -/

/-- **The content of Stacks 00U4 for a pair.** Let `S` be an étale `R`-algebra and `𝔮` a prime of
`S` lying over `𝔪`. Then `𝔪 S_𝔮 = 𝔮 S_𝔮`, so an element of `𝔮` becomes a member of `𝔪 S` after
multiplication by some `g ∉ 𝔮`.

The equality `𝔪 S_𝔮 = maximalIdeal S_𝔮` is item (1) of Stacks 00U4; only unramifiedness of
`R → S` is used, as the formalized statement of that tag records, and in that form the equality is
Mathlib's `Algebra.FormallyUnramified.map_maximalIdeal`, applied to the local `R`-algebra `S_𝔮`.
Clearing the denominator is the source's step "we may assume `𝔪 S = 𝔮`", carried out after
localizing at a single element instead of at the whole prime. -/
private theorem exists_mul_mem_map_maximalIdeal {S : Type u} [CommRing S] [Algebra R S]
    [Algebra.Etale R S] {q : Ideal S} [q.IsPrime]
    (hover : maximalIdeal R = q.comap (algebraMap R S)) {y : S} (hy : y ∈ q) :
    ∃ g ∉ q, g * y ∈ (maximalIdeal R).map (algebraMap R S) := by
  have : q.LiesOver (maximalIdeal R) := ⟨hover⟩
  have : IsLocalHom (algebraMap R (Localization.AtPrime q)) := by
    refine ⟨fun r hr => ?_⟩
    by_contra hnu
    have h0 : r ∈ maximalIdeal R := (mem_maximalIdeal r).2 (mem_nonunits_iff.2 hnu)
    rw [hover, Ideal.mem_comap] at h0
    have h2 : algebraMap S (Localization.AtPrime q) (algebraMap R S r) ∈
        maximalIdeal (Localization.AtPrime q) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff _ q _).2 h0
    rw [← IsScalarTower.algebraMap_apply] at h2
    exact (mem_maximalIdeal _).1 h2 hr
  have h1 : (maximalIdeal R).map (algebraMap R (Localization.AtPrime q)) =
      maximalIdeal (Localization.AtPrime q) := Algebra.FormallyUnramified.map_maximalIdeal
  have h2 : algebraMap S (Localization.AtPrime q) y ∈ maximalIdeal (Localization.AtPrime q) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ q y).2 hy
  rw [← h1, IsScalarTower.algebraMap_eq R S (Localization.AtPrime q), ← Ideal.map_map] at h2
  exact (IsLocalization.algebraMap_mem_map_algebraMap_iff (M := q.primeCompl)
    (S := Localization.AtPrime q) _ _).1 h2

/-- **Item (3), one pair at a time.** If the augmentation of a pair kills `y`, then after one
morphism of pairs `y` lies in the ideal generated by `𝔪`: multiply by the `g ∉ 𝔮` of
`exists_mul_mem_map_maximalIdeal` and localize away from `g`. -/
private theorem Pairs.exists_mem_map_maximalIdeal (A : Pairs R) (y : (A.left.obj : Type u))
    (hy : A.hom.hom y = 0) :
    ∃ (C : Pairs R) (u : A ⟶ C),
      Pairs.map R u y ∈ (maximalIdeal R).map (algebraMap R (C.left.obj : Type u)) := by
  have hq : (RingHom.ker A.hom.hom : Ideal (A.left.obj : Type u)).IsPrime :=
    RingHom.ker_isPrime _
  have hover : maximalIdeal R =
      (RingHom.ker A.hom.hom : Ideal (A.left.obj : Type u)).comap
        (algebraMap R (A.left.obj : Type u)) := by
    ext r
    have h : A.hom.hom (algebraMap R (A.left.obj : Type u) r) = residue R r :=
      A.hom.hom.commutes r
    rw [Ideal.mem_comap, RingHom.mem_ker, h, residue_eq_zero_iff]
  obtain ⟨g, hg, hgy⟩ :=
    exists_mul_mem_map_maximalIdeal R hover (y := y) (RingHom.mem_ker.2 hy)
  obtain ⟨C, u, hu⟩ := Pairs.exists_away R A g fun h => hg (RingHom.mem_ker.2 h)
  refine ⟨C, u, (Ideal.unit_mul_mem_iff_mem _ hu).1 ?_⟩
  rw [← map_mul]
  exact mem_map_of_algHom R (Pairs.map R u) hgy

/-! ### Points and polynomials living on a single pair -/

/-- Since the category of pairs is filtered, any finite set of elements of `R^h` is in the image
of a single pair. -/
private theorem exists_stage_finset (s : Finset (henselization R : Type u)) :
    ∃ A : Pairs R, ∀ x ∈ s, ∃ y : (A.left.obj : Type u), stageHom R A y = x :=
  exists_app_eq_finset R (pairsCocone R) (pairsCoconeIsColimit R) s

/-- A monic polynomial over `R^h` and an element of `R^h` come from a single pair: the
polynomial from a monic polynomial of the same degree, by
`Polynomial.lifts_and_degree_eq_and_monic` applied to the finitely many coefficients. -/
private theorem exists_stage_polynomial (p : Polynomial (henselization R : Type u))
    (hp : p.Monic) (a₀ : (henselization R : Type u)) :
    ∃ (A : Pairs R) (Q : Polynomial (A.left.obj : Type u)) (b : (A.left.obj : Type u)),
      Q.Monic ∧ Q.map (stageHom R A).toRingHom = p ∧ stageHom R A b = a₀ := by
  classical
  obtain ⟨A, hA⟩ := exists_stage_finset R (insert a₀ (p.support.image p.coeff))
  obtain ⟨b, hb⟩ := hA a₀ (Finset.mem_insert_self _ _)
  have hlifts : p ∈ Polynomial.lifts (stageHom R A).toRingHom := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases hn : n ∈ p.support
    · obtain ⟨y, hy⟩ := hA (p.coeff n) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hn))
      exact ⟨y, hy⟩
    · rw [Polynomial.notMem_support_iff.1 hn]
      exact ⟨0, map_zero _⟩
  obtain ⟨Q, hQ1, -, hQ3⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts hp
  exact ⟨A, Q, b, hQ3, hQ1, hb⟩

/-- A polynomial over a pair has the same image in `R^h[T]` as its image over any later pair. -/
private theorem stageHom_map_polynomial {A C : Pairs R} (u : A ⟶ C)
    (Q : Polynomial (A.left.obj : Type u)) :
    (Q.map (Pairs.map R u).toRingHom).map (stageHom R C).toRingHom
      = Q.map (stageHom R A).toRingHom := by
  have h : (stageHom R C).toRingHom.comp (Pairs.map R u).toRingHom = (stageHom R A).toRingHom :=
    RingHom.ext fun y => stageHom_map R u y
  rw [Polynomial.map_map, h]

/-- The augmentation of `R^h` reads the value of a polynomial lifted from a pair, at a point
lifted from that pair, off the pair itself. -/
private theorem aug_eval_map (A : Pairs R) (Q : Polynomial (A.left.obj : Type u))
    (b : (A.left.obj : Type u)) :
    aug R ((Q.map (stageHom R A).toRingHom).eval (stageHom R A b)) = A.hom.hom (Q.eval b) := by
  rw [eval_map_toRingHom, aug_stageHom]

/-! ### Item (1): adjoining a root -/

/-- **Adjoining a root to a pair.** Let `(S, α)` be a pair, `Q ∈ S[T]` monic and `b ∈ S` a point
with `α(Q(b)) = 0` and `α(Q'(b)) ≠ 0`. The standard étale `S`-algebra `S[T]/(Q)[1/Q']` — Mathlib's
`StandardEtalePair.Ring` for the pair `(Q, Q')` — is then étale over `R`, carries an augmentation
extending `α` sending the class of `T` to `α b`, and in it `Q` has the root `T`.

This is the source's `S' = S[T]/(Q)` with the maximal ideal `𝔮' = 𝔮S' + (T - a')S'`, localized at
the `g ∉ 𝔮'` that makes `S → S'_g` étale; the localization is at `Q'`, so no choice of `g` has to
be made. -/
private theorem Pairs.exists_root (A : Pairs R) (Q : Polynomial (A.left.obj : Type u))
    (hQ : Q.Monic) (b : (A.left.obj : Type u)) (h0 : A.hom.hom (Q.eval b) = 0)
    (h1 : A.hom.hom ((Polynomial.derivative Q).eval b) ≠ 0) :
    ∃ (C : Pairs R) (u : A ⟶ C) (t : (C.left.obj : Type u)),
      (Q.map (Pairs.map R u).toRingHom).eval t = 0 ∧ C.hom.hom t = A.hom.hom b := by
  let _ : Algebra (A.left.obj : Type u)
      ((CommAlgCat.of R (ResidueField R) : CommAlgCat.{u} R) : Type u) :=
    A.hom.hom.toRingHom.toAlgebra
  have : IsScalarTower R (A.left.obj : Type u)
      ((CommAlgCat.of R (ResidueField R) : CommAlgCat.{u} R) : Type u) :=
    IsScalarTower.of_algebraMap_eq fun r => (A.hom.hom.commutes r).symm
  obtain ⟨P, hPf, hPg⟩ : ∃ P : StandardEtalePair (A.left.obj : Type u),
      P.f = Q ∧ P.g = Polynomial.derivative Q :=
    ⟨⟨Q, hQ, Polynomial.derivative Q, ⟨Polynomial.derivative Q, 0, 2, by ring⟩⟩, rfl, rfl⟩
  have haeval : ∀ T : Polynomial (A.left.obj : Type u),
      Polynomial.aeval (A.hom.hom b) T = A.hom.hom (T.eval b) :=
    fun T => Polynomial.eval₂_at_apply A.hom.hom.toRingHom b
  have hmap : P.HasMap (A.hom.hom b) := by
    refine ⟨by rwa [hPf, haeval], ?_⟩
    rw [hPg, haeval]
    exact isUnit_iff_ne_zero.2 h1
  let _ : Algebra R P.Ring :=
    ((algebraMap (A.left.obj : Type u) P.Ring).comp
      (algebraMap R (A.left.obj : Type u))).toAlgebra
  have : IsScalarTower R (A.left.obj : Type u) P.Ring := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.Etale R P.Ring := Algebra.Etale.comp R (A.left.obj : Type u) P.Ring
  refine ⟨Pairs.ofAug R inferInstance ((P.lift (A.hom.hom b) hmap).restrictScalars R),
    Pairs.homOfAlgHom R (IsScalarTower.toAlgHom R (A.left.obj : Type u) P.Ring)
      (AlgHom.ext fun s => ?_), P.X, ?_, ?_⟩
  · exact (P.lift (A.hom.hom b) hmap).commutes s
  · show (Q.map (algebraMap (A.left.obj : Type u) P.Ring)).eval P.X = 0
    rw [Polynomial.eval_map, ← Polynomial.aeval_def, ← hPf]
    exact P.hasMap_X.1
  · exact P.lift_X _ hmap

/-- Item (3): `𝔪 R^h` is the maximal ideal of `R^h`. The maximal ideal is the kernel of the
augmentation, and an element of `R^h` killed by the augmentation is killed by the augmentation of
a pair it comes from, hence lies in `𝔪` times that pair. -/
private theorem map_maximalIdeal_henselization :
    (maximalIdeal R).map (algebraMap R (henselization R : Type u)) =
      maximalIdeal (henselization R : Type u) := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.2 fun r hr => ?_) fun x hx => ?_
  · rwa [Ideal.mem_comap, mem_maximalIdeal_iff_aug_eq_zero, aug_algebraMap, residue_eq_zero_iff]
  · rw [mem_maximalIdeal_iff_aug_eq_zero] at hx
    obtain ⟨A, y, rfl⟩ := exists_stage R x
    rw [aug_stageHom] at hx
    obtain ⟨C, u, hmem⟩ := Pairs.exists_mem_map_maximalIdeal R A y hx
    rw [← stageHom_map R u y]
    exact mem_map_of_algHom R (stageHom R C) hmem

/-- Item (4): the residue field of `R^h` is `κ`. The map is injective because it is a ring map
between fields, and surjective because the residue class of `x` is that of any `r : R` with
`residue r = aug x`. -/
private theorem bijective_residueField_map_henselization :
    Function.Bijective (ResidueField.map (algebraMap R (henselization R : Type u))) := by
  refine ⟨(ResidueField.map (algebraMap R (henselization R : Type u))).injective, fun z => ?_⟩
  obtain ⟨x, rfl⟩ := residue_surjective z
  obtain ⟨r, hr⟩ := residue_surjective (aug R x)
  refine ⟨residue R r, ?_⟩
  rw [ResidueField.map_residue, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff,
    mem_maximalIdeal_iff_aug_eq_zero, map_sub, aug_algebraMap, hr, sub_self]

/-- Item (1): the henselization is henselian. A monic `P ∈ R^h[T]` and a point `a₀` come from a
single pair `(S, α)`, as a monic `Q ∈ S[T]` and a point `b`; the hypotheses say that `α(Q(b)) = 0`
and `α(Q'(b)) ≠ 0`, so `Pairs.exists_root` produces a pair in which `Q` has a root with the same
augmentation as `b`, and its image in `R^h` is the required root of `P`. -/
private theorem henselianLocalRing_henselization :
    HenselianLocalRing (henselization R : Type u) := by
  refine { is_henselian := fun p hp a₀ hpa₀ hunit => ?_ }
  obtain ⟨A, Q, b, hQ, hQmap, rfl⟩ := exists_stage_polynomial R p hp a₀
  have h0 : A.hom.hom (Q.eval b) = 0 := by
    rw [← aug_eval_map, hQmap]
    exact (mem_maximalIdeal_iff_aug_eq_zero R _).1 hpa₀
  have h1 : A.hom.hom ((Polynomial.derivative Q).eval b) ≠ 0 := by
    rw [← aug_eval_map, ← Polynomial.derivative_map, hQmap]
    exact (isUnit_iff_aug_ne_zero R _).1 hunit
  obtain ⟨C, u, t, ht0, htb⟩ := Pairs.exists_root R A Q hQ b h0 h1
  refine ⟨stageHom R C t, ?_, ?_⟩
  · show Polynomial.eval (stageHom R C t) p = 0
    rw [← hQmap, ← stageHom_map_polynomial R u Q, eval_map_toRingHom, ht0, map_zero]
  · rw [mem_maximalIdeal_iff_aug_eq_zero, map_sub, aug_stageHom, aug_stageHom, htb, sub_self]

end

open scoped Classical in
public theorem solution (R : Type u) [CommRing R] [IsLocalRing R] :
    ∃ (Rh : Type u) (_ : CommRing Rh) (_ : Algebra R Rh) (_ : IsLocalRing Rh)
      (_ : IsLocalHom (algebraMap R Rh)),
      HenselianLocalRing Rh ∧
      (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R Rh) ∧
      (maximalIdeal R).map (algebraMap R Rh) = maximalIdeal Rh ∧
      Function.Bijective (ResidueField.map (algebraMap R Rh)) :=
  ⟨(henselization R : Type u), inferInstance, inferInstance,
    isLocalRing_henselization R, isLocalHom_algebraMap_henselization R,
    henselianLocalRing_henselization R, ind_henselization R,
    map_maximalIdeal_henselization R, bijective_residueField_map_henselization R⟩

end Stacks.Henselization.EtaleColimit

/-!
# Existence of the henselization of a local ring

Let `(R, 𝔪, κ)` be a local ring. There is a local `R`-algebra `Rh` which is henselian, is a
filtered colimit of étale `R`-algebras, has `𝔪 Rh` for its maximal ideal, and has `κ` for its
residue field. Together with the uniqueness statement 08HT these four properties pin `Rh` down
up to a unique isomorphism over `R`, and the local ring map `R → Rh` is then called the
henselization of `R` (Definition 04GQ).

The construction, which is no part of the statement, takes `Rh` to be the colimit of the filtered
category of pairs `(S, 𝔮)` with `R → S` étale and `𝔮` a prime of `S` over `𝔪` with `κ(𝔮) = κ`.

## Main results

* `IsLocalRing.exists_henselization`: a local ring `R` admits a local `R`-algebra which is
  henselian, ind-étale over `R`, has maximal ideal `𝔪 Rh` and has residue field `κ`.

## Implementation notes

*A filtered colimit of étale `R`-algebras is an ind-étale `R`-algebra.* Item (2) is
`(CommAlgCat.etale R).ind (CommAlgCat.of R Rh)`: Mathlib's
`CategoryTheory.ObjectProperty.ind P X` says exactly that `X` is the colimit of a filtered
diagram all of whose values satisfy `P`, and `CommAlgCat.etale R` is the object property of
étale `R`-algebras. The colimit is taken in `CommAlgCat R`, so the diagram, the cocone and the
colimit are all over `R` and the map `R → Rh` is the one the presentation induces; since filtered
colimits of `R`-algebras are computed on underlying rings, this is neither weaker nor stronger
than the source's condition. The index category is taken in the same universe as `R`, which is no
restriction: étale algebras are of finite presentation, so the category of pairs used in the
construction is essentially small there.

*The local ring map is the algebra map.* The source's `R → Rh` is `algebraMap R Rh`, and being
local is `IsLocalHom`; this is what makes items (3) and (4) statements about a canonical map
rather than about some map or other. The `IsLocalRing Rh` and `IsLocalHom` binders are the
lemma's preamble ("there exists a local ring map"), the four conjuncts its items (1)–(4).

*Items (3) and (4).* `𝔪 Rh` is `(maximalIdeal R).map (algebraMap R Rh)`, the ideal of `Rh`
generated by the image of `𝔪`, and (4) is bijectivity of the canonical residue field map
`IsLocalRing.ResidueField.map (algebraMap R Rh) : κ → Rh ⧸ maximalIdeal Rh`. Given (3) the
target is `Rh/𝔪 Rh`, so (3) and (4) together are the source's (3) and (4). Injectivity of a ring
map between fields is automatic, so asking for bijectivity rather than surjectivity costs nothing
and is the more usable form.

Faithfulness to [StacksProject 04GN], point by point. (1) No hypothesis is dead: `R` local is
used by all four conjuncts, through `maximalIdeal R` and its residue field, and there is nothing
else to be dead. (2) The scalars and the base are the source's: `Rh` is an `R`-algebra, the
colimit is one of `R`-algebras, `𝔪 Rh` is the ideal generated by the image of the maximal ideal of
`R` itself, and the residue field map is the one induced by `R → Rh`, not by a localization or a
quotient of `R`. (3) The canonical maps are pinned: the ring map is `algebraMap R Rh`, item (3)
speaks of `Ideal.map` along it, and item (4) of `IsLocalRing.ResidueField.map` along it, so no
conjunct is satisfiable by an unrelated isomorphism of `κ` with the residue field of `Rh`. (4) The
instantiation is not degenerate: a henselian local ring is its own henselization, so for a field
`K`, or for `ℤ_[p]`, all four items hold with `Rh = R` (`R` is étale over `R`, hence ind-étale by
`CategoryTheory.ObjectProperty.le_ind`), while for `R = ℤ` localized at `p` the ring `Rh` is a
proper subring of `ℤ_[p]` and the statement has content.

## References

* [StacksProject 04GN](https://stacks.math.columbia.edu/tag/04GN)
* [StacksProject 04GQ](https://stacks.math.columbia.edu/tag/04GQ), the henselization `R → R^h`
* [StacksProject 08HT](https://stacks.math.columbia.edu/tag/08HT), uniqueness of `R^h`

## Tags

henselization, henselian local ring, ind-étale, étale algebra, filtered colimit, residue field
-/



@[expose] public section

open IsLocalRing in
/-- **Existence of the henselization of a local ring** (Stacks 04GN). For a local ring
`(R, 𝔪, κ)` there is a local ring map `R → Rh` such that (1) `Rh` is henselian, (2) `Rh` is a
filtered colimit of étale `R`-algebras, (3) `𝔪 Rh` is the maximal ideal of `Rh`, and (4) the
residue field of `Rh` is `κ`. -/
@[stacks 04GN "The lemma's preamble, a local ring map `R → Rh`, is the `Algebra R Rh`,
`IsLocalRing Rh` and `IsLocalHom (algebraMap R Rh)` binders; the four conjuncts are its items
(1)–(4). `Rh` being a filtered colimit of étale `R`-algebras is `(CommAlgCat.etale R).ind`, i.e.
`Rh` is ind-étale over `R`; `𝔪 Rh` is `Ideal.map`; and `κ = Rh/𝔪 Rh` is bijectivity of the
canonical `IsLocalRing.ResidueField.map`. See the module docstring.", sga "4 VIII 4.1"
  "henselization", ega "IV 18.6.6" "(i), part of (iii)", sga "4 VIII 4.1" "henselization"]
public theorem IsLocalRing.exists_henselization (R : Type u) [CommRing R] [IsLocalRing R] :
    ∃ (Rh : Type u) (_ : CommRing Rh) (_ : Algebra R Rh) (_ : IsLocalRing Rh)
      (_ : IsLocalHom (algebraMap R Rh)),
      HenselianLocalRing Rh ∧
      (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R Rh) ∧
      (maximalIdeal R).map (algebraMap R Rh) = maximalIdeal Rh ∧
      Function.Bijective (ResidueField.map (algebraMap R Rh)) :=
  Stacks.Henselization.EtaleColimit.solution R

end
