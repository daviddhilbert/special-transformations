module

public import Mathlib.Algebra.Lie.OfAssociative
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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Unramified.LocalStructure
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
public import Mathlib.Topology.Sheaves.Init
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.RingTheory.Etale.ModuloPowers
public import StacksFrontier.RingTheory.Henselian.EtaleLifting

/-!
# The universal property of the henselization
-/

@[expose] public section

universe u v w

/-!
# The universal property of the henselization

Let `(R, 𝔪, κ)` be a local ring, let `Rh` be a local `R`-algebra with `R → Rh` local which is a
filtered colimit of étale `R`-algebras and whose residue field is `κ`, and let `Sh` be a henselian
local ring with `R → Sh` local. Then there is exactly one `R`-algebra map `Rh → Sh` which is a
local ring map. Applied to the henselizations of a local map of local rings `R → S`, with
`Rh = R^h` and `Sh = S^h` over `R → S → S^h`, this is Stacks 04GS: the unique local ring map
`R^h → S^h` fitting into the commutative square.

The proof is the source's, namely that this follows from Lemma 08HR
(`Stacks.Henselian.EtaleLifting.algHom`). That lemma lifts a *residue datum* along an ind-étale
`R`-algebra `A`: given a prime `q ⊆ A` over `p = R ∩ 𝔪 Sh` and a `κ(p)`-algebra map
`τ : κ(q) → κ(Sh)`, there is exactly one `R`-algebra map `f : A → Sh` with `q = f⁻¹(𝔪 Sh)` which
induces `τ` on residue fields. Here the datum is not a choice but is forced by the hypotheses, at
both of its two places:

* `q = 𝔪 Rh`, whose contraction to `R` is `𝔪` because `R → Rh` is local, and which is therefore
  the unique prime of `Rh` that a local map can pull `𝔪 Sh` back to;
* `τ` is the composite `κ(𝔪 Rh) ≅ κ → κ(Sh)`, the first map being the inverse of `κ → κ(𝔪 Rh)`,
  which is bijective by `bijective_residueFieldMapFib` — surjective by hypothesis and injective as
  a map of fields.

With the datum pinned this way, 08HR's two conditions on `f` are together equivalent to the single
assertion that `f` is a local ring map, which is what turns 08HR's conclusion into this one. In one
direction `q = f⁻¹(𝔪 Sh)` for `q = 𝔪 Rh` *is* locality, which is
`isLocalHom_iff_maximalIdeal_eq_comap`. In the other, a local `f` induces `τ` automatically rather
than by assumption, which is `inducesResidueMap_of_le_comap`: `τ ∘ (Rh → κ(𝔪 Rh))` and
`residue Sh ∘ f` both kill `𝔪 Rh` and agree on the image of `R`, and every element of `Rh` is
congruent mod `𝔪 Rh` to one coming from `R`. So no residue datum has to be supplied, and none is:
that is the sense in which 04GS is the case of 08HR where the residue field extension is trivial.

## Main results

* `Stacks.Henselian.HenselizationUnique.map`,
  `Stacks.Henselian.HenselizationUnique.isLocalHom_map`,
  `Stacks.Henselian.HenselizationUnique.map_unique`: the map of `HenselianLocalRing.indEtaleAlgHom`
  (Stacks 04GS), its locality and its uniqueness.

## Implementation notes

The surjectivity hypothesis is used only through the consequence that every element of `Rh` is
congruent mod `𝔪 Rh` to one coming from `R`
(`Stacks.Etale.PrincipalPowerIso.exists_sub_mem_maximalIdeal_of_surjective_residueFieldMap`),
and it is used twice: once to see that `κ → κ(𝔪 Rh)` is bijective, so that `τ` exists, and once to
see that a local map induces `τ`. The second use is the one that carries the mathematics of the
reduction, so it is stated for an arbitrary `R`-algebra `A` and an arbitrary prime `q` of it, where
the hypothesis reads "`A = R + q`" and the conclusion is that 08HR's residue condition holds for
every `R`-algebra map carrying `q` into `𝔪 Sh`; `𝔪 Rh` is the case `A = Rh`, `q = 𝔪 Rh`.

## References

* [StacksProject 04GS](https://stacks.math.columbia.edu/tag/04GS)
* [StacksProject 08HR](https://stacks.math.columbia.edu/tag/08HR)
-/

namespace Stacks.Henselian.HenselizationUnique

open CategoryTheory IsLocalRing Stacks.Henselian.EtaleLifting

/-- A ring map between local rings is local exactly when it pulls the maximal ideal back to the
maximal ideal. -/
@[ega "0 1.0.7" "partial"]
private theorem isLocalHom_iff_maximalIdeal_eq_comap {R S F : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [FunLike F R S] [RingHomClass F R S] (f : F) :
    IsLocalHom f ↔ maximalIdeal R = (maximalIdeal S).comap f := by
  simp only [Ideal.ext_iff, Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff, not_iff_not]
  exact ⟨fun hf a => ⟨fun hu => hu.map f, hf.map_nonunit a⟩, fun h => ⟨fun a ha => (h a).2 ha⟩⟩

/-- The residue field extension of a local `R`-algebra `Rh` with `R → Rh` local is trivial as soon
as every element of `Rh` agrees modulo `𝔪 Rh` with one coming from `R`. -/
private theorem bijective_residueFieldMapFib {R : Type u} {Rh : Type v} [CommRing R] [CommRing Rh]
    [IsLocalRing R] [IsLocalRing Rh] [Algebra R Rh]
    (hpq : maximalIdeal R = (maximalIdeal Rh).comap (algebraMap R Rh))
    (hgen : ∀ x : Rh, ∃ r : R, x - algebraMap R Rh r ∈ maximalIdeal Rh) :
    Function.Bijective (residueFieldMapFib (maximalIdeal R) (maximalIdeal Rh) hpq) := by
  refine ⟨(residueFieldMapFib _ _ hpq).injective, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := Ideal.algebraMap_residueField_surjective (maximalIdeal Rh) y
  obtain ⟨r, hr⟩ := hgen x
  refine ⟨algebraMap R (maximalIdeal R).ResidueField r, ?_⟩
  rw [residueFieldMapFib, Ideal.ResidueField.map_algebraMap, ← sub_eq_zero, ← map_sub,
    Ideal.algebraMap_residueField_eq_zero]
  simpa using (maximalIdeal Rh).neg_mem hr

/-- **The residue datum of Tag 08HR is not data when the residue extension is trivial.** Let `S`
be a local ring, `A` an `R`-algebra and `q` a prime of `A` lying over `p = R ∩ 𝔪 S` such that
`A = R + q`, i.e. every element of `A` agrees modulo `q` with one coming from `R`. Then *every*
`R`-algebra map `f : A → S` carrying `q` into `𝔪 S` induces the prescribed `κ(p)`-algebra map
`τ : κ(q) → κ(S)` on residue fields, so the second of 08HR's two conditions on `f` follows from
the first. Indeed `τ ∘ (A → κ(q))` and `residue S ∘ f` both kill `q` and agree on the image of
`R`, by `hτ`; and modulo `q` that is all of `A`. -/
private theorem inducesResidueMap_of_le_comap {R : Type u} {A : Type v} {S : Type w} [CommRing R]
    [CommRing A] [CommRing S] [IsLocalRing S] [Algebra R A] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (hp : p = (maximalIdeal S).comap (algebraMap R S))
    (q : Ideal A) [q.IsPrime] (hpq : p = q.comap (algebraMap R A))
    {τ : q.ResidueField →+* ResidueField S}
    (hτ : τ.comp (residueFieldMapFib p q hpq) = residueFieldMapBase p hp)
    (hgen : ∀ x : A, ∃ r : R, x - algebraMap R A r ∈ q)
    (f : A →ₐ[R] S) (hf : q ≤ (maximalIdeal S).comap (f : A →+* S)) :
    InducesResidueMap q (f : A →+* S) τ := by
  refine RingHom.ext fun x => ?_
  obtain ⟨r, hr⟩ := hgen x
  have hbase : τ (algebraMap A q.ResidueField (algebraMap R A r))
      = residue S (algebraMap R S r) := by
    rw [show algebraMap A q.ResidueField (algebraMap R A r)
        = residueFieldMapFib p q hpq (algebraMap R p.ResidueField r) from
      (Ideal.ResidueField.map_algebraMap ..).symm, ← RingHom.comp_apply, hτ,
      residueFieldMapBase, Ideal.ResidueField.lift_algebraMap, RingHom.comp_apply]
  have hLzero : τ (algebraMap A q.ResidueField (x - algebraMap R A r)) = 0 := by
    rw [Ideal.algebraMap_residueField_eq_zero.mpr hr, map_zero]
  have hRzero : residue S (f (x - algebraMap R A r)) = 0 := (residue_eq_zero_iff _).mpr (hf hr)
  simp only [RingHom.comp_apply, AlgHom.coe_toRingHom]
  rw [show x = algebraMap R A r + (x - algebraMap R A r) by ring, map_add, map_add, hLzero,
    map_add, map_add, hRzero, add_zero, add_zero, hbase, f.commutes r]

open IsLocalRing in
/-- An `R`-algebra map between local rings is local exactly when it pulls the maximal ideal back
to the maximal ideal. -/
private theorem isLocalHom_algHom_iff {R : Type u} {Rh : Type v} {Sh : Type w} [CommRing R]
    [CommRing Rh] [CommRing Sh] [IsLocalRing Rh] [IsLocalRing Sh] [Algebra R Rh] [Algebra R Sh]
    (f : Rh →ₐ[R] Sh) :
    IsLocalHom f ↔ maximalIdeal Rh = (maximalIdeal Sh).comap (f : Rh →+* Sh) := by
  rw [Ideal.comap_coe]; exact isLocalHom_iff_maximalIdeal_eq_comap f

open IsLocalRing in
/-- The residue datum that Tag 08HR takes as input, in the case where `R → Rh` is surjective on
residue fields: the inverse of the resulting isomorphism `κ(𝔪 R) → κ(𝔪 Rh)`, followed by the
canonical map `κ(𝔪 R) → κ(Sh)`. -/
private noncomputable def residueDatum
    {R : Type u} {Rh : Type v} {Sh : Type w} [CommRing R] [CommRing Rh] [CommRing Sh]
    [IsLocalRing R] [IsLocalRing Rh] [IsLocalRing Sh] [Algebra R Rh] [Algebra R Sh]
    [IsLocalHom (algebraMap R Rh)] [IsLocalHom (algebraMap R Sh)]
    (hres : Function.Surjective (ResidueField.map (algebraMap R Rh))) :
    (maximalIdeal Rh).ResidueField →+* ResidueField Sh :=
  (residueFieldMapBase (maximalIdeal R) (maximalIdeal_comap (algebraMap R Sh)).symm).comp
    (RingEquiv.ofBijective _ (bijective_residueFieldMapFib
        (maximalIdeal_comap (algebraMap R Rh)).symm
        (Stacks.Etale.PrincipalPowerIso.exists_sub_mem_maximalIdeal_of_surjective_residueFieldMap
          (algebraMap R Rh) hres))).symm.toRingHom

open IsLocalRing in
/-- `residueDatum` is a `κ(𝔪 R)`-algebra map, which is 08HR's hypothesis on its residue datum. -/
private theorem residueDatum_spec
    {R : Type u} {Rh : Type v} {Sh : Type w} [CommRing R] [CommRing Rh] [CommRing Sh]
    [IsLocalRing R] [IsLocalRing Rh] [IsLocalRing Sh] [Algebra R Rh] [Algebra R Sh]
    [IsLocalHom (algebraMap R Rh)] [IsLocalHom (algebraMap R Sh)]
    (hres : Function.Surjective (ResidueField.map (algebraMap R Rh))) :
    (residueDatum (Sh := Sh) hres).comp (residueFieldMapFib (maximalIdeal R) (maximalIdeal Rh)
        (maximalIdeal_comap (algebraMap R Rh)).symm)
      = residueFieldMapBase (maximalIdeal R) (maximalIdeal_comap (algebraMap R Sh)).symm := by
  refine RingHom.ext fun x => ?_
  simp only [residueDatum, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom]
  congr 1
  exact (RingEquiv.ofBijective _ (bijective_residueFieldMapFib
    (maximalIdeal_comap (algebraMap R Rh)).symm
    (Stacks.Etale.PrincipalPowerIso.exists_sub_mem_maximalIdeal_of_surjective_residueFieldMap
      (algebraMap R Rh) hres))).symm_apply_apply x

open IsLocalRing in
/-- Tag 08HR's lift at the forced residue datum. -/
private noncomputable def map
    {R : Type u} {Rh : Type v} {Sh : Type w} [CommRing R] [CommRing Rh] [CommRing Sh]
    [IsLocalRing R] [IsLocalRing Rh] [HenselianLocalRing Sh] [Algebra R Rh] [Algebra R Sh]
    [IsLocalHom (algebraMap R Rh)] [IsLocalHom (algebraMap R Sh)]
    (hind : (CommAlgCat.etale.{max u v} R).ind.{max u v}
      (CommAlgCat.of R (ULift.{u} Rh)))
    (hres : Function.Surjective (ResidueField.map (algebraMap R Rh))) :
    Rh →ₐ[R] Sh :=
  Stacks.Henselian.EtaleLifting.algHom hind (maximalIdeal R) (maximalIdeal_comap (algebraMap R
    Sh)).symm
    (maximalIdeal Rh) (maximalIdeal_comap (algebraMap R Rh)).symm (residueDatum hres)
    (residueDatum_spec hres)

open IsLocalRing in
/-- `map` is a local ring map: 08HR's condition `𝔪 Rh = f⁻¹(𝔪 Sh)` *is* locality. -/
@[sga "4 VIII 4.1" "partial"]
private theorem isLocalHom_map
    {R : Type u} {Rh : Type v} {Sh : Type w} [CommRing R] [CommRing Rh] [CommRing Sh]
    [IsLocalRing R] [IsLocalRing Rh] [HenselianLocalRing Sh] [Algebra R Rh] [Algebra R Sh]
    [IsLocalHom (algebraMap R Rh)] [IsLocalHom (algebraMap R Sh)]
    (hind : (CommAlgCat.etale.{max u v} R).ind.{max u v}
      (CommAlgCat.of R (ULift.{u} Rh)))
    (hres : Function.Surjective (ResidueField.map (algebraMap R Rh))) :
    IsLocalHom (map (Sh := Sh) hind hres) :=
  (isLocalHom_algHom_iff _).mpr
    (Stacks.Henselian.EtaleLifting.comap_maximalIdeal_algHom hind (maximalIdeal R)
      (maximalIdeal_comap (algebraMap R Sh)).symm (maximalIdeal Rh)
      (maximalIdeal_comap (algebraMap R Rh)).symm (residueDatum hres) (residueDatum_spec hres))

open IsLocalRing in
/-- `map` is the only local `R`-algebra map `Rh → Sh`: a local map induces `residueDatum` rather
than being assumed to, so 08HR's uniqueness applies to it. -/
@[sga "4 VIII 4.1" "partial"]
private theorem map_unique
    {R : Type u} {Rh : Type v} {Sh : Type w} [CommRing R] [CommRing Rh] [CommRing Sh]
    [IsLocalRing R] [IsLocalRing Rh] [HenselianLocalRing Sh] [Algebra R Rh] [Algebra R Sh]
    [IsLocalHom (algebraMap R Rh)] [IsLocalHom (algebraMap R Sh)]
    (hind : (CommAlgCat.etale.{max u v} R).ind.{max u v}
      (CommAlgCat.of R (ULift.{u} Rh)))
    (hres : Function.Surjective (ResidueField.map (algebraMap R Rh)))
    (f : Rh →ₐ[R] Sh) (hf : IsLocalHom f) :
    f = map hind hres := by
  have hf' := (isLocalHom_algHom_iff f).mp hf
  exact Stacks.Henselian.EtaleLifting.algHom_unique hind (maximalIdeal R)
    (maximalIdeal_comap (algebraMap R Sh)).symm (maximalIdeal Rh)
    (maximalIdeal_comap (algebraMap R Rh)).symm (residueDatum hres) (residueDatum_spec hres) f
    ⟨hf', inducesResidueMap_of_le_comap _ (maximalIdeal_comap (algebraMap R Sh)).symm _
      (maximalIdeal_comap (algebraMap R Rh)).symm (residueDatum_spec hres)
      (Stacks.Etale.PrincipalPowerIso.exists_sub_mem_maximalIdeal_of_surjective_residueFieldMap
        (algebraMap R Rh) hres) f hf'.le⟩

end Stacks.Henselian.HenselizationUnique

/-!
# The universal property of the henselization

Let `R → S` be a local map of local rings and let `R → R^h`, `S → S^h` be the henselizations.
Then there is a unique local ring map `R^h → S^h` fitting into the commutative square
`R → R^h → S^h`, `R → S → S^h`; this is what makes the henselization a functor.

The map is produced, and pinned, by the universal property of `R^h`: *any* henselian local ring
receiving a local map from `R` receives a unique local `R`-algebra map from `R^h`. That is the
form stated here. Of a henselization `R → R^h` it uses only two of the four properties of
Lemma 04GN — that `R^h` is a filtered colimit of étale `R`-algebras and that `R → R^h` induces a
surjection on residue fields — and of the target only that it is henselian local; so `R^h` is the
initial object of the category of henselian local rings under `R` and local maps, and `S^h` is one
such object, by way of `R → S → S^h`.

## Main results

* `HenselianLocalRing.indEtaleAlgHom`: the map, with
  `HenselianLocalRing.isLocalHom_indEtaleAlgHom` saying that it is local and
  `HenselianLocalRing.indEtaleAlgHom_unique` that it is the only such map.

## Implementation notes

*Departure from the source's form: the intermediate ring `S` is eliminated.* In the source's
square, `S` enters only through the composite `R → S → S^h`, and what the proof uses of that
composite is that it is a local ring map. Carrying `S` would therefore make `IsLocalRing S` and
the hypotheses saying that `S^h` is a henselization of `S` dead, so they are dropped and `S^h` is
replaced by an arbitrary henselian local ring `Sh` with `R → Sh` local. Lemma 04GS is the
instance `Rh = R^h`, `Sh = S^h` with `Algebra R Sh` the composite of `R → S` and `S → S^h`: the
`IsLocalHom (algebraMap R Sh)` instance is then `RingHom.isLocalHom_comp` applied to the two local
maps, and an `R`-algebra map `R^h → S^h` is exactly a ring map making the source's square commute.

*The square is the `R`-algebra structure.* As in Lemma 08HT, a map `f : Rh →ₐ[R] Sh` is precisely
a ring map with `f ∘ algebraMap R Rh = algebraMap R Sh`, so the commutativity of the square is
carried by the type of `f` and no separate compatibility hypothesis is needed, nor omitted.

*The two properties of a henselization that are used.* "`Rh` is a filtered colimit of étale
`R`-algebras" is `(CommAlgCat.etale R).ind (CommAlgCat.of R Rh)`, the spelling of Lemma 04GN:
`CategoryTheory.ObjectProperty.ind P X` says that `X` is the colimit of a filtered diagram all of
whose values satisfy `P`, and the colimit is taken in `CommAlgCat R`, so diagram, cocone and
colimit are all over `R`. "The residue field of `Rh` is `κ`" is asked for in the weakest form the
proof uses, surjectivity of the canonical `IsLocalRing.ResidueField.map (algebraMap R Rh)`; since
a ring map between fields is injective, that is equivalent to the bijectivity stated in
Lemma 04GN, and it is what forces the map on residue fields, hence `f`, to be unique. The two
remaining items of Lemma 04GN — `HenselianLocalRing Rh` and `𝔪 Rh = 𝔪_{Rh}` — are not used and
are not assumed. Neither Mathlib nor this repository has a predicate `IsHenselization`; when one
is introduced this becomes `IsHenselization.existsUnique_isLocalHom`, with the two hypotheses
collapsing into it.

*Universes.* `R` and `Rh` share a universe, as the index category of the colimit in Lemma 04GN
is taken there, while the henselian target is in a universe of its own: nothing about it is
constructed.

Faithfulness to [StacksProject 04GS], point by point. (1) No hypothesis is dead, and each is
necessary. Dropping `hind`: for a field `K`, `Rh = K⟦t⟧` and `Sh = K⟦u⟧` satisfy everything else,
and `t ↦ 0` and `t ↦ u` are two local `K`-algebra maps. Dropping `hres`: `R = ℚ`, `Rh = ℚ(i)`
(étale, hence ind-étale) and `Sh = ℂ` admit the two maps `i ↦ ± i`. Dropping
`HenselianLocalRing Sh`: for `R = Sh = ℤ` localized at `(5)` and `Rh = R^h`, a local `R`-algebra
map `Rh → Sh` would send a root of `x² - 6` in `Rh` — one exists, `1` being a simple root of
`x² - 6` mod `5` — to a square root of `6` in `ℚ`, so existence fails. Dropping
`IsLocalHom (algebraMap R Sh)`: it is implied by the conclusion, `algebraMap R Sh` being
`f ∘ algebraMap R Rh`, and fails for `R = ℤ` localized at `(5)` and `Sh = ℚ`. (2) The scalars and
the base are the source's: `Rh` and `Sh` are algebras over the ring `R` at the foot of the
square, the colimit is one of `R`-algebras, the residue field map is the one induced by
`R → Rh` itself, and the unique map is a map of `R`-algebras — not of `Rh`-algebras and not over a
localization of `R`. (3) The map the source names is pinned, not merely asserted to exist: it is
the unique element of `Rh →ₐ[R] Sh` that is a local ring map, so the statement is the
characterisation, which is the content of the lemma; uniqueness among local maps rather than among
all `R`-algebra maps is the source's, and is what these hypotheses give — with `𝔪 Rh = 𝔪_{Rh}`
added, locality would be automatic. (4) The instantiation is not degenerate: `R = Rh = Sh = K` a
field with `f` the identity satisfies every hypothesis (`Field.henselian`; `K` is étale over `K`,
hence ind-étale by `CategoryTheory.ObjectProperty.le_ind`; the residue field of a field is itself),
and the statement has content at `R = ℤ` localized at `(5)`, `Rh = R^h` and `Sh = ℤ_[5]`, where it
produces the canonical local map `R^h → ℤ_[5]` and no other.

## References

* [StacksProject 04GS](https://stacks.math.columbia.edu/tag/04GS)
* [StacksProject 08HR](https://stacks.math.columbia.edu/tag/08HR), the lemma the source deduces
  this from, which prescribes the map on residue fields instead of deriving it
* [StacksProject 04GN](https://stacks.math.columbia.edu/tag/04GN), the four properties of a
  henselization, and `IsLocalRing.exists_henselization`
* [StacksProject 04GQ](https://stacks.math.columbia.edu/tag/04GQ), the henselization `R → R^h`
* [StacksProject 08HT](https://stacks.math.columbia.edu/tag/08HT), the isomorphism-level sibling

## Tags

henselization, henselian local ring, universal property, ind-étale, étale algebra, local ring map,
residue field
-/



@[expose] public section

open IsLocalRing in
/-- **The map given by the universal property of the henselization** (Stacks 04GS). Let
`(R, 𝔪, κ)` be a local ring, let `Rh` be a local `R`-algebra with `R → Rh` local which is a
filtered colimit of étale `R`-algebras and has residue field `κ`, and let `Sh` be a henselian
local ring with `R → Sh` local. This is the `R`-algebra map `Rh → Sh` that is a local ring map,
unique as such by `indEtaleAlgHom_unique`. Applied to the henselizations `Rh = R^h` and
`Sh = S^h` of a local map of local rings `R → S`, it is the local ring map `R^h → S^h` over
`R → S` that makes the henselization a functor. -/
@[stacks 04GS "The map of the universal property of `R^h`: the target is an arbitrary henselian
local ring `Sh` with `R → Sh` local, since the source's `S` enters only through the composite
`R → S → S^h`. Of the henselization `R → Rh` only the two items of Lemma 04GN that the proof uses
are assumed — ind-étale, `(CommAlgCat.etale R).ind`, and surjectivity on residue fields. The
commutative square is the `R`-algebra structure of the map. `isLocalHom_indEtaleAlgHom` and
`indEtaleAlgHom_unique` are its defining property and its uniqueness. See the module
docstring.", no_expose]
noncomputable def HenselianLocalRing.indEtaleAlgHom
    {R : Type u} {Rh : Type v} {Sh : Type w} [CommRing R] [CommRing Rh] [CommRing Sh]
    [IsLocalRing R]
    [IsLocalRing Rh] [HenselianLocalRing Sh] [Algebra R Rh] [Algebra R Sh]
    [IsLocalHom (algebraMap R Rh)] [IsLocalHom (algebraMap R Sh)]
    (hind : (CommAlgCat.etale.{max u v} R).ind.{max u v}
      (CommAlgCat.of R (ULift.{u} Rh)))
    (hres : Function.Surjective (ResidueField.map (algebraMap R Rh))) :
    Rh →ₐ[R] Sh :=
  Stacks.Henselian.HenselizationUnique.map hind hres

open IsLocalRing in
/-- `HenselianLocalRing.indEtaleAlgHom` is a local ring map. -/
@[stacks 04GS "the defining property of `indEtaleAlgHom`"]
public theorem HenselianLocalRing.isLocalHom_indEtaleAlgHom
    {R : Type u} {Rh : Type v} {Sh : Type w} [CommRing R] [CommRing Rh] [CommRing Sh]
    [IsLocalRing R]
    [IsLocalRing Rh] [HenselianLocalRing Sh] [Algebra R Rh] [Algebra R Sh]
    [IsLocalHom (algebraMap R Rh)] [IsLocalHom (algebraMap R Sh)]
    (hind : (CommAlgCat.etale.{max u v} R).ind.{max u v}
      (CommAlgCat.of R (ULift.{u} Rh)))
    (hres : Function.Surjective (ResidueField.map (algebraMap R Rh))) :
    IsLocalHom (HenselianLocalRing.indEtaleAlgHom (Sh := Sh) hind hres) :=
  Stacks.Henselian.HenselizationUnique.isLocalHom_map hind hres

open IsLocalRing in
/-- `HenselianLocalRing.indEtaleAlgHom` is the only local `R`-algebra map `Rh → Sh`. -/
@[stacks 04GS "uniqueness of `indEtaleAlgHom`"]
public theorem HenselianLocalRing.indEtaleAlgHom_unique
    {R : Type u} {Rh : Type v} {Sh : Type w} [CommRing R] [CommRing Rh] [CommRing Sh]
    [IsLocalRing R]
    [IsLocalRing Rh] [HenselianLocalRing Sh] [Algebra R Rh] [Algebra R Sh]
    [IsLocalHom (algebraMap R Rh)] [IsLocalHom (algebraMap R Sh)]
    (hind : (CommAlgCat.etale.{max u v} R).ind.{max u v}
      (CommAlgCat.of R (ULift.{u} Rh)))
    (hres : Function.Surjective (ResidueField.map (algebraMap R Rh)))
    (f : Rh →ₐ[R] Sh) (hf : IsLocalHom f) :
    f = HenselianLocalRing.indEtaleAlgHom hind hres :=
  Stacks.Henselian.HenselizationUnique.map_unique hind hres f hf

end

end

/-!
# Étale algebras and the henselization of a local ring

Stacks Tag 04GR (Stacks project Lemma 10.155.5).

Let `R` and `S` be local rings and let `R → S` be a local ring homomorphism.
Let `S → Sʰ` be a ring homomorphism into a henselian local ring `Sʰ` such that
`S → Sʰ` is local (this captures the structural map `S → S^h` to the
henselization; the henselization functor itself is not constructed in the
available Mathlib, so we abstract `Sʰ` by the only two properties of it used in
the proof: it is henselian and the structural map is local).

Let `R → A` be an étale ring map and let `𝔮 ⊆ A` be a prime ideal lying over
the maximal ideal `𝔪_R` of `R` such that the induced map of residue fields
`R/𝔪_R → κ(𝔮)` is an isomorphism.

Then there exists a unique ring homomorphism `f : A → Sʰ` such that:
1. (Commutativity) `f ∘ (algebraMap R A) = (S → Sʰ) ∘ (R → S)`, i.e. `f` is a
   homomorphism of `R`-algebras when `Sʰ` is given the `R`-algebra structure
   through `R → S → Sʰ`;
2. (Prime condition) `(𝔪_{Sʰ}).comap f = 𝔮`.
-/

@[expose] public section
-- Conventions:
-- * "Local ring map" is `IsLocalHom`.
-- * "Henselian" is `HenselianLocalRing`.
-- * "Étale" is `Algebra.Etale R A`.
-- * "Lying over `𝔪_R`" is `Ideal.LiesOver q (IsLocalRing.maximalIdeal R)`,
--   i.e. `IsLocalRing.maximalIdeal R = q.comap (algebraMap R A)`.
-- * `κ(𝔮)` is `Ideal.ResidueField q`, the residue field of the localization
--   `A_𝔮`; `R/𝔪_R` is `Ideal.ResidueField (IsLocalRing.maximalIdeal R)`.
-- * The canonical map `R/𝔪_R → κ(𝔮)` induced by `R → A` is
--   `Ideal.ResidueField.map (IsLocalRing.maximalIdeal R) q (algebraMap R A) _`.
--   The residue field condition `R/𝔪_R ≅ κ(𝔮)` is its bijectivity.

open IsLocalRing

/-- Localizing away from `g ∉ q` keeps the image of the prime `q` prime and contracts to `q`. -/
private theorem isPrime_map_away_and_comap {A : Type*} [CommRing A] (q : Ideal A) [q.IsPrime]
    {g : A} (hg : g ∉ q) :
    (q.map (algebraMap A (Localization.Away g))).IsPrime ∧
      (q.map (algebraMap A (Localization.Away g))).comap (algebraMap A (Localization.Away g))
        = q := by
  have hdisj : Disjoint (Submonoid.powers g : Set A) (q : Set A) :=
    (Ideal.disjoint_powers_iff_notMem g (Ideal.IsPrime.isRadical inferInstance)).mpr hg
  exact ⟨IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) _ q inferInstance
      (by simpa using hdisj),
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) _ (I := q) inferInstance
      (by simpa using hdisj)⟩

/-- Two `R`-algebra maps out of a standard étale algebra agree once they agree at the generator. -/
private theorem algHom_ext_of_standardEtalePresentation {R T B : Type*} [CommRing R] [CommRing T]
    [CommRing B] [Algebra R T] [Algebra R B] (pres : StandardEtalePresentation R T)
    {u v : T →ₐ[R] B} (h : u pres.x = v pres.x) : u = v := by
  rw [← AlgHom.cancel_right (g₁ := u) (g₂ := v) pres.equivRing.symm.surjective]
  exact pres.P.hom_ext (by simpa using h)

/-- If `Q ⊆ T` lies over `q ⊆ A` for a localization `T` of `A` and `R/𝔪 → κ(q)` is bijective, then
`κ(Q)` embeds over `R` into the residue field of any `R`-algebra `Sh` with `R → Sh` local, and
`R → κ(Q)` is surjective. -/
private theorem exists_residueField_hom_of_comap_eq {R A T Sh : Type*} [CommRing R] [CommRing A]
    [CommRing T] [CommRing Sh] [IsLocalRing R] [IsLocalRing Sh] [Algebra R A] [Algebra A T]
    [Algebra R T] [IsScalarTower R A T] [Algebra R Sh] [IsLocalHom (algebraMap R Sh)] (g : A)
    [IsLocalization.Away g T] (q : Ideal A) [q.IsPrime] [q.LiesOver (maximalIdeal R)]
    (Q : Ideal T) [Q.IsPrime] (hQ : Q.comap (algebraMap A T) = q)
    (hres : Function.Bijective
      (Ideal.ResidueField.map (maximalIdeal R) q (algebraMap R A) Ideal.LiesOver.over)) :
    ∃ θ : Q.ResidueField →+* (maximalIdeal Sh).ResidueField, Function.Injective θ ∧
      (∀ r : R, θ (algebraMap R Q.ResidueField r) = algebraMap R (maximalIdeal Sh).ResidueField r)
      ∧ Function.Surjective (algebraMap R Q.ResidueField) := by
  have hbijQ : Function.Bijective (Ideal.ResidueField.map q Q (algebraMap A T) hQ.symm) :=
    (RingHom.surjectiveOnStalks_of_isLocalization (M := Submonoid.powers g)
      (S := T)).residueFieldMap_bijective q Q hQ.symm
  set eqQ : q.ResidueField ≃+* Q.ResidueField := RingEquiv.ofBijective _ hbijQ with heqQ
  set eres : (maximalIdeal R).ResidueField ≃+* q.ResidueField :=
    RingEquiv.ofBijective _ hres with heres
  set mapRSh : (maximalIdeal R).ResidueField →+* (maximalIdeal Sh).ResidueField :=
    Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal Sh) (algebraMap R Sh)
      (maximalIdeal_comap (algebraMap R Sh)).symm with hmapRSh
  have heqQ_R : ∀ r : R, eqQ (algebraMap R q.ResidueField r) = algebraMap R Q.ResidueField r := by
    intro r
    rw [heqQ, RingEquiv.ofBijective_apply, IsScalarTower.algebraMap_apply R A q.ResidueField r,
      Ideal.ResidueField.map_algebraMap, ← IsScalarTower.algebraMap_apply A T Q.ResidueField,
      ← IsScalarTower.algebraMap_apply R A Q.ResidueField]
  have heres_R : ∀ r : R, eres (algebraMap R (maximalIdeal R).ResidueField r)
      = algebraMap R q.ResidueField r := by
    intro r
    rw [heres, RingEquiv.ofBijective_apply, Ideal.ResidueField.map_algebraMap,
      ← IsScalarTower.algebraMap_apply R A q.ResidueField]
  refine ⟨mapRSh.comp ((eres.symm.toRingHom).comp eqQ.symm.toRingHom),
    mapRSh.injective.comp (eres.symm.injective.comp eqQ.symm.injective), fun r => ?_, fun y => ?_⟩
  · have h1 : eqQ.symm.toRingHom (algebraMap R Q.ResidueField r) = algebraMap R q.ResidueField r :=
      by rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, ← heqQ_R r,
        RingEquiv.symm_apply_apply]
    have h2 : eres.symm.toRingHom (algebraMap R q.ResidueField r)
        = algebraMap R (maximalIdeal R).ResidueField r := by
      rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, ← heres_R r,
        RingEquiv.symm_apply_apply]
    rw [RingHom.comp_apply, RingHom.comp_apply, h1, h2, hmapRSh, Ideal.ResidueField.map_algebraMap,
      ← IsScalarTower.algebraMap_apply R Sh (maximalIdeal Sh).ResidueField]
  · obtain ⟨r₀, hr₀⟩ := Ideal.algebraMap_residueField_surjective (maximalIdeal R)
      (eres.symm (eqQ.symm y))
    refine ⟨r₀, ?_⟩
    rw [← heqQ_R r₀, ← heres_R r₀, hr₀, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

/-- **Stacks Tag 04GR.**
Let `R, S, Sh` be local rings, `R → S` (`rs`) a local ring homomorphism, and
`S → Sh` (`ssh`) a local ring homomorphism into a henselian local ring `Sh`.
Let `R → A` be étale and let `q ⊆ A` be a prime lying over the maximal ideal of
`R` whose induced residue-field map `R/𝔪_R → κ(q)` is bijective. Then there is a
unique ring homomorphism `f : A → Sh` that is `R`-linear (`f ∘ algebraMap R A =
ssh ∘ rs`) and satisfies `(maximalIdeal Sh).comap f = q`. -/
@[stacks 04GR,
  ega "IV 18.5.11" "special case",
  ega "IV 18.5.12" "special case",
  ega "IV 18.5.17" "affine étale morphisms",
  ega "IV 18.6.2",
  ega "IV 18.8.1" "(a)⇒(c), special case",
  ega "IV 18.8.4" "special case",
  sga "1 I 6.2" "special case",
  sga "3 XI 1.11" "special case",
  sga "4 VIII 4.1" "(iii)"]
theorem existsUnique_ringHom_to_henselian_of_etale
    (R S Sh A : Type*)
    [CommRing R] [CommRing S] [CommRing Sh] [CommRing A]
    [IsLocalRing R] [IsLocalRing S]
    [Algebra R A] [Algebra.Etale R A]
    (rs : R →+* S) [IsLocalHom rs]
    (ssh : S →+* Sh) [IsLocalHom ssh] [HenselianLocalRing Sh]
    (q : Ideal A) [q.IsPrime] [q.LiesOver (maximalIdeal R)]
    (hres : Function.Bijective
      (Ideal.ResidueField.map (maximalIdeal R) q (algebraMap R A)
        Ideal.LiesOver.over)) :
    ∃! f : A →+* Sh,
      f.comp (algebraMap R A) = ssh.comp rs ∧ (maximalIdeal Sh).comap f = q := by
  -- Abbreviation for the conjunction of the two required properties of a solution.
  -- A solution is an `R`-linear ring hom `f : A → Sh` (`f ∘ (algebraMap R A) =
  -- ssh ∘ rs`) whose comap of the maximal ideal of `Sh` is exactly `q`.
  set P : (A →+* Sh) → Prop :=
    fun f => f.comp (algebraMap R A) = ssh.comp rs ∧ (maximalIdeal Sh).comap f = q
    with hP
  -- Give `Sh` its `R`-algebra structure through `R → S → Sh` (`ssh ∘ rs`).
  let : Algebra R Sh := (ssh.comp rs).toAlgebra
  have hRSh : (algebraMap R Sh) = ssh.comp rs := rfl
  have : IsLocalHom (algebraMap R Sh) := by rw [hRSh]; infer_instance
  -- The standard-étale neighborhood `T = A_g` of `q`, and the prime `Q` of `T` over `q`.
  obtain ⟨g, hg, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) q
  obtain ⟨hQprime, hQcomap⟩ := isPrime_map_away_and_comap q hg
  set T := Localization.Away g with hT
  set Q : Ideal T := q.map (algebraMap A T) with hQ
  obtain ⟨θ, hθinj, hθ_R, hRQsurj⟩ :=
    exists_residueField_hom_of_comap_eq (Sh := Sh) g q Q hQcomap hres
  obtain ⟨pres⟩ := hstd.nonempty_standardEtalePresentation
  -- The residue of the generator at `Q`, transported to the residue field of `Sh`.
  set χ₂ : T →ₐ[R] (maximalIdeal Sh).ResidueField :=
    ({ θ with commutes' := hθ_R } : Q.ResidueField →ₐ[R] (maximalIdeal Sh).ResidueField).comp
      (IsScalarTower.toAlgHom R T Q.ResidueField) with hχ₂
  set a₀ : (maximalIdeal Sh).ResidueField := χ₂ pres.x with ha₀
  have hmap : pres.P.HasMap a₀ := pres.hasMap.map χ₂
  -- An `∃!` is exactly: existence of a witness together with uniqueness of any two
  -- witnesses.  Each is treated separately below.
  --
  -- ────────────────────────────────────────────────────────────────────────────
  -- SUB-LEMMA (E)  EXISTENCE.
  -- ────────────────────────────────────────────────────────────────────────────
  -- Claim: there is `f : A →+* Sh` with `P f`.
  --
  -- Rigorous argument (Stacks 04GR existence, via the standard-étale local
  -- structure theorem reduced to monic Hensel lifting, which IS in Mathlib as
  -- `HenselianLocalRing.is_henselian`; the étale-lift universal property
  -- (Stacks 04GG cond. 8) is NOT in this Mathlib, so we go through the explicit
  -- polynomial route):
  --
  --   1. `R → A` is étale, hence of finite presentation and étale at every prime;
  --      in particular at `q` (`Algebra.IsEtaleAt`, derivable from `Algebra.Etale`).
  --      By `Algebra.IsEtaleAt.exists_isStandardEtale` there is `g ∈ A \ q` such
  --      that `A_g := Localization.Away g` is a STANDARD étale `R`-algebra:
  --      `A_g ≅ R[X,Y]/(p, Y·h − 1)` with `p` monic and `p'` a unit in `R[X][1/h]`
  --      (`Algebra.IsStandardEtale.nonempty_standardEtalePresentation`,
  --      `StandardEtalePresentation`).  Note `q` survives in `A_g` since `g ∉ q`.
  --   2. The composite `R → S → Sh` (`ssh.comp rs`) is a local hom into the
  --      henselian local ring `Sh`, so `maximalIdeal Sh` lies over `maximalIdeal R`
  --      and (because every `IsLocalHom` between local rings induces a map of
  --      residue fields) we get `R/m_R → Sh/m_Sh`.  Composing the residue-field
  --      isomorphism `R/m_R ≅ κ(q)` (hypothesis `hres`, inverse direction) with
  --      the image of the standard-étale root `X ↦ ā ∈ κ(q)` produces a residue
  --      `a₀ ∈ Sh/m_Sh` of the monic polynomial `p̄` at which `p̄'` is a unit.
  --   3. Transport `p` to `Sh[X]` along `R → Sh`; lift `a₀` to a representative in
  --      `Sh`.  Apply `HenselianLocalRing.is_henselian` to the (monic) image of `p`
  --      to get a UNIQUE-up-to-`m_Sh` element `a ∈ Sh` with `p(a) = 0` and
  --      `a ≡ a₀ (mod m_Sh)`; here `p'(a)` is a unit since `p'(a) ≡ p̄'(a₀) ≠ 0`.
  --   4. `X ↦ a` defines an `R`-algebra hom `R[X]/(p) → Sh`.  Because `h(a)` is a
  --      unit in `Sh` (its residue `h̄(a₀)` is nonzero: `g ∉ q` means `h` is
  --      invertible at `q`, and `R → Sh` is local), this extends over the
  --      localization to an `R`-algebra hom `A_g ≅ (R[X]/p)_h → Sh`.  Precompose
  --      with the localization map `A → A_g` to obtain `f : A →+* Sh`.
  --   5. By construction `f` is `R`-linear, i.e. `f ∘ algebraMap R A = ssh ∘ rs`,
  --      and `(maximalIdeal Sh).comap f = q`: an element of `A` lands in `m_Sh`
  --      under `f` iff its image in `κ(q)` (via `a₀`/the residue iso) vanishes,
  --      which characterises exactly the prime `q` (uses the residue iso `hres`
  --      again, plus `g ∉ q`).  Hence `P f`.
  have existence : ∃ f : A →+* Sh, P f := by
    rw [hP]
    obtain ⟨atilde, hatilde⟩ := Ideal.algebraMap_residueField_surjective (maximalIdeal Sh) a₀
    have hbridge : ∀ (x : Sh) (p : Polynomial R),
        algebraMap Sh (maximalIdeal Sh).ResidueField (Polynomial.aeval x p)
          = Polynomial.aeval (algebraMap Sh (maximalIdeal Sh).ResidueField x) p := fun x p =>
      (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom R Sh _) x p).symm
    have hunit : ∀ s : Sh, IsUnit (algebraMap Sh (maximalIdeal Sh).ResidueField s) → IsUnit s :=
      fun s hs => by
        by_contra hnu
        exact hs.ne_zero (Ideal.algebraMap_residueField_eq_zero.mpr
          ((IsLocalRing.mem_maximalIdeal _).mpr hnu))
    -- Henselian lift of the residue root `a₀` of the monic polynomial.
    have hmem : Polynomial.eval atilde (pres.P.f.map (algebraMap R Sh)) ∈ maximalIdeal Sh := by
      rw [Polynomial.eval_map_algebraMap, ← Ideal.algebraMap_residueField_eq_zero, hbridge,
        hatilde]
      exact hmap.1
    have hderiv : IsUnit (Polynomial.eval atilde
        (Polynomial.derivative (pres.P.f.map (algebraMap R Sh)))) := by
      rw [Polynomial.derivative_map, Polynomial.eval_map_algebraMap]
      exact hunit _ (by rw [hbridge, hatilde]; exact hmap.isUnit_derivative_f)
    obtain ⟨a, ha_root, ha_res⟩ :=
      HenselianLocalRing.is_henselian _ (pres.P.monic_f.map _) atilde hmem hderiv
    have hres_a : (algebraMap Sh (maximalIdeal Sh).ResidueField) a = a₀ := by
      rw [← hatilde, ← sub_eq_zero, ← map_sub, Ideal.algebraMap_residueField_eq_zero]
      exact ha_res
    have hasMap : pres.P.HasMap a :=
      ⟨by rwa [Polynomial.IsRoot.def, Polynomial.eval_map_algebraMap] at ha_root,
        hunit _ (by rw [hbridge, hres_a]; exact hmap.2)⟩
    -- The `R`-algebra map `φ : T → Sh` sending the generator to `a`.
    set φ : T →ₐ[R] Sh := (pres.P.lift a hasMap).comp pres.equivRing.toAlgHom with hφ
    have hφx : φ pres.x = a := by
      change pres.P.lift a hasMap (pres.equivRing pres.x) = a
      rw [pres.equivRing_x]
      exact pres.P.lift_X a hasMap
    have hχeq : (IsScalarTower.toAlgHom R Sh (maximalIdeal Sh).ResidueField).comp φ = χ₂ :=
      algHom_ext_of_standardEtalePresentation pres (by
        change algebraMap Sh (maximalIdeal Sh).ResidueField (φ pres.x) = a₀
        rw [hφx, hres_a])
    -- The prime condition: `x ∈ φ⁻¹ 𝔪 ↔ χ₂ x = 0 ↔ x ∈ Q`, as `θ` is injective.
    have hprime : (maximalIdeal Sh).comap φ.toRingHom = Q := by
      ext x
      have hx : algebraMap Sh (maximalIdeal Sh).ResidueField (φ x) = χ₂ x :=
        DFunLike.congr_fun hχeq x
      rw [Ideal.mem_comap, ← Ideal.algebraMap_residueField_eq_zero (I := Q),
        ← Ideal.algebraMap_residueField_eq_zero, ← map_eq_zero_iff θ hθinj]
      exact (congrArg (· = (0 : (maximalIdeal Sh).ResidueField)) hx).to_iff
    -- Assemble `f := φ ∘ (A → T)`.
    refine ⟨(φ.toRingHom).comp (algebraMap A T), ?_, ?_⟩
    · have hlin : ((φ.toRingHom).comp (algebraMap A T)).comp
          (algebraMap R A) = algebraMap R Sh := by
        ext r
        change φ (algebraMap A T (algebraMap R A r)) = algebraMap R Sh r
        rw [← IsScalarTower.algebraMap_apply R A T r, AlgHom.commutes φ r]
      rw [hlin]; rfl
    · rw [← Ideal.comap_comap, hprime, hQcomap]
  -- ────────────────────────────────────────────────────────────────────────────
  -- SUB-LEMMA (U)  UNIQUENESS.
  -- ────────────────────────────────────────────────────────────────────────────
  -- Claim: any two solutions agree.
  --
  -- Rigorous argument: let `f₁ f₂ : A →+* Sh` with `P f₁`, `P f₂`.  Both are
  -- `R`-algebra maps `A → Sh` (the `R`-algebra structure on `Sh` is via
  -- `ssh.comp rs`).  Working with the standard-étale presentation
  -- `A_g ≅ (R[X]/p)_h` from step (E.1), each `fᵢ` is determined by the image
  -- `aᵢ := fᵢ(X) ∈ Sh`, a root of (the image of) `p`.  Both `a₁, a₂` reduce mod
  -- `m_Sh` to the SAME residue `a₀` (the one coming from `q` via the residue
  -- isomorphism `hres`): indeed `P fᵢ` forces `(maximalIdeal Sh).comap fᵢ = q`,
  -- which pins down the residue of `fᵢ` at `q`, hence the residue of `aᵢ`.  Both
  -- are roots of the monic `p` with `p'` a unit and congruent mod `m_Sh` to `a₀`;
  -- by the UNIQUENESS half of the henselian lifting property (`a₁ ≡ a₂ (mod m_Sh)`
  -- + `p(a₁)=p(a₂)=0` + `p'` unit ⇒ `a₁ = a₂`, the standard Newton/henselian
  -- uniqueness, provable from `is_henselian` + `IsLocalRing` cancellation) we get
  -- `a₁ = a₂`, so `f₁ = f₂` on `A_g` and hence on `A`.
  --
  -- Equivalent Mathlib-flavoured route for the uniqueness engine: étale ⇒
  -- `Algebra.FormallyUnramified R A`, and `Algebra.FormallyUnramified.lift_unique'`
  -- / `ext_of_iInf` give equality of `R`-algebra maps that agree modulo a suitable
  -- (nil/separated) ideal; the henselian root-uniqueness supplies that agreement.
  have uniqueness : ∀ f₁ f₂ : A →+* Sh, P f₁ → P f₂ → f₁ = f₂ := by
    -- Henselian root uniqueness: two roots of `f` congruent mod the maximal ideal, with unit
    -- derivative, are equal.
    have root_unique : ∀ a₁ a₂ : Sh, pres.P.HasMap a₁ → pres.P.HasMap a₂ →
        a₂ - a₁ ∈ maximalIdeal Sh → a₁ = a₂ := by
      intro a₁ a₂ h1 h2 hcong
      obtain ⟨k, hk⟩ := (pres.P.f.map (algebraMap R Sh)).binomExpansion a₁ (a₂ - a₁)
      have hadd : a₁ + (a₂ - a₁) = a₂ := by ring
      simp only [hadd, Polynomial.eval_map_algebraMap, Polynomial.derivative_map, h1.1, h2.1,
        zero_add] at hk
      have hfac : (a₂ - a₁) * (Polynomial.aeval a₁ (Polynomial.derivative pres.P.f)
          + k * (a₂ - a₁)) = 0 := by
        linear_combination -hk
      have hunit :
          IsUnit (Polynomial.aeval a₁ (Polynomial.derivative pres.P.f) + k * (a₂ - a₁)) := by
        have hmem : k * (a₂ - a₁) ∈ maximalIdeal Sh := Ideal.mul_mem_left _ k hcong
        rw [← IsLocalRing.notMem_maximalIdeal]
        intro hcon
        exact (IsLocalRing.notMem_maximalIdeal.mpr h1.isUnit_derivative_f)
          (by simpa using Ideal.sub_mem (maximalIdeal Sh) hcon hmem)
      exact (sub_eq_zero.mp (hunit.mul_left_eq_zero.mp hfac)).symm
    -- Any `R`-algebra map `Φ : T → Sh` with `Φ⁻¹ 𝔪 = Q` sends the generator to a residue `a₀`.
    have keyΦ : ∀ Φ : T →ₐ[R] Sh, (maximalIdeal Sh).comap Φ.toRingHom = Q →
        algebraMap Sh (maximalIdeal Sh).ResidueField (Φ pres.x) = a₀ := by
      intro Φ hΦ
      obtain ⟨r₀, hr₀⟩ := hRQsurj (algebraMap T Q.ResidueField pres.x)
      have hdiff : pres.x - algebraMap R T r₀ ∈ Q := by
        rw [← Ideal.algebraMap_residueField_eq_zero, map_sub, sub_eq_zero,
          ← IsScalarTower.algebraMap_apply R T Q.ResidueField r₀, hr₀]
      have hΦdiff : Φ pres.x - algebraMap R Sh r₀ ∈ maximalIdeal Sh := by
        have : pres.x - algebraMap R T r₀ ∈ (maximalIdeal Sh).comap Φ.toRingHom := by
          rw [hΦ]; exact hdiff
        change Φ (pres.x - algebraMap R T r₀) ∈ maximalIdeal Sh at this
        rwa [map_sub, AlgHom.commutes] at this
      rw [← Ideal.algebraMap_residueField_eq_zero, map_sub, sub_eq_zero,
        ← IsScalarTower.algebraMap_apply R Sh (maximalIdeal Sh).ResidueField r₀] at hΦdiff
      rw [hΦdiff]
      change _ = θ (algebraMap T Q.ResidueField pres.x)
      rw [← hr₀, hθ_R]
    -- Each solution `f` factors through an `R`-algebra map `T → Sh` with `Φ⁻¹ 𝔪 = Q`.
    have lift : ∀ f : A →+* Sh, f.comp (algebraMap R A) = ssh.comp rs →
        (maximalIdeal Sh).comap f = q → ∃ Φ : T →ₐ[R] Sh,
          Φ.toRingHom.comp (algebraMap A T) = f ∧ (maximalIdeal Sh).comap Φ.toRingHom = Q := by
      intro f hlin hcomap
      have hfg : IsUnit (f g) := by
        rw [← IsLocalRing.notMem_maximalIdeal]
        exact fun hcon => hg (hcomap ▸ hcon)
      have hcomp : (Localization.awayLift f g hfg).comp (algebraMap A T) = f :=
        IsLocalization.lift_comp _
      have hcomm : ∀ r : R,
          Localization.awayLift f g hfg (algebraMap R T r) = algebraMap R Sh r := fun r => by
        rw [IsScalarTower.algebraMap_apply R A T r]
        exact (RingHom.congr_fun hcomp (algebraMap R A r)).trans
          (RingHom.congr_fun hlin r)
      set Φ : T →ₐ[R] Sh := { Localization.awayLift f g hfg with commutes' := hcomm } with hΦ
      refine ⟨Φ, hcomp, ?_⟩
      rw [hQ, ← show ((maximalIdeal Sh).comap Φ.toRingHom).comap (algebraMap A T) = q by
        rw [Ideal.comap_comap]
        exact (congrArg (Ideal.comap · (maximalIdeal Sh)) hcomp).trans hcomap]
      exact (IsLocalization.map_under (Submonoid.powers g) T _).symm
    rintro f₁ f₂ ⟨hlin1, hcomap1⟩ ⟨hlin2, hcomap2⟩
    obtain ⟨Φ₁, hΦ₁, hQ₁⟩ := lift f₁ hlin1 hcomap1
    obtain ⟨Φ₂, hΦ₂, hQ₂⟩ := lift f₂ hlin2 hcomap2
    have hΦ : Φ₁ = Φ₂ := algHom_ext_of_standardEtalePresentation pres
      (root_unique _ _ (pres.hasMap.map Φ₁) (pres.hasMap.map Φ₂) (by
        rw [← Ideal.algebraMap_residueField_eq_zero, map_sub, keyΦ Φ₁ hQ₁, keyΦ Φ₂ hQ₂, sub_self]))
    rw [← hΦ₁, ← hΦ₂, hΦ]
  -- ────────────────────────────────────────────────────────────────────────────
  -- ASSEMBLY: `∃!` from existence + uniqueness.
  -- ────────────────────────────────────────────────────────────────────────────
  obtain ⟨f, hf⟩ := existence
  exact ⟨f, hf, fun f' hf' => uniqueness f' f hf' hf⟩

end
