module

public import StacksFrontier.RingTheory.Henselian.EtaleLifting.SolutionsRigidity
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
# Solutions of an étale system over strictly henselian local rings

Let `φ : R → S` be a local homomorphism of strictly henselian local rings, and let
`P_1, …, P_n ∈ R[x_1, …, x_n]` be polynomials such that `R[x_1, …, x_n]/(P_1, …, P_n)` is
étale over `R`. Then the coordinatewise map `R^n → S^n`,
`(h_1, …, h_n) ↦ (φ(h_1), …, φ(h_n))`, restricts to a bijection between the solution set of
the `P_i` over `R` and the solution set of the images `P_i^φ` over `S`. This is Stacks
Tag 04GX, proved here as `bijOn_solutions_of_etale`.

## Conventions

* A *local ring* is a commutative ring with a unique maximal ideal (`IsLocalRing R`); its
  residue field is `IsLocalRing.ResidueField R = R / maximalIdeal R`.
* A *henselian local ring* (`HenselianLocalRing R`) is a local ring satisfying Hensel's
  lemma: every monic `f ∈ R[X]` with a simple root mod the maximal ideal has a unique lift
  to a root of `f` in `R`.
* A *strictly henselian local ring* is a henselian local ring whose residue field is
  separably algebraically closed (`IsSepClosed (IsLocalRing.ResidueField R)`). Mathlib has
  no single bundled predicate, so the two hypotheses are stated separately.
* A *local homomorphism* `φ : R →+* S` (`IsLocalHom φ`) maps non-units to non-units,
  equivalently `φ⁻¹(m_S) = m_R`.
* The *presentation ring* for `P : Fin n → MvPolynomial (Fin n) R` is the quotient
  `MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range P)`, i.e. `R[x_1, …, x_n]/(P_1, …, P_n)`,
  with its canonical `R`-algebra structure. It is *étale* when `Algebra.Etale R A` holds,
  that is, when it is formally étale and of finite presentation.
* The *image of a polynomial under `φ`* is `MvPolynomial.map φ Q`, applying `φ`
  coefficientwise; this is the `P_i^φ` of the statement.
* The *solution sets* use `MvPolynomial.eval`: over `R` it is
  `{r : Fin n → R | ∀ i, MvPolynomial.eval r (P i) = 0}` and over `S` it is
  `{s : Fin n → S | ∀ i, MvPolynomial.eval s (MvPolynomial.map φ (P i)) = 0}`.

Following Stacks, the number of polynomials equals the number of variables (both `n`), so
the presentation is a complete intersection; this is essential for the étale hypothesis to
be meaningful. A point of `R^n` is modelled as `Fin n → R`, and the coordinatewise map
`(h_i) ↦ (φ(h_i))` is `fun r i => φ (r i)`. Finally `Set.BijOn f A B` packages the three
required facts — `f` maps `A` into `B`, `f` is injective on `A`, and `f` restricted to `A`
surjects onto `B` — i.e. `f` induces a bijection between the two solution sets.

## Structure of the proof

`Set.BijOn f solR solS` unpacks into three obligations, `MapsTo`, `InjOn` and `SurjOn`.

* The `MapsTo` half is purely algebraic: a solution over `R` maps to one over `S`, by
  `MvPolynomial.eval_map` and `MvPolynomial.eval₂_comp_left`. It is proved inline in
  `bijOn_solutions_of_etale`.
* `injOn_solutions_of_etale` is the *rigidity* half. Two `R`-solutions that become equal after
  applying `φ` coordinatewise are already equal. This is the uniqueness of henselian/étale
  lifts (Stacks 04GG): an `R`-point of the étale algebra `A` is determined by its
  reduction, and `φ` does not collapse distinct `R`-points.
* `surjOn_solutions_of_etale` is the *existence* half. Every `S`-solution arises from an
  `R`-solution, by strict henselianness of `R` together with the étale structure over the
  separably closed residue field (Stacks 04GG/04GE).

The mathematical depth of Tag 04GX sits in these last two, and both are reformulated in
terms of the canonical correspondence

    solutions of `P` over a ring `T`   ≃   `R`-algebra homs  `A → T`,
    where  `A := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range P)`,

under which the coordinatewise `φ`-map is post-composition with `φ`, viewing `S` as an
`R`-algebra via `φ`.
-/

@[expose] public section

open scoped Classical in
/-- A `kR`-point of a finite product `∏ Ai` of finite separable field extensions of a
separably closed field `kR`, valued in another field `kS`, descends to a `kR`-point valued
in `kR`. (The product hom factors through one projection; over `IsSepClosed kR` the chosen
factor field is `kR` itself.) -/
private theorem pi_field_point_descends
    {kR kS : Type*} [Field kR] [Field kS] [Algebra kR kS] [IsSepClosed kR]
    {I : Type*} [Finite I] (Ai : I → Type*) [∀ i, Field (Ai i)] [∀ i, Algebra kR (Ai i)]
    (hsep : ∀ i, Module.Finite kR (Ai i) ∧ Algebra.IsSeparable kR (Ai i))
    (gP : (Π i, Ai i) →ₐ[kR] kS) :
    ∃ gP' : (Π i, Ai i) →ₐ[kR] kR, ∀ x, algebraMap kR kS (gP' x) = gP x := by
  let := Fintype.ofFinite I
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : I, gP (Pi.single j₀ 1) = 1 := by
    have hidem : ∀ j, gP (Pi.single j 1) * gP (Pi.single j 1) = gP (Pi.single j 1) := by
      intro j; rw [← map_mul]; congr 1; ext k
      by_cases hk : k = j
      · subst hk; simp [Pi.single_eq_same]
      · simp [Pi.single_eq_of_ne hk]
    have hsum : ∑ j, gP (Pi.single j 1) = 1 := by
      rw [← map_sum]
      have : ∑ j : I, (Pi.single j 1 : Π i, Ai i) = 1 := by
        ext k; rw [Finset.sum_apply, Finset.sum_eq_single k]
        · simp [Pi.single_eq_same]
        · intro b _ hb; rw [Pi.single_eq_of_ne (Ne.symm hb)]
        · intro h; exact absurd (Finset.mem_univ k) h
      rw [this, map_one]
    by_contra hcon
    push Not at hcon
    have hall0 : ∀ j, gP (Pi.single j 1) = 0 := by
      intro j
      have hd := hidem j
      have hz : gP (Pi.single j 1) * (gP (Pi.single j 1) - 1) = 0 := by
        ring_nf; linear_combination hd
      rcases mul_eq_zero.mp hz with h | h
      · exact h
      · exact absurd (by linear_combination h) (hcon j)
    rw [show (∑ j, gP (Pi.single j 1)) = ∑ j : I, (0:kS) from
      Finset.sum_congr rfl (fun j _ => hall0 j)] at hsum
    simp at hsum
  have := (hsep j₀).left
  have := (hsep j₀).right
  have hbij : Function.Bijective (algebraMap kR (Ai j₀)) :=
    ⟨(algebraMap kR (Ai j₀)).injective, IsSepClosed.algebraMap_surjective kR (Ai j₀)⟩
  let ej : kR ≃ₐ[kR] Ai j₀ := AlgEquiv.ofBijective (Algebra.ofId kR (Ai j₀)) hbij
  let gP' : (Π i, Ai i) →ₐ[kR] kR := ej.symm.toAlgHom.comp (Pi.evalAlgHom kR Ai j₀)
  refine ⟨gP', ?_⟩
  intro x
  show algebraMap kR kS (ej.symm (x j₀)) = gP x
  have hfac : gP x = gP (Pi.single j₀ (x j₀)) := by
    have hmul : x * Pi.single j₀ 1 = Pi.single j₀ (x j₀) := by
      ext k
      by_cases hk : k = j₀
      · subst hk; simp [Pi.single_eq_same]
      · simp [Pi.single_eq_of_ne hk]
    rw [← hmul, map_mul, hj₀, mul_one]
  rw [hfac]
  set r := ej.symm (x j₀)
  have hxj : x j₀ = algebraMap kR (Ai j₀) r := (ej.apply_symm_apply (x j₀)).symm
  rw [hxj]
  have hsmul : (Pi.single j₀ (algebraMap kR (Ai j₀) r) : Π i, Ai i) = r • Pi.single j₀ 1 := by
    ext k
    by_cases hk : k = j₀
    · subst hk; simp [Pi.single_eq_same, Algebra.algebraMap_eq_smul_one]
    · simp [Pi.single_eq_of_ne hk]
  rw [hsmul, map_smul, hj₀, Algebra.algebraMap_eq_smul_one r]

open scoped Classical in
/-- **Étale point descent over a separably closed field (Stacks 00U3).**
If `B` is étale over a separably closed field `kR` and `kS` is any `kR`-algebra (field),
then every `kR`-algebra hom `B → kS` factors through `algebraMap kR kS`, i.e. descends to a
`kR`-algebra hom `B → kR`. (Étale over `kR` means `B ≅ ∏ Ai` with each `Ai` a finite
separable extension; over `IsSepClosed kR` these are all `kR`, so `kR`-points and `kS`-points
coincide.) -/
private theorem etale_field_point_descends
    {kR kS : Type*} [Field kR] [Field kS] [Algebra kR kS] [IsSepClosed kR]
    (B : Type*) [CommRing B] [Algebra kR B] [Algebra.Etale kR B]
    (g : B →ₐ[kR] kS) :
    ∃ g' : B →ₐ[kR] kR, ∀ x, algebraMap kR kS (g' x) = g x := by
  obtain ⟨I, hI, Ai, hfield, halg, e, hsep⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod kR B).mp inferInstance
  let : Fintype I := Fintype.ofFinite I
  let : ∀ i, Field (Ai i) := hfield
  let : ∀ i, Algebra kR (Ai i) := halg
  obtain ⟨gP', hgP'⟩ := pi_field_point_descends Ai hsep (g.comp e.symm.toAlgHom)
  exact ⟨gP'.comp e.toAlgHom, fun x => by simpa using hgP' (e x)⟩

/-- `aeval` is `eval` of the polynomial mapped along `algebraMap`. -/
private lemma aeval_eq_eval_map {R T : Type*} [CommRing R] [CommRing T] [Algebra R T] {n : ℕ}
    (s : Fin n → T) (p : MvPolynomial (Fin n) R) :
    MvPolynomial.aeval s p = MvPolynomial.eval s (MvPolynomial.map (algebraMap R T) p) := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval_map]

/-- Roots `s` of the `P i` in an `R`-algebra `T` give an `R`-algebra hom `R[x]/(P) → T`
sending `x_i` to `s i`. -/
private lemma exists_algHom_quotient_of_aeval_eq_zero {R T : Type*} [CommRing R] [CommRing T]
    [Algebra R T] {n : ℕ} (P : Fin n → MvPolynomial (Fin n) R) (s : Fin n → T)
    (hs : ∀ i, MvPolynomial.aeval s (P i) = 0) :
    ∃ g : MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range P) →ₐ[R] T,
      ∀ i, g (Ideal.Quotient.mk _ (MvPolynomial.X i)) = s i := by
  have hv : Ideal.span (Set.range P) ≤ RingHom.ker (MvPolynomial.aeval (R := R) s) := by
    rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩; exact hs i
  have hv' : ∀ x ∈ Ideal.span (Set.range P), MvPolynomial.aeval (R := R) s x = 0 :=
    fun x hx => RingHom.mem_ker.1 (hv hx)
  refine ⟨Ideal.Quotient.liftₐ _ (MvPolynomial.aeval s)
    (by intro x hx; exact hv' x hx), fun i => ?_⟩
  exact MvPolynomial.aeval_X s i

/-- A root `r` of `q` maps to a root `f ∘ r` of `map f q`. -/
private lemma eval_map_comp_eq_zero {R S : Type*} [CommRing R] [CommRing S] {σ : Type*}
    (f : R →+* S) (q : MvPolynomial σ R) (r : σ → R) (h : MvPolynomial.eval r q = 0) :
    MvPolynomial.eval (fun j => f (r j)) (MvPolynomial.map f q) = 0 := by
  have := MvPolynomial.map_eval f r q
  rw [h, map_zero] at this
  exact this.symm

/-- The images of the variables under an `R`-algebra hom `R[x]/(P) → T` are roots of the
`P i`. -/
private lemma aeval_apply_mk_X_eq_zero {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    {n : ℕ} (P : Fin n → MvPolynomial (Fin n) R)
    (t : MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range P) →ₐ[R] T) (i : Fin n) :
    MvPolynomial.aeval (fun j => t (Ideal.Quotient.mk _ (MvPolynomial.X j))) (P i) = 0 := by
  refine (AlgHom.congr_fun (MvPolynomial.aeval_unique
    (t.comp (Ideal.Quotient.mkₐ R (Ideal.span (Set.range P))))) (P i)).symm.trans ?_
  have hz : Ideal.Quotient.mk (Ideal.span (Set.range P)) (P i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)
  change t (Ideal.Quotient.mk _ (P i)) = 0
  rw [hz, map_zero]

set_option backward.isDefEq.respectTransparency false in
-- needed: `exists_root_residueField_map_eq` rewrites through the reduced system's residue maps,
-- which match only with defeq unfolding past the default transparency
open MvPolynomial TensorProduct in
/-- **Residue descent.**
A residue solution `sbar : Fin n → k_S` of the reduced system descends to a
residue solution `rbar : Fin n → k_R` of the reduced system over `k_R`, matching
under `k_R → k_S`.

Mathematical content (Stacks 00U3 over separably closed fields): the special
fibre `A ⊗_R k_R` is étale over the separably closed field `k_R`, hence
(`Algebra.Etale.iff_exists_algEquiv_prod` + `IsSepClosed`) a finite product of
copies of `k_R`; its `k_R`-points are the projections (the finite index set `I`).
The same holds for `A ⊗_R k_S` over `k_S` with the *same* index set `I` (base
change along the separably-closed-field extension `k_R → k_S`). Hence every
`k_S`-point of the special fibre is the image of a (unique) `k_R`-point. -/
theorem exists_root_residueField_map_eq
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [IsSepClosed (IsLocalRing.ResidueField R)] [IsSepClosed (IsLocalRing.ResidueField S)]
    (φ : R →+* S) [IsLocalHom φ]
    (n : ℕ) (P : Fin n → MvPolynomial (Fin n) R)
    [Algebra.Etale R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range P))]
    (sbar : Fin n → IsLocalRing.ResidueField S)
    (hsbar : ∀ i, MvPolynomial.eval sbar
      (MvPolynomial.map ((IsLocalRing.ResidueField.map φ).comp (IsLocalRing.residue R)) (P i)) = 0)
          :
    ∃ rbar : Fin n → IsLocalRing.ResidueField R,
      (∀ i, MvPolynomial.eval rbar (MvPolynomial.map (IsLocalRing.residue R) (P i)) = 0) ∧
      (∀ i, IsLocalRing.ResidueField.map φ (rbar i) = sbar i) := by
  -- Set A = R[x]/(P), kR = k(R), kS = k(S), ψ = ResidueField.map φ. View kS as a kR-algebra
  -- via ψ and as an R-algebra via residue S ∘ φ = ψ ∘ residue R. The base change
  -- B := kR ⊗[R] A is étale over kR. `sbar` (a solution of the descended system) yields an
  -- R-algebra hom fS : A → kS, hence a kR-algebra hom gS : B → kS. Étale-over-sep-closed-kR
  -- descent (`etale_field_point_descends`) produces gR : B → kR with ψ ∘ gR = gS. Reading off
  -- `rbar i := gR (1 ⊗ mk(Xᵢ))` gives the required residue solution matching `sbar` under ψ.
  set A := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range P) with hA
  let algKSkR : Algebra (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    (IsLocalRing.ResidueField.map φ).toAlgebra
  let algKSR : Algebra R (IsLocalRing.ResidueField S) :=
    ((IsLocalRing.residue S).comp φ).toAlgebra
  have tower : IsScalarTower R (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalRing.ResidueField.map_residue φ x).symm
  have etB : Algebra.Etale (IsLocalRing.ResidueField R) (TensorProduct R (IsLocalRing.ResidueField
      R) A) :=
    Algebra.Etale.baseChange R A (IsLocalRing.ResidueField R)
  have towerB : IsScalarTower R (IsLocalRing.ResidueField R) (TensorProduct R
      (IsLocalRing.ResidueField R) A) :=
    inferInstance
  obtain ⟨fS, hfS⟩ := exists_algHom_quotient_of_aeval_eq_zero P sbar fun i => by
    rw [aeval_eq_eval_map]; exact hsbar i
  let gS : TensorProduct R (IsLocalRing.ResidueField R) A →ₐ[IsLocalRing.ResidueField R]
      IsLocalRing.ResidueField S :=
    Algebra.TensorProduct.lift
      (Algebra.ofId (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)) fS
      (fun _ _ => mul_comm _ _)
  obtain ⟨gR, hgR⟩ := etale_field_point_descends (TensorProduct R (IsLocalRing.ResidueField R) A) gS
  let incR : A →ₐ[R] TensorProduct R (IsLocalRing.ResidueField R) A :=
      Algebra.TensorProduct.includeRight
  let t : A →ₐ[R] IsLocalRing.ResidueField R := (gR.restrictScalars R).comp incR
  let mk := Ideal.Quotient.mk (Ideal.span (Set.range P))
  refine ⟨fun i => t (mk (MvPolynomial.X i)), fun i => ?_, fun i => ?_⟩
  · have := aeval_apply_mk_X_eq_zero P t i
    rwa [aeval_eq_eval_map] at this
  · change algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
      (gR (incR (mk (MvPolynomial.X i)))) = sbar i
    rw [hgR, ← hfS i]
    change gS (Algebra.TensorProduct.includeRight (mk (MvPolynomial.X i))) = _
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.lift_tmul]
    simp; rfl

/-- `residue` commutes with univariate `aeval`. -/
private lemma residue_aeval {R : Type*} [CommRing R] [IsLocalRing R] (a : R) (p : Polynomial R) :
    IsLocalRing.residue R (Polynomial.aeval a p)
      = Polynomial.aeval (IsLocalRing.residue R a) p := by
  simp only [Polynomial.aeval_def]; rw [Polynomial.hom_eval₂]; rfl

/-- In a local ring, an element whose residue is a unit is itself a unit. -/
private lemma isUnit_of_residue {R : Type*} [CommRing R] [IsLocalRing R] (a : R)
    (h : IsUnit (IsLocalRing.residue R a)) : IsUnit a := by
  by_contra hu
  have hmem : a ∈ IsLocalRing.maximalIdeal R := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact hu
  rw [← Ideal.Quotient.eq_zero_iff_mem] at hmem
  exact h.ne_zero hmem

/-- **Henselian section of a standard-étale pair.** A `StandardEtalePair R` over a
henselian local ring `R` admits an `R`-point lifting any given residue-field point.
This is the univariate henselian content (the simple-root lift of `HenselianLocalRing`). -/
@[ega "IV 18.5.11" "(f), special case", sga "3 X 4.5" "(f), special case"]
private theorem hensel_section {R : Type*} [CommRing R] [HenselianLocalRing R]
    (P : StandardEtalePair R) (x₀ : IsLocalRing.ResidueField R) (hx : P.HasMap x₀) :
    ∃ a : R, P.HasMap a ∧ IsLocalRing.residue R a = x₀ := by
  obtain ⟨hf0, hgu⟩ := hx
  have hderiv : Polynomial.aeval x₀ (Polynomial.derivative P.f) ≠ 0 := by
    obtain ⟨p₁, p₂, k, hcond⟩ := P.cond
    intro hd
    have hz : Polynomial.aeval x₀ (P.g ^ k) = 0 := by rw [← hcond]; simp [hd, hf0]
    rw [map_pow] at hz; exact (hgu.pow k).ne_zero hz
  have H := HenselianLocalRing.TFAE R
  have hb := (H.out 1 2).mp (by infer_instance)
  obtain ⟨a, haroot, harez⟩ := hb P.f P.monic_f x₀ hf0 hderiv
  refine ⟨a, ⟨haroot, ?_⟩, harez⟩
  apply isUnit_of_residue; rw [residue_aeval, harez]; exact hgu

/-- Extend an `R`-algebra hom `g : A → K` to the localization `A_f` when `g f` is a unit. -/
private noncomputable def liftAwayHom {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {K : Type*} [CommRing K] [Algebra R K] (g : A →ₐ[R] K) (f : A) (hf : IsUnit (g f)) :
    (Localization.Away f) →ₐ[R] K :=
  IsLocalization.liftAlgHom (M := Submonoid.powers f) (f := g) (by
    rintro ⟨y, k, rfl⟩; simpa using hf.pow k)

private lemma liftAwayHom_comp {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {K : Type*} [CommRing K] [Algebra R K] (g : A →ₐ[R] K) (f : A) (hf : IsUnit (g f)) (a : A) :
    liftAwayHom g f hf (algebraMap A (Localization.Away f) a) = g a := by
  unfold liftAwayHom; rw [IsLocalization.liftAlgHom_apply]; exact IsLocalization.lift_eq _ _

/-- **Abstract étale lift over a henselian local ring (Stacks 04GG, existence).**
An étale, finitely-presented `R`-algebra `A` over a henselian local ring `R`, equipped
with a residue-field point `g : A →ₐ[R] k_R`, admits an honest `R`-point `s : A →ₐ[R] R`
whose reduction is `g`. The proof reduces, via the local structure of étale morphisms
(`Algebra.IsEtaleAt.exists_isStandardEtale`), to a standard-étale localization and then
applies the univariate henselian section `hensel_section`. -/
@[ega "IV 18.5.11" "special case", sga "3 X 4.5" "special case"]
private theorem etale_kR_point_lifts
    {R A : Type*} [CommRing R] [HenselianLocalRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] [Algebra.Etale R A]
    (g : A →ₐ[R] IsLocalRing.ResidueField R) :
    ∃ s : A →ₐ[R] R, ∀ x, IsLocalRing.residue R (s x) = g x := by
  set Q : Ideal A := RingHom.ker g.toRingHom with hQ
  have : Q.IsPrime := by rw [hQ]; exact RingHom.ker_isPrime _
  have : Algebra.IsEtaleAt R Q := inferInstance
  obtain ⟨f, hfQ, hSE⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) Q
  have hgf : IsUnit (g f) := by
    rw [isUnit_iff_ne_zero]; intro h0; apply hfQ; rw [hQ, RingHom.mem_ker]; exact h0
  set gf : (Localization.Away f) →ₐ[R] IsLocalRing.ResidueField R := liftAwayHom g f hgf with hgfdef
  obtain ⟨pres⟩ := hSE.nonempty_standardEtalePresentation
  set xbar : IsLocalRing.ResidueField R := gf pres.x with hxbar
  have hxmap : pres.P.HasMap xbar := pres.hasMap.map gf
  obtain ⟨a, hxa, harez⟩ := hensel_section pres.P xbar hxmap
  set lifta : pres.P.Ring →ₐ[R] R := pres.P.lift a hxa with hlifta
  set sf : (Localization.Away f) →ₐ[R] R := lifta.comp pres.equivRing.toAlgHom with hsf
  set s : A →ₐ[R] R := sf.comp (IsScalarTower.toAlgHom R A (Localization.Away f)) with hsdef
  refine ⟨s, ?_⟩
  set resAlg : R →ₐ[R] IsLocalRing.ResidueField R := Algebra.ofId R _ with hresAlg
  have hkey : resAlg.comp sf = gf := by
    apply pres.hom_ext
    show resAlg (sf pres.x) = gf pres.x
    have hsfx : sf pres.x = a := by
      rw [hsf]; change lifta (pres.equivRing pres.x) = a
      rw [pres.equivRing_x, hlifta, StandardEtalePair.lift_X]
    rw [hsfx, ← hxbar]; change IsLocalRing.residue R a = xbar; exact harez
  intro x
  show IsLocalRing.residue R (s x) = g x
  have h1 : IsLocalRing.residue R (s x) = resAlg (s x) := rfl
  rw [h1, hsdef]
  show resAlg (sf (algebraMap A (Localization.Away f) x)) = g x
  have hc := AlgHom.congr_fun hkey (algebraMap A (Localization.Away f) x)
  simp only [AlgHom.comp_apply] at hc
  rw [hc, hgfdef, liftAwayHom_comp]

-- needed: `exists_eval_eq_zero_and_residue_eq` rewrites through the same residue-system encoding
-- as `exists_root_residueField_map_eq`, needing defeq past the default transparency
set_option backward.isDefEq.respectTransparency false in
open MvPolynomial in
/-- **The multivariate étale lift (Stacks 04GG, existence half).**
Over a strictly henselian local ring `R` — henselian with separably closed residue field —
any residue solution `rbar : Fin n → k_R` of the reduced étale system lifts to an honest
`R`-solution `r` with `residue R (r i) = rbar i`.

Equivalently: for `A` étale over a henselian local ring `R` the reduction map
`Hom_R(A, R) → Hom_R(A, k_R)` is surjective. The residue solution `rbar` is packaged as an
`R`-algebra hom `A → k_R`, and `etale_kR_point_lifts` lifts it to an `R`-point of `A` by
reducing, via the local structure of étale morphisms, to a standard-étale localization on
which the univariate henselian section `hensel_section` applies. -/
@[ega "IV 18.5.11" "b), special case", sga "3 X 4.5" "special case"]
theorem exists_eval_eq_zero_and_residue_eq
    {R : Type*} [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    (n : ℕ) (P : Fin n → MvPolynomial (Fin n) R)
    [Algebra.Etale R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range P))]
    (rbar : Fin n → IsLocalRing.ResidueField R)
    (hrbar : ∀ i, MvPolynomial.eval rbar (MvPolynomial.map (IsLocalRing.residue R) (P i)) = 0) :
    ∃ r : Fin n → R, (∀ i, MvPolynomial.eval r (P i) = 0) ∧
      (∀ i, IsLocalRing.residue R (r i) = rbar i) := by
  obtain ⟨g, hgX⟩ := exists_algHom_quotient_of_aeval_eq_zero P rbar fun i => by
    rw [aeval_eq_eval_map]; exact hrbar i
  obtain ⟨s, hsg⟩ := etale_kR_point_lifts g
  refine ⟨fun i => s (Ideal.Quotient.mk _ (MvPolynomial.X i)), fun i => ?_, fun i => ?_⟩
  · have := aeval_apply_mk_X_eq_zero P s i
    rwa [aeval_eq_eval_map, Algebra.algebraMap_self, MvPolynomial.map_id] at this
  · rw [hsg, hgX i]

open MvPolynomial in
/-- **Existence / `SurjOn` half of Tag 04GX.**
Every solution `s` of `map φ (P i)` over `S` is `φ ∘ r` for some solution `r` of
`P` over `R`.

Proof (Stacks 04GX, existence half), in four steps:
1. Reduce `s` mod `𝔪_S` to `sbar : Fin n → k_S` (a residue solution of the
   reduced system); the residue square `(ResidueField.map φ) ∘ residue R
   = residue S ∘ φ` makes this a solution of the descended system.
2. `exists_root_residueField_map_eq`: descend `sbar` to `rbar : Fin n → k_R` matching
   under `k_R → k_S` (étale-over-sep-closed-field split, Stacks 00U3).
3. `exists_eval_eq_zero_and_residue_eq`: lift `rbar` to an honest `R`-solution `r` with
   `residue R (r i) = rbar i` (strictly henselian lift, Stacks 04GG — the deep
   core).
4. `φ ∘ r` and `s` are both `S`-solutions of `map φ P` with the same residue
   `sbar` mod `𝔪_S`, hence congruent mod `𝔪_S`; `eq_of_sub_mem_maximalIdeal_of_etale_map`
   then gives `φ ∘ r = s`. -/
theorem surjOn_solutions_of_etale
    {R S : Type*} [CommRing R] [CommRing S]
    [HenselianLocalRing R] [HenselianLocalRing S]
    [IsSepClosed (IsLocalRing.ResidueField R)] [IsSepClosed (IsLocalRing.ResidueField S)]
    (φ : R →+* S) (hφ : IsLocalHom φ)
    (n : ℕ) (P : Fin n → MvPolynomial (Fin n) R)
    [Algebra.Etale R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range P))] :
    Set.SurjOn (fun r : Fin n → R => (fun i => φ (r i) : Fin n → S))
      {r : Fin n → R | ∀ i, MvPolynomial.eval r (P i) = 0}
      {s : Fin n → S | ∀ i, MvPolynomial.eval s (MvPolynomial.map φ (P i)) = 0} := by
  intro s hs
  simp only [Set.mem_ofPred_eq] at hs
  -- residue of s
  set sbar : Fin n → IsLocalRing.ResidueField S :=
    fun i => IsLocalRing.residue S (s i) with hsbar_def
  -- the residue square commutes: (ResidueField.map φ).comp (residue R) = (residue S).comp φ
  have hsquare : (IsLocalRing.ResidueField.map φ).comp (IsLocalRing.residue R)
      = (IsLocalRing.residue S).comp φ := by
    ext x
    simp [IsLocalRing.ResidueField.map_residue]
  -- sbar solves the descended system
  have hsbar : ∀ i, MvPolynomial.eval sbar
      (MvPolynomial.map ((IsLocalRing.ResidueField.map φ).comp (IsLocalRing.residue R)) (P i))
        = 0 := by
    intro i
    rw [hsquare, ← MvPolynomial.map_map]
    exact eval_map_comp_eq_zero (IsLocalRing.residue S) _ s (hs i)
  -- descend to a k_R-point
  obtain ⟨rbar, hrbar_sol, hrbar_match⟩ := exists_root_residueField_map_eq φ n P sbar hsbar
  -- lift to an R-point
  obtain ⟨r, hr_sol, hr_match⟩ := exists_eval_eq_zero_and_residue_eq n P rbar hrbar_sol
  refine ⟨r, hr_sol, ?_⟩
  -- show φ ∘ r = s via uniqueness over S
  have hφr_sol := fun i => eval_map_comp_eq_zero φ (P i) r (hr_sol i)
  have hcong : ∀ i, (fun i => φ (r i)) i - s i ∈ IsLocalRing.maximalIdeal S := by
    intro i
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    show (IsLocalRing.residue S) (φ (r i) - s i) = 0
    rw [map_sub]
    have e1 : (IsLocalRing.residue S) (φ (r i)) = sbar i := by
      have : (IsLocalRing.residue S) (φ (r i))
          = IsLocalRing.ResidueField.map φ (IsLocalRing.residue R (r i)) := by
        rw [IsLocalRing.ResidueField.map_residue]
      rw [this, hr_match i, hrbar_match i]
    rw [e1]
    show sbar i - (IsLocalRing.residue S) (s i) = 0
    rw [hsbar_def]
    simp
  exact eq_of_sub_mem_maximalIdeal_of_etale_map φ n P (fun i => φ (r i)) s hφr_sol hs hcong

open MvPolynomial in
/-- **Stacks Tag 04GX.**
Let `φ : R → S` be a local homomorphism of strictly henselian local rings and let
`P_1, …, P_n ∈ R[x_1, …, x_n]` be polynomials such that `R[x_1, …, x_n]/(P_1, …, P_n)` is
étale over `R`. Then the coordinatewise map `r ↦ (fun i => φ (r i))` induces a bijection
between the solutions of the `P_i` over `R` and the solutions of their images `P_i^φ` over
`S`. -/
@[stacks 04GX]
theorem bijOn_solutions_of_etale
    {R S : Type*} [CommRing R] [CommRing S]
    [HenselianLocalRing R] [HenselianLocalRing S]
    [IsSepClosed (IsLocalRing.ResidueField R)] [IsSepClosed (IsLocalRing.ResidueField S)]
    (φ : R →+* S) (hφ : IsLocalHom φ)
    (n : ℕ) (P : Fin n → MvPolynomial (Fin n) R)
    [Algebra.Etale R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range P))] :
    Set.BijOn (fun r : Fin n → R => (fun i => φ (r i) : Fin n → S))
      {r : Fin n → R | ∀ i, MvPolynomial.eval r (P i) = 0}
      {s : Fin n → S | ∀ i, MvPolynomial.eval s (MvPolynomial.map φ (P i)) = 0} := by
  refine ⟨?_, ?_, ?_⟩
  · -- MapsTo: purely algebraic, `eval (φ∘r) (map φ Q) = φ (eval r Q)`.
    exact fun r hr i => eval_map_comp_eq_zero φ (P i) r (hr i)
  · -- InjOn: rigidity half, delegated.
    exact injOn_solutions_of_etale φ n P
  · -- SurjOn: existence half, delegated.
    exact surjOn_solutions_of_etale φ hφ n P

end
