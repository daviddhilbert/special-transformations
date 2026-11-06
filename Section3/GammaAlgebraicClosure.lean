import Section3.GammaFullDescent

/- Algebraic closure over genuine real/Gamma parameter bases. Finite
real support and finite algebraic tuple covers adapt the checked ordinary
AlgebraicTransitivity proof; full-code Gamma relations retain the original
imaginary base throughout. No saturation, size or characteristic premise. -/

/- Component: GammaAlgebraicParameters -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem DefinableOverBase.finite_real_support {B : Base (M := M)} {n : ℕ}
    {sn : Fin n → SortTag} {U : Set (Fin n → M)} (hU : DefinableOverBase B sn U) :
    ∃ F : Finset M, (F : Set M) ⊆ B.real ∧ DefinableOverBase ⟨F,B.gamma⟩ sn U := by
  obtain ⟨k,γ,hγ,Q,hQU⟩ := hU
  obtain ⟨F,hFB,R,hRQ⟩ := Q.finite_real_support
  refine ⟨F,hFB,k,γ,hγ,R,?_⟩
  have he : R.fibre γ = Q.fibre γ :=
    congrArg (fun V : Set ((Fin k → M) × (Fin n → M)) =>
      {z | (rawTuple (representatives γ),z) ∈ V}) hRQ
  exact he.trans hQU

theorem AlgebraicAtBase.sorted {B : Base (M := M)} {σ : SortTag} {b : M}
    (hb : AlgebraicAtBase B σ b) : sortEval σ b := by
  obtain ⟨W,hW,hWf,hbW⟩ := hb
  exact hW.proper b hbW

/-- A finite tuple of same-base algebraic real elements lies in a finite
same-base definable tuple set. No conjugate or representative is named. -/
theorem algebraic_tuple_finite_cover (B : Base (M := M)) {n : ℕ}
    (sn : Fin n → SortTag) (a : Fin n → M) (ha : ∀ i, AlgebraicAtBase B (sn i) (a i)) :
    ∃ A : Set (Fin n → M), DefinableOverBase B sn A ∧ A.Finite ∧ a ∈ A := by
  choose W hWd hWf haW using ha
  let A : Set (Fin n → M) := {z | ∀ i, z i ∈ W i}
  have hA := DefinableOverBase.finite_iInter (Finset.univ : Finset (Fin n))
    (fun i => {z | z i ∈ W i ∧ z ∈ sortedUniverse sn})
    (fun i _ => (hWd i).preimage_real sn (fun _ : Fin 1 => i))
  have hsort (z : Fin n → M) (hz : z ∈ A) : z ∈ sortedUniverse sn :=
    fun i => (hWd i).proper (z i) (hz i)
  refine ⟨A,?_,Set.Finite.pi' hWf,haW⟩
  convert hA using 1
  ext z
  change (∀ i, z i ∈ W i) ↔ z ∈ sortedUniverse sn ∧
    ∀ i ∈ Finset.univ, z i ∈ W i ∧ z ∈ sortedUniverse sn
  exact ⟨fun hz => ⟨hsort z hz,fun i _ => ⟨hz i,hsort z hz⟩⟩,fun hz i => (hz.2 i (Finset.mem_univ i)).1⟩

/-- Only finitely many algebraic real names are needed. Gamma-algebraic
names are definable by their proved order property and are eliminated as
entire value fibres over the original B. -/
theorem DefinableOverBase.promote_algebraic_parameters {B C : Base (M := M)} {m : ℕ}
    {sm : Fin m → SortTag} {U : Set (Fin m → M)} (hU : DefinableOverBase C sm U)
    (hr : ∀ c ∈ C.real, ∃ σ, AlgebraicAtBase B σ c)
    (hγ : ∀ γ ∈ C.gamma, GammaAlgebraicAtBase B γ) :
    ∃ n, ∃ sn : Fin n → SortTag, ∃ a : Fin n → M,
      (∀ i, AlgebraicAtBase B (sn i) (a i)) ∧
      DefinableOverBase ⟨B.real ∪ Set.range a,B.gamma⟩ sm U := by
  obtain ⟨F,hFC,hUF⟩ := hU.finite_real_support
  let e : F ≃ Fin F.card := F.equivFin
  let a : Fin F.card → M := fun i => (e.symm i).val
  have haC (i : Fin F.card) : a i ∈ C.real := hFC (e.symm i).property
  choose sn hsn using fun i => hr (a i) (haC i)
  refine ⟨F.card,sn,a,hsn,?_⟩
  apply hUF.eliminate_definable_params
  · intro c hc
    apply (subset_closureBase (⟨B.real ∪ Set.range a,B.gamma⟩ : Base (M := M))).1
    right
    refine ⟨e ⟨c,hc⟩,?_⟩
    exact congrArg Subtype.val (e.symm_apply_apply ⟨c,hc⟩)
  · intro γ hγC
    exact ((gamma_algebraic_iff_definable_base B γ).mp (hγ γ hγC)).mono
      Set.subset_union_left (Set.Subset.refl _)

end SpecialTransformations.Section3.GammaParameters

/- Component: GammaAlgebraicTransitivity -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

def baseRelationImage (A : Set (Fin n → M)) (R : Set ((Fin n → M) × M)) : Set M :=
  {t | ∃ a ∈ A, (a,t) ∈ R}

theorem baseRelationImage_definable (B : Base (M := M))
    (sn : Fin n → SortTag) (A : Set (Fin n → M)) (hA : DefinableOverBase B sn A)
    (σ : SortTag) (R : Set ((Fin n → M) × M))
    (hR : DefinableOverBase B (Fin.lastCases σ sn) {z | (Fin.init z,z (Fin.last n)) ∈ R}) :
    DefinableAtBase B σ (baseRelationImage A R) := by
  let sm : Fin (n+1) → SortTag := Fin.lastCases σ sn
  have hA' := hA.preimage_real sm Fin.castSucc
  have him := (hA'.inter hR).image_real (fun _ : Fin 1 => Fin.last n)
  have hsm : sm ∘ (fun _ : Fin 1 => Fin.last n) = (fun _ : Fin 1 => σ) := by
    funext i
    simp only [sm,Function.comp_apply,Fin.lastCases_last]
  rw [hsm] at him
  change DefinableOverBase B (fun _ : Fin 1 => σ) {z | z 0 ∈ baseRelationImage A R}
  convert him using 1
  all_goals try rfl
  ext z
  constructor
  · rintro ⟨a,ha,ht⟩
    let w : Fin (n+1) → M := Fin.snoc a (z 0)
    have hwR : (Fin.init w,w (Fin.last n)) ∈ R := by
      simpa only [w,Fin.init_snoc,Fin.snoc_last] using ht
    refine ⟨w,⟨⟨?_,hR.proper w hwR⟩,hwR⟩,?_⟩
    · have hi : w ∘ Fin.castSucc = a := by
        funext i
        simp only [w,Function.comp_apply,Fin.snoc_castSucc]
      rwa [hi]
    · funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst i
      change w (Fin.last n) = z 0
      simp only [w,Fin.snoc_last]
  · rintro ⟨w,⟨⟨ha,_⟩,ht⟩,he⟩
    have hl : w (Fin.last n) = z 0 := congrFun he 0
    refine ⟨Fin.init w,ha,?_⟩
    rwa [← hl]

theorem baseRelationImage_finite (A : Set (Fin n → M)) (hA : A.Finite)
    (R : Set ((Fin n → M) × M)) (hR : ∀ a, {t | (a,t) ∈ R}.Finite) :
    (baseRelationImage A R).Finite := by
  letI : Finite A := hA.to_subtype
  have hh := Set.finite_iUnion (fun a : A => hR a.val)
  apply hh.subset
  rintro t ⟨a,ha,ht⟩
  exact Set.mem_iUnion.mpr ⟨⟨a,ha⟩,ht⟩

theorem GoodBaseGammaRelation.finite_image (B : Base (M := M))
    (sn : Fin n → SortTag) (R : GoodBaseGammaRelation B n sn)
    (A : Set (Fin n → M)) (hA : DefinableOverBase B sn A) (hAfin : A.Finite) :
    let W : Set (Values.Gamma (M := M)) := {γ | ∃ a ∈ A, γ ∈ gammaRow R.carrier a}
    GammaDefinableOverBase B W ∧ W.Finite := by
  intro W
  have he : Values.gammaPullback W = baseRelationImage A R.carrier := by
    ext t
    constructor
    · intro ht
      have htNZ : NonzeroRV t := ⟨ht.1,ht.2.1⟩
      let c : Code (M := M) := ⟨⟨t,htNZ.1⟩,htNZ.2⟩
      obtain ⟨a,ha,hac⟩ := (mem_gammaPullback_code W c).mp ht
      exact ⟨a,ha,(R.mem_raw_iff B sn a c).mpr hac⟩
    · rintro ⟨a,ha,ht⟩
      have htNZ := R.proper a t ht
      let c : Code (M := M) := ⟨⟨t,htNZ.1⟩,htNZ.2⟩
      apply (mem_gammaPullback_code W c).mpr
      exact ⟨a,ha,(R.mem_raw_iff B sn a c).mp ht⟩
  refine ⟨?_,?_⟩
  · change DefinableAtBase B .rv (Values.gammaPullback W)
    rw [he]
    exact baseRelationImage_definable B sn A hA .rv R.carrier R.definable
  · letI : Finite A := hAfin.to_subtype
    have hh := Set.finite_iUnion (fun a : A => R.finite a.val)
    apply hh.subset
    rintro γ ⟨a,ha,hγ⟩
    exact Set.mem_iUnion.mpr ⟨⟨a,ha⟩,hγ⟩

/-- Transitivity of real algebraic closure over arbitrary real/Gamma
bases. The finite-row cut and finite algebraic tuple cover are proved data;
no saturation, cardinality bound or extra representative is assumed. -/
theorem AlgebraicAtBase.eliminate_algebraic_params {B C : Base (M := M)}
    {σ : SortTag} {b : M} (hb : AlgebraicAtBase C σ b)
    (hr : ∀ c ∈ C.real, ∃ τ, AlgebraicAtBase B τ c)
    (hγ : ∀ γ ∈ C.gamma, GammaAlgebraicAtBase B γ) : AlgebraicAtBase B σ b := by
  obtain ⟨T,hTd,hTf,hbT⟩ := hb
  obtain ⟨n,sn,a,ha,hTD⟩ := DefinableOverBase.promote_algebraic_parameters hTd hr hγ
  have hbD : AlgebraicAtBase ⟨B.real ∪ Set.range a,B.gamma⟩ σ b := ⟨T,hTD,hTf,hbT⟩
  obtain ⟨R,haR⟩ := good_base_relation_of_algebraic B sn a (fun i => (ha i).sorted) σ b hbD
  obtain ⟨A,hAd,hAf,haA⟩ := algebraic_tuple_finite_cover B sn a ha
  exact ⟨baseRelationImage A R.carrier,baseRelationImage_definable B sn A hAd σ R.carrier R.definable,
    baseRelationImage_finite A hAf R.carrier R.finite,a,haA,haR⟩

/-- Transitivity in the actual ordered Gamma sort, over arbitrary
real/Gamma bases, with no saturation or cardinality assumptions. -/
theorem GammaAlgebraicAtBase.eliminate_algebraic_params {B C : Base (M := M)}
    {δ : Values.Gamma (M := M)} (hδ : GammaAlgebraicAtBase C δ)
    (hr : ∀ c ∈ C.real, ∃ τ, AlgebraicAtBase B τ c)
    (hγ : ∀ γ ∈ C.gamma, GammaAlgebraicAtBase B γ) : GammaAlgebraicAtBase B δ := by
  obtain ⟨W,hWd,hWf,hδW⟩ := hδ
  obtain ⟨n,sn,a,ha,hWD⟩ := DefinableOverBase.promote_algebraic_parameters hWd hr hγ
  have hδD : GammaAlgebraicAtBase ⟨B.real ∪ Set.range a,B.gamma⟩ δ := ⟨W,hWD,hWf,hδW⟩
  obtain ⟨R,haR⟩ := good_base_gamma_relation_of_algebraic B sn a (fun i => (ha i).sorted) δ hδD
  obtain ⟨A,hAd,hAf,haA⟩ := algebraic_tuple_finite_cover B sn a ha
  obtain ⟨hId,hIf⟩ := R.finite_image B sn A hAd hAf
  exact ⟨{γ | ∃ a ∈ A, γ ∈ gammaRow R.carrier a},hId,hIf,a,haA,haR⟩

end SpecialTransformations.Section3.GammaParameters

/- Component: GammaAlgebraicClosure -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def algebraicClosureBase (B : Base (M := M)) : Base (M := M) where
  real := {b | ∃ σ, AlgebraicAtBase B σ b}
  gamma := {γ | GammaAlgebraicAtBase B γ}

theorem subset_algebraicClosureBase (B : Base (M := M)) :
    B.real ⊆ (algebraicClosureBase B).real ∧ B.gamma ⊆ (algebraicClosureBase B).gamma := by
  constructor
  · intro b hb
    obtain ⟨σ,hbD⟩ := (subset_closureBase B).1 hb
    exact ⟨σ,{b},hbD,Set.finite_singleton b,Set.mem_singleton b⟩
  · intro γ hγ
    exact (gamma_algebraic_iff_definable_base B γ).mpr (gamma_name_definable B γ hγ)

theorem algebraicClosureBase_mono {B C : Base (M := M)}
    (hr : B.real ⊆ C.real) (hγ : B.gamma ⊆ C.gamma) :
    (algebraicClosureBase B).real ⊆ (algebraicClosureBase C).real ∧
      (algebraicClosureBase B).gamma ⊆ (algebraicClosureBase C).gamma := by
  constructor
  · rintro b ⟨σ,hb⟩
    exact ⟨σ,hb.mono hr hγ⟩
  · exact fun γ h => h.mono hr hγ

theorem AlgebraicAtBase.algebraicClosureBase_iff (B : Base (M := M)) (σ : SortTag) (b : M) :
    AlgebraicAtBase (algebraicClosureBase B) σ b ↔ AlgebraicAtBase B σ b := by
  constructor
  · intro hb
    exact hb.eliminate_algebraic_params (fun _ h => h) (fun _ h => h)
  · intro hb
    exact hb.mono (subset_algebraicClosureBase B).1 (subset_algebraicClosureBase B).2

theorem GammaAlgebraicAtBase.algebraicClosureBase_iff (B : Base (M := M)) (γ : Values.Gamma (M := M)) :
    GammaAlgebraicAtBase (algebraicClosureBase B) γ ↔ GammaAlgebraicAtBase B γ := by
  constructor
  · intro hγ
    exact hγ.eliminate_algebraic_params (fun _ h => h) (fun _ h => h)
  · intro hγ
    exact hγ.mono (subset_algebraicClosureBase B).1 (subset_algebraicClosureBase B).2

theorem algebraicClosureBase_idempotent (B : Base (M := M)) :
    algebraicClosureBase (algebraicClosureBase B) = algebraicClosureBase B := by
  have hr : (algebraicClosureBase (algebraicClosureBase B)).real = (algebraicClosureBase B).real := by
    ext b
    exact exists_congr (fun σ => AlgebraicAtBase.algebraicClosureBase_iff B σ b)
  have hg : (algebraicClosureBase (algebraicClosureBase B)).gamma = (algebraicClosureBase B).gamma := by
    ext γ
    exact GammaAlgebraicAtBase.algebraicClosureBase_iff B γ
  cases hC : algebraicClosureBase (algebraicClosureBase B)
  cases hB : algebraicClosureBase B
  simp_all only [Base.mk.injEq,true_and]

theorem definableClosureAt_algebraicClosureBase_iff (B : Base (M := M)) (σ : SortTag) (b : M) :
    DefinableClosureAtBase (algebraicClosureBase B) σ b ↔ AlgebraicAtBase B σ b := by
  constructor
  · intro hb
    apply (AlgebraicAtBase.algebraicClosureBase_iff B σ b).mp
    exact ⟨{b},hb,Set.finite_singleton b,Set.mem_singleton b⟩
  · intro hb
    apply real_definableAtBase (algebraicClosureBase B) σ {b}
    exact definableClosureAt_of_mem (show b ∈ (algebraicClosureBase B).real from ⟨σ,hb⟩) hb.sorted

theorem gamma_definableClosureAt_algebraicClosureBase_iff (B : Base (M := M))
    (γ : Values.Gamma (M := M)) :
    GammaDefinableClosureAtBase (algebraicClosureBase B) γ ↔ GammaAlgebraicAtBase B γ :=
  (gamma_algebraic_iff_definable_base (algebraicClosureBase B) γ).symm.trans
    (GammaAlgebraicAtBase.algebraicClosureBase_iff B γ)

theorem closureBase_algebraicClosureBase (B : Base (M := M)) :
    closureBase (algebraicClosureBase B) = algebraicClosureBase B := by
  have hr : (closureBase (algebraicClosureBase B)).real = (algebraicClosureBase B).real := by
    ext b
    exact exists_congr (fun σ => definableClosureAt_algebraicClosureBase_iff B σ b)
  have hg : (closureBase (algebraicClosureBase B)).gamma = (algebraicClosureBase B).gamma := by
    ext γ
    exact gamma_definableClosureAt_algebraicClosureBase_iff B γ
  cases hC : closureBase (algebraicClosureBase B)
  cases hB : algebraicClosureBase B
  simp_all only [Base.mk.injEq,true_and]

end SpecialTransformations.Section3.GammaParameters
