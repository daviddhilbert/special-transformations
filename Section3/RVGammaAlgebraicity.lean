import Section3.GammaBaseDescent
import Section3.GammaRVSeparation

/- Component: GammaLastProjection -/
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem rawTuple_lastCases {k : ℕ} (c : Code (M := M)) (t : Fin k → Code (M := M)) :
    rawTuple (Fin.lastCases c t) = Fin.lastCases (raw c) (rawTuple t) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp only [rawTuple,Fin.lastCases_last]
  · intro j
    simp only [rawTuple,Fin.lastCases_castSucc]

theorem values_lastCases {k : ℕ} (c : Code (M := M)) (t : Fin k → Code (M := M)) :
    values (Fin.lastCases c t) = Fin.lastCases (value c) (values t) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp only [values,Fin.lastCases_last]
  · intro j
    simp only [values,Fin.lastCases_castSucc]

/-- Existentially quantifying a Gamma coordinate means quantifying its
entire proper RV-code fibre. The remaining coordinates retain their full
invariance; no section is added to the real parameter base. -/
def Relation.imageLastGamma {S : Set M} {k n : ℕ} {sn : Fin n → SortTag}
    (Q : Relation S (k+1) n sn) : Relation S k n sn where
  carrier := {p | ∃ a, (Fin.lastCases a p.1,p.2) ∈ Q.carrier}
  definable := by
    let U := Q.carrier
    have hd := Q.definable
    let α := Fin k ⊕ Fin n
    let idx : Fin (k+1) ⊕ Fin n → α ⊕ Fin 1 :=
      Sum.elim (Fin.lastCases (.inr 0) (fun i => .inl (.inl i))) (fun i => .inl (.inr i))
    letI := CanonicalStructure.normalize (M := M)
    have hraw : S.Definable LRV {z : α ⊕ Fin 1 → M |
        (Fin.lastCases (z (.inr 0)) ((z ∘ Sum.inl) ∘ Sum.inl),(z ∘ Sum.inl) ∘ Sum.inr) ∈ U} := by
      convert hd.preimage_comp idx using 1
      ext z
      have he : (z ∘ idx) ∘ Sum.inl =
          Fin.lastCases (z (.inr 0)) ((z ∘ Sum.inl) ∘ Sum.inl) := by
        funext i
        refine Fin.lastCases ?_ ?_ i
        · simp only [Function.comp_apply,idx,Sum.elim_inl,Fin.lastCases_last]
        · intro j
          simp only [Function.comp_apply,idx,Sum.elim_inl,Fin.lastCases_castSucc]
      change (Fin.lastCases (z (.inr 0)) ((z ∘ Sum.inl) ∘ Sum.inl),(z ∘ Sum.inl) ∘ Sum.inr) ∈ U ↔
        (((z ∘ idx) ∘ Sum.inl),(z ∘ idx) ∘ Sum.inr) ∈ U
      rw [he]
      rfl
    exact SpecialTransformations.ModelTheory.definable_exists_one
      (P := fun z a => (Fin.lastCases a (z ∘ Sum.inl),z ∘ Sum.inr) ∈ U) hraw
  proper := by
    rintro p ⟨a,ha⟩
    obtain ⟨hp,hs⟩ := Q.proper _ ha
    refine ⟨fun i => ?_,hs⟩
    simpa only [Fin.lastCases_castSucc] using hp i.castSucc
  invariant := by
    intro t u htu b
    have hf (t u : Fin k → Code (M := M)) (htu : values t = values u)
        (h : ∃ a, (Fin.lastCases a (rawTuple t),b) ∈ Q.carrier) :
        ∃ a, (Fin.lastCases a (rawTuple u),b) ∈ Q.carrier := by
      obtain ⟨a,ha⟩ := h
      have hap : NonzeroRV a := by
        simpa only [NonzeroRV,Fin.lastCases_last] using (Q.proper _ ha).1 (Fin.last k)
      let c : Code (M := M) := ⟨⟨a,hap.1⟩,hap.2⟩
      have htu' : values (Fin.lastCases c t) = values (Fin.lastCases c u) := by
        rw [values_lastCases,values_lastCases,htu]
      have hq := Q.invariant (Fin.lastCases c t) (Fin.lastCases c u) htu' b
      rw [rawTuple_lastCases,rawTuple_lastCases] at hq
      exact ⟨a,hq.mp ha⟩
    exact ⟨hf t u htu,hf u t htu.symm⟩

theorem Relation.imageLastGamma_fibre {S : Set M} {k n : ℕ} {sn : Fin n → SortTag}
    (Q : Relation S (k+1) n sn) (δ : Fin k → Values.Gamma (M := M)) :
    Q.imageLastGamma.fibre δ = {b | ∃ β, b ∈ Q.fibre (Fin.lastCases β δ)} := by
  ext b
  constructor
  · rintro ⟨a,ha⟩
    have hap : NonzeroRV a := by
      simpa only [NonzeroRV,Fin.lastCases_last] using (Q.proper _ ha).1 (Fin.last k)
    let c : Code (M := M) := ⟨⟨a,hap.1⟩,hap.2⟩
    have hv : values (Fin.lastCases c (representatives δ)) = Fin.lastCases (value c) δ := by
      rw [values_lastCases,representatives_values]
    refine ⟨value c,(Q.mem_fibre_iff _ _ hv b).mpr ?_⟩
    rw [rawTuple_lastCases]
    exact ha
  · rintro ⟨β,hb⟩
    let c := representative β
    have hv : values (Fin.lastCases c (representatives δ)) = Fin.lastCases β δ := by
      rw [values_lastCases,representatives_values,representative_value]
    have hh := (Q.mem_fibre_iff _ _ hv b).mp hb
    refine ⟨raw c,?_⟩
    simpa only [rawTuple_lastCases] using hh

end SpecialTransformations.Section3.GammaParameters

/- Component: GammaTupleRVFamilies -/
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Specializing only the other Gamma coordinates produces a genuine
one-Gamma family over their temporary real names. Its varying Gamma input
still uses every proper RV representative. -/
noncomputable def GammaRVFamily.ofRelationLast {S : Set M} {k : ℕ}
    (Q : Relation S (k+1) 1 (fun _ => .rv)) (δ : Fin k → Values.Gamma (M := M)) :
    GammaRVFamily (M := M) (S ∪ Set.range (rawTuple (representatives δ))) where
  relation := fun β t => (![t] : Fin 1 → M) ∈ Q.fibre (Fin.lastCases β δ)
  sorted := by
    intro β t ht
    exact Q.fibre_proper (Fin.lastCases β δ) ![t] ht 0
  definable := by
    let names := rawTuple (representatives δ)
    let T := S ∪ Set.range names
    let U := Q.carrier
    have hd := Q.definable
    have he : {p : M × M | NonzeroRV p.1 ∧
        (![p.2] : Fin 1 → M) ∈ Q.fibre (Fin.lastCases (codeValue p.1) δ)} =
        {p | (Fin.lastCases p.1 names,(![p.2] : Fin 1 → M)) ∈ U} := by
      ext p
      constructor
      · rintro ⟨ha,hb⟩
        let c : Code (M := M) := ⟨⟨p.1,ha.1⟩,ha.2⟩
        have hv : values (Fin.lastCases c (representatives δ)) = Fin.lastCases (codeValue p.1) δ := by
          rw [values_lastCases,representatives_values,← codeValue_raw c]
          rfl
        have hh := (Q.mem_fibre_iff _ _ hv (![p.2] : Fin 1 → M)).mp hb
        change (Fin.lastCases p.1 names,(![p.2] : Fin 1 → M)) ∈ U
        rw [rawTuple_lastCases] at hh
        exact hh
      · intro hh
        have ha : NonzeroRV p.1 := by
          simpa only [NonzeroRV,Fin.lastCases_last] using (Q.proper _ hh).1 (Fin.last k)
        let c : Code (M := M) := ⟨⟨p.1,ha.1⟩,ha.2⟩
        have hv : values (Fin.lastCases c (representatives δ)) = Fin.lastCases (codeValue p.1) δ := by
          rw [values_lastCases,representatives_values,← codeValue_raw c]
          rfl
        refine ⟨ha,(Q.mem_fibre_iff _ _ hv (![p.2] : Fin 1 → M)).mpr ?_⟩
        rw [rawTuple_lastCases]
        exact hh
    rw [he]
    letI := CanonicalStructure.normalize (M := M)
    let m (z : Fin 2 → M) : Fin (k+1) ⊕ Fin 1 → M :=
      Sum.elim (Fin.lastCases (z 0) names) (fun _ => z 1)
    have hm : T.DefinableMap LRV m := by
      intro i
      cases i with
      | inl i =>
        refine Fin.lastCases ?_ ?_ i
        · simpa only [m,Sum.elim_inl,Fin.lastCases_last] using
            (Set.DefinableFun.proj (L := LRV) (A := T) (i := (0 : Fin 2)))
        · intro j
          have hj : names j ∈ T := Or.inr ⟨j,rfl⟩
          simpa only [m,Sum.elim_inl,Fin.lastCases_castSucc] using
            (LRV.definableFun_const (Fin 2) hj)
      | inr i =>
        simpa only [m,Sum.elim_inr] using
          (Set.DefinableFun.proj (L := LRV) (A := T) (i := (1 : Fin 2)))
    change T.Definable LRV {z : Fin 2 → M | (Fin.lastCases (z 0) names,(![z 1] : Fin 1 → M)) ∈ U}
    convert (hd.mono (Set.subset_union_left : S ⊆ T)).preimage_map hm using 1
    ext z
    have hb : m z ∘ Sum.inr = (![z 1] : Fin 1 → M) := by
      funext i; fin_cases i; rfl
    change (Fin.lastCases (z 0) names,(![z 1] : Fin 1 → M)) ∈ U ↔
      (m z ∘ Sum.inl,m z ∘ Sum.inr) ∈ U
    rw [hb]
    rfl

theorem Relation.imageLastGamma_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    {S : Set M} (hsmall : Cardinal.mk S < κ) {k : ℕ}
    (Q : Relation S (k+1) 1 (fun _ => .rv))
    (hfinite : ∀ γ, (Q.fibre γ).Finite) (δ : Fin k → Values.Gamma (M := M)) :
    (Q.imageLastGamma.fibre δ).Finite := by
  let F := GammaRVFamily.ofRelationLast Q δ
  have hsmall' := small_union_range hκ S hsmall (rawTuple (representatives δ))
  have hf (β : Values.Gamma (M := M)) : {t | F.relation β t}.Finite := by
    apply (hfinite (Fin.lastCases β δ)).preimage
    intro x _ y _ hxy
    exact congrFun hxy 0
  have hp := F.finite_projection hκ hs h00 hsmall' hf
  have hsub : (fun b : Fin 1 → M => b 0) '' (Q.imageLastGamma.fibre δ) ⊆ F.nonemptyDomain := by
    rintro t ⟨b,hb,rfl⟩
    rw [Relation.imageLastGamma_fibre] at hb
    obtain ⟨β,hβ⟩ := hb
    refine ⟨β,?_⟩
    change (![b 0] : Fin 1 → M) ∈ Q.fibre (Fin.lastCases β δ)
    have he : (![b 0] : Fin 1 → M) = b := by funext i; fin_cases i; rfl
    rwa [he]
  apply (hp.subset hsub).of_finite_image
  intro b _ c _ hbc
  funext i
  fin_cases i
  exact hbc

end SpecialTransformations.Section3.GammaParameters

/- Component: GammaTotalRVProjection -/
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def Relation.totalRVProjection {S : Set M} {k : ℕ} (Q : Relation S k 1 (fun _ => .rv)) : Set M :=
  {t | ∃ γ, (![t] : Fin 1 → M) ∈ Q.fibre γ}

theorem Relation.totalRVProjection_definable {S : Set M} {k : ℕ}
    (Q : Relation S k 1 (fun _ => .rv)) : DefinableAt S .rv Q.totalRVProjection := by
  let A := Q.totalRVProjection
  let U := Q.carrier
  have he : A = {t | ∃ a, (a,(![t] : Fin 1 → M)) ∈ U} := by
    ext t
    constructor
    · rintro ⟨γ,hγ⟩
      exact ⟨rawTuple (representatives γ),hγ⟩
    · rintro ⟨a,ha⟩
      let u := ofRaw a (Q.proper _ ha).1
      refine ⟨values u,(Q.full_preimage u (![t] : Fin 1 → M)).mpr ?_⟩
      rwa [rawTuple_ofRaw]
  have hQ := Q.definable
  have hd : @Set.Definable₁ M S LRV (CanonicalStructure.normalize (M := M))
      {t | ∃ a, (a,(![t] : Fin 1 → M)) ∈ U} := by
    letI := CanonicalStructure.normalize (M := M)
    have hh := (hQ.preimage_comp (Sum.swap : Fin k ⊕ Fin 1 → Fin 1 ⊕ Fin k)).exists_of_finite
    change S.Definable LRV {z : Fin 1 → M | ∃ a, (a,(![z 0] : Fin 1 → M)) ∈ U}
    convert hh using 1
    ext z
    change (∃ a, (a,(![z 0] : Fin 1 → M)) ∈ U) ↔ ∃ a, (a,z) ∈ U
    have hz : (![z 0] : Fin 1 → M) = z := by funext i; fin_cases i; rfl
    rw [hz]
  apply (definableAt_iff_normalized_raw S .rv A).mpr
  refine ⟨he.symm ▸ hd,?_⟩
  rintro t ⟨γ,hγ⟩
  exact Q.fibre_proper γ ![t] hγ 0

theorem Relation.totalRVProjection_imageLastGamma {S : Set M} {k : ℕ}
    (Q : Relation S (k+1) 1 (fun _ => .rv)) :
    Q.totalRVProjection = Q.imageLastGamma.totalRVProjection := by
  ext t
  constructor
  · rintro ⟨γ,hγ⟩
    refine ⟨Fin.init γ,?_⟩
    rw [Relation.imageLastGamma_fibre]
    refine ⟨γ (Fin.last k),?_⟩
    have he : Fin.lastCases (γ (Fin.last k)) (Fin.init γ) = γ := by
      funext i
      refine Fin.lastCases ?_ ?_ i
      · simp only [Fin.lastCases_last]
      · intro j
        simp only [Fin.lastCases_castSucc,Fin.init]
    rwa [he]
  · rintro ⟨δ,hδ⟩
    rw [Relation.imageLastGamma_fibre] at hδ
    obtain ⟨β,hβ⟩ := hδ
    exact ⟨Fin.lastCases β δ,hβ⟩

theorem Relation.totalRVProjection_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    {S : Set M} (hsmall : Cardinal.mk S < κ) {k : ℕ}
    (Q : Relation S k 1 (fun _ => .rv)) (hfinite : ∀ γ, (Q.fibre γ).Finite) :
    Q.totalRVProjection.Finite := by
  induction k with
  | zero =>
    have he : Q.totalRVProjection =
        (fun b : Fin 1 → M => b 0) '' Q.fibre (Fin.elim0) := by
      ext t
      constructor
      · rintro ⟨γ,hγ⟩
        have hγ0 : γ = Fin.elim0 := by funext i; exact i.elim0
        rw [hγ0] at hγ
        exact ⟨![t],hγ,rfl⟩
      · rintro ⟨b,hb,rfl⟩
        refine ⟨Fin.elim0,?_⟩
        have hb' : (![b 0] : Fin 1 → M) = b := by funext i; fin_cases i; rfl
        rwa [hb']
    rw [he]
    exact (hfinite _).image _
  | succ k ih =>
    rw [Q.totalRVProjection_imageLastGamma]
    exact ih Q.imageLastGamma (Q.imageLastGamma_finite hκ hs h00 hsmall hfinite)

end SpecialTransformations.Section3.GammaParameters

/- Component: RVGammaAlgebraicity -/
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The checked real-row cut specializes directly to a scalar RV output
with no real input coordinates. Every resulting Gamma row is finite. -/
theorem Relation.cutFiniteRVRows_finite {S : Set M} {k : ℕ}
    (Q : Relation S k 1 (fun _ => .rv)) (d : ℕ) (γ : Fin k → Values.Gamma (M := M)) :
    ((Q.cutFiniteRows d).fibre γ).Finite := by
  let e : Fin 0 → M := Fin.elim0
  have hf := cutFiniteRows_finite Q d (rawTuple (representatives γ)) e
  apply (hf.image (fun x => Fin.snoc e x)).subset
  intro b hb
  have he : Fin.snoc e (b 0) = b := by funext i; fin_cases i; rfl
  refine ⟨b 0,?_,he⟩
  change (rawTuple (representatives γ),Fin.snoc e (b 0)) ∈ (Q.cutFiniteRows d).carrier
  rw [he]
  exact hb

/-- Gamma names do not enlarge RV algebraic closure. Each witness has
finite formula support, so only the real part of the ambient base must
be small. No cardinal bound on its entire Gamma-name set is required. -/
theorem algebraic_rv_gamma_base_iff {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (b : M) :
    AlgebraicAtBase B .rv b ↔ AlgebraicAt B.real .rv b := by
  constructor
  · rintro ⟨W,⟨k,γ,hγ,Q,hQW⟩,hWf,hbW⟩
    let c := rawTuple (representatives γ)
    let e : Fin 0 → M := Fin.elim0
    let X : Set M := {x | (c,Fin.snoc e x) ∈ Q.carrier}
    have heX : X = W := by
      ext x
      change (Fin.snoc e x) ∈ Q.fibre γ ↔ x ∈ W
      rw [hQW]
      rfl
    have hXf : X.Finite := heX.symm ▸ hWf
    have hXd : X.ncard ≤ W.ncard := by rw [heX]
    have hrow := cutFiniteRows_row_eq Q W.ncard c e hXf hXd
    let R := Q.cutFiniteRows W.ncard
    have hbR : (c,Fin.snoc e b) ∈ R.carrier := by
      have hbX : b ∈ X := heX.symm ▸ hbW
      have hh : b ∈ {x | (c,Fin.snoc e x) ∈ (Q.cutFiniteRows W.ncard).carrier} := by
        rw [hrow]
        exact hbX
      exact hh
    refine ⟨R.totalRVProjection,R.totalRVProjection_definable,
      R.totalRVProjection_finite hκ hs h00 hsmall (fun δ => Q.cutFiniteRVRows_finite W.ncard δ),γ,?_⟩
    change (c,(![b] : Fin 1 → M)) ∈ R.carrier
    have he : Fin.snoc e b = (![b] : Fin 1 → M) := by funext i; fin_cases i; rfl
    rwa [← he]
  · rintro ⟨W,hW,hWf,hbW⟩
    exact ⟨W,real_definableAtBase B .rv W hW,hWf,hbW⟩

theorem algebraic_rv_adjoin_gamma_iff {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (γ : Values.Gamma (M := M)) (b : M) :
    AlgebraicAtBase ⟨B.real,insert γ B.gamma⟩ .rv b ↔ AlgebraicAtBase B .rv b :=
  (algebraic_rv_gamma_base_iff hκ hs h00 ⟨B.real,insert γ B.gamma⟩ hsmall b).trans
    (algebraic_rv_gamma_base_iff hκ hs h00 B hsmall b).symm

/-- The Gamma assertion of Corollary 3.7, allowing any pre-existing
Gamma names in the ambient base. -/
theorem corollary_3_7_gamma_base {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (γ : Values.Gamma (M := M)) (t : M) (ht : ¬ AlgebraicAtBase B .rv t) :
    ¬ AlgebraicAtBase ⟨B.real,insert γ B.gamma⟩ .rv t :=
  fun h => ht ((algebraic_rv_adjoin_gamma_iff hκ hs h00 B hsmall γ t).mp h)

end SpecialTransformations.Section3.GammaParameters
