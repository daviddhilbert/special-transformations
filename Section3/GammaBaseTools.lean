import Section3.FibrePromotion
import Section3.GammaCodeDefinability
import Section3.GammaParameters
import Section3.GammaRealRestriction
import Section3.GammaSpecialization
import Section3.GammaSupport
import Section3.SmallFiniteParameters

/- Component: TupleParameterPromotion -/

set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
namespace SpecialTransformations.ModelTheory

/-- Tuple-output generalization of Section3.FibrePromotion's checked
promote_definable_fibre, with Language as a parameter. No finiteness or
algebraicity assumption is needed to promote named real parameters. -/
theorem promote_definable_tuple_fibre (L : FirstOrder.Language) {M : Type} [L.Structure M]
    (S : Set M) {n : ℕ} {ι : Type} (a : Fin n → M) (T : Set (ι → M))
    (hT : (S ∪ Set.range a).Definable L T) :
    ∃ R : Set ((Fin n → M) × (ι → M)),
      S.Definable L {z : Fin n ⊕ ι → M | (z ∘ Sum.inl,z ∘ Sum.inr) ∈ R} ∧
      {x | (a,x) ∈ R} = T := by
  classical
  obtain ⟨φ,hφ⟩ := Set.definable_iff_exists_formula_sum.mp hT
  let index (u : ↥(S ∪ Set.range a)) (hu : u.val ∉ S) : Fin n :=
    Classical.choose ((u.property : u.val ∈ S ∨ u.val ∈ Set.range a).resolve_left hu)
  have hindex (u : ↥(S ∪ Set.range a)) (hu : u.val ∉ S) : a (index u hu) = u.val :=
    Classical.choose_spec ((u.property : u.val ∈ S ∨ u.val ∈ Set.range a).resolve_left hu)
  let g : (↥(S ∪ Set.range a) ⊕ ι) → S ⊕ (Fin n ⊕ ι) :=
    Sum.elim (fun u => if hu : u.val ∈ S then Sum.inl ⟨u.val,hu⟩
      else Sum.inr (Sum.inl (index u hu))) (fun i => Sum.inr (Sum.inr i))
  let ψ : L.Formula (S ⊕ (Fin n ⊕ ι)) := φ.relabel g
  let R : Set ((Fin n → M) × (ι → M)) :=
    {p | ψ.Realize (Sum.elim Subtype.val (Sum.elim p.1 p.2))}
  have hreal (x : ι → M) : (a,x) ∈ R ↔ x ∈ T := by
    change (φ.relabel g).Realize (Sum.elim Subtype.val (Sum.elim a x)) ↔ x ∈ T
    rw [Formula.realize_relabel]
    have he : Sum.elim (Subtype.val : S → M) (Sum.elim a x) ∘ g =
        Sum.elim (Subtype.val : ↥(S ∪ Set.range a) → M) x := by
      funext u
      cases u with
      | inl u =>
        by_cases hu : u.val ∈ S
        · simp [g,hu]
        · simp only [Function.comp_apply,g,Sum.elim_inl,dif_neg hu,Sum.elim_inr]
          exact hindex u hu
      | inr i => rfl
    rw [he]
    have hm := congrArg (fun U : Set (ι → M) => x ∈ U) hφ
    exact (Iff.of_eq hm).symm
  refine ⟨R,?_,Set.ext hreal⟩
  rw [Set.definable_iff_exists_formula_sum]
  refine ⟨ψ,?_⟩
  ext z
  have hz : Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr) = z := by
    funext i
    cases i <;> rfl
  simp only [R,Set.mem_ofPred_eq,hz]

end SpecialTransformations.ModelTheory

/- Component: GammaBoolean -/



set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def sortedUniverse {n : ℕ} (sn : Fin n → SortTag) : Set (Fin n → M) :=
  {z | ∀ i, sortEval (sn i) (z i)}

theorem sortedUniverse_definable (S : Set M) {n : ℕ} (sn : Fin n → SortTag) :
    SpecialTransformations.Section3.DefinableOver S sn (sortedUniverse sn) := by
  have hsort (i : Fin n) :=
    ((definableAt_iff_normalized_raw S (sn i) {x | sortEval (sn i) x}).mp
      (definableAt_sort S (sn i))).1
  apply (definableOver_iff_normalized_raw S sn _).mpr
  refine ⟨?_,fun z hz => hz⟩
  let N := CanonicalStructure.normalize (M := M)
  letI := N
  convert Set.definable_iInter_of_finite (fun i =>
    (hsort i).preimage_comp (fun _ : Fin 1 => i)) using 1
  ext z
  simp only [sortedUniverse,Set.mem_iInter,Set.mem_preimage,Set.mem_setOf_eq,Function.comp_apply]

/-- Complement inside the actual sorted universe. Wrong-sort values and
improper Gamma codes are excluded on both sides of the interface. -/
def Relation.compl {S : Set M} {k n : ℕ} {sn : Fin n → SortTag}
    (Q : Relation S k n sn) : Relation S k n sn where
  carrier := {p | Proper p.1 ∧ p.2 ∈ sortedUniverse sn ∧ p ∉ Q.carrier}
  definable := by
    have hQ := Q.definable
    have hp := proper_normalized_definable (M := M) S (n := k)
    have hs := ((definableOver_iff_normalized_raw S sn _).mp
      (sortedUniverse_definable S sn)).1
    let N := CanonicalStructure.normalize (M := M)
    letI := N
    exact (hp.preimage_comp (Sum.inl : Fin k → Fin k ⊕ Fin n)).inter
      ((hs.preimage_comp (Sum.inr : Fin n → Fin k ⊕ Fin n)).inter hQ.compl)
  proper := fun p hp => ⟨hp.1,hp.2.1⟩
  invariant := by
    intro t u htu b
    change (Proper (rawTuple t) ∧ b ∈ sortedUniverse sn ∧ (rawTuple t,b) ∉ Q.carrier) ↔
      (Proper (rawTuple u) ∧ b ∈ sortedUniverse sn ∧ (rawTuple u,b) ∉ Q.carrier)
    simp only [rawTuple_proper,true_and]
    exact and_congr Iff.rfl (not_congr (Q.invariant t u htu b))

theorem DefinableWith.compl {S : Set M} {k n : ℕ}
    {γ : Fin k → Values.Gamma (M := M)} {sn : Fin n → SortTag} {A : Set (Fin n → M)}
    (hA : DefinableWith S γ sn A) : DefinableWith S γ sn (sortedUniverse sn \ A) := by
  obtain ⟨Q,hQA⟩ := hA
  refine ⟨Q.compl,?_⟩
  ext z
  change (Proper (rawTuple (representatives γ)) ∧ z ∈ sortedUniverse sn ∧ z ∉ Q.fibre γ) ↔
    (z ∈ sortedUniverse sn ∧ z ∉ A)
  rw [and_iff_right (rawTuple_proper (representatives γ)),hQA]

theorem DefinableOverBase.compl {B : Base (M := M)} {n : ℕ} {sn : Fin n → SortTag}
    {A : Set (Fin n → M)} (hA : DefinableOverBase B sn A) :
    DefinableOverBase B sn (sortedUniverse sn \ A) := by
  obtain ⟨k,γ,hγ,hA⟩ := hA
  exact ⟨k,γ,hγ,hA.compl⟩

theorem DefinableOverBase.preimage_real {B : Base (M := M)} {n m : ℕ}
    {sn : Fin n → SortTag} {A : Set (Fin n → M)} (hA : DefinableOverBase B sn A)
    (sm : Fin m → SortTag) (π : Fin n → Fin m) :
    DefinableOverBase B sm {z | z ∘ π ∈ A ∧ z ∈ sortedUniverse sm} :=
  hA.inter_real_preimage sm _ (sortedUniverse_definable B.real sm) π

/-- Union preserves full code invariance without naming representatives. -/
def Relation.union {S : Set M} {k n : ℕ} {sn : Fin n → SortTag}
    (Q R : Relation S k n sn) : Relation S k n sn where
  carrier := Q.carrier ∪ R.carrier
  definable := by
    have hQ := Q.definable
    have hR := R.definable
    let N := CanonicalStructure.normalize (M := M)
    letI := N
    exact hQ.union hR
  proper := fun p hp => hp.elim (Q.proper p) (R.proper p)
  invariant := fun t u htu b => or_congr (Q.invariant t u htu b) (R.invariant t u htu b)

theorem DefinableWith.union {S : Set M} {k n : ℕ}
    {γ : Fin k → Values.Gamma (M := M)} {sn : Fin n → SortTag}
    {A C : Set (Fin n → M)} (hA : DefinableWith S γ sn A) (hC : DefinableWith S γ sn C) :
    DefinableWith S γ sn (A ∪ C) := by
  obtain ⟨Q,hQA⟩ := hA
  obtain ⟨R,hRC⟩ := hC
  refine ⟨Q.union R,?_⟩
  ext b
  change (b ∈ Q.fibre γ ∨ b ∈ R.fibre γ) ↔ (b ∈ A ∨ b ∈ C)
  rw [hQA,hRC]

theorem DefinableOverBase.union {B : Base (M := M)} {n : ℕ} {sn : Fin n → SortTag}
    {A C : Set (Fin n → M)} (hA : DefinableOverBase B sn A) (hC : DefinableOverBase B sn C) :
    DefinableOverBase B sn (A ∪ C) := by
  obtain ⟨k,γ,hγ,hA⟩ := hA
  obtain ⟨l,δ,hδ,hC⟩ := hC
  let e : Fin k ⊕ Fin l ≃ Fin (k+l) := finSumFinEquiv
  let η : Fin (k+l) → Values.Gamma (M := M) := Sum.elim γ δ ∘ e.symm
  let π : Fin k → Fin (k+l) := fun i => e (.inl i)
  let ρ : Fin l → Fin (k+l) := fun i => e (.inr i)
  have hη (i : Fin (k+l)) : η i ∈ B.gamma := by
    change Sum.elim γ δ (e.symm i) ∈ B.gamma
    cases e.symm i with
    | inl j => exact hγ j
    | inr j => exact hδ j
  have hπ : η ∘ π = γ := by
    funext i
    simp only [η,π,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inl]
  have hρ : η ∘ ρ = δ := by
    funext i
    simp only [η,ρ,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inr]
  exact ⟨k+l,η,hη,(hA.reparam π hπ).union (hC.reparam ρ hρ)⟩

theorem DefinableOverBase.empty (B : Base (M := M)) {n : ℕ} (sn : Fin n → SortTag) :
    DefinableOverBase B sn (∅ : Set (Fin n → M)) := by
  have hraw : @Set.Definable M B.real LRV (CanonicalStructure.normalize (M := M)) (Fin n) ∅ := by
    letI := CanonicalStructure.normalize (M := M)
    exact Set.definable_empty
  exact real_definableOverBase B sn ∅
    ((definableOver_iff_normalized_raw B.real sn ∅).mpr ⟨hraw,fun z hz => False.elim hz⟩)

theorem DefinableOverBase.finite_iUnion {B : Base (M := M)} {n : ℕ}
    {sn : Fin n → SortTag} {ι : Type} (s : Finset ι) (F : ι → Set (Fin n → M))
    (hF : ∀ i ∈ s, DefinableOverBase B sn (F i)) :
    DefinableOverBase B sn (⋃ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using DefinableOverBase.empty B sn
  | @insert a s ha ih =>
    simpa only [Finset.mem_insert,Set.iUnion_iUnion_eq_or_left] using
      (hF a (Finset.mem_insert_self a s)).union
        (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))

end SpecialTransformations.Section3.GammaParameters

/- Component: GammaSupportHull -/

set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {n k m : ℕ}

/-- Universal closure on all equivalent support codes. This repairs code
invariance after promoting real parameters out of a defining formula. -/
def supportHull (R : Set ((Fin n → M) × ((Fin k → M) × (Fin m → M)))) :
    Set ((Fin n → M) × ((Fin k → M) × (Fin m → M))) :=
  {p | Proper p.2.1 ∧ ∀ c, Same c p.2.1 → (p.1,c,p.2.2) ∈ R}

theorem supportHull_definable (S : Set M)
    (R : Set ((Fin n → M) × ((Fin k → M) × (Fin m → M))))
    (hR : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M))
      (Fin n ⊕ (Fin k ⊕ Fin m))
      {z | (z ∘ Sum.inl,z ∘ Sum.inr ∘ Sum.inl,z ∘ Sum.inr ∘ Sum.inr) ∈ R}) :
    @Set.Definable M S LRV (CanonicalStructure.normalize (M := M))
      (Fin n ⊕ (Fin k ⊕ Fin m))
      {z | (z ∘ Sum.inl,z ∘ Sum.inr ∘ Sum.inl,z ∘ Sum.inr ∘ Sum.inr) ∈ supportHull R} := by
  have hE := same_normalized_definable (M := M) S (n := k)
  have hP := proper_normalized_definable (M := M) S (n := k)
  let E := Same (M := M) (n := k)
  let P := Proper (M := M) (n := k)
  let H := supportHull R
  let N := CanonicalStructure.normalize (M := M)
  letI := N
  let α := Fin n ⊕ (Fin k ⊕ Fin m)
  let idx : α → α ⊕ Fin k :=
    Sum.elim (fun i => .inl (.inl i))
      (Sum.elim Sum.inr (fun i => .inl (.inr (.inr i))))
  let eqidx : Fin k ⊕ Fin k → α ⊕ Fin k :=
    Sum.elim Sum.inr (fun i => .inl (.inr (.inl i)))
  have he := hE.preimage_comp eqidx
  have hr := hR.preimage_comp idx
  have hu := (he.himp hr).forall_of_finite
  have hp := hP.preimage_comp (fun i : Fin k => (Sum.inr (Sum.inl i) : α))
  change S.Definable LRV {z : α → M |
    (z ∘ Sum.inl,z ∘ Sum.inr ∘ Sum.inl,z ∘ Sum.inr ∘ Sum.inr) ∈ H}
  convert hp.inter hu using 1
  ext z
  change (P (z ∘ Sum.inr ∘ Sum.inl) ∧ ∀ c, E c (z ∘ Sum.inr ∘ Sum.inl) →
    (z ∘ Sum.inl,c,z ∘ Sum.inr ∘ Sum.inr) ∈ R) ↔ _
  rfl

theorem supportHull_invariant
    (R : Set ((Fin n → M) × ((Fin k → M) × (Fin m → M))))
    (a : Fin n → M) (b : Fin m → M) (t u : Fin k → Code (M := M))
    (htu : values t = values u) :
    (a,rawTuple t,b) ∈ supportHull R ↔ (a,rawTuple u,b) ∈ supportHull R := by
  simp only [supportHull,Set.mem_ofPred_eq,rawTuple_proper,true_and]
  exact forall_congr' (fun c => imp_congr_left (same_with_codes_iff c t u htu))

end SpecialTransformations.Section3.GammaParameters

/- Component: GammaParameterPromotion -/



set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Promote a tuple of named real parameters while retaining a genuine,
globally invariant Gamma support. At the designated tuple, the entire
original proper-code relation is preserved. -/
theorem promote_gamma_relation (S : Set M) {n k m : ℕ} (a : Fin n → M)
    {sn : Fin m → SortTag} (Q : Relation (S ∪ Set.range a) k m sn) :
    ∃ H : Set ((Fin n → M) × ((Fin k → M) × (Fin m → M))),
      @Set.Definable M S LRV (CanonicalStructure.normalize (M := M))
        (Fin n ⊕ (Fin k ⊕ Fin m))
        {z | (z ∘ Sum.inl,z ∘ Sum.inr ∘ Sum.inl,z ∘ Sum.inr ∘ Sum.inr) ∈ H} ∧
      (∀ v b (t u : Fin k → Code (M := M)), values t = values u →
        ((v,rawTuple t,b) ∈ H ↔ (v,rawTuple u,b) ∈ H)) ∧
      ∀ c b, Proper c → ((a,c,b) ∈ H ↔ (c,b) ∈ Q.carrier) := by
  let U := Q.carrier
  have hQd := Q.definable
  let N := CanonicalStructure.normalize (M := M)
  letI := sM
  obtain ⟨P,hPd,hPa⟩ := @ModelTheory.promote_definable_tuple_fibre LRV M N S n
    (Fin k ⊕ Fin m) a {z | (z ∘ Sum.inl,z ∘ Sum.inr) ∈ U} hQd
  let R : Set ((Fin n → M) × ((Fin k → M) × (Fin m → M))) :=
    {p | (p.1,Sum.elim p.2.1 p.2.2) ∈ P}
  have hRd : @Set.Definable M S LRV N (Fin n ⊕ (Fin k ⊕ Fin m))
      {z | (z ∘ Sum.inl,z ∘ Sum.inr ∘ Sum.inl,z ∘ Sum.inr ∘ Sum.inr) ∈ R} := by
    letI := N
    convert hPd using 1
    ext z
    have hz : Sum.elim (z ∘ Sum.inr ∘ Sum.inl) (z ∘ Sum.inr ∘ Sum.inr) = z ∘ Sum.inr := by
      funext i
      cases i <;> rfl
    change (z ∘ Sum.inl,Sum.elim (z ∘ Sum.inr ∘ Sum.inl) (z ∘ Sum.inr ∘ Sum.inr)) ∈ P ↔ _
    rw [hz]
    rfl
  have hRa (c : Fin k → M) (b : Fin m → M) : (a,c,b) ∈ R ↔ (c,b) ∈ U := by
    have hh := Set.ext_iff.mp hPa (Sum.elim c b)
    exact hh
  refine ⟨supportHull R,supportHull_definable S R hRd,?_,?_⟩
  · exact fun v b t u he => supportHull_invariant R v b t u he
  · intro c b hc
    constructor
    · intro h
      exact (hRa c b).mp (h.2 c (same_refl c hc))
    · intro h
      refine ⟨hc,?_⟩
      intro d hd
      let t := ofRaw d (Same.proper_left hd)
      let u := ofRaw c hc
      have ht : rawTuple t = d := rawTuple_ofRaw d (Same.proper_left hd)
      have hu : rawTuple u = c := rawTuple_ofRaw c hc
      have he : values t = values u := (same_codes_iff t u).mp (by rw [ht,hu]; exact hd)
      have hh := Q.invariant t u he b
      rw [ht,hu] at hh
      exact (hRa d b).mpr (hh.mpr h)

end SpecialTransformations.Section3.GammaParameters

/- Component: GammaCommonNames -/



set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Proof-only common real names for compactness. This set is never used
as the parameter base in a descent conclusion. -/
noncomputable def commonRealNames (B : Base (M := M)) : Set M :=
  B.real ∪ (fun δ => raw (representative δ)) '' B.gamma

theorem commonRealNames_small {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ) :
    Cardinal.mk ↥(commonRealNames B) < κ := by
  apply lt_of_le_of_lt (Cardinal.mk_union_le _ _)
  exact Cardinal.add_lt_of_lt hκ hr (lt_of_le_of_lt Cardinal.mk_image_le hγ)

theorem DefinableOverBase.common_names {B : Base (M := M)} {n : ℕ}
    {sn : Fin n → SortTag} {A : Set (Fin n → M)} (hA : DefinableOverBase B sn A) :
    SpecialTransformations.Section3.DefinableOver (commonRealNames B) sn A := by
  obtain ⟨k,γ,hγ,hA⟩ := hA
  have hd := hA.specialize (representatives γ) (representatives_values γ)
  apply hd.mono
  intro x hx
  rcases hx with hx | ⟨i,rfl⟩
  · exact Or.inl hx
  · exact Or.inr ⟨γ i,hγ i,rfl⟩

theorem DefinableAtBase.common_names {B : Base (M := M)} {σ : SortTag} {A : Set M}
    (hA : DefinableAtBase B σ A) :
    SpecialTransformations.Section3.DefinableAt (commonRealNames B) σ A :=
  ⟨DefinableOverBase.common_names hA,hA.proper⟩

end SpecialTransformations.Section3.GammaParameters
