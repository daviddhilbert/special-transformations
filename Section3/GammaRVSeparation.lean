module

public import Section3.GammaBaseDescent
public import Section3.GammaBaseTools
public import Section3.GammaCodeDefinability
public import Section3.GammaGoodRelations
public import Section3.GammaThresholdGeometry
public import Section3.RVFibreGeometry

@[expose] public section

/- Component: NoOrderRVMaps -/
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The finite/cofinite fibre theorem in the raw real carrier. A definable
subset of a fixed RV value fibre leaves a finite side in every definable
subdomain of that fibre. Parameter sets for the two sets may differ. -/
theorem rv_subset_finite_or_finite_sdiff (S T D C : Set M)
    (hD : DefinableAt S .rv D) (hC : DefinableAt T .rv C) (hCD : C ⊆ D)
    (γ : Values.Gamma (M := M))
    (hDγ : ∀ t : CanonicalRV.RVSort M, t.val ∈ D → Values.vrv t = γ.val) :
    C.Finite ∨ (D \ C).Finite := by
  rcases rv_value_fibre_finite_or_cofinite T C hC γ with hf | hf
  · left
    have he : Subtype.val '' Values.fibre C γ = C := by
      ext x
      constructor
      · rintro ⟨t,ht,rfl⟩; exact ht.2
      · intro hx
        let t : CanonicalRV.RVSort M := ⟨x,hC.2 hx⟩
        exact ⟨t,⟨hDγ t (hCD hx),hx⟩,rfl⟩
    rw [← he]
    exact hf.image Subtype.val
  · right
    apply (hf.image Subtype.val).subset
    rintro x ⟨hxD,hxC⟩
    let t : CanonicalRV.RVSort M := ⟨x,hD.2 hxD⟩
    exact ⟨t,⟨hDγ t hxD,hxC⟩,rfl⟩

namespace GammaParameters

/-- Total semantic decoding used only to state full real-code preimages.
Definability is always asserted for the entire guarded relation, never for
a fictitious first-order language structure on the Gamma carrier. -/
noncomputable def codeValue (a : M) : Values.Gamma (M := M) :=
  if h : NonzeroRV a then value ⟨⟨a,h.1⟩,h.2⟩ else 1

theorem codeValue_raw (t : Code (M := M)) : codeValue (raw t) = value t := by
  have hp : NonzeroRV (raw t) := ⟨raw_rv t,raw_ne_zero t⟩
  simp only [codeValue,dif_pos hp]
  rfl

def cutFamily (D : Set M) (f : M → Values.Gamma (M := M)) : Set ((Fin 1 → M) × M) :=
  {p | NonzeroRV (p.1 0) ∧ p.2 ∈ D ∧ f p.2 < codeValue (p.1 0)}

theorem nonzero_codes_normalized_definable (S : Set M) :
    @Set.Definable₁ M S LRV (CanonicalStructure.normalize (M := M)) {x | NonzeroRV x} := by
  have he : {x : M | @NonzeroRV M (CanonicalStructure.normalize (M := M)) x} =
      {x | NonzeroRV x} := Set.ext (fun x => nonzero_rv_normalize x)
  exact he ▸ @nonzero_rv_definable M (CanonicalStructure.normalize (M := M)) S

theorem cut_row_definable (S D : Set M) (hD : DefinableAt S .rv D)
    (f : M → Values.Gamma (M := M))
    (hR : @RawClosure.Tuple.RelationDefinable M (CanonicalStructure.normalize (M := M)) 1 S
      (cutFamily D f)) (w : M) :
    DefinableAt (insert w S) .rv {x | ((fun _ : Fin 1 => w),x) ∈ cutFamily D f} := by
  let R := cutFamily D f
  let C : Set M := {x | ((fun _ : Fin 1 => w),x) ∈ R}
  have hd : @Set.Definable₁ M (insert w S) LRV (CanonicalStructure.normalize (M := M)) C := by
    letI := CanonicalStructure.normalize (M := M)
    have hr := hR.mono (Set.subset_insert w S)
    let F (z : Fin 1 → M) : Fin 1 ⊕ Fin 1 → M := Sum.elim (fun _ => w) z
    have hF : (insert w S).DefinableMap LRV F := by
      intro i
      cases i with
      | inl i => exact LRV.definableFun_const (Fin 1) (Set.mem_insert w S)
      | inr i => exact Set.DefinableFun.proj LRV
    change (insert w S).Definable LRV {z : Fin 1 → M | z 0 ∈ C}
    convert hr.preimage_map hF using 1
    ext z
    rfl
  apply (definableAt_iff_normalized_raw (insert w S) .rv C).mpr
  exact ⟨hd,fun x hx => hD.2 hx.2.1⟩

/-- Uniformly first-order order cuts on a definable RV-fibre
domain have finite image. This derives the no-order conclusion from actual
saturation, C-minimality and the finite-image cut argument. The premise is
the complete guarded real-code cut family; no stability result is assumed. -/
theorem finite_image_of_definable_cuts {κ : Cardinal} (hs : Saturated M κ)
    (S D : Set M) (hsmall : Cardinal.mk S < κ) (hD : DefinableAt S .rv D)
    (γ : Values.Gamma (M := M))
    (hDγ : ∀ t : CanonicalRV.RVSort M, t.val ∈ D → Values.vrv t = γ.val)
    (f : M → Values.Gamma (M := M))
    (hR : @RawClosure.Tuple.RelationDefinable M (CanonicalStructure.normalize (M := M)) 1 S
      (cutFamily D f)) : (f '' D).Finite := by
  let R := cutFamily D f
  let P : Set (Fin 1 → M) := {a | NonzeroRV (a 0)}
  let Q : Set ((Fin 1 → M) × M) :=
    {p | NonzeroRV (p.1 0) ∧ p.2 ∈ D ∧ p ∉ R}
  have hP := nonzero_codes_normalized_definable (M := M) S
  have hDn := (definableAt_iff_normalized_raw S .rv D).mp hD
  have hQ : @RawClosure.Tuple.RelationDefinable M (CanonicalStructure.normalize (M := M)) 1 S Q := by
    letI := CanonicalStructure.normalize (M := M)
    have hp := hP.preimage_comp (Sum.inl : Fin 1 → Fin 1 ⊕ Fin 1)
    have hd := hDn.1.preimage_comp (Sum.inr : Fin 1 → Fin 1 ⊕ Fin 1)
    change S.Definable LRV {z : Fin 1 ⊕ Fin 1 → M | (z ∘ Sum.inl,z (.inr 0)) ∈ Q}
    convert hp.inter (hd.inter hR.compl) using 1
    ext z
    rfl
  have hside (a : Fin 1 → M) (ha : a ∈ P) :
      {x | (a,x) ∈ R}.Finite ∨ {x | (a,x) ∈ Q}.Finite := by
    have hrow := cut_row_definable S D hD f hR (a 0)
    have he : (fun _ : Fin 1 => a 0) = a := by funext i; fin_cases i; rfl
    rw [he] at hrow
    have hsub : {x | (a,x) ∈ R} ⊆ D := fun x hx => hx.2.1
    have hh := rv_subset_finite_or_finite_sdiff S (insert (a 0) S) D _ hD hrow hsub γ hDγ
    have hdiff : D \ {x | (a,x) ∈ R} = {x | (a,x) ∈ Q} := by
      ext x
      exact ⟨fun h => ⟨ha,h.1,h.2⟩,fun h => ⟨h.2.1,h.2.2⟩⟩
    rw [hdiff] at hh
    exact hh
  have hsN := hs.normalize
  obtain ⟨d,hd⟩ := @RawClosure.Tuple.uniform_finite_side M (CanonicalStructure.normalize (M := M)) 1 κ hsN S hsmall P hP R Q hR hQ hside
  apply finite_image_of_uniform_small_cut D f d
  intro β
  let t := representative β
  let a : Fin 1 → M := fun _ => raw t
  have ha : a ∈ P := ⟨raw_rv t,raw_ne_zero t⟩
  have ha' : NonzeroRV (a 0) := ha
  have hvalue : codeValue (a 0) = β := (codeValue_raw t).trans (representative_value β)
  have hleft : {x | (a,x) ∈ R} = {x | x ∈ D ∧ f x < β} := by
    ext x
    change (NonzeroRV (a 0) ∧ x ∈ D ∧ f x < codeValue (a 0)) ↔ _
    rw [and_iff_right ha',hvalue]
    rfl
  have hright : {x | (a,x) ∈ Q} = {x | x ∈ D ∧ ¬ f x < β} := by
    ext x
    change (NonzeroRV (a 0) ∧ x ∈ D ∧ ¬ (a,x) ∈ R) ↔ _
    rw [and_iff_right ha']
    have hrx : (a,x) ∈ R ↔ x ∈ D ∧ f x < β := Set.ext_iff.mp hleft x
    rw [hrx]
    change (x ∈ D ∧ ¬ (x ∈ D ∧ f x < β)) ↔ (x ∈ D ∧ ¬ f x < β)
    tauto
  simpa only [hleft,hright] using hd a ha

end GammaParameters
end SpecialTransformations.Section3

/- Component: EndpointCodeLogic -/
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.ModelTheory
variable {L : FirstOrder.Language} {M : Type} [L.Structure M] {S : Set M} {ι : Type}

theorem definable_exists_one {P : (ι → M) → M → Prop}
    (h : S.Definable L {z : ι ⊕ Fin 1 → M | P (z ∘ Sum.inl) (z (.inr 0))}) :
    S.Definable L {z : ι → M | ∃ x, P z x} := by
  convert h.exists_of_finite using 1
  ext z
  change (∃ x, P z x) ↔ ∃ u : Fin 1 → M, P z (u 0)
  exact ⟨fun ⟨x,hx⟩ => ⟨fun _ => x,hx⟩,fun ⟨u,hu⟩ => ⟨u 0,hu⟩⟩

theorem definable_forall_one {P : (ι → M) → M → Prop}
    (h : S.Definable L {z : ι ⊕ Fin 1 → M | P (z ∘ Sum.inl) (z (.inr 0))}) :
    S.Definable L {z : ι → M | ∀ x, P z x} := by
  have hn := definable_exists_one (P := fun z a => ¬ P z a) h.compl
  convert hn.compl using 1
  ext z
  change (∀ x, P z x) ↔ ¬ ∃ x, ¬ P z x
  exact not_exists_not.symm

theorem definable_binary_at {R : M → M → Prop}
    (h : S.Definable₂ L {p | R p.1 p.2}) (i j : ι) :
    S.Definable L {z : ι → M | R (z i) (z j)} := by
  convert h.preimage_comp (![i,j] : Fin 2 → ι) using 1
  ext z
  rfl

theorem definable_unary_at {R : M → Prop}
    (h : S.Definable₁ L {x | R x}) (i : ι) :
    S.Definable L {z : ι → M | R (z i)} := by
  exact h.preimage_comp (fun _ : Fin 1 => i)

end SpecialTransformations.ModelTheory

namespace SpecialTransformations.Section3.GammaParameters.EndpointLogic
open SpecialTransformations.ModelTheory
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The normalized raw order is used inside formulas; on proper codes it
agrees with the original order, including when the original structure has
different interpretations away from the indicated sorts. -/
def codeLe (a b : M) : Prop := @iLe M (CanonicalStructure.normalize (M := M)) a b

def Lower (P : M → M → Prop) (b t : M) : Prop :=
  NonzeroRV b ∧ ∀ a, NonzeroRV a → P a t → codeLe b a

def Infimum (P : M → M → Prop) (b t : M) : Prop :=
  Lower P b t ∧ ∀ c, Lower P c t → codeLe c b

def Bounded (P : M → M → Prop) (t : M) : Prop := ∃ b, Lower P b t

def Complement (P : M → M → Prop) (a t : M) : Prop :=
  NonzeroRV a ∧ iRV t ∧ ¬ P a t

def Endpoint (P : M → M → Prop) (b t : M) : Prop :=
  NonzeroRV b ∧ iRV t ∧
    ((Bounded P t ∧ Infimum P b t) ∨ (¬ Bounded P t ∧ Infimum (Complement P) b t))

theorem codeLe_definable (S : Set M) :
    @Set.Definable₂ M S LRV (CanonicalStructure.normalize (M := M))
      {p | codeLe p.1 p.2} := by
  exact @raw_le_definable M (CanonicalStructure.normalize (M := M)) S

theorem lower_definable (S : Set M) (P : M → M → Prop)
    (hP : @Set.Definable₂ M S LRV (CanonicalStructure.normalize (M := M))
      {p | P p.1 p.2}) :
    @Set.Definable₂ M S LRV (CanonicalStructure.normalize (M := M))
      {p | Lower P p.1 p.2} := by
  have hp := @nonzero_rv_definable M (CanonicalStructure.normalize (M := M)) S
  have he : {x : M | @NonzeroRV M (CanonicalStructure.normalize (M := M)) x} =
      {x | NonzeroRV x} := Set.ext (nonzero_rv_normalize (M := M))
  rw [he] at hp
  have hl := codeLe_definable (M := M) S
  let nz : M → Prop := NonzeroRV
  let le : M → M → Prop := codeLe
  let lo := Lower P
  let N := CanonicalStructure.normalize (M := M)
  letI := N
  have hb := definable_unary_at hp (0 : Fin 2)
  have ha := definable_unary_at hp (Sum.inr (0 : Fin 1) : Fin 2 ⊕ Fin 1)
  have hPa := definable_binary_at hP (Sum.inr (0 : Fin 1)) (Sum.inl (1 : Fin 2))
  have hba := definable_binary_at hl (Sum.inl (0 : Fin 2)) (Sum.inr (0 : Fin 1))
  have hall := definable_forall_one (P := fun z a => ¬ (nz a ∧ P a (z 1)) ∨ le (z 0) a)
    ((ha.inter hPa).compl.union hba)
  change S.Definable LRV {z : Fin 2 → M | lo (z 0) (z 1)}
  convert hb.inter hall using 1
  ext z
  change lo (z 0) (z 1) ↔ (nz (z 0) ∧ ∀ a, ¬ (nz a ∧ P a (z 1)) ∨ le (z 0) a)
  simp only [lo,Lower,nz,le]
  apply and_congr Iff.rfl
  exact forall_congr' (fun a => by tauto)

theorem infimum_definable (S : Set M) (P : M → M → Prop)
    (hP : @Set.Definable₂ M S LRV (CanonicalStructure.normalize (M := M))
      {p | P p.1 p.2}) :
    @Set.Definable₂ M S LRV (CanonicalStructure.normalize (M := M))
      {p | Infimum P p.1 p.2} := by
  have hlow := lower_definable S P hP
  have hl := codeLe_definable (M := M) S
  let lo := Lower P
  let inf := Infimum P
  let le : M → M → Prop := codeLe
  let N := CanonicalStructure.normalize (M := M)
  letI := N
  have hc := definable_binary_at hlow (Sum.inr (0 : Fin 1)) (Sum.inl (1 : Fin 2))
  have hcb := definable_binary_at hl (Sum.inr (0 : Fin 1)) (Sum.inl (0 : Fin 2))
  have hall := definable_forall_one (P := fun z c => ¬ lo c (z 1) ∨ le c (z 0)) (hc.compl.union hcb)
  change S.Definable LRV {z : Fin 2 → M | inf (z 0) (z 1)}
  convert hlow.inter hall using 1
  ext z
  change inf (z 0) (z 1) ↔ (lo (z 0) (z 1) ∧ ∀ c, ¬ lo c (z 1) ∨ le c (z 0))
  simp only [inf,Infimum,lo,le]
  apply and_congr Iff.rfl
  exact forall_congr' (fun c => by tauto)

theorem bounded_definable (S : Set M) (P : M → M → Prop)
    (hP : @Set.Definable₂ M S LRV (CanonicalStructure.normalize (M := M))
      {p | P p.1 p.2}) :
    @Set.Definable₁ M S LRV (CanonicalStructure.normalize (M := M)) {t | Bounded P t} := by
  have hlow := lower_definable S P hP
  let N := CanonicalStructure.normalize (M := M)
  letI := N
  have hr := definable_binary_at hlow (Sum.inr (0 : Fin 1)) (Sum.inl (0 : Fin 1))
  exact definable_exists_one hr

theorem complement_definable (S : Set M) (P : M → M → Prop)
    (hP : @Set.Definable₂ M S LRV (CanonicalStructure.normalize (M := M))
      {p | P p.1 p.2}) :
    @Set.Definable₂ M S LRV (CanonicalStructure.normalize (M := M))
      {p | Complement P p.1 p.2} := by
  have hp := @nonzero_rv_definable M (CanonicalStructure.normalize (M := M)) S
  have he : {x : M | @NonzeroRV M (CanonicalStructure.normalize (M := M)) x} =
      {x | NonzeroRV x} := Set.ext (nonzero_rv_normalize (M := M))
  rw [he] at hp
  have ht := ((definableAt_iff_normalized_raw S .rv {x | iRV x}).mp
    (definableAt_sort S .rv)).1
  let C := Complement P
  let N := CanonicalStructure.normalize (M := M)
  letI := N
  have h := ((definable_unary_at hp (0 : Fin 2)).inter
    (definable_unary_at ht (1 : Fin 2))).inter hP.compl
  change S.Definable LRV {z : Fin 2 → M | C (z 0) (z 1)}
  convert h using 1
  ext z
  exact and_assoc.symm

theorem endpoint_definable (S : Set M) (P : M → M → Prop)
    (hP : @Set.Definable₂ M S LRV (CanonicalStructure.normalize (M := M))
      {p | P p.1 p.2}) :
    @Set.Definable₂ M S LRV (CanonicalStructure.normalize (M := M))
      {p | Endpoint P p.1 p.2} := by
  have hp := @nonzero_rv_definable M (CanonicalStructure.normalize (M := M)) S
  have he : {x : M | @NonzeroRV M (CanonicalStructure.normalize (M := M)) x} =
      {x | NonzeroRV x} := Set.ext (nonzero_rv_normalize (M := M))
  rw [he] at hp
  have ht := ((definableAt_iff_normalized_raw S .rv {x | iRV x}).mp
    (definableAt_sort S .rv)).1
  have hb := bounded_definable S P hP
  have hi := infimum_definable S P hP
  have hj := infimum_definable S (Complement P) (complement_definable S P hP)
  let E := Endpoint P
  let N := CanonicalStructure.normalize (M := M)
  letI := N
  have hb' := definable_unary_at hb (1 : Fin 2)
  change S.Definable LRV {z : Fin 2 → M | E (z 0) (z 1)}
  convert ((definable_unary_at hp (0 : Fin 2)).inter (definable_unary_at ht (1 : Fin 2))).inter
    ((hb'.inter hi).union (hb'.compl.inter hj))
    using 1
  ext z
  exact and_assoc.symm

end SpecialTransformations.Section3.GammaParameters.EndpointLogic

/- Component: EndpointCodeSemantics -/
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters.EndpointLogic
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem codeValue_surjective : ∀ γ : Values.Gamma (M := M),
    ∃ a : M, NonzeroRV a ∧ codeValue a = γ := by
  intro γ
  let u := representative γ
  exact ⟨raw u,⟨raw_rv u,raw_ne_zero u⟩,(codeValue_raw u).trans (representative_value γ)⟩

theorem codeLe_iff (a b : M) (ha : NonzeroRV a) (hb : NonzeroRV b) :
    codeLe a b ↔ codeValue a ≤ codeValue b := by
  simp only [codeValue,dif_pos ha,dif_pos hb]
  change @iLe M (CanonicalStructure.normalize (M := M)) a b ↔
    Values.vrv (⟨a,ha.1⟩ : CanonicalRV.RVSort M) ≤ Values.vrv ⟨b,hb.1⟩
  exact (rv_le_normalize a b ha.1 hb.1).trans
    (Values.vrv_le_iff (⟨a,ha.1⟩ : CanonicalRV.RVSort M) ⟨b,hb.1⟩).symm

theorem lower_iff (R : Values.Gamma (M := M) → M → Prop) (P : M → M → Prop)
    (t b : M) (hb : NonzeroRV b)
    (hP : ∀ a, NonzeroRV a → (P a t ↔ R (codeValue a) t)) :
    Lower P b t ↔ ∀ γ, R γ t → codeValue b ≤ γ := by
  constructor
  · intro h γ hγ
    obtain ⟨a,ha,he⟩ := codeValue_surjective γ
    have hp : P a t := (hP a ha).mpr (he.symm ▸ hγ)
    have hle := (codeLe_iff b a hb ha).mp (h.2 a ha hp)
    rwa [he] at hle
  · intro h
    exact ⟨hb,fun a ha hp => (codeLe_iff b a hb ha).mpr (h _ ((hP a ha).mp hp))⟩

theorem bounded_iff (R : Values.Gamma (M := M) → M → Prop) (P : M → M → Prop)
    (t : M) (hP : ∀ a, NonzeroRV a → (P a t ↔ R (codeValue a) t)) :
    Bounded P t ↔ FiniteThresholds.BoundedBelow {γ | R γ t} := by
  constructor
  · rintro ⟨b,hb⟩
    exact ⟨codeValue b,(lower_iff R P t b hb.1 hP).mp hb⟩
  · rintro ⟨β,hβ⟩
    obtain ⟨b,hb,he⟩ := codeValue_surjective β
    refine ⟨b,(lower_iff R P t b hb hP).mpr ?_⟩
    intro γ hγ
    rw [he]
    exact hβ γ hγ

theorem infimum_iff (R : Values.Gamma (M := M) → M → Prop) (P : M → M → Prop)
    (t b : M) (hb : NonzeroRV b)
    (hP : ∀ a, NonzeroRV a → (P a t ↔ R (codeValue a) t)) :
    Infimum P b t ↔ FiniteThresholds.IsInfimum {γ | R γ t} (codeValue b) := by
  constructor
  · rintro ⟨hl,hgreat⟩
    refine ⟨(lower_iff R P t b hb hP).mp hl,?_⟩
    intro β hβ
    obtain ⟨a,ha,he⟩ := codeValue_surjective β
    have hla : Lower P a t := (lower_iff R P t a ha hP).mpr (by
      intro γ hγ
      rw [he]
      exact hβ γ hγ)
    have hle := (codeLe_iff a b ha hb).mp (hgreat a hla)
    rwa [he] at hle
  · rintro ⟨hl,hgreat⟩
    refine ⟨(lower_iff R P t b hb hP).mpr hl,?_⟩
    intro a ha
    exact (codeLe_iff a b ha.1 hb).mpr (hgreat _ ((lower_iff R P t a ha.1 hP).mp ha))

theorem endpoint_iff (R : Values.Gamma (M := M) → M → Prop) (P : M → M → Prop)
    (t b : M) (ht : iRV t) (hb : NonzeroRV b)
    (hP : ∀ a, NonzeroRV a → (P a t ↔ R (codeValue a) t)) :
    Endpoint P b t ↔ FiniteThresholds.CanonicalEndpoint {γ | R γ t} (codeValue b) := by
  have hPc : ∀ a, NonzeroRV a → (Complement P a t ↔ ¬ R (codeValue a) t) := by
    intro a ha
    simp only [Complement,and_iff_right ha,and_iff_right ht,hP a ha]
  change (NonzeroRV b ∧ iRV t ∧
    ((Bounded P t ∧ Infimum P b t) ∨ (¬ Bounded P t ∧ Infimum (Complement P) b t))) ↔ _
  rw [and_iff_right hb,and_iff_right ht,bounded_iff R P t hP,
    infimum_iff R P t b hb hP,infimum_iff (fun γ t => ¬ R γ t) (Complement P) t b hb hPc]
  rfl

def codeLt (a b : M) : Prop := codeLe a b ∧ ¬ codeLe b a

theorem codeLt_iff (a b : M) (ha : NonzeroRV a) (hb : NonzeroRV b) :
    codeLt a b ↔ codeValue a < codeValue b := by
  rw [codeLt,codeLe_iff a b ha hb,codeLe_iff b a hb ha,lt_iff_le_not_ge]

theorem codeLt_definable (S : Set M) :
    @Set.Definable₂ M S LRV (CanonicalStructure.normalize (M := M))
      {p | codeLt p.1 p.2} := by
  have hl := codeLe_definable (M := M) S
  let N := CanonicalStructure.normalize (M := M)
  letI := N
  exact hl.inter (SpecialTransformations.ModelTheory.definable_binary_at hl (1 : Fin 2) 0).compl

/-- The complete order-cut graph of the intrinsic endpoint selector is
first-order definable on all proper threshold codes. The selector itself
is supplied only with its proved endpoint property; uniqueness removes
the temporary code used in the existential formula. -/
theorem endpoint_cuts_definable (S D : Set M)
    (hD : DefinableAt S .rv D)
    (R : Values.Gamma (M := M) → M → Prop) (P : M → M → Prop)
    (hP : @Set.Definable₂ M S LRV (CanonicalStructure.normalize (M := M))
      {p | P p.1 p.2})
    (hPR : ∀ t ∈ D, ∀ a, NonzeroRV a → (P a t ↔ R (codeValue a) t))
    (f : M → Values.Gamma (M := M))
    (hf : ∀ t ∈ D, FiniteThresholds.CanonicalEndpoint {γ | R γ t} (f t)) :
    @Set.Definable₂ M S LRV (CanonicalStructure.normalize (M := M))
      {p | NonzeroRV p.1 ∧ p.2 ∈ D ∧ f p.2 < codeValue p.1} := by
  have hp := nonzero_codes_normalized_definable (M := M) S
  have hd := (definableAt_iff_normalized_raw S .rv D).mp hD |>.1
  have he := endpoint_definable S P hP
  have hl := codeLt_definable (M := M) S
  let E (a t : M) := ∃ b, Endpoint P b t ∧ codeLt b a
  have hE : @Set.Definable₂ M S LRV (CanonicalStructure.normalize (M := M))
      {p | E p.1 p.2} := by
    let N := CanonicalStructure.normalize (M := M)
    letI := N
    have he' := SpecialTransformations.ModelTheory.definable_binary_at he
      (Sum.inr (0 : Fin 1)) (Sum.inl (1 : Fin 2))
    have hl' := SpecialTransformations.ModelTheory.definable_binary_at hl
      (Sum.inr (0 : Fin 1)) (Sum.inl (0 : Fin 2))
    exact SpecialTransformations.ModelTheory.definable_exists_one (he'.inter hl')
  have hEq : {p : M × M | NonzeroRV p.1 ∧ p.2 ∈ D ∧ f p.2 < codeValue p.1} =
      {p | NonzeroRV p.1 ∧ p.2 ∈ D ∧ E p.1 p.2} := by
    ext p
    constructor
    · rintro ⟨ha,ht,hcut⟩
      obtain ⟨b,hb,hbval⟩ := codeValue_surjective (f p.2)
      refine ⟨ha,ht,b,?_,(codeLt_iff b p.1 hb ha).mpr (by simpa only [hbval] using hcut)⟩
      apply (endpoint_iff R P p.2 b (hD.2 ht) hb (hPR p.2 ht)).mpr
      simpa only [hbval] using hf p.2 ht
    · rintro ⟨ha,ht,b,hb,hcut⟩
      have hb' := (endpoint_iff R P p.2 b (hD.2 ht) hb.1 (hPR p.2 ht)).mp hb
      have hval : codeValue b = f p.2 := FiniteThresholds.canonicalEndpoint_unique hb' (hf p.2 ht)
      refine ⟨ha,ht,?_⟩
      simpa only [hval] using (codeLt_iff b p.1 hb.1 ha).mp hcut
  rw [hEq]
  let A : Set (M × M) := {p | NonzeroRV p.1 ∧ p.2 ∈ D ∧ E p.1 p.2}
  change @Set.Definable₂ M S LRV (CanonicalStructure.normalize (M := M)) A
  let N := CanonicalStructure.normalize (M := M)
  letI := N
  change S.Definable LRV {z : Fin 2 → M | (z 0,z 1) ∈ A}
  convert ((SpecialTransformations.ModelTheory.definable_unary_at hp (0 : Fin 2)).inter
    (SpecialTransformations.ModelTheory.definable_unary_at hd (1 : Fin 2))).inter hE using 1
  ext z
  exact and_assoc.symm

end SpecialTransformations.Section3.GammaParameters.EndpointLogic

/- Component: CofiniteRelationBounds -/
open Classical
namespace SpecialTransformations.Section3

/-- A relation with at most d outputs at every point of an infinite set
has at most d parameters whose reverse fibres are cofinite in that set. -/
theorem cofinite_reverse_fibres_bounded {α β : Type} (X : Set α) (hX : X.Infinite)
    (R : α → β → Prop) (d : ℕ)
    (hrows : ∀ x ∈ X, {t | R x t}.Finite ∧ {t | R x t}.ncard ≤ d) :
    {t | {x | x ∈ X ∧ ¬ R x t}.Finite}.Finite ∧
      {t | {x | x ∈ X ∧ ¬ R x t}.Finite}.ncard ≤ d := by
  apply GammaParameters.no_injection_iff_finite_ncard_le.mp
  rintro ⟨u,hu,hm⟩
  let F : Set α := ⋃ i : Fin (d+1), {x | x ∈ X ∧ ¬ R x (u i)}
  have hF : F.Finite := Set.finite_iUnion (fun i => hm i)
  obtain ⟨x,hx,hxF⟩ := (hX.sdiff hF).nonempty
  apply GammaParameters.no_injection_iff_finite_ncard_le.mpr (hrows x hx)
  refine ⟨u,hu,fun i => ?_⟩
  by_contra hn
  exact hxF (Set.mem_iUnion.mpr ⟨i,hx,hn⟩)

end SpecialTransformations.Section3

/- Component: UniformFiniteRows -/
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
namespace SpecialTransformations.Section3.RawClosure.Tuple
variable {M : Type} [LRV.Structure M] {n : ℕ}

theorem uniform_finite_rows {κ : Cardinal} (hs : Saturated M κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ)
    (D : Set (Fin n → M)) (hD : S.Definable LRV D)
    (R : Set ((Fin n → M) × M)) (hR : RelationDefinable S R)
    (hfinite : ∀ a ∈ D, {x | (a,x) ∈ R}.Finite) :
    ∃ N : ℕ, ∀ a ∈ D, {x | (a,x) ∈ R}.Finite ∧ {x | (a,x) ∈ R}.ncard ≤ N := by
  let C (k : ℕ) : Set (Fin n → M) := (HasMore R k)ᶜ
  have hCd (k : ℕ) : S.Definable LRV (C k) := (hasMore_definable S R hR k).compl
  have hcover : ∀ a ∈ D, ∃ c ∈ Set.range C, a ∈ c := by
    intro a ha
    refine ⟨C {x | (a,x) ∈ R}.ncard,Set.mem_range_self _,?_⟩
    exact no_inj_iff_finite_ncard_le.mpr ⟨hfinite a ha,le_rfl⟩
  obtain ⟨C₀,hC₀,hsub,hcov⟩ := hs.definable_finite_subcover_tuple
    S hsmall D hD (Set.range C) (by rintro c ⟨k,rfl⟩; exact hCd k) hcover
  letI := hC₀.fintype
  choose k hk using fun c : C₀ => hsub c.property
  let N := Finset.univ.sup k
  refine ⟨N,fun a ha => ?_⟩
  obtain ⟨c,hc,hac⟩ := hcov a ha
  let c' : C₀ := ⟨c,hc⟩
  have hkN : k c' ≤ N := Finset.le_sup (Finset.mem_univ c')
  have hac' : a ∈ C (k c') := (hk c').symm ▸ hac
  have hh := (no_inj_iff_finite_ncard_le (s := {x | (a,x) ∈ R}) (k := k c')).mp hac'
  exact ⟨hh.1,hh.2.trans hkN⟩

end SpecialTransformations.Section3.RawClosure.Tuple

/- Component: GammaRVFamilies -/
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem rv_finite_of_finite_value_fibres (h00 : M ⊨ Axioms.ACVF00)
    (S A : Set M) (hA : DefinableAt S .rv A)
    (hfibres : ∀ γ : Values.Gamma (M := M), (Values.fibre A γ).Finite) : A.Finite := by
  have hV := Values.finite_nonempty_values_finite h00 S A hA
  let z : CanonicalRV.RVSort M := ⟨iRVZero,SpecialTransformations.Milestone0.Transfer.rv_zero_mem hM⟩
  have hfinite : ({z} ∪ ⋃ γ ∈ Values.finiteNonemptyValues A, Values.fibre A γ).Finite :=
    (Set.finite_singleton z).union (hV.biUnion (fun γ _ => hfibres γ))
  let T : Set (CanonicalRV.RVSort M) := {t | t.val ∈ A}
  have hT : T.Finite := hfinite.subset (by
    intro t ht
    by_cases ht0 : t.val = iRVZero
    · exact Or.inl (Subtype.ext ht0)
    · right
      let γ := Values.gammaOf t ht0
      have htγ : t ∈ Values.fibre A γ := ⟨rfl,ht⟩
      exact Set.mem_iUnion.mpr ⟨γ,Set.mem_iUnion.mpr ⟨⟨⟨t,htγ⟩,hfibres γ⟩,htγ⟩⟩)
  have he : Subtype.val '' T = A := by
    ext a
    exact ⟨fun ⟨t,ht,he⟩ => he ▸ ht,fun ha => ⟨⟨a,hA.2 ha⟩,ha,rfl⟩⟩
  rw [← he]
  exact hT.image Subtype.val

/-- A genuine uniform family indexed by actual Gamma, with its entire
first-order preimage on all nonzero RV representatives. -/
structure GammaRVFamily (S : Set M) where
  relation : Values.Gamma (M := M) → M → Prop
  sorted : ∀ γ t, relation γ t → iRV t
  definable : @Set.Definable₂ M S LRV (CanonicalStructure.normalize (M := M))
    {p | NonzeroRV p.1 ∧ relation (codeValue p.1) p.2}

namespace GammaRVFamily
variable {S : Set M} (F : GammaRVFamily (M := M) S)

def rawRelation (a t : M) : Prop := NonzeroRV a ∧ F.relation (codeValue a) t

def mono {T : Set M} (hST : S ⊆ T) : GammaRVFamily (M := M) T where
  relation := F.relation
  sorted := F.sorted
  definable := by
    have hd := F.definable
    letI := CanonicalStructure.normalize (M := M)
    exact hd.mono hST

theorem column_definable (t : M) :
    Values.GammaDefinable (insert t S) {γ | F.relation γ t} := by
  let P := F.rawRelation
  have he : {a | P a t} = Values.gammaPullback {γ | F.relation γ t} := by
    ext a
    constructor
    · rintro ⟨ha,hr⟩
      refine ⟨ha.1,ha.2,?_⟩
      have hv : codeValue a = Values.gammaOf ⟨a,ha.1⟩ ha.2 := by
        simp only [codeValue,dif_pos ha]
        rfl
      exact hv ▸ hr
    · rintro ⟨hr,h0,hmem⟩
      have ha : NonzeroRV a := ⟨hr,h0⟩
      refine ⟨ha,?_⟩
      have hv : codeValue a = Values.gammaOf ⟨a,hr⟩ h0 := by
        simp only [codeValue,dif_pos ha]
        rfl
      exact hv.symm ▸ hmem
  have hraw := F.definable
  have hd : @Set.Definable₁ M (insert t S) LRV (CanonicalStructure.normalize (M := M)) {a | P a t} := by
    letI := CanonicalStructure.normalize (M := M)
    have hmap : (insert t S).DefinableMap LRV
        (fun z : Fin 1 → M => (![z 0,t] : Fin 2 → M)) := by
      intro i
      fin_cases i
      · exact Set.DefinableFun.proj LRV
      · exact LRV.definableFun_const (Fin 1) (Set.mem_insert t S)
    exact (hraw.mono (Set.subset_insert t S)).preimage_map hmap
  change DefinableAt (insert t S) .rv _
  rw [← he]
  exact (definableAt_iff_normalized_raw (insert t S) .rv _).mpr
    ⟨hd,fun a ha => ha.1.1⟩

theorem column_thresholds (h00 : M ⊨ Axioms.ACVF00) (t : M) :
    ∃ E : Finset (Values.Gamma (M := M)), FiniteThresholds.Determines E {γ | F.relation γ t} := by
  exact gamma_definable_finite_thresholds h00 ⟨insert t S,∅⟩ _
    (real_definableAtBase ⟨insert t S,∅⟩ .rv _ (F.column_definable t))

theorem finite_endpoint_fibres (h00 : M ⊨ Axioms.ACVF00) (d : ℕ)
    (hrows : ∀ γ, {t | F.relation γ t}.Finite ∧ {t | F.relation γ t}.ncard ≤ d)
    (D : Set M) (f : M → Values.Gamma (M := M))
    (hne : ∀ t ∈ D, {γ | F.relation γ t}.Nonempty)
    (hf : ∀ t ∈ D, FiniteThresholds.CanonicalEndpoint {γ | F.relation γ t} (f t))
    (β : Values.Gamma (M := M)) : {t | t ∈ D ∧ f t = β}.Finite := by
  apply FiniteThresholds.finite_touched_parameters F.relation β d hrows
  rintro t ⟨ht,he⟩
  obtain ⟨E,hE⟩ := F.column_thresholds h00 t
  have hb : FiniteThresholds.CanonicalEndpoint {γ | F.relation γ t} β := he ▸ hf t ht
  have htouch := FiniteThresholds.canonicalEndpoint_touches E _ hE (hne t ht) β hb
  rcases htouch with h | ⟨e,hbe,hlocal⟩ | ⟨e,heb,hlocal⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨e,hbe,fun x hx hxe => hlocal ⟨hx,hxe⟩⟩)
  · exact Or.inr (Or.inr ⟨e,heb,fun x hx hex => hlocal ⟨hex,hx⟩⟩)

/-- On a fixed actual RV value fibre, a definable domain of selected
nonempty column endpoints is finite. Finite image comes from first-order
cuts; finite inverse fibres come from the uniform finite-row bound. -/
theorem finite_in_value_fibre {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk S < κ)
    (γ : Values.Gamma (M := M)) (D : Set M) (hD : DefinableAt S .rv D)
    (hDγ : ∀ t : CanonicalRV.RVSort M, t.val ∈ D → Values.vrv t = γ.val)
    (d : ℕ) (hrows : ∀ β, {t | F.relation β t}.Finite ∧ {t | F.relation β t}.ncard ≤ d)
    (f : M → Values.Gamma (M := M))
    (hne : ∀ t ∈ D, {β | F.relation β t}.Nonempty)
    (hf : ∀ t ∈ D, FiniteThresholds.CanonicalEndpoint {β | F.relation β t} (f t)) :
    D.Finite := by
  have hcuts := EndpointLogic.endpoint_cuts_definable S D hD F.relation F.rawRelation F.definable
    (fun t _ a ha => and_iff_right ha) f hf
  have hraw : @RawClosure.Tuple.RelationDefinable M (CanonicalStructure.normalize (M := M)) 1 S
      (cutFamily D f) := by
    let C := cutFamily D f
    letI := CanonicalStructure.normalize (M := M)
    change S.Definable LRV {z : Fin 1 ⊕ Fin 1 → M | (z ∘ Sum.inl,z (.inr 0)) ∈ C}
    exact hcuts.preimage_comp (![Sum.inl 0,Sum.inr 0] : Fin 2 → Fin 1 ⊕ Fin 1)
  have himage := finite_image_of_definable_cuts hs S D hsmall hD γ hDγ f hraw
  apply Set.Finite.of_finite_fibers f himage
  intro β _
  exact F.finite_endpoint_fibres h00 d hrows D f hne hf β

end GammaRVFamily
end SpecialTransformations.Section3.GammaParameters

/- Component: ValueFibreDomains -/
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- A single real representative defines the full value fibre, rather
than a selected angular class. This is a temporary parameter extension. -/
theorem value_fibre_domain_definable (S : Set M) (γ : Values.Gamma (M := M)) :
    DefinableAt (insert (raw (representative γ)) S) .rv (Values.gammaPullback {γ}) := by
  let a := raw (representative γ)
  let T := insert a S
  have ha : NonzeroRV a := ⟨raw_rv _,raw_ne_zero _⟩
  let P : M → M → Prop := SameScalar
  have hs : @Set.Definable M T LRV (CanonicalStructure.normalize (M := M)) (Fin 2)
      {z | P (z 0) (z 1)} := by
    have hd := @same_scalar_definable M (CanonicalStructure.normalize (M := M)) T
    have he : {z : Fin 2 → M |
        @SameScalar M (CanonicalStructure.normalize (M := M)) (z 0) (z 1)} =
        {z | P (z 0) (z 1)} := Set.ext (fun z => same_scalar_normalize (z 0) (z 1))
    exact he ▸ hd
  have hd : @Set.Definable₁ M T LRV (CanonicalStructure.normalize (M := M)) {t | P a t} := by
    letI := CanonicalStructure.normalize (M := M)
    have hm : T.DefinableMap LRV (fun z : Fin 1 → M => (![a,z 0] : Fin 2 → M)) := by
      intro i
      fin_cases i
      · exact LRV.definableFun_const (Fin 1) (Set.mem_insert a S)
      · exact Set.DefinableFun.proj LRV
    exact hs.preimage_map hm
  have he : {t | P a t} = Values.gammaPullback {γ} := by
    ext t
    constructor
    · intro h
      let u : Code (M := M) := ⟨⟨t,h.2.1.1⟩,h.2.1.2⟩
      have hu : value u = γ :=
        ((value_eq_iff (representative γ) u).mpr h.2.2).symm.trans (representative_value γ)
      exact (mem_gammaPullback_code {γ} u).mpr (Set.mem_singleton_iff.mpr hu)
    · rintro ⟨ht,h0,hmem⟩
      let u : Code (M := M) := ⟨⟨t,ht⟩,h0⟩
      have hu : value u = γ := Set.mem_singleton_iff.mp hmem
      have hh := (value_eq_iff (representative γ) u).mp ((representative_value γ).trans hu.symm)
      exact ⟨ha,⟨ht,h0⟩,hh⟩
  rw [← he]
  exact (definableAt_iff_normalized_raw T .rv _).mpr ⟨hd,fun t ht => ht.2.1.1⟩

end SpecialTransformations.Section3.GammaParameters

/- Component: GammaRVDomains -/
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem DefinableAt.sdiff {S A C : Set M} {σ : SortTag}
    (hA : DefinableAt S σ A) (hC : DefinableAt S σ C) : DefinableAt S σ (A \ C) := by
  have ha := (definableAt_iff_normalized_raw S σ A).mp hA
  have hc := (definableAt_iff_normalized_raw S σ C).mp hC
  apply (definableAt_iff_normalized_raw S σ (A \ C)).mpr
  refine ⟨?_,fun x hx => hA.2 hx.1⟩
  letI := CanonicalStructure.normalize (M := M)
  exact ha.1.sdiff hc.1

end SpecialTransformations.Section3

namespace SpecialTransformations.Section3.GammaParameters.GammaRVFamily
open SpecialTransformations.ModelTheory
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} (F : GammaRVFamily (M := M) S)

def nonemptyDomain : Set M := {t | ∃ γ, F.relation γ t}
def wholeDomain : Set M := {t | ∀ γ, F.relation γ t}
def properDomain : Set M := F.nonemptyDomain \ F.wholeDomain

theorem nonempty_domain_definable : DefinableAt S .rv F.nonemptyDomain := by
  let P := F.rawRelation
  let D := F.nonemptyDomain
  have he : D = {t | ∃ a, P a t} := by
    ext t
    constructor
    · rintro ⟨γ,hγ⟩
      obtain ⟨a,ha,hval⟩ := EndpointLogic.codeValue_surjective γ
      exact ⟨a,ha,hval.symm ▸ hγ⟩
    · rintro ⟨a,ha⟩
      exact ⟨codeValue a,ha.2⟩
  have hp := F.definable
  have hd : @Set.Definable₁ M S LRV (CanonicalStructure.normalize (M := M)) {t | ∃ a, P a t} := by
    letI := CanonicalStructure.normalize (M := M)
    have hr := definable_binary_at (R := P) hp (Sum.inr (0 : Fin 1)) (Sum.inl (0 : Fin 1))
    exact definable_exists_one (P := fun z a => P a (z 0)) hr
  apply (definableAt_iff_normalized_raw S .rv D).mpr
  refine ⟨he.symm ▸ hd,?_⟩
  rintro t ⟨γ,hγ⟩
  exact F.sorted γ t hγ

theorem whole_domain_definable : DefinableAt S .rv F.wholeDomain := by
  let P := F.rawRelation
  let nz : M → Prop := NonzeroRV
  let D := F.wholeDomain
  have he : D = {t | ∀ a, ¬ nz a ∨ P a t} := by
    ext t
    constructor
    · intro ht a
      by_cases ha : nz a
      · exact Or.inr ⟨ha,ht (codeValue a)⟩
      · exact Or.inl ha
    · intro ht γ
      obtain ⟨a,ha,hval⟩ := EndpointLogic.codeValue_surjective γ
      have hpa : P a t := (ht a).resolve_left (not_not.mpr ha)
      exact hval ▸ hpa.2
  have hp := F.definable
  have hn := nonzero_codes_normalized_definable (M := M) S
  have hd : @Set.Definable₁ M S LRV (CanonicalStructure.normalize (M := M))
      {t | ∀ a, ¬ nz a ∨ P a t} := by
    letI := CanonicalStructure.normalize (M := M)
    have hp' := definable_binary_at (R := P) hp (Sum.inr (0 : Fin 1)) (Sum.inl (0 : Fin 1))
    have hn' := definable_unary_at hn (Sum.inr (0 : Fin 1) : Fin 1 ⊕ Fin 1)
    exact definable_forall_one (P := fun z a => ¬ nz a ∨ P a (z 0)) (hn'.compl.union hp')
  apply (definableAt_iff_normalized_raw S .rv D).mpr
  exact ⟨he.symm ▸ hd,fun t ht => F.sorted 1 t (ht 1)⟩

theorem proper_domain_definable : DefinableAt S .rv F.properDomain :=
  F.nonempty_domain_definable.sdiff F.whole_domain_definable

theorem endpoint_on_proper_domain (h00 : M ⊨ Axioms.ACVF00) (t : M)
    (ht : t ∈ F.properDomain) :
    ∃ c : Values.Gamma (M := M),
      FiniteThresholds.CanonicalEndpoint {γ | F.relation γ t} c := by
  obtain ⟨E,hE⟩ := F.column_thresholds h00 t
  have hne : {γ | F.relation γ t}.Nonempty := ht.1
  have hcomp : {γ | F.relation γ t}ᶜ.Nonempty := by
    have hn : ¬ ∀ γ, F.relation γ t := ht.2
    push_neg at hn
    exact hn
  exact FiniteThresholds.canonicalEndpoint_exists E _ hE hne hcomp

noncomputable def endpointSelector (h00 : M ⊨ Axioms.ACVF00) (t : M) : Values.Gamma (M := M) :=
  if h : t ∈ F.properDomain then Classical.choose (F.endpoint_on_proper_domain h00 t h) else 1

theorem endpointSelector_spec (h00 : M ⊨ Axioms.ACVF00) (t : M) (ht : t ∈ F.properDomain) :
    FiniteThresholds.CanonicalEndpoint {γ | F.relation γ t} (F.endpointSelector h00 t) := by
  simp only [endpointSelector,dif_pos ht]
  exact Classical.choose_spec (F.endpoint_on_proper_domain h00 t ht)

end SpecialTransformations.Section3.GammaParameters.GammaRVFamily

/- Component: GammaRVSeparation -/
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters.GammaRVFamily
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} (F : GammaRVFamily (M := M) S)

theorem uniform_row_bound {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (hfinite : ∀ γ, {t | F.relation γ t}.Finite) :
    ∃ d : ℕ, ∀ γ, {t | F.relation γ t}.Finite ∧ {t | F.relation γ t}.ncard ≤ d := by
  let P : Set (Fin 1 → M) := {a | NonzeroRV (a 0)}
  let R : Set ((Fin 1 → M) × M) := {p | F.rawRelation (p.1 0) p.2}
  have hp := nonzero_codes_normalized_definable (M := M) S
  have hd := F.definable
  have hr : @RawClosure.Tuple.RelationDefinable M (CanonicalStructure.normalize (M := M)) 1 S R := by
    letI := CanonicalStructure.normalize (M := M)
    exact hd.preimage_comp (![Sum.inl 0,Sum.inr 0] : Fin 2 → Fin 1 ⊕ Fin 1)
  have hf (a : Fin 1 → M) (_ : a ∈ P) : {t | (a,t) ∈ R}.Finite :=
    (hfinite (codeValue (a 0))).subset (fun t ht => ht.2)
  obtain ⟨d,hbound⟩ := @RawClosure.Tuple.uniform_finite_rows M
    (CanonicalStructure.normalize (M := M)) 1 κ hs.normalize S hsmall P hp R hr hf
  refine ⟨d,fun γ => ?_⟩
  let a : Fin 1 → M := fun _ => raw (representative γ)
  have ha : a ∈ P := ⟨raw_rv _,raw_ne_zero _⟩
  have he : {t | (a,t) ∈ R} = {t | F.relation γ t} := by
    ext t
    change (NonzeroRV (a 0) ∧ F.relation (codeValue (a 0)) t) ↔ F.relation γ t
    have hp' : NonzeroRV (a 0) := ha
    rw [and_iff_right hp',codeValue_raw,representative_value]
  simpa only [he] using hbound a ha

theorem proper_domain_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk S < κ)
    (d : ℕ) (hrows : ∀ γ, {t | F.relation γ t}.Finite ∧ {t | F.relation γ t}.ncard ≤ d) :
    F.properDomain.Finite := by
  let D := F.properDomain
  let f := F.endpointSelector h00
  have hD : DefinableAt S .rv D := F.proper_domain_definable
  apply rv_finite_of_finite_value_fibres h00 S D hD
  intro γ
  let a := raw (representative γ)
  let T := insert a S
  let E : Set M := D ∩ Values.gammaPullback {γ}
  have hST : S ⊆ T := Set.subset_insert a S
  have heDef : DefinableAt T .rv E :=
    (hD.mono hST).inter (value_fibre_domain_definable S γ)
  have heγ (t : CanonicalRV.RVSort M) (ht : t.val ∈ E) : Values.vrv t = γ.val := by
    obtain ⟨hr,h0,hmem⟩ := ht.2
    have he : Values.gammaOf ⟨t.val,hr⟩ h0 = γ := Set.mem_singleton_iff.mp hmem
    exact congrArg Subtype.val he
  have hT : Cardinal.mk T < κ := small_insert hκ S hsmall a
  have heFinite : E.Finite := (F.mono hST).finite_in_value_fibre hs h00 hT γ E heDef heγ d hrows f
    (fun t ht => ht.1.1) (fun t ht => F.endpointSelector_spec h00 t ht.1)
  have hpre : (Subtype.val ⁻¹' E : Set (CanonicalRV.RVSort M)).Finite :=
    heFinite.preimage Subtype.val_injective.injOn
  apply hpre.subset
  rintro t ⟨htγ,htD⟩
  refine ⟨htD,?_⟩
  have ht0 : t.val ≠ iRVZero := by
    intro hz
    exact γ.property (htγ.symm.trans ((Values.vrv_eq_infinity_iff t).mpr hz))
  exact ⟨t.property,ht0,Set.mem_singleton_iff.mpr (Subtype.ext htγ)⟩

/-- A genuinely first-order actual-Gamma family with finite RV rows has
finite union. The proof derives actual threshold bases, defines the endpoint
cuts, applies saturation on each angular fibre, then uses checked 3.15. -/
theorem finite_projection {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk S < κ)
    (hfinite : ∀ γ, {t | F.relation γ t}.Finite) : F.nonemptyDomain.Finite := by
  obtain ⟨d,hrows⟩ := F.uniform_row_bound hs hsmall hfinite
  have hproper := F.proper_domain_finite hκ hs h00 hsmall d hrows
  have hwhole : F.wholeDomain.Finite := (hfinite 1).subset (fun t ht => ht 1)
  apply (hproper.union hwhole).subset
  intro t ht
  by_cases h : t ∈ F.wholeDomain
  · exact Or.inr h
  · exact Or.inl ⟨ht,h⟩

end SpecialTransformations.Section3.GammaParameters.GammaRVFamily
