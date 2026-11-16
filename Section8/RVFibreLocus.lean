module

public import Section8.RVLocalConstancy
public import Section8.VFDefinableTopology

@[expose] public section

/-! A single formula defines the locus where the actual RV fibre is
constant on a VF neighbourhood. -/

set_option backward.isDefEq.respectTransparency false

open Filter Topology FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [sM : LRV.Structure M] {n m : ℕ}

def rvConstantRaw (G : Set (Fin n ⊕ Fin m → M)) : Set (Fin n → M) :=
  {a | a ∈ vfRawUniverse n ∧ ∃ r : M, iVF r ∧ r ≠ iVFZero ∧
    ∀ b ∈ uniformBall a r, ∀ t : Fin m → M, (∀ i, iRV (t i)) →
      (Sum.elim b t ∈ G ↔ Sum.elim a t ∈ G)}

def rvConstantFamilyRaw {ι : Type} (G : Set (ι ⊕ (Fin n ⊕ Fin m) → M)) :
    Set (ι ⊕ Fin n → M) :=
  {z | z ∘ Sum.inr ∈ rvConstantRaw {w | Sum.elim (z ∘ Sum.inl) w ∈ G}}

theorem rvConstantFamilyRaw_definable {ι : Type} {S : Set M}
    {G : Set (ι ⊕ (Fin n ⊕ Fin m) → M)} (hG : S.Definable LRV G) :
    S.Definable LRV (rvConstantFamilyRaw G) := by
  let A := ι ⊕ Fin n
  let Z := A ⊕ Fin 1
  let X := Fin n ⊕ Fin m
  let W := Z ⊕ X
  let idx : (Fin n ⊕ Fin n) ⊕ Fin 1 → W := Sum.elim
    (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inr) (Sum.inr ∘ Sum.inl)) (Sum.inl ∘ Sum.inr)
  let fixed : ι → W := Sum.inl ∘ Sum.inl ∘ Sum.inl
  let centre : ι ⊕ X → W := Sum.elim fixed
    (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inr) (Sum.inr ∘ Sum.inr))
  let competitor : ι ⊕ X → W := Sum.elim fixed Sum.inr
  have hA := hG.preimage_comp centre
  have hB := hG.preimage_comp competitor
  have hbox := (uniformBallRelation_definable S n).preimage_comp idx
  have hRV : S.Definable LRV {z : W → M | ∀ i : Fin m, iRV (z (.inr (.inr i)))} := by
    rw [Set.ofPred_forall]
    exact Set.definable_iInter_of_finite (fun i => ((definableAt_sort S .rv).raw_definable).preimage_comp
      (fun _ : Fin 1 => (Sum.inr (Sum.inr i) : W)))
  have hBad := (hbox.inter (hRV.inter ((hA.inter hB.compl).union (hB.inter hA.compl)))).exists_of_finite
  have hr := ((definableAt_sort S .vf).raw_definable).preimage_comp (Sum.inr : Fin 1 → Z)
  have hzero : S.DefinableFun LRV (fun _ : Z → M => iVFZero) :=
    DefinableConstants.constant (DefinableConstants.function_symbol
      (L := LRV) Fn.vfZero Fin.elim0 (fun i => i.elim0))
  have hr₀ := ((Set.DefinableFun.proj LRV (i := (Sum.inr 0 : Z))).ofPred_eq hzero).compl
  have hVF := (vfRawUniverse_definable S n).preimage_comp (Sum.inr : Fin n → A)
  convert hVF.inter ((hr.inter (hr₀.inter hBad.compl)).exists_of_finite) using 1
  ext a
  have hcentre (r : Fin 1 → M) (w : X → M) :
      Sum.elim (Sum.elim a r) w ∘ centre =
        Sum.elim (a ∘ Sum.inl) (Sum.elim (a ∘ Sum.inr) (w ∘ Sum.inr)) := by
    funext i
    rcases i with _ | (_ | _) <;> rfl
  have hcompetitor (r : Fin 1 → M) (w : X → M) :
      Sum.elim (Sum.elim a r) w ∘ competitor = Sum.elim (a ∘ Sum.inl) w := by
    funext i
    cases i <;> rfl
  let row : Set (X → M) := {w | Sum.elim (a ∘ Sum.inl) w ∈ G}
  change a ∘ Sum.inr ∈ rvConstantRaw row ↔ _
  constructor
  · rintro ⟨ha, r, hr, hr₀, h⟩
    refine ⟨ha, ![r], hr, hr₀, ?_⟩
    rintro ⟨w, hw⟩
    have he : w = Sum.elim (w ∘ Sum.inl) (w ∘ Sum.inr) := by
      funext i
      cases i <;> rfl
    have hA' := h (w ∘ Sum.inl) hw.1 (w ∘ Sum.inr) hw.2.1
    have hBad' := hw.2.2
    change ((Sum.elim (Sum.elim a ![r]) w ∘ centre ∈ G ∧
      Sum.elim (Sum.elim a ![r]) w ∘ competitor ∉ G) ∨
      (Sum.elim (Sum.elim a ![r]) w ∘ competitor ∈ G ∧
        Sum.elim (Sum.elim a ![r]) w ∘ centre ∉ G)) at hBad'
    rw [hcentre, hcompetitor] at hBad'
    rw [← he] at hA'
    exact hBad'.elim (fun h => h.2 (hA'.mpr h.1)) (fun h => h.2 (hA'.mp h.1))
  · rintro ⟨ha, r, hr, hr₀, h⟩
    refine ⟨ha, r 0, hr, hr₀, fun b hb t ht => ?_⟩
    have hfalse : ¬ ((Sum.elim (a ∘ Sum.inr) t ∈ row ∧ Sum.elim b t ∉ row) ∨
        (Sum.elim b t ∈ row ∧ Sum.elim (a ∘ Sum.inr) t ∉ row)) := by
      intro hdiff
      refine h ⟨Sum.elim b t, hb, ht, ?_⟩
      change ((Sum.elim (Sum.elim a r) (Sum.elim b t) ∘ centre ∈ G ∧
        Sum.elim (Sum.elim a r) (Sum.elim b t) ∘ competitor ∉ G) ∨
        (Sum.elim (Sum.elim a r) (Sum.elim b t) ∘ competitor ∈ G ∧
          Sum.elim (Sum.elim a r) (Sum.elim b t) ∘ centre ∉ G))
      rw [hcentre, hcompetitor, Sum.elim_comp_inr]
      exact hdiff
    tauto

theorem rvConstantRaw_definable {S : Set M} {G : Set (Fin n ⊕ Fin m → M)}
    (hG : S.Definable LRV G) : S.Definable LRV (rvConstantRaw G) := by
  let G' : Set (Empty ⊕ (Fin n ⊕ Fin m) → M) := {z | z ∘ Sum.inr ∈ G}
  have hG' : S.Definable LRV G' := hG.preimage_comp Sum.inr
  have hswap := (rvConstantFamilyRaw_definable hG').preimage_comp
    (Sum.swap : Empty ⊕ Fin n → Fin n ⊕ Empty)
  convert hswap.exists_of_finite using 1
  ext a
  change a ∈ rvConstantRaw G ↔ ∃ u : Empty → M, a ∈ rvConstantRaw G
  exact ⟨fun h => ⟨Empty.elim, h⟩, fun ⟨_, h⟩ => h⟩

variable [M ⊨ Axioms.ACVF]

theorem rvConstantRaw_normalize (G : Set (Fin n ⊕ Fin m → M)) :
    @rvConstantRaw M (CanonicalStructure.normalize (M := M)) n m G = rvConstantRaw G := by
  ext a
  simp only [rvConstantRaw, vfRawUniverse, Set.mem_ofPred_eq]
  refine and_congr Iff.rfl (exists_congr (fun r => ?_))
  have he : @uniformBall M (CanonicalStructure.normalize (M := M)) n a r =
      @uniformBall M sM n a r := uniformBall_normalize a r
  have hz : @iVFZero M (CanonicalStructure.normalize (M := M)) = @iVFZero M sM :=
    CanonicalStructure.normalize_fun Fn.vfZero (fun j => j.elim0) (fun j => j.elim0)
  rw [he, hz]
  simp only [iVF, iRV, CanonicalStructure.normalize_unary]

variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]

theorem mem_rvConstantRaw_iff
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (G : Set (Fin n ⊕ Fin m → M)) (a : Fin n → VFType (M := M)) :
    vfValues a ∈ rvConstantRaw G ↔ rvLocallyConstantAt (rvFibre G) a := by
  rw [rvLocallyConstantAt_iff_uniformBall hv]
  constructor
  · rintro ⟨_, r, hr, hr₀, h⟩
    refine ⟨⟨r, hr⟩, fun he => hr₀ (congrArg Subtype.val he), fun b hb => ?_⟩
    exact Set.ext (fun t => h (vfValues b) hb (rvValues t) (fun i => (t i).property))
  · rintro ⟨r, hr, h⟩
    refine ⟨fun i => (a i).property, r.val, r.property, fun he => hr (Subtype.ext he), ?_⟩
    intro b hb t ht
    let b' : Fin n → VFType (M := M) := fun i => ⟨b i, (hb i).2.1⟩
    let t' : Fin m → CanonicalRV.RVSort M := fun i => ⟨t i, ht i⟩
    exact Set.ext_iff.mp (h b' hb) t'

theorem isClosed_rvFibreBadLocus
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (G : Set (Fin n ⊕ Fin m → M)) : IsClosed {a | vfValues a ∉ rvConstantRaw G} := by
  have he : {a | vfValues a ∉ rvConstantRaw G} = {a | rvLocallyConstantAt (rvFibre G) a}ᶜ :=
    Set.ext (fun a => not_congr (mem_rvConstantRaw_iff hv G a))
  rw [he]
  exact (isOpen_rvLocallyConstantAt (rvFibre G)).isClosed_compl

end SpecialTransformations.Section8
