import Section8.VFDefinableTopology
import Section8.IsolationFibres

/-! The discontinuity set of a definable VF map is definable over the
graph's parameter base, using the valuation topology on both tuples. -/

set_option backward.isDefEq.respectTransparency false

open Filter Topology FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] {n m : ℕ}

def stayInBall (G : Set (Fin n ⊕ Fin m → M)) :
    Set ((((Fin n ⊕ Fin m) ⊕ Fin 1) ⊕ Fin 1) → M) :=
  {z | ¬ ∃ w ∈ G,
    w ∘ Sum.inl ∈ uniformBall (fun i => z (.inl (.inl (.inl i)))) (z (.inr 0)) ∧
    w ∘ Sum.inr ∉ uniformBall (fun i => z (.inl (.inl (.inr i)))) (z (.inl (.inr 0)))}

private theorem stayInBall_definable {S : Set M} {G : Set (Fin n ⊕ Fin m → M)}
    (hG : S.Definable LRV G) : S.Definable LRV (stayInBall G) := by
  let X := Fin n ⊕ Fin m
  let Z := (X ⊕ Fin 1) ⊕ Fin 1
  let W := Z ⊕ X
  let A : (Fin n ⊕ Fin n) ⊕ Fin 1 → W := Sum.elim
    (Sum.elim (fun i => .inl (.inl (.inl (.inl i)))) (fun i => .inr (.inl i)))
    (fun i => .inl (.inr i))
  let B : (Fin m ⊕ Fin m) ⊕ Fin 1 → W := Sum.elim
    (Sum.elim (fun i => .inl (.inl (.inl (.inr i)))) (fun i => .inr (.inr i)))
    (fun i => .inl (.inl (.inr i)))
  exact ((hG.preimage_comp (Sum.inr : X → W)).inter
    (((uniformBallRelation_definable S n).preimage_comp A).inter
      ((uniformBallRelation_definable S m).preimage_comp B).compl)).exists_of_finite.compl

theorem properRadiusAt_definable (S : Set M) {ι : Type} (i : ι) :
    S.Definable LRV {z : ι → M | iVF (z i) ∧ z i ≠ iVFZero} := by
  have hz : S.DefinableFun LRV (fun _ : ι → M => iVFZero) :=
    DefinableConstants.constant (DefinableConstants.function_symbol
      (L := LRV) Fn.vfZero Fin.elim0 (fun j => j.elim0))
  exact (((definableAt_sort S .vf).raw_definable).preimage_comp (fun _ : Fin 1 => i)).inter
    ((Set.DefinableFun.proj LRV (i := i)).ofPred_eq hz).compl

def continuousGraph (G : Set (Fin n ⊕ Fin m → M)) : Set (Fin n ⊕ Fin m → M) :=
  {z | z ∈ G ∧ ∀ s : M, iVF s → s ≠ iVFZero →
    ∃ r : M, iVF r ∧ r ≠ iVFZero ∧ Sum.elim (Sum.elim z ![s]) ![r] ∈ stayInBall G}

private theorem continuousGraph_definable {S : Set M} {G : Set (Fin n ⊕ Fin m → M)}
    (hG : S.Definable LRV G) : S.Definable LRV (continuousGraph G) := by
  let X := Fin n ⊕ Fin m
  let W := (X ⊕ Fin 1) ⊕ Fin 1
  have hGood := ((properRadiusAt_definable S (.inr 0 : W)).inter
    (stayInBall_definable hG)).exists_of_finite
  have hBad := ((properRadiusAt_definable S (.inr 0 : X ⊕ Fin 1)).inter hGood.compl).exists_of_finite
  convert hG.inter hBad.compl using 1
  ext z
  change (z ∈ G ∧ ∀ s : M, iVF s → s ≠ iVFZero → ∃ r : M, iVF r ∧ r ≠ iVFZero ∧
    Sum.elim (Sum.elim z ![s]) ![r] ∈ stayInBall G) ↔
    z ∈ G ∧ ¬ ∃ s : Fin 1 → M, (iVF (s 0) ∧ s 0 ≠ iVFZero) ∧
      ¬ ∃ r : Fin 1 → M, (iVF (r 0) ∧ r 0 ≠ iVFZero) ∧
        Sum.elim (Sum.elim z s) r ∈ stayInBall G
  have hcode (t : Fin 1 → M) : ![t 0] = t := by
    funext i
    fin_cases i
    rfl
  refine and_congr_right (fun _ => ⟨?_, ?_⟩)
  · rintro h ⟨s, hs, hno⟩
    obtain ⟨r, hr, hr₀, hstay⟩ := h (s 0) hs.1 hs.2
    rw [hcode s] at hstay
    exact hno ⟨![r], ⟨hr, hr₀⟩, hstay⟩
  · intro h s hs hs₀
    by_contra hno
    apply h ⟨![s], ⟨hs, hs₀⟩, ?_⟩
    rintro ⟨r, hr, hstay⟩
    exact hno ⟨r 0, hr.1, hr.2, by simpa only [hcode r] using hstay⟩

def continuousInputs (G : Set (Fin n ⊕ Fin m → M)) : Set (Fin n → M) :=
  (fun z => z ∘ Sum.inl) '' continuousGraph G

theorem continuousInputs_definable {S : Set M} {G : Set (Fin n ⊕ Fin m → M)}
    (hG : S.Definable LRV G) : S.Definable LRV (continuousInputs G) :=
  (continuousGraph_definable hG).image_comp Sum.inl

def continuityExceptionRaw (G : Set (Fin n ⊕ Fin m → M)) : Set (Fin n → M) :=
  vfRawClosure (vfRawUniverse n \ continuousInputs G)

theorem continuityExceptionRaw_definable {S : Set M} {G : Set (Fin n ⊕ Fin m → M)}
    (hG : S.Definable LRV G) : S.Definable LRV (continuityExceptionRaw G) :=
  vfRawClosure_definable ((vfRawUniverse_definable S n).inter (continuousInputs_definable hG).compl)

variable [M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]

theorem mem_continuousInputs_iff
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : (Fin n → VFType (M := M)) → (Fin m → VFType (M := M)))
    (a : Fin n → VFType (M := M)) : vfValues a ∈ continuousInputs (vfGraph f) ↔ ContinuousAt f a := by
  have hstay (r s : VFType (M := M)) :
      Sum.elim (Sum.elim (Sum.elim (vfValues a) (vfValues (f a))) ![s.val]) ![r.val] ∈ stayInBall (vfGraph f) ↔
        ∀ b : Fin n → VFType (M := M), vfValues b ∈ uniformBall (vfValues a) r.val →
          vfValues (f b) ∈ uniformBall (vfValues (f a)) s.val := by
    constructor
    · intro h b hb
      by_contra hn
      exact h ⟨Sum.elim (vfValues b) (vfValues (f b)), ⟨b, rfl⟩, hb, hn⟩
    · intro h
      rintro ⟨w, ⟨b, rfl⟩, hb, hn⟩
      exact hn (h b hb)
  constructor
  · rintro ⟨z, ⟨⟨b, rfl⟩, hz⟩, he⟩
    have hba : b = a := vfValues_injective he
    subst b
    intro U hU
    obtain ⟨s, hs, hsub⟩ := exists_uniformBall_subset_of_mem_nhds hv (f a) hU
    obtain ⟨r, hr, hr₀, h⟩ := hz s.val s.property (fun hz => hs (Subtype.ext hz))
    let r' : VFType (M := M) := ⟨r, hr⟩
    have hr' : r' ≠ 0 := fun he => hr₀ (congrArg Subtype.val he)
    change f ⁻¹' U ∈ 𝓝 a
    exact Filter.mem_of_superset (uniformBall_mem_nhds hv a r' hr') (fun x hx =>
      show f x ∈ U from hsub ((hstay r' s).mp h x hx))
  · intro hf
    refine ⟨Sum.elim (vfValues a) (vfValues (f a)), ⟨⟨a, rfl⟩, ?_⟩, rfl⟩
    intro s hs hs₀
    let s' : VFType (M := M) := ⟨s, hs⟩
    have hs' : s' ≠ 0 := fun he => hs₀ (congrArg Subtype.val he)
    obtain ⟨r, hr, h⟩ := exists_uniformBall_subset_of_mem_nhds hv a
      (hf (uniformBall_mem_nhds hv (f a) s' hs'))
    exact ⟨r.val, r.property, fun he => hr (Subtype.ext he), (hstay r s').mpr h⟩

end SpecialTransformations.Section8
