import Section8.BijectionSlope
import Section8.GammaPairChoice
import Section3.RVOperations

/-! Name the slope-one intercept and the ball radius over the original
base. The witness formula works on the partial graph itself. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section3.GammaParameters.EndpointLogic (codeValue_surjective)

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def centeredGammaSlope (A : Set M) (f : VFType (M := M) → VFType (M := M))
    (c r : Values.Gamma (M := M)) : Prop :=
  ∀ x : VFType (M := M), r.val < Values.vfValueHom x →
    x.val ∈ A ∧ Values.vfValueHom (f x) = c.val * Values.vfValueHom x

private def centeredLine (c x y : M) : Prop :=
  iLe (iRv y) (iRVMul c (iRv x)) ∧ iLe (iRVMul c (iRv x)) (iRv y)

private theorem centeredLine_definable {I : Type} (S : Set M) (c x y : I) :
    S.Definable LRV {z : I → M | centeredLine (z c) (z x) (z y)} := by
  have hrv (i : I) : S.DefinableFun LRV (fun z : I → M => iRv (z i)) := by
    apply (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMap)).comp
    intro j
    fin_cases j
    exact Set.DefinableFun.proj LRV
  have hmul : S.DefinableFun LRV (fun z : I → M => iRVMul (z c) (iRv (z x))) := by
    apply (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMul)).comp
    intro j
    fin_cases j
    · exact Set.DefinableFun.proj LRV
    · exact hrv x
  have hle := raw_le_definable (M := M) S
  have hmap (u w : (I → M) → M) (hu : S.DefinableFun LRV u) (hw : S.DefinableFun LRV w) :
      S.DefinableMap LRV (fun z : I → M => ![u z, w z]) := by
    intro i
    fin_cases i
    · exact hu
    · exact hw
  exact (hle.preimage_map (hmap _ _ (hrv y) hmul)).inter (hle.preimage_map (hmap _ _ hmul (hrv y)))

private theorem centeredLine_iff {c : M} (hc : NonzeroRV c) (x y : VFType (M := M)) :
    centeredLine c x.val y.val ↔ Values.vfValueHom y = (codeValue c).val * Values.vfValueHom x := by
  let d : CanonicalRV.RVSort M := ⟨c, hc.1⟩
  have h : (codeValue c).val = Values.vrv d := by rw [codeValue, dif_pos hc]; rfl
  rw [h]
  have hmul : (d * CanonicalRV.encodedRv x).val = iRVMul c (iRv x.val) :=
    RVOperations.mul_val d (CanonicalRV.encodedRv x)
  unfold centeredLine
  rw [← hmul]
  change (iLe (CanonicalRV.encodedRv y).val (d * CanonicalRV.encodedRv x).val ∧
    iLe (d * CanonicalRV.encodedRv x).val (CanonicalRV.encodedRv y).val) ↔
    Values.vrv (CanonicalRV.encodedRv y) = Values.vrv d * Values.vrv (CanonicalRV.encodedRv x)
  have hval : Values.vrv (d * CanonicalRV.encodedRv x) =
      Values.vrv d * Values.vrv (CanonicalRV.encodedRv x) :=
    map_mul RVOperations.vrvHom d (CanonicalRV.encodedRv x)
  rw [← Values.vrv_le_iff, ← Values.vrv_le_iff, hval]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

private theorem centeredCodeBall_iff {r : M} (hr : NonzeroRV r) (x : VFType (M := M)) :
    (fun _ : Fin 1 => x.val) ∈ rvUniformBall (fun _ => iVFZero) r ↔
      (codeValue r).val < Values.vfValueHom x := by
  obtain ⟨s, hs⟩ := CanonicalRV.encodedRv_surjective ⟨r, hr.1⟩
  have he : iRv s.val = r := congrArg Subtype.val hs
  have hs₀ : s ≠ 0 := fun h => hr.2 (he.symm.trans ((CanonicalRV.encodedRv_zero_iff s).mpr h))
  have hγ : Values.vfValueHom s = (codeValue r).val := by
    rw [codeValue, dif_pos hr]
    exact congrArg Values.vrv hs
  have hEq : rvUniformBall (fun _ : Fin 1 => iVFZero) r = uniformBall (fun _ => iVFZero) s.val := by
    rw [← he, rvUniformBall_eq _ s hs₀]
  rw [hEq]
  have hball : (fun _ : Fin 1 => x.val) ∈ uniformBall (fun _ => iVFZero) s.val ↔
      x.val ∈ rawOpenBall iVFZero s.val := ⟨fun h => h 0, fun h _ => h⟩
  rw [hball]
  have hv := Values.presentation_compatible (M := M)
  have hv' := (mem_rawOpenBall_iff Values.presentationValuation hv (0 : VFType (M := M)) s x hs₀)
  rw [sub_zero] at hv'
  change x.val ∈ rawOpenBall iVFZero s.val ↔ _ at hv'
  rw [hv', ← hγ]
  exact lt_iff_not_ge.trans ((not_congr ((Values.presentation_compatible s x).symm.trans
    (Values.vf_pred_iff_gamma_le s x))).trans lt_iff_not_ge.symm)

private theorem centeredCodeBall_definable (S : Set M) {I : Type} (r x : I) :
    S.Definable LRV {z : I → M | (fun _ : Fin 1 => z x) ∈ rvUniformBall (fun _ => iVFZero) (z r)} := by
  let e (z : I → M) : (Fin 1 ⊕ Fin 1) ⊕ Fin 1 → M :=
    Sum.elim (Sum.elim (fun _ => iVFZero) (fun _ => z x)) (fun _ => z r)
  have he : S.DefinableMap LRV e := by
    rintro ((i | i) | i)
    · exact DefinableConstants.constant (DefinableConstants.function_symbol
        (L := LRV) Fn.vfZero Fin.elim0 (fun j => j.elim0))
    · exact Set.DefinableFun.proj LRV
    · exact Set.DefinableFun.proj LRV
  exact (rvUniformBallRelation_definable S 1).preimage_map he

private theorem centeredSlope_witnesses (hc : CanonicalStructure.IsCanonical (M := M))
    {B : Base (M := M)} {A : Set M} {f : VFType (M := M) → VFType (M := M)}
    (hA : DefinableAtBase B .vf A)
    (hf : DefinableOverBase B (fun _ => .vf) (partialUnaryGraph A f)) :
    ∃ P : Set (Fin 2 → M), DefinableOverBase B (fun _ => .rv) P ∧ (∀ z ∈ P, Proper z) ∧
      ∀ z : Fin 2 → M, Proper z → (z ∈ P ↔ centeredGammaSlope A f (codeValue (z 0)) (codeValue (z 1))) := by
  let s : Fin 3 → SortTag := ![.rv, .rv, .vf]
  let t : Fin 4 → SortTag := ![.rv, .rv, .vf, .vf]
  let keep₁ : Fin 2 → Fin 3 := Fin.castSucc
  let keep₂ : Fin 2 → Fin 4 := Fin.castAdd 2
  let L : Set (Fin 3 → M) := {z | z ∈ sortedUniverse s ∧
    (fun _ : Fin 1 => z 2) ∈ rvUniformBall (fun _ => iVFZero) (z 1)}
  let E : Set (Fin 4 → M) := {z | z ∈ sortedUniverse t ∧
    (fun _ : Fin 1 => z 2) ∈ rvUniformBall (fun _ => iVFZero) (z 1) ∧ ¬ centeredLine (z 0) (z 2) (z 3)}
  have hL : DefinableOver B.real s L :=
    raw_definableOver_sorted hc B.real s L ((sortedUniverse_definable B.real s).raw_definable.inter
      (centeredCodeBall_definable B.real 1 2)) (fun _ h => h.1)
  have hE : DefinableOver B.real t E :=
    raw_definableOver_sorted hc B.real t E ((sortedUniverse_definable B.real t).raw_definable.inter
      ((centeredCodeBall_definable B.real 1 2).inter (centeredLine_definable B.real 0 2 3).compl)) (fun _ h => h.1)
  let Outside := L ∩ (sortedUniverse s \ {z | z 2 ∈ A ∧ z ∈ sortedUniverse s})
  let Fail := {z : Fin 4 → M | z ∘ (![2, 3] : Fin 2 → Fin 4) ∈ partialUnaryGraph A f ∧ z ∈ E}
  have hOutside := (real_definableOverBase B s L hL).inter
    (hA.preimage_real s (fun _ : Fin 1 => (2 : Fin 3))).compl
  have hFail := hf.inter_real_preimage t E hE (![2, 3] : Fin 2 → Fin 4)
  let U := (fun w => w ∘ keep₁) '' Outside
  let V := (fun w => w ∘ keep₂) '' Fail
  have hU : DefinableOverBase B (fun _ : Fin 2 => .rv) U := by
    have hs : s ∘ keep₁ = fun _ => .rv := by funext i; fin_cases i <;> rfl
    have h := hOutside.image_real keep₁
    rwa [hs] at h
  have hV : DefinableOverBase B (fun _ : Fin 2 => .rv) V := by
    have ht : t ∘ keep₂ = fun _ => .rv := by funext i; fin_cases i <;> rfl
    have h := hFail.image_real keep₂
    rwa [ht] at h
  have hp : DefinableOver B.real (fun _ : Fin 2 => .rv) {z | Proper z} := by
    apply raw_definableOver_sorted hc B.real _ _ _ (fun z h i => (h i).1)
    change B.real.Definable LRV {z : Fin 2 → M | ∀ i, NonzeroRV (z i)}
    rw [Set.ofPred_forall]
    exact Set.definable_iInter_of_finite (fun i => (nonzero_rv_definable B.real).preimage_comp (fun _ : Fin 1 => i))
  let P : Set (Fin 2 → M) := {z | Proper z ∧ z ∈ sortedUniverse (fun _ => .rv) \ (U ∪ V)}
  refine ⟨P, (real_definableOverBase B _ _ hp).inter (hU.union hV).compl, fun _ hz => hz.1, ?_⟩
  intro z hz
  constructor
  · intro h x hx
    have hball := (centeredCodeBall_iff (hz 1) x).mpr hx
    have hA' : x.val ∈ A := by
      by_contra hn
      let w : Fin 3 → M := ![z 0, z 1, x.val]
      have hw : w ∈ sortedUniverse s := by
        intro i
        fin_cases i
        · exact (hz 0).1
        · exact (hz 1).1
        · exact x.property
      apply h.2.2
      exact Or.inl ⟨w, ⟨⟨hw, hball⟩, hw, fun h => hn h.1⟩, funext (fun i => by fin_cases i <;> rfl)⟩
    refine ⟨hA', (centeredLine_iff (hz 0) x (f x)).mp ?_⟩
    by_contra hn
    let w : Fin 4 → M := ![z 0, z 1, x.val, (f x).val]
    have hw : w ∈ sortedUniverse t := by
      intro i
      fin_cases i
      · exact (hz 0).1
      · exact (hz 1).1
      · exact x.property
      · exact (f x).property
    apply h.2.2
    exact Or.inr ⟨w, ⟨⟨hA', x, rfl, rfl⟩, hw, hball, hn⟩, funext (fun i => by fin_cases i <;> rfl)⟩
  · intro h
    refine ⟨hz, fun i => (hz i).1, ?_⟩
    rintro (⟨w, ⟨⟨hw, hb⟩, _, hn⟩, he⟩ | ⟨w, ⟨⟨_, x, hx, hy⟩, _, hb, hn⟩, he⟩)
    · let x : VFType (M := M) := ⟨w 2, hw 2⟩
      have he₁ : w 1 = z 1 := congrFun he 1
      have hb' : (fun _ : Fin 1 => x.val) ∈ rvUniformBall (fun _ => iVFZero) (z 1) := he₁ ▸ hb
      exact hn ⟨(h x ((centeredCodeBall_iff (hz 1) x).mp hb')).1, hw⟩
    · have he₀ : w 0 = z 0 := congrFun he 0
      have he₁ : w 1 = z 1 := congrFun he 1
      have hx' : x.val = w 2 := hx
      have hy' : (f x).val = w 3 := hy
      have hb' : (fun _ : Fin 1 => x.val) ∈ rvUniformBall (fun _ => iVFZero) (z 1) := by
        rw [hx', ← he₁]
        exact hb
      apply hn
      rw [he₀, ← hx', ← hy']
      exact (centeredLine_iff (hz 0) x (f x)).mpr (h x ((centeredCodeBall_iff (hz 1) x).mp hb')).2

theorem lemma_8_4_named_gamma_base [CharZero (VFType (M := M))]
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {B : Base (M := M)} (hsmall : Cardinal.mk ↥B.real < κ)
    {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hEP : ∀ E : Subfield (VFType (M := M)), ∃ H, E ≤ H ∧ ImmediateHenselianExtension Valued.v E H)
    (f : VFType (M := M) → VFType (M := M)) (a b : VFType (M := M)) (hb : b ≠ 0)
    (hf : DefinableOverBase B (fun _ => .vf)
      (partialUnaryGraph ((fun x : VFType (M := M) => x.val) '' centeredBall Valued.v a) f))
    (hbij : Set.BijOn f (centeredBall Valued.v a) (centeredBall Valued.v b))
    (hballs : ∀ r : VFType (M := M), r ≠ 0 → ∃ s : VFType (M := M), s ≠ 0 ∧
      f '' (centeredBall Valued.v a ∩ centeredBall Valued.v r) =
        centeredBall Valued.v b ∩ centeredBall Valued.v s) :
    ∃ c r : Values.Gamma (M := M), GammaDefinableClosureAtBase B c ∧ GammaDefinableClosureAtBase B r ∧
      centeredGammaSlope ((fun x : VFType (M := M) => x.val) '' centeredBall Valued.v a) f c r := by
  let A := (fun x : VFType (M := M) => x.val) '' centeredBall Valued.v a
  have hA : DefinableAtBase B .vf A := by
    have h := hf.image_real (fun _ : Fin 1 => (0 : Fin 2))
    change DefinableOverBase B (fun _ : Fin 1 => .vf) {z | z 0 ∈ A}
    convert h using 1 <;> try rfl
    apply Set.ext
    intro z
    constructor
    · rintro ⟨x, hx, he⟩
      exact ⟨![x.val, (f x).val], ⟨⟨x, hx, rfl⟩, x, rfl, rfl⟩, funext (fun i => by fin_cases i; exact he)⟩
    · rintro ⟨w, hw, rfl⟩
      exact hw.1
  obtain ⟨c, r, hc₀, hr₀, hsub, hlaw⟩ := lemma_8_4_partial_gamma_base hc hκ hs hsmall hv hEP f a b hb hf hbij hballs
  let cΓ := GammaThresholdGeometry.vfGamma c hc₀
  let rΓ := GammaThresholdGeometry.vfGamma r hr₀
  have hL : centeredGammaSlope A f cΓ rΓ := by
    intro x hx
    have hxr : x ∈ centeredBall Valued.v r := by
      change Valued.v x < Valued.v r
      by_cases h : x = 0
      · rw [h, map_zero]
        exact pos_iff_ne_zero.mpr (Valued.v.ne_zero_iff.mpr hr₀)
      · exact (GammaThresholdGeometry.value_lt_gamma Valued.v hv x r h hr₀).mpr hx
    refine ⟨⟨x, hsub hxr, rfl⟩, ?_⟩
    have he : Valued.v (f x) = Valued.v (c * x) := (hlaw x hxr).trans (map_mul _ _ _).symm
    have h := (Values.vf_value_eq_iff Valued.v hv (f x) (c * x)).mpr he
    change Values.vfValueHom (f x) = Values.vfValueHom (c * x) at h
    rwa [map_mul] at h
  obtain ⟨P, hP, hp, hsem⟩ := centeredSlope_witnesses hc hA hf
  have hne : P.Nonempty := by
    obtain ⟨u, hu, heu⟩ := codeValue_surjective cΓ
    obtain ⟨w, hw, hew⟩ := codeValue_surjective rΓ
    let z : Fin 2 → M := ![u, w]
    have hz : Proper z := by
      intro i
      fin_cases i
      · exact hu
      · exact hw
    refine ⟨z, (hsem z hz).mpr ?_⟩
    change centeredGammaSlope A f (codeValue u) (codeValue w)
    rwa [heu, hew]
  apply gamma_named_unique_shift_radius h00 B (centeredGammaSlope A f) P hP hne hp hsem
  · intro c r d s h₁ h₂
    obtain ⟨γ, hγ⟩ := exists_gt (max r s)
    obtain ⟨x, hx, hxγ⟩ := gamma_has_vf_representative γ
    have hr : r.val < Values.vfValueHom x := by
      rw [hxγ]
      exact (le_max_left r s).trans_lt hγ
    have hs : s.val < Values.vfValueHom x := by
      rw [hxγ]
      exact (le_max_right r s).trans_lt hγ
    have hx₀ : Values.vfValueHom x ≠ 0 := by
      rw [hxγ, ← Values.infinity_eq_zero]
      exact γ.property
    exact Subtype.ext (mul_right_cancel₀ hx₀ ((h₁ x hr).2.symm.trans (h₂ x hs).2))
  · intro c r hr s hrs x hx
    exact hr x ((show r.val ≤ s.val from hrs).trans_lt hx)
  · intro c r hr x hx
    have he : ∃ s : Values.Gamma (M := M), r < s ∧ s.val < Values.vfValueHom x := by
      by_cases h : x = 0
      · subst x
        obtain ⟨s, hs⟩ := exists_gt r
        refine ⟨s, hs, ?_⟩
        rw [map_zero, ← Values.infinity_eq_zero]
        exact lt_of_le_of_ne (Values.le_infinity _) s.property
      · exact exists_between (show r < GammaThresholdGeometry.vfGamma x h from hx)
    obtain ⟨s, hs, hx'⟩ := he
    exact hr s hs x hx'

end SpecialTransformations.Section8
