import Section8.UniformBalls
import Section3.RVOperations
import Section8.UnarySlope
import Section3.SmallFamilyConstancy
import Section8.UnaryPolynomial
import Section8.BijectionSlope
import Section8.VFNeighbourhoods
import Section8.GenericOutputBall
import Section4.VFFiniteMaps
import Section8.RVFibreLocus
import Section8.MixedLocalFormula
import Section3.SortedParameterElimination

section

/-! The pairwise identity in 8.5 follows on any ball on which the
single-centre identity has a common radius and RV multiplier. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]

theorem rvDifference_of_uniform_centre_law
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (f : VFType (M := M) → VFType (M := M)) (a r s : VFType (M := M)) (hs : s ≠ 0)
    (hr : r ≠ 0) (hsr : v s ≤ v r) (t : CanonicalRV.RVSort M)
    (h : ∀ b : VFType (M := M), b.val ∈ rawOpenBall a.val s.val →
      ∀ x : VFType (M := M), x.val ∈ rawOpenBall b.val r.val →
        CanonicalRV.encodedRv (f x - f b) = t * CanonicalRV.encodedRv (x - b)) :
    ∀ b b' : VFType (M := M), b.val ∈ rawOpenBall a.val s.val → b'.val ∈ rawOpenBall a.val s.val →
      CanonicalRV.encodedRv (f b - f b') = t * CanonicalRV.encodedRv (b - b') := by
  intro b b' hb hb'
  apply h b' hb' b
  apply (mem_rawOpenBall_iff v hv b' r b hr).mpr
  exact ((mem_rawOpenBall_iff v hv b' s b hs).mp (rawOpenBall_recentre v hv hb' hb)).trans_le hsr

theorem rvDifference_multiplier_unique (f : VFType (M := M) → VFType (M := M))
    (a x : VFType (M := M)) (hxa : x ≠ a) (t u : CanonicalRV.RVSort M)
    (ht : CanonicalRV.encodedRv (f x - f a) = t * CanonicalRV.encodedRv (x - a))
    (hu : CanonicalRV.encodedRv (f x - f a) = u * CanonicalRV.encodedRv (x - a)) : t = u := by
  have hrv : CanonicalRV.encodedRv (x - a) ≠ 0 := fun h => hxa
    (sub_eq_zero.mp ((CanonicalRV.encodedRv_zero_iff (x - a)).mp
      ((congrArg Subtype.val h).trans RVOperations.zero_val)))
  exact mul_right_cancel₀ hrv (ht.symm.trans hu)

end SpecialTransformations.Section8

end

section

/-! A slope-one value law bounds the angular ratio on the punctured
ball. The checked 3.17 then gives a constant nonzero multiplier. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

noncomputable def angularRatio (f : VFType (M := M) → VFType (M := M))
    (a d : VFType (M := M)) : CanonicalRV.RVSort M :=
  CanonicalRV.encodedRv (f (d + a) - f a) / CanonicalRV.encodedRv d

def angularRatioFibre (f : VFType (M := M) → VFType (M := M))
    (a : VFType (M := M)) (r : Values.Gamma (M := M)) (d : VFType (M := M)) :
    Set (Fin 1 → CanonicalRV.RVSort M) :=
  {ys | r.val < Values.vfValueHom d ∧ ys 0 = angularRatio f a d}

theorem rvDifference_germ_of_slope_one (S : Set M)
    (f : VFType (M := M) → VFType (M := M)) (a : VFType (M := M))
    (c r : Values.Gamma (M := M))
    (hdef : DefinableOver S (MixedPolynomialSyntax.contextSort (m := 1))
      (RVMonomial.puncturedGraph (angularRatioFibre f a r)))
    (hlinear : ∀ d : VFType (M := M), d ≠ 0 → r.val < Values.vfValueHom d →
      Values.vfValueHom (f (d + a) - f a) = c.val * Values.vfValueHom d) :
    ∃ s : Values.Gamma (M := M), ∃ t : CanonicalRV.RVSort M, t ≠ 0 ∧
      ∀ x : VFType (M := M), s.val < Values.vfValueHom (x - a) →
        CanonicalRV.encodedRv (f x - f a) = t * CanonicalRV.encodedRv (x - a) := by
  have hval (d : VFType (M := M)) (hd : d ≠ 0) (hnear : r.val < Values.vfValueHom d) :
      Values.vrv (angularRatio f a d) = c.val := by
    change RVOperations.vrvHom (CanonicalRV.encodedRv (f (d + a) - f a) /
      CanonicalRV.encodedRv d) = _
    rw [map_div₀]
    change Values.vfValueHom (f (d + a) - f a) / Values.vfValueHom d = _
    rw [hlinear d hd hnear, mul_div_assoc, div_self (by
      change Values.vrv (CanonicalRV.encodedRv d) ≠ 0
      intro h
      have hz := (Values.vrv_eq_infinity_iff (CanonicalRV.encodedRv d)).mp
        (h.trans Values.infinity_eq_zero.symm)
      exact hd ((CanonicalRV.encodedRv_zero_iff d).mp hz)), mul_one]
  obtain ⟨s₀, hs₀⟩ := lemma_3_17 S (angularRatioFibre f a r) hdef c c (by
    intro d hd ys hys i _
    fin_cases i
    change c.val ≤ Values.vrv (ys 0) ∧ Values.vrv (ys 0) ≤ c.val
    rw [hys.2, hval d hd hys.1]
    exact ⟨le_rfl, le_rfl⟩)
  let s := max r s₀
  obtain ⟨γ, hγ⟩ := exists_gt s
  obtain ⟨d, hd, he⟩ := gamma_has_vf_representative γ
  have hsd : s.val < Values.vfValueHom d := by rwa [he]
  let t := angularRatio f a d
  have ht : t ≠ 0 := by
    intro hz
    have h := hval d hd ((show r.val ≤ s.val from le_max_left r s₀).trans_lt hsd)
    change Values.vrv t = c.val at h
    rw [hz, RVOperations.vrv_zero] at h
    exact c.property (h.symm.trans Values.infinity_eq_zero.symm)
  refine ⟨s, t, ht, fun x hx => ?_⟩
  by_cases hxa : x = a
  · subst x
    simp only [sub_self, RVOperations.rv_zero, mul_zero]
  · let e := x - a
    have he₀ : e ≠ 0 := sub_ne_zero.mpr hxa
    have heNear : r.val < Values.vfValueHom e := (show r.val ≤ s.val from le_max_left r s₀).trans_lt hx
    have hEq := hs₀ s (le_max_right r s₀) e d he₀ hd hx hsd
    have heMem : (![angularRatio f a e] : Fin 1 → CanonicalRV.RVSort M) ∈ angularRatioFibre f a r e :=
      ⟨heNear, rfl⟩
    rw [hEq] at heMem
    have heq : angularRatio f a e = t := heMem.2
    unfold angularRatio at heq
    rw [sub_add_cancel] at heq
    exact (div_eq_iff ((RVOperations.rv_ne_zero e).mpr he₀)).mp heq

end SpecialTransformations.Section8

end

section

/-! First-order graph for the angular ratio used in 8.5. The VF
representative of the radius is a temporary name for Lemma 3.17. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

private theorem raw_add_definable {S : Set M} {ι : Type} {g h : (ι → M) → M}
    (hg : S.DefinableFun LRV g) (hh : S.DefinableFun LRV h) :
    S.DefinableFun LRV (fun x => iVFAdd (g x) (h x)) :=
  (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfAdd)).comp
    (show S.DefinableMap LRV (fun x : ι → M => ![g x, h x]) from by
      intro i
      fin_cases i
      · exact hg
      · exact hh)

private theorem raw_rv_definable {S : Set M} {ι : Type} {g : (ι → M) → M}
    (hg : S.DefinableFun LRV g) : S.DefinableFun LRV (fun x => iRv (g x)) :=
  (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMap)).comp
    (show S.DefinableMap LRV (fun x : ι → M => ![g x]) from by
      intro i
      fin_cases i
      exact hg)

theorem translated_unaryScalarGraph_definable {S : Set M}
    {f : VFType (M := M) → VFType (M := M)} (hf : S.Definable LRV (unaryScalarGraph f))
    (a b : VFType (M := M)) :
    (insert a.val (insert b.val S)).Definable LRV
      (unaryScalarGraph (fun x => f (x + a) - b)) := by
  let T := insert a.val (insert b.val S)
  let e (z : Fin 2 → M) := ![iVFAdd (z 0) a.val, iVFAdd (z 1) b.val]
  have ha : a.val ∈ T := Set.mem_insert _ _
  have hb : b.val ∈ T := Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have hS : S ⊆ T := fun _ hx => Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hx)
  have he : T.DefinableMap LRV e := by
    intro i
    fin_cases i
    · exact raw_add_definable (Set.DefinableFun.proj LRV) (LRV.definableFun_const _ ha)
    · exact raw_add_definable (Set.DefinableFun.proj LRV) (LRV.definableFun_const _ hb)
  have hVF : T.Definable LRV {z : Fin 2 → M | ∀ i, iVF (z i)} := by
    rw [Set.ofPred_forall]
    exact Set.definable_iInter_of_finite (fun i =>
      ((definableAt_sort T .vf).raw_definable).preimage_comp (fun _ : Fin 1 => i))
  convert hVF.inter ((hf.mono hS).preimage_map he) using 1
  ext z
  constructor
  · rintro ⟨x, hx, hy⟩
    refine ⟨?_, x + a, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact hx ▸ x.property
      · exact hy ▸ (f (x + a) - b).property
    · change (x + a).val = iVFAdd (z 0) a.val
      rw [← hx]
      rfl
    · change (f (x + a)).val = iVFAdd (z 1) b.val
      rw [← hy]
      exact congrArg Subtype.val (sub_add_cancel (f (x + a)) b).symm
  · rintro ⟨hVF, x, hx, hy⟩
    let w : VFType (M := M) := ⟨z 0, hVF 0⟩
    let u : VFType (M := M) := ⟨z 1, hVF 1⟩
    have hx' : x = w + a := Subtype.ext hx
    have hy' : f x = u + b := Subtype.ext hy
    refine ⟨w, rfl, ?_⟩
    change (f (w + a) - b).val = z 1
    rw [← hx', hy', add_sub_cancel_right]

theorem angularRatioFibre_puncturedGraph_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} {f : VFType (M := M) → VFType (M := M)} (hf : S.Definable LRV (unaryScalarGraph f))
    (a s : VFType (M := M)) (hs : s ≠ 0) :
    DefinableOver (insert (0 : VFType (M := M)).val (insert (f a).val (insert a.val (insert s.val S))))
      (MixedPolynomialSyntax.contextSort (m := 1))
      (RVMonomial.puncturedGraph (angularRatioFibre f a (GammaThresholdGeometry.vfGamma s hs))) := by
  let z₀ : VFType (M := M) := 0
  let B := insert z₀.val (insert (f a).val (insert a.val (insert s.val S)))
  let I := Fin 2 ⊕ Fin 2
  let d : I := .inl 0
  let t : I := .inl 1
  let x : I := .inr 0
  let y : I := .inr 1
  let C : Set (I → M) := {z | z ∘ Sum.inr ∈ unaryScalarGraph f ∧
    z x = iVFAdd (z d) a.val ∧ z d ∈ rawOpenBall z₀.val s.val ∧ z d ≠ z₀.val ∧
    iRV (z t) ∧ iRVMul (z t) (iRv (z d)) = iRv (iVFAdd (z y) (iVFNeg (f a).val))}
  have hS : S ⊆ B := fun z hz => Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hz)))
  have hfa : (f a).val ∈ B := Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have ha : a.val ∈ B := Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hsB : s.val ∈ B := Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
    (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  have hd : B.DefinableFun LRV (fun z : I → M => iVFAdd (z d) a.val) :=
    raw_add_definable (Set.DefinableFun.proj LRV) (LRV.definableFun_const I ha)
  have hdy : B.DefinableFun LRV (fun z : I → M => iVFAdd (z y) (iVFNeg (f a).val)) := by
    apply raw_add_definable (Set.DefinableFun.proj LRV)
    exact (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfNeg)).comp
      (show B.DefinableMap LRV (fun _ : I → M => ![(f a).val]) from by
        intro i
        fin_cases i
        exact LRV.definableFun_const I hfa)
  have hprod : B.DefinableFun LRV (fun z : I → M => iRVMul (z t) (iRv (z d))) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMul)).comp
      (show B.DefinableMap LRV (fun z : I → M => ![z t, iRv (z d)]) from by
        intro i
        fin_cases i
        · exact Set.DefinableFun.proj LRV
        · exact raw_rv_definable (Set.DefinableFun.proj LRV))
  have hC : B.Definable LRV C :=
    ((hf.mono hS).preimage_comp (Sum.inr : Fin 2 → I)).inter
      (((Set.DefinableFun.proj LRV (i := x)).ofPred_eq hd).inter
        (((rawOpenBall_definable (S := B) (Set.mem_insert _ _) hsB).preimage_comp (fun _ : Fin 1 => d)).inter
          ((((Set.DefinableFun.proj LRV (i := d)).ofPred_eq
              (LRV.definableFun_const I (Set.mem_insert _ _))).compl).inter
            ((((definableAt_sort B .rv).raw_definable).preimage_comp (fun _ : Fin 1 => t)).inter
              (hprod.ofPred_eq (raw_rv_definable hdy))))))
  let r := GammaThresholdGeometry.vfGamma s hs
  have hball (w : VFType (M := M)) (hw : w ≠ 0) :
      w.val ∈ rawOpenBall z₀.val s.val ↔ r.val < Values.vfValueHom w := by
    have h₁ := mem_rawOpenBall_iff Values.presentationValuation Values.presentation_compatible z₀ s w hs
    rw [show z₀ = 0 from rfl, sub_zero] at h₁
    exact h₁.trans (GammaThresholdGeometry.value_lt_gamma
      Values.presentationValuation Values.presentation_compatible w s hw hs)
  have hgraph : B.Definable LRV (RVMonomial.puncturedGraph (angularRatioFibre f a r)) := by
    convert hC.exists_of_finite using 1
    ext u
    constructor
    · rintro ⟨w, hw₀, ys, rfl, hw⟩
      have hrv := (RVOperations.rv_ne_zero w).mpr hw₀
      have he : ys 0 * CanonicalRV.encodedRv w = CanonicalRV.encodedRv (f (w + a) - f a) :=
        (div_eq_iff hrv).mp hw.2.symm |>.symm
      refine ⟨![(w + a).val, (f (w + a)).val], ⟨w + a, rfl, rfl⟩, rfl,
        (hball w hw₀).mpr hw.1, fun h => hw₀ (Subtype.ext h), (ys 0).property, ?_⟩
      rw [sub_eq_add_neg] at he
      exact (RVOperations.mul_val _ _).symm.trans (congrArg Subtype.val he)
    · rintro ⟨v, ⟨b, hbx, hby⟩, hb, hd, hd₀, ht, he⟩
      have hv : v = ![b.val, (f b).val] := by
        funext i
        fin_cases i
        · exact hbx.symm
        · exact hby.symm
      subst v
      let w : VFType (M := M) := ⟨u 0, hd.2.1⟩
      let ys : Fin 1 → CanonicalRV.RVSort M := fun _ => ⟨u 1, ht⟩
      have hw₀ : w ≠ 0 := fun h => hd₀ (congrArg Subtype.val h)
      have hb' : b = w + a := Subtype.ext hb
      refine ⟨w, hw₀, ys, ?_, (hball w hw₀).mp hd, ?_⟩
      · funext i
        fin_cases i <;> rfl
      · apply (eq_div_iff ((RVOperations.rv_ne_zero w).mpr hw₀)).mpr
        apply Subtype.ext
        rw [RVOperations.mul_val, ← hb', sub_eq_add_neg]
        exact he
  apply raw_definableOver_sorted hc B _ _ hgraph
  rintro _ ⟨w, _, ys, rfl, _⟩ i
  refine Fin.cases w.property (fun j => (ys j).property) i

end SpecialTransformations.Section8

end

section

/-! At a point where a definable bijection is continuous and its domain
contains a neighbourhood, the translated graph has slope one. The
bounded angular ratio is therefore constant on a smaller punctured ball. -/

set_option backward.isDefEq.respectTransparency false

open Filter Topology FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]

theorem rvDifference_of_local_definable_inverse [CharZero (VFType (M := M))]
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hEP : ∀ E : Subfield (VFType (M := M)), ∃ H, E ≤ H ∧ ImmediateHenselianExtension Valued.v E H)
    (f g : VFType (M := M) → VFType (M := M))
    (hf : S.Definable LRV (unaryScalarGraph f)) (hg : S.Definable LRV (unaryScalarGraph g))
    (a : VFType (M := M)) (A : Set (VFType (M := M))) (ha : a ∈ A) (hA : A ∈ 𝓝 a)
    (hcont : ContinuousAt f a) (hInv : ∀ x ∈ A, g (f x) = x) :
    ∃ s : Values.Gamma (M := M), ∃ t : CanonicalRV.RVSort M, t ≠ 0 ∧
      ∀ x : VFType (M := M), s.val < Values.vfValueHom (x - a) →
        CanonicalRV.encodedRv (f x - f a) = t * CanonicalRV.encodedRv (x - a) := by
  let v : Valuation (VFType (M := M)) Γ := Valued.v
  let F := fun x => f (x + a) - f a
  let G := fun y => g (y + f a) - a
  let B := insert a.val (insert (f a).val S)
  have hB := small_insert hκ _ (small_insert hκ S hsmall (f a).val) a.val
  have hF : B.Definable LRV (unaryScalarGraph F) := translated_unaryScalarGraph_definable hf a (f a)
  have hG : B.Definable LRV (unaryScalarGraph G) := by
    simpa only [B, G, Set.insert_comm] using translated_unaryScalarGraph_definable hg (f a) a
  have hF₀ : F 0 = 0 := by simp [F]
  have hclose (r s : VFType (M := M)) (hr : r ≠ 0) (hs : s ≠ 0) :
      ∃ x, x ≠ 0 ∧ v x < v r ∧ F x ≠ 0 ∧ v (F x) < v s ∧ G (F x) = x := by
    let D : ValuedPolydisc v 1 := ⟨fun _ => a, fun _ => r, fun _ => hr⟩
    let E : ValuedPolydisc v 1 := ⟨fun _ => f a, fun _ => s, fun _ => hs⟩
    have hnear := Filter.inter_mem hA
      (Filter.inter_mem (D.side_mem_nhds 0) (hcont (E.side_mem_nhds 0)))
    have hinf := infinite_valued_neighbourhood (model_valuation_nontrivial hv) a hnear
    have hnot : ¬ A ∩ (D.side 0 ∩ f ⁻¹' E.side 0) ⊆ {a} :=
      fun h => hinf ((Set.finite_singleton a).subset h)
    obtain ⟨x, hx, hxa⟩ := Set.not_subset.mp hnot
    have hxa' : x ≠ a := hxa
    have hfx : f x ≠ f a := fun he => hxa' ((hInv x hx.1).symm.trans ((congrArg g he).trans (hInv a ha)))
    refine ⟨x - a, sub_ne_zero.mpr hxa', hx.2.1, ?_, ?_, ?_⟩
    · simpa only [F, sub_add_cancel] using sub_ne_zero.mpr hfx
    · have hx' := hx.2.2
      change v (f x - f a) < v s at hx'
      simpa only [F, sub_add_cancel] using hx'
    · simp only [F, G, sub_add_cancel, hInv x hx.1]
  obtain ⟨c, r, hc₀, hr₀, hlin⟩ :=
    definable_local_inverse_slope_one hc hκ hs hB hv hEP F G hF hG hF₀ hclose
  let cΓ := GammaThresholdGeometry.vfGamma c hc₀
  let rΓ := GammaThresholdGeometry.vfGamma r hr₀
  apply rvDifference_germ_of_slope_one _ f a cΓ rΓ (angularRatioFibre_puncturedGraph_definable hc hf a r hr₀)
  intro d hd hnear
  have hdr : v d < v r := (GammaThresholdGeometry.value_lt_gamma v hv d r hd hr₀).mpr hnear
  have hval : v (F d) = v (c * d) := (hlin d hdr).trans (map_mul v c d).symm
  have he := (Values.vf_value_eq_iff v hv _ _).mpr hval
  change Values.vfValueHom (F d) = Values.vfValueHom (c * d) at he
  rw [map_mul] at he
  exact he

end SpecialTransformations.Section8

end

section

/-! Unary forms of generic continuity and the dimension-zero
finiteness criterion. -/

set_option backward.isDefEq.respectTransparency false

open Filter Topology FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]

theorem continuous_unary_tuple : Continuous (fun x : VFType (M := M) => (![x] : Fin 1 → VFType (M := M))) := by
  apply continuous_pi
  intro i
  fin_cases i
  exact continuous_id

theorem continuousAt_unary_of_independent (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : VFType (M := M) → VFType (M := M)) (hf : S.Definable LRV (unaryScalarGraph f))
    (a : VFType (M := M)) (ha : AlgebraicIndependent (vfParameterField S) (![a] : Fin 1 → VFType (M := M))) :
    ContinuousAt f a := by
  let F (x : Fin 1 → VFType (M := M)) : Fin 1 → VFType (M := M) := ![f (x 0)]
  let e : Fin 2 → Fin 1 ⊕ Fin 1 := ![.inl 0, .inr 0]
  have hF : S.Definable LRV (vfGraph F) := by
    convert hf.preimage_comp e using 1
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x 0, rfl, rfl⟩
    · rintro ⟨x, hx, hy⟩
      refine ⟨![x], ?_⟩
      funext i
      rcases i with i | i
      · fin_cases i
        exact hx
      · fin_cases i
        exact hy
  have hFcont := continuousAt_of_independent hc hκ hs hsmall hv F hF ![a] ha
  have h₁ : ContinuousAt (fun z : Fin 1 → VFType (M := M) => F z 0) ![a] :=
    (continuous_apply (0 : Fin 1)).continuousAt.comp hFcont
  have h₂ : ContinuousAt (fun x : VFType (M := M) => (![x] : Fin 1 → VFType (M := M))) a :=
    continuous_unary_tuple.continuousAt
  exact ContinuousAt.comp (f := fun x : VFType (M := M) => (![x] : Fin 1 → VFType (M := M)))
    (g := fun z : Fin 1 → VFType (M := M) => F z 0) (x := a) h₁ h₂

theorem rawUnary_finite_of_no_independent (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ) {A : Set (Fin 1 → M)} (hA : S.Definable LRV A)
    (hVF : A ⊆ vfRawUniverse 1)
    (hno : ∀ x : Fin 1 → VFType (M := M), vfValues x ∈ A → ¬ AlgebraicIndependent (vfParameterField S) x) :
    A.Finite := by
  let D := vfObjectOfRaw hA
  let Δ := rawRVSpace (M := M) 1
  have hΔ : Δ.RVCoded := rawRVSpace_rvCoded 1
  have hdim : vfDim Δ D ≤ 0 := Nat.le_of_lt_succ
    (vfDim_lt_of_no_independent hc hs hsmall Δ hΔ (by decide) hA hno)
  obtain ⟨g, hg⟩ := (vf_bounded_finite_iff_finite_map hc hκ hs hsmall Δ hΔ D).mp
    ⟨hdim, fun _ => Set.Subsingleton.finite (fun _ _ _ _ => funext (fun i => i.elim0))⟩
  have hgf : g.image.carrier.Finite := Set.Subsingleton.finite (fun _ _ _ _ => funext (fun i => i.elim0))
  have hfin := g.finite_source_of_finite_image hg hgf
  apply (hfin.image (fun p => vfValues p.1)).subset
  intro a ha
  let b : Fin 1 → VFType (M := M) := fun i => ⟨a i, hVF ha i⟩
  exact ⟨(b, Fin.elim0), ha, rfl⟩

end SpecialTransformations.Section8

end

section

/-! Keep all pairs of radius codes and RV multipliers that satisfy the
single-centre law. Lemma 8.9 can hold a witness fixed near a centre. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def rvDifferenceClause (a u b w t : M) : Prop :=
  iRv (iVFAdd w (iVFNeg u)) = iRVMul t (iRv (iVFAdd b (iVFNeg a)))

theorem rvDifferenceClause_definable {I : Type} (S : Set M) (a u b w t : I) :
    S.Definable LRV {z : I → M | rvDifferenceClause (z a) (z u) (z b) (z w) (z t)} := by
  have hdiff (i j : I) : S.DefinableFun LRV (fun z : I → M => iRv (iVFAdd (z i) (iVFNeg (z j)))) := by
    have hneg : S.DefinableFun LRV (fun z : I → M => iVFNeg (z j)) :=
      (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfNeg)).comp
        (show S.DefinableMap LRV (fun z : I → M => ![z j]) from by
          intro l
          fin_cases l
          exact Set.DefinableFun.proj LRV)
    have hadd : S.DefinableFun LRV (fun z : I → M => iVFAdd (z i) (iVFNeg (z j))) :=
      (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfAdd)).comp
        (show S.DefinableMap LRV (fun z : I → M => ![z i, iVFNeg (z j)]) from by
          intro l
          fin_cases l
          · exact Set.DefinableFun.proj LRV
          · exact hneg)
    exact (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMap)).comp
      (show S.DefinableMap LRV (fun z : I → M => ![iVFAdd (z i) (iVFNeg (z j))]) from by
        intro l
        fin_cases l
        exact hadd)
  have hmul : S.DefinableFun LRV (fun z : I → M => iRVMul (z t) (iRv (iVFAdd (z b) (iVFNeg (z a))))) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMul)).comp
      (show S.DefinableMap LRV (fun z : I → M => ![z t, iRv (iVFAdd (z b) (iVFNeg (z a)))]) from by
        intro l
        fin_cases l
        · exact Set.DefinableFun.proj LRV
        · exact hdiff b a)
  exact (hdiff w u).ofPred_eq hmul

def rvDifferenceWitnesses (G : Set (Fin 2 → M)) : Set (Fin 1 ⊕ Fin 2 → M) :=
  {p | ∃ u : Fin 1 → M, ![p (.inl 0), u 0] ∈ G ∧
    GammaParameters.NonzeroRV (p (.inr 0)) ∧ GammaParameters.NonzeroRV (p (.inr 1)) ∧
    ¬ ∃ z ∈ G, (![z 0] : Fin 1 → M) ∈ rvUniformBall (fun _ => p (.inl 0)) (p (.inr 0)) ∧
      ¬ rvDifferenceClause (p (.inl 0)) (u 0) (z 0) (z 1) (p (.inr 1))}

theorem rvDifferenceWitnesses_definable {S : Set M} {G : Set (Fin 2 → M)}
    (hG : S.Definable LRV G) : S.Definable LRV (rvDifferenceWitnesses G) := by
  let P := Fin 1 ⊕ Fin 2
  let Z := P ⊕ Fin 1
  let I := Z ⊕ Fin 2
  let centre : Fin 2 → Z := ![.inl (.inl 0), .inr 0]
  let a : I := .inl (.inl (.inl 0))
  let u : I := .inl (.inr 0)
  let b : I := .inr 0
  let w : I := .inr 1
  let r : I := .inl (.inl (.inr 0))
  let t : I := .inl (.inl (.inr 1))
  let box : (Fin 1 ⊕ Fin 1) ⊕ Fin 1 → I := Sum.elim (Sum.elim (fun _ => a) (fun _ => b)) (fun _ => r)
  have hC := (rvDifferenceClause_definable S a u b w t).compl
  have hBox := (rvUniformBallRelation_definable S 1).preimage_comp box
  have hBad := ((hG.preimage_comp (Sum.inr : Fin 2 → I)).inter (hBox.inter hC)).exists_of_finite
  have hr := (GammaParameters.nonzero_rv_definable S).preimage_comp (fun _ : Fin 1 => (.inl (.inr 0) : Z))
  have ht := (GammaParameters.nonzero_rv_definable S).preimage_comp (fun _ : Fin 1 => (.inl (.inr 1) : Z))
  convert ((hG.preimage_comp centre).inter (hr.inter (ht.inter hBad.compl))).exists_of_finite using 1
  ext p
  have hc (u : Fin 1 → M) : Sum.elim p u ∘ centre = ![p (.inl 0), u 0] := by
    funext i
    fin_cases i <;> rfl
  have hinput (z : Fin 2 → M) : (![z 0] : Fin 1 → M) = fun _ => z 0 := by
    funext i
    fin_cases i
    rfl
  change _ ↔ ∃ x : Fin 1 → M, Sum.elim p x ∘ centre ∈ G ∧
    GammaParameters.NonzeroRV (p (.inr 0)) ∧ GammaParameters.NonzeroRV (p (.inr 1)) ∧
    ¬ ∃ z ∈ G, (fun _ : Fin 1 => z 0) ∈ rvUniformBall (fun _ => p (.inl 0)) (p (.inr 0)) ∧
      ¬ rvDifferenceClause (p (.inl 0)) (x 0) (z 0) (z 1) (p (.inr 1))
  simp only [rvDifferenceWitnesses, Set.mem_ofPred_eq, hc, hinput]

variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]

theorem mem_rvRadius_iff (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (a b r : VFType (M := M)) (hr : r ≠ 0) :
    (![b.val] : Fin 1 → M) ∈ rvUniformBall (fun _ => a.val) (iRv r.val) ↔ v (b - a) < v r := by
  have hrV : GammaParameters.NonzeroRV (iRv r.val) :=
    ⟨(CanonicalRV.encodedRv r).property, fun he => hr ((CanonicalRV.encodedRv_zero_iff r).mp he)⟩
  constructor
  · rintro ⟨_, s, hs, hrv, hmem⟩
    let c : VFType (M := M) := ⟨s, hs⟩
    have hc : c ≠ 0 := fun he => hrV.2 (hrv.symm.trans ((CanonicalRV.encodedRv_zero_iff c).mpr he))
    have hval := (Values.vf_value_eq_iff v hv c r).mp (congrArg Values.vrv (Subtype.ext hrv))
    exact hval ▸ (mem_rawOpenBall_iff v hv a c b hc).mp (hmem 0)
  · intro h
    refine ⟨hrV, r.val, r.property, rfl, ?_⟩
    intro i
    fin_cases i
    exact (mem_rawOpenBall_iff v hv a r b hr).mpr h

theorem mem_rvDifferenceWitnesses_iff (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (f : VFType (M := M) → VFType (M := M)) (a r : VFType (M := M)) (hr : r ≠ 0)
    (t : CanonicalRV.RVSort M) (ht : t ≠ 0) :
    ![CanonicalRV.encodedRv r, t] ∈ rvFibre (rvDifferenceWitnesses (unaryScalarGraph f)) ![a] ↔
      ∀ x : VFType (M := M), v (x - a) < v r →
        CanonicalRV.encodedRv (f x - f a) = t * CanonicalRV.encodedRv (x - a) := by
  have he (x : VFType (M := M)) :
      rvDifferenceClause a.val (f a).val x.val (f x).val t.val ↔
        CanonicalRV.encodedRv (f x - f a) = t * CanonicalRV.encodedRv (x - a) := by
    rw [Subtype.ext_iff, RVOperations.mul_val, sub_eq_add_neg, sub_eq_add_neg]
    rfl
  constructor
  · rintro ⟨u, ⟨a', ha', hua'⟩, _, _, hbad⟩ x hx
    have ha : a' = a := Subtype.ext ha'
    subst a'
    apply (he x).mp
    rw [hua']
    by_contra hfail
    exact hbad ⟨![x.val, (f x).val], ⟨x, rfl, rfl⟩, (mem_rvRadius_iff v hv a x r hr).mpr hx, hfail⟩
  · intro h
    refine ⟨![(f a).val], ⟨a, rfl, rfl⟩, ⟨(CanonicalRV.encodedRv r).property,
      fun he => hr ((CanonicalRV.encodedRv_zero_iff r).mp he)⟩,
      ⟨t.property, fun he => ht (Subtype.ext (he.trans RVOperations.zero_val.symm))⟩, ?_⟩
    rintro ⟨z, ⟨x, hx, hy⟩, hb, hn⟩
    rw [← hx] at hb
    apply hn
    rw [← hx, ← hy]
    exact (he x).mpr (h x ((mem_rvRadius_iff v hv a x r hr).mp hb))

variable [Valued (VFType (M := M)) Γ]

theorem rvDifference_pairwise_of_locally_constant_witnesses
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : VFType (M := M) → VFType (M := M)) (a r : VFType (M := M)) (hr : r ≠ 0)
    (t : CanonicalRV.RVSort M) (ht : t ≠ 0)
    (ha : ![CanonicalRV.encodedRv r, t] ∈ rvFibre (rvDifferenceWitnesses (unaryScalarGraph f)) ![a])
    (hloc : rvLocallyConstantAt (rvFibre (rvDifferenceWitnesses (unaryScalarGraph f))) ![a]) :
    ∃ s : VFType (M := M), s ≠ 0 ∧
      ∀ b b' : VFType (M := M), b.val ∈ rawOpenBall a.val s.val → b'.val ∈ rawOpenBall a.val s.val →
        CanonicalRV.encodedRv (f b - f b') = t * CanonicalRV.encodedRv (b - b') := by
  let v : Valuation (VFType (M := M)) Γ := Valued.v
  obtain ⟨s, hs, hstay⟩ := (rvLocallyConstantAt_iff_uniformBall hv _ ![a]).mp hloc
  let u := if v s ≤ v r then s else r
  have hu : u ≠ 0 := by
    by_cases h : v s ≤ v r <;> simp [u, h, hs, hr]
  have hur : v u ≤ v r := by
    by_cases h : v s ≤ v r <;> simp [u, h]
  have hus : v u ≤ v s := by
    by_cases h : v s ≤ v r
    · simp [u, h]
    · simp only [u, h, if_false]
      exact le_of_lt (lt_of_not_ge h)
  refine ⟨u, hu, rvDifference_of_uniform_centre_law v hv f a r u hu hr hur t (fun b hb x hx => ?_)⟩
  have hbs : vfValues (![b] : Fin 1 → VFType (M := M)) ∈ uniformBall (vfValues ![a]) s.val := by
    intro i
    fin_cases i
    exact (mem_rawOpenBall_iff v hv a s b hs).mpr
      (((mem_rawOpenBall_iff v hv a u b hu).mp hb).trans_le hus)
  have hw : ![CanonicalRV.encodedRv r, t] ∈ rvFibre (rvDifferenceWitnesses (unaryScalarGraph f)) ![b] :=
    (hstay ![b] hbs).symm ▸ ha
  exact (mem_rvDifferenceWitnesses_iff v hv f b r hr t ht).mp hw x ((mem_rawOpenBall_iff v hv b r x hr).mp hx)

end SpecialTransformations.Section8

end

section

/-! The full first-order relation of radius codes and multipliers for
the paired-point identity. The ball is also required to lie in the domain. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def rvPairwiseWitnesses (A : Set M) (G : Set (Fin 2 → M)) : Set (Fin 1 ⊕ Fin 2 → M) :=
  {z | z ∈ rvDifferenceWitnesses G ∧
    ∀ b : Fin 1 → M, b ∈ rvUniformBall (z ∘ Sum.inl) (z (.inr 0)) →
      b 0 ∈ A ∧ Sum.elim b (z ∘ Sum.inr) ∈ rvDifferenceWitnesses G}

theorem rvPairwiseWitnesses_definable {S : Set M} {A : Set M} {G : Set (Fin 2 → M)}
    (hA : S.Definable₁ LRV A) (hG : S.Definable LRV G) :
    S.Definable LRV (rvPairwiseWitnesses A G) := by
  let P := Fin 1 ⊕ Fin 2
  let W := P ⊕ Fin 1
  let box : (Fin 1 ⊕ Fin 1) ⊕ Fin 1 → W :=
    Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr) (fun _ => .inl (.inr 0))
  let e : P → W := Sum.elim Sum.inr (Sum.inl ∘ Sum.inr)
  have hW := rvDifferenceWitnesses_definable hG
  have hBad := ((rvUniformBallRelation_definable S 1).preimage_comp box).inter
    ((hA.preimage_comp (Sum.inr : Fin 1 → W)).inter (hW.preimage_comp e)).compl
  convert hW.inter hBad.exists_of_finite.compl using 1
  ext z
  have he (b : Fin 1 → M) : Sum.elim z b ∘ e = Sum.elim b (z ∘ Sum.inr) := by
    funext i
    cases i <;> rfl
  change (z ∈ rvDifferenceWitnesses G ∧ ∀ b : Fin 1 → M,
      b ∈ rvUniformBall (z ∘ Sum.inl) (z (.inr 0)) →
        b 0 ∈ A ∧ Sum.elim b (z ∘ Sum.inr) ∈ rvDifferenceWitnesses G) ↔
    z ∈ rvDifferenceWitnesses G ∧ ¬ ∃ b : Fin 1 → M,
      b ∈ rvUniformBall (z ∘ Sum.inl) (z (.inr 0)) ∧
        ¬ (b 0 ∈ A ∧ Sum.elim z b ∘ e ∈ rvDifferenceWitnesses G)
  simp only [he]
  refine and_congr_right (fun _ => ⟨?_, ?_⟩)
  · rintro h ⟨b, hb, hn⟩
    exact hn (h b hb)
  · intro h b hb
    by_contra hn
    exact h ⟨b, hb, hn⟩

variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]

/-- The paired law on a ball contained in the domain only uses graph
points over that domain. -/
theorem rvPairwiseWitnesses_congr_on_domain (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (A : Set M) {G H : Set (Fin 2 → M)}
    (hG : ∀ w ∈ G, iVF (w 0)) (hH : ∀ w ∈ H, iVF (w 0))
    (hGH : ∀ w : Fin 2 → M, w 0 ∈ A → (w ∈ G ↔ w ∈ H)) :
    rvPairwiseWitnesses A G = rvPairwiseWitnesses A H := by
  suffices hmono : ∀ G H : Set (Fin 2 → M), (∀ w ∈ G, iVF (w 0)) →
      (∀ w : Fin 2 → M, w 0 ∈ A → (w ∈ G ↔ w ∈ H)) →
        rvPairwiseWitnesses A G ⊆ rvPairwiseWitnesses A H from
    le_antisymm (hmono G H hG hGH) (hmono H G hH (fun w hw => (hGH w hw).symm))
  intro G H hG hGH z hz
  obtain ⟨hcentre, h⟩ := hz
  have hcoords : iVF (z (.inl 0)) ∧ GammaParameters.NonzeroRV (z (.inr 0)) := by
    obtain ⟨u, hu, hr, _, _⟩ := hcentre
    exact ⟨hG _ hu, hr⟩
  obtain ⟨r, hr⟩ := CanonicalRV.encodedRv_surjective ⟨z (.inr 0), hcoords.2.1⟩
  have hr' : iRv r.val = z (.inr 0) := congrArg Subtype.val hr
  have hr₀ : r ≠ 0 := fun h => hcoords.2.2 (hr'.symm.trans ((CanonicalRV.encodedRv_zero_iff r).mpr h))
  let a := z ∘ Sum.inl
  let D := rvUniformBall a (z (.inr 0))
  have ha : a ∈ D := by
    change a ∈ rvUniformBall a (z (.inr 0))
    rw [← hr', rvUniformBall_eq a r hr₀]
    intro i
    fin_cases i
    exact rawOpenBall_self v hv hcoords.1 r.property (fun e => hr₀ (Subtype.ext e))
  have hsubset (b : Fin 1 → M) (hb : b ∈ D) : b 0 ∈ A := (h b hb).1
  have hstep (b : Fin 1 → M) (hb : b ∈ D) :
      Sum.elim b (z ∘ Sum.inr) ∈ rvDifferenceWitnesses H := by
    obtain ⟨u, hu, hr, ht, hbad⟩ := (h b hb).2
    refine ⟨u, (hGH _ (hsubset b hb)).mp hu, hr, ht, ?_⟩
    rintro ⟨w, hw, hbw, hfail⟩
    let x : Fin 1 → M := ![w 0]
    have hb' : b ∈ uniformBall a r.val := by
      change b ∈ rvUniformBall a (z (.inr 0)) at hb
      rwa [← hr', rvUniformBall_eq a r hr₀] at hb
    have hx : x ∈ uniformBall b r.val := by
      have he : (fun _ : Fin 1 => b 0) = b := by funext i; fin_cases i; rfl
      change x ∈ rvUniformBall (fun _ : Fin 1 => b 0) (z (.inr 0)) at hbw
      rwa [he, ← hr', rvUniformBall_eq b r hr₀] at hbw
    have hx' : x ∈ D := by
      change x ∈ rvUniformBall a (z (.inr 0))
      rw [← hr', rvUniformBall_eq a r hr₀]
      intro i
      have hai : a i ∈ rawOpenBall (a i) r.val := by
        fin_cases i
        exact rawOpenBall_self v hv hcoords.1 r.property (fun e => hr₀ (Subtype.ext e))
      exact rawOpenBall_recentre v hv (rawOpenBall_recentre v hv (hb' i) hai) (hx i)
    exact hbad ⟨w, (hGH w (hsubset x hx')).mpr hw, hbw, hfail⟩
  have he : Sum.elim a (z ∘ Sum.inr) = z := by funext i; cases i <;> rfl
  exact ⟨he ▸ hstep a ha, fun b hb => ⟨hsubset b hb, hstep b hb⟩⟩

theorem mem_rvPairwiseWitnesses_iff (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (A : Set M) (f : VFType (M := M) → VFType (M := M))
    (a r : VFType (M := M)) (hr : r ≠ 0) (t : CanonicalRV.RVSort M) (ht : t ≠ 0) :
    ![CanonicalRV.encodedRv r, t] ∈ rvFibre (rvPairwiseWitnesses A (unaryScalarGraph f)) ![a] ↔
      (∀ b : VFType (M := M), b.val ∈ rawOpenBall a.val r.val → b.val ∈ A) ∧
      ∀ b b' : VFType (M := M), b.val ∈ rawOpenBall a.val r.val → b'.val ∈ rawOpenBall a.val r.val →
        CanonicalRV.encodedRv (f b - f b') = t * CanonicalRV.encodedRv (b - b') := by
  have hself : a.val ∈ rawOpenBall a.val r.val :=
    rawOpenBall_self v hv a.property r.property (fun h => hr (Subtype.ext h))
  have ha : vfValues (![a] : Fin 1 → VFType (M := M)) = fun _ => a.val := by
    funext i
    fin_cases i
    rfl
  constructor
  · rintro ⟨_, h⟩
    have hrow (b : VFType (M := M)) (hb : b.val ∈ rawOpenBall a.val r.val) :
        b.val ∈ A ∧ ![CanonicalRV.encodedRv r, t] ∈
          rvFibre (rvDifferenceWitnesses (unaryScalarGraph f)) ![b] :=
      h ![b.val] (by
        change ![b.val] ∈ rvUniformBall (vfValues (![a] : Fin 1 → VFType (M := M))) (iRv r.val)
        rw [ha]
        exact (mem_rvRadius_iff v hv a b r hr).mpr ((mem_rawOpenBall_iff v hv a r b hr).mp hb))
    refine ⟨fun b hb => (hrow b hb).1, fun b b' hb hb' => ?_⟩
    apply (mem_rvDifferenceWitnesses_iff v hv f b' r hr t ht).mp (hrow b' hb').2 b
    exact (mem_rawOpenBall_iff v hv b' r b hr).mp (rawOpenBall_recentre v hv hb' hb)
  · rintro ⟨hA, hPair⟩
    have hrow (b : VFType (M := M)) (hb : b.val ∈ rawOpenBall a.val r.val) :
        ![CanonicalRV.encodedRv r, t] ∈ rvFibre (rvDifferenceWitnesses (unaryScalarGraph f)) ![b] := by
      apply (mem_rvDifferenceWitnesses_iff v hv f b r hr t ht).mpr
      intro x hx
      have ha : a.val ∈ rawOpenBall b.val r.val := rawOpenBall_recentre v hv hb hself
      exact hPair x b (rawOpenBall_recentre v hv ha ((mem_rawOpenBall_iff v hv b r x hr).mpr hx)) hb
    refine ⟨hrow a hself, fun b hb => ?_⟩
    have hsort : iVF (b 0) := by
      obtain ⟨_, _, _, _, hs⟩ := hb
      exact (hs 0).2.1
    let b' : VFType (M := M) := ⟨b 0, hsort⟩
    have he : b = ![b'.val] := by
      funext i
      fin_cases i
      rfl
    rw [he] at hb ⊢
    change ![b'.val] ∈ rvUniformBall (vfValues (![a] : Fin 1 → VFType (M := M))) (iRv r.val) at hb
    rw [ha] at hb
    have hball := (mem_rawOpenBall_iff v hv a r b' hr).mpr ((mem_rvRadius_iff v hv a b' r hr).mp hb)
    exact ⟨hA b' hball, hrow b' hball⟩

end SpecialTransformations.Section8

end

section

/-! The generic-point argument for 8.5 gives a first-order good locus
whose complement in the unary domain is finite. -/

set_option backward.isDefEq.respectTransparency false

open Filter Topology FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]

def rvPairwiseGood (A : Set M) (f : VFType (M := M) → VFType (M := M)) : Set (Fin 1 → M) :=
  {a | a 0 ∈ A ∧ ∃ d : Fin 2 → M, Sum.elim a d ∈ rvPairwiseWitnesses A (unaryScalarGraph f)}

theorem rvPairwiseGood_definable {S : Set M} {A : Set M} {f : VFType (M := M) → VFType (M := M)}
    (hA : S.Definable₁ LRV A) (hf : S.Definable LRV (unaryScalarGraph f)) :
    S.Definable LRV (rvPairwiseGood A f) :=
  hA.inter (rvPairwiseWitnesses_definable hA hf).exists_of_finite

theorem rvPairwiseGood_finite_exception [CharZero (VFType (M := M))]
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hEP : ∀ E : Subfield (VFType (M := M)), ∃ H, E ≤ H ∧ ImmediateHenselianExtension Valued.v E H)
    (f g : VFType (M := M) → VFType (M := M))
    (hf : S.Definable LRV (unaryScalarGraph f)) (hg : S.Definable LRV (unaryScalarGraph g))
    (A : Set M) (hA : DefinableAt S .vf A) (hInv : ∀ x : VFType (M := M), x.val ∈ A → g (f x) = x) :
    ({z : Fin 1 → M | z 0 ∈ A} \ rvPairwiseGood A f).Finite := by
  let v : Valuation (VFType (M := M)) Γ := Valued.v
  have hRaw := hA.raw_definable
  have hE := hRaw.inter (rvPairwiseGood_definable hRaw hf).compl
  apply rawUnary_finite_of_no_independent hc hκ hs hsmall hE
  · intro z hz i
    fin_cases i
    exact hA.2 hz.1
  · intro z hz hind
    let a := z 0
    have ha : (![a] : Fin 1 → VFType (M := M)) = z := by
      funext i
      fin_cases i
      rfl
    have haA : a.val ∈ A := hz.1
    have haI : AlgebraicIndependent (vfParameterField S) (![a] : Fin 1 → VFType (M := M)) := ha.symm ▸ hind
    have hA' : DefinableOver S (fun _ : Fin 1 => .vf) {z | z 0 ∈ A} := by
      apply raw_definableOver_sorted hc S (fun _ => .vf) _ hRaw
      intro x hx i
      fin_cases i
      exact hA.2 hx
    let X : Set (VFType (M := M)) := {x | x.val ∈ A}
    have hX : X ∈ 𝓝 a :=
      continuous_unary_tuple.continuousAt.preimage_mem_nhds
        (independent_definable_mem_nhds hv S _ hA' ![a] haI haA)
    have hcont := continuousAt_unary_of_independent hc hκ hs hsmall hv f hf a haI
    obtain ⟨γ, t, ht, hLaw⟩ := rvDifference_of_local_definable_inverse hc hκ hs hsmall hv hEP f g hf hg
      a X haA hX hcont hInv
    obtain ⟨r, hr, hγ⟩ := gamma_has_vf_representative γ
    have hW : ![CanonicalRV.encodedRv r, t] ∈
        rvFibre (rvDifferenceWitnesses (unaryScalarGraph f)) ![a] := by
      apply (mem_rvDifferenceWitnesses_iff v hv f a r hr t ht).mpr
      intro x hx
      by_cases he : x = a
      · subst x
        simp only [sub_self, RVOperations.rv_zero, mul_zero]
      · apply hLaw
        rw [← hγ]
        exact (GammaThresholdGeometry.value_lt_gamma v hv (x - a) r (sub_ne_zero.mpr he) hr).mp hx
    have hloc := rvFibre_locallyConstant_of_independent hc hv (rvDifferenceWitnesses_definable hf) ![a] haI
    obtain ⟨s, hs₀, hPair⟩ := rvDifference_pairwise_of_locally_constant_witnesses hv f a r hr t ht hW hloc
    obtain ⟨u, hu₀, hU⟩ := exists_nonzero_ball_subset a hX
    let w := if v s ≤ v u then s else u
    have hw : w ≠ 0 := by by_cases h : v s ≤ v u <;> simp [w, h, hs₀, hu₀]
    have hws : v w ≤ v s := by
      by_cases h : v s ≤ v u
      · simp [w, h]
      · simpa only [w, if_neg h] using (le_of_lt (lt_of_not_ge h))
    have hwu : v w ≤ v u := by by_cases h : v s ≤ v u <;> simp [w, h]
    have hball (x : VFType (M := M)) (hx : x.val ∈ rawOpenBall a.val w.val) : v (x - a) < v w :=
      (mem_rawOpenBall_iff v hv a w x hw).mp hx
    apply hz.2
    rw [← ha]
    refine ⟨haA, rvValues ![CanonicalRV.encodedRv w, t],
      (mem_rvPairwiseWitnesses_iff v hv A f a w hw t ht).mpr ⟨?_, ?_⟩⟩
    · exact fun x hx => hU ((hball x hx).trans_le hwu)
    · intro x y hx hy
      exact hPair x y ((mem_rawOpenBall_iff v hv a s x hs₀).mpr ((hball x hx).trans_le hws))
        ((mem_rawOpenBall_iff v hv a s y hs₀).mpr ((hball y hy).trans_le hws))

end SpecialTransformations.Section8

end

section

/-! On the paired-law locus the multiplier is unique. Its valid radii
form a definable upper ray containing its finite endpoint. -/

set_option backward.isDefEq.respectTransparency false

open Filter Topology FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]

def rvPairwiseGammaLaw (A : Set M) (f : VFType (M := M) → VFType (M := M))
    (a : VFType (M := M)) (t : CanonicalRV.RVSort M) (r : Values.Gamma (M := M)) : Prop :=
  (∀ x : VFType (M := M), r.val < Values.vfValueHom (x - a) → x.val ∈ A) ∧
  ∀ x y : VFType (M := M), r.val < Values.vfValueHom (x - a) → r.val < Values.vfValueHom (y - a) →
    CanonicalRV.encodedRv (f x - f y) = t * CanonicalRV.encodedRv (x - y)

private theorem gamma_lt_centreValue (r : Values.Gamma (M := M)) (a : VFType (M := M)) :
    r.val < Values.vfValueHom (a - a) := by
  rw [sub_self, map_zero, ← Values.infinity_eq_zero]
  exact lt_of_le_of_ne (Values.le_infinity _) r.property

theorem rvPairwiseGammaLaw_witness_iff
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : Set M) (f : VFType (M := M) → VFType (M := M)) (a r : VFType (M := M)) (hr : r ≠ 0)
    (t : CanonicalRV.RVSort M) (ht : t ≠ 0) :
    ![CanonicalRV.encodedRv r, t] ∈ rvFibre (rvPairwiseWitnesses A (unaryScalarGraph f)) ![a] ↔
      rvPairwiseGammaLaw A f a t (GammaThresholdGeometry.vfGamma r hr) := by
  rw [mem_rvPairwiseWitnesses_iff Valued.v hv A f a r hr t ht]
  have he (x : VFType (M := M)) : x.val ∈ rawOpenBall a.val r.val ↔
      (GammaThresholdGeometry.vfGamma r hr).val < Values.vfValueHom (x - a) := by
    by_cases hxa : x = a
    · subst x
      exact iff_of_true (rawOpenBall_self Valued.v hv a.property r.property (fun h => hr (Subtype.ext h)))
        (gamma_lt_centreValue _ a)
    · exact (mem_rawOpenBall_iff Valued.v hv a r x hr).trans
        (GammaThresholdGeometry.value_lt_gamma Valued.v hv (x - a) r (sub_ne_zero.mpr hxa) hr)
  simp only [rvPairwiseGammaLaw, he]

theorem rvPairwiseGammaLaw_unique {A : Set M} {f : VFType (M := M) → VFType (M := M)}
    {a : VFType (M := M)} {t u : CanonicalRV.RVSort M} {r s : Values.Gamma (M := M)}
    (ht : rvPairwiseGammaLaw A f a t r) (hu : rvPairwiseGammaLaw A f a u s) : t = u := by
  obtain ⟨γ, hγ⟩ := exists_gt (max r s)
  obtain ⟨d, hd, hval⟩ := gamma_has_vf_representative γ
  let x := d + a
  have hxa : x - a = d := add_sub_cancel_right d a
  have hne : x ≠ a := fun h => hd (by rw [← hxa, h, sub_self])
  have hr : r.val < Values.vfValueHom (x - a) := by
    rw [hxa, hval]
    exact (le_max_left r s).trans_lt hγ
  have hs : s.val < Values.vfValueHom (x - a) := by
    rw [hxa, hval]
    exact (le_max_right r s).trans_lt hγ
  exact rvDifference_multiplier_unique f a x hne t u (ht.2 x a hr (gamma_lt_centreValue r a))
    (hu.2 x a hs (gamma_lt_centreValue s a))

theorem rvPairwiseGammaLaw_of_larger {A : Set M} {f : VFType (M := M) → VFType (M := M)}
    {a : VFType (M := M)} {t : CanonicalRV.RVSort M} (r : Values.Gamma (M := M))
    (h : ∀ s : Values.Gamma (M := M), r < s → rvPairwiseGammaLaw A f a t s) :
    rvPairwiseGammaLaw A f a t r := by
  have hstep (x : VFType (M := M)) (hx : r.val < Values.vfValueHom (x - a)) :
      ∃ s : Values.Gamma (M := M), r < s ∧ s.val < Values.vfValueHom (x - a) := by
    by_cases hxa : x = a
    · subst x
      obtain ⟨s, hs⟩ := exists_gt r
      exact ⟨s, hs, gamma_lt_centreValue s a⟩
    · let γ := GammaThresholdGeometry.vfGamma (x - a) (sub_ne_zero.mpr hxa)
      obtain ⟨s, hs, hsγ⟩ := exists_between (show r < γ from hx)
      exact ⟨s, hs, hsγ⟩
  constructor
  · intro x hx
    obtain ⟨s, hs, hsx⟩ := hstep x hx
    exact (h s hs).1 x hsx
  · intro x y hx hy
    obtain ⟨s, hs, hsx⟩ := hstep x hx
    obtain ⟨u, hu, huy⟩ := hstep y hy
    exact (h (min s u) (lt_min hs hu)).2 x y
      ((show (min s u).val ≤ s.val from min_le_left s u).trans_lt hsx)
      ((show (min s u).val ≤ u.val from min_le_right s u).trans_lt huy)

theorem named_pairwise_rv_law (h00 : M ⊨ Axioms.ACVF00)
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} {A : Set M} {f : VFType (M := M) → VFType (M := M)}
    (hA : S.Definable₁ LRV A) (hf : S.Definable LRV (unaryScalarGraph f))
    (a : VFType (M := M)) (ha : vfValues (![a] : Fin 1 → VFType (M := M)) ∈ rvPairwiseGood A f) :
    ∃ (r : Values.Gamma (M := M)) (t : CanonicalRV.RVSort M), t ≠ 0 ∧
      Values.GammaDefinable (insert a.val S) {r} ∧
      DefinableClosureAt (insert a.val S) .rv t.val ∧ rvPairwiseGammaLaw A f a t r := by
  let B := insert a.val S
  let Q := rvPairwiseWitnesses A (unaryScalarGraph f)
  let q (r t : M) := Sum.elim (vfValues (![a] : Fin 1 → VFType (M := M))) (![r, t] : Fin 2 → M)
  have hQ : S.Definable LRV Q := rvPairwiseWitnesses_definable hA hf
  have hproper {r t : M} (h : q r t ∈ Q) :
      GammaParameters.NonzeroRV r ∧ GammaParameters.NonzeroRV t := by
    obtain ⟨_, _, hr, ht, _⟩ := h.1
    exact ⟨hr, ht⟩
  have hdecode {r t : M} (h : q r t ∈ Q) :
      ∃ (ρ : Values.Gamma (M := M)) (u : CanonicalRV.RVSort M),
        ∃ hr : iRV r, ∃ hr₀ : r ≠ iRVZero, ρ = Values.gammaOf ⟨r, hr⟩ hr₀ ∧
          u.val = t ∧ u ≠ 0 ∧ rvPairwiseGammaLaw A f a u ρ := by
    obtain ⟨hr, ht⟩ := hproper h
    obtain ⟨s, he⟩ := CanonicalRV.encodedRv_surjective ⟨r, hr.1⟩
    have he' : iRv s.val = r := congrArg Subtype.val he
    have hs : s ≠ 0 := fun hz => hr.2 (he'.symm.trans ((CanonicalRV.encodedRv_zero_iff s).mpr hz))
    let u : CanonicalRV.RVSort M := ⟨t, ht.1⟩
    have hu : u ≠ 0 := fun hz => ht.2 ((congrArg Subtype.val hz).trans RVOperations.zero_val)
    refine ⟨GammaThresholdGeometry.vfGamma s hs, u, hr.1, hr.2,
      Subtype.ext (congrArg Values.vrv he), rfl, hu, ?_⟩
    apply (rvPairwiseGammaLaw_witness_iff hv A f a s hs u hu).mp
    have heq : rvValues (![CanonicalRV.encodedRv s, u] : Fin 2 → CanonicalRV.RVSort M) = ![iRv s.val, t] := by
      funext i
      fin_cases i <;> rfl
    change Sum.elim (vfValues (![a] : Fin 1 → VFType (M := M))) (rvValues _) ∈ Q
    rw [heq]
    change q (iRv s.val) t ∈ Q
    rwa [he']
  obtain ⟨d, hd⟩ := ha.2
  have hd' : q (d 0) (d 1) ∈ Q := by
    have he : (![d 0, d 1] : Fin 2 → M) = d := by funext i; fin_cases i <;> rfl
    simpa only [q, he] using hd
  obtain ⟨ρ, t, _, _, _, htd, ht, hρ⟩ := hdecode hd'
  let V : Set M := {u | ∃ r : M, q r u ∈ Q}
  have hV : B.Definable₁ LRV V := by
    let e (z : Fin 1 ⊕ Fin 1 → M) := q (z (.inr 0)) (z (.inl 0))
    have he : B.DefinableMap LRV e := by
      rintro (i | i)
      · fin_cases i
        exact LRV.definableFun_const _ (Set.mem_insert _ _)
      · fin_cases i <;> exact Set.DefinableFun.proj LRV
    change B.Definable LRV {z : Fin 1 → M | z 0 ∈ V}
    convert ((hQ.mono (Set.subset_insert _ _)).preimage_map he).exists_of_finite using 1
    ext z
    exact ⟨fun ⟨r, hr⟩ => ⟨![r], hr⟩, fun ⟨r, hr⟩ => ⟨r 0, hr⟩⟩
  have hVt : V = {t.val} := by
    ext u
    constructor
    · rintro ⟨r, hr⟩
      obtain ⟨s, u', _, _, _, hu', _, hu⟩ := hdecode hr
      exact hu'.symm.trans (congrArg Subtype.val (rvPairwiseGammaLaw_unique hu hρ))
    · intro hu
      have he : u = d 1 := hu.trans htd
      exact ⟨d 0, he.symm ▸ hd'⟩
  have htdcl : DefinableClosureAt B .rv t.val := by
    rw [hVt] at hV
    exact raw_definable_sorted hc B _ .rv hV (by rintro _ rfl; exact t.property)
  let C : Set (Values.Gamma (M := M)) := {r | rvPairwiseGammaLaw A f a t r}
  let D : Set M := {r | q r t.val ∈ Q}
  have hDC : D = Values.gammaPullback C := by
    ext r
    constructor
    · intro hr
      obtain ⟨s, u, hrv, hr₀, he, hu, _, hs⟩ := hdecode hr
      have hut : u = t := Subtype.ext hu
      rw [hut] at hs
      exact ⟨hrv, hr₀, he ▸ hs⟩
    · rintro ⟨hrv, hr₀, hs⟩
      obtain ⟨s, he⟩ := CanonicalRV.encodedRv_surjective ⟨r, hrv⟩
      have he' : iRv s.val = r := congrArg Subtype.val he
      have hs₀ : s ≠ 0 := fun hz => hr₀ (he'.symm.trans ((CanonicalRV.encodedRv_zero_iff s).mpr hz))
      have hγ : GammaThresholdGeometry.vfGamma s hs₀ = Values.gammaOf ⟨r, hrv⟩ hr₀ :=
        Subtype.ext (congrArg Values.vrv he)
      have h := (rvPairwiseGammaLaw_witness_iff hv A f a s hs₀ t ht).mpr (hγ.symm ▸ hs)
      have heq : rvValues (![CanonicalRV.encodedRv s, t] : Fin 2 → CanonicalRV.RVSort M) = ![iRv s.val, t.val] := by
        funext i
        fin_cases i <;> rfl
      change Sum.elim (vfValues (![a] : Fin 1 → VFType (M := M))) (rvValues _) ∈ Q at h
      rw [heq] at h
      change q (iRv s.val) t.val ∈ Q at h
      rwa [he'] at h
  have hDef : Values.GammaDefinable B C := by
    rw [Values.GammaDefinable, ← hDC]
    let T := insert t.val B
    let e (z : Fin 1 → M) := q (z 0) t.val
    have he : T.DefinableMap LRV e := by
      rintro (i | i)
      · fin_cases i
        exact LRV.definableFun_const _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      · fin_cases i
        · exact Set.DefinableFun.proj LRV
        · exact LRV.definableFun_const _ (Set.mem_insert _ _)
    have hDT : T.Definable₁ LRV D :=
      (hQ.mono ((Set.subset_insert _ _).trans (Set.subset_insert _ _))).preimage_map he
    apply (raw_definable_sorted hc T D .rv hDT (fun r hr => (hproper hr).1.1)).eliminate_sorted_definable_params
    rintro u (rfl | hu)
    · exact ⟨.rv, htdcl⟩
    · rcases TypedModelMap.sort_cover u with h | h
      · exact ⟨.vf, definableClosureAt_of_mem hu h⟩
      · exact ⟨.rv, definableClosureAt_of_mem hu h⟩
  obtain ⟨r, hr, hrd⟩ := gamma_upper_ray_has_definable_radius h00 hDef ⟨ρ, hρ⟩
    (by
      intro x hx y hxy
      have he : x.val ≤ y.val := hxy
      exact ⟨fun b hb => hx.1 b (he.trans_lt hb), fun b b' hb hb' => hx.2 b b' (he.trans_lt hb) (he.trans_lt hb')⟩)
    (fun r hr => rvPairwiseGammaLaw_of_larger r hr)
  exact ⟨r, t, ht, hrd, htdcl, hr⟩

theorem lemma_8_5_canonical [CharZero (VFType (M := M))]
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hEP : ∀ E : Subfield (VFType (M := M)), ∃ H, E ≤ H ∧ ImmediateHenselianExtension Valued.v E H)
    (f g : VFType (M := M) → VFType (M := M))
    (hf : S.Definable LRV (unaryScalarGraph f)) (hg : S.Definable LRV (unaryScalarGraph g))
    (A : Set M) (hA : DefinableAt S .vf A) (hInv : ∀ x : VFType (M := M), x.val ∈ A → g (f x) = x) :
    ∃ U : Set (Fin 1 → M), S.Definable LRV U ∧ U ⊆ {z | z 0 ∈ A} ∧
      ({z : Fin 1 → M | z 0 ∈ A} \ U).Finite ∧
      ∀ a : VFType (M := M), vfValues (![a] : Fin 1 → VFType (M := M)) ∈ U →
        ∃ (r : Values.Gamma (M := M)) (t : CanonicalRV.RVSort M), t ≠ 0 ∧
          Values.GammaDefinable (insert a.val S) {r} ∧ DefinableClosureAt (insert a.val S) .rv t.val ∧
          rvPairwiseGammaLaw A f a t r :=
  ⟨rvPairwiseGood A f, rvPairwiseGood_definable hA.raw_definable hf, fun _ h => h.1,
    rvPairwiseGood_finite_exception hc hκ hs hsmall hv hEP f g hf hg A hA hInv,
    named_pairwise_rv_law h00 hc hv hA.raw_definable hf⟩

end SpecialTransformations.Section8

end

section

/-! State the paired RV law on its original partial graph. The
definable zero extensions and inverse are internal to the proofs. -/

set_option backward.isDefEq.respectTransparency false

open Filter Topology FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]

theorem lemma_8_5_partial [CharZero (VFType (M := M))]
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hEP : ∀ E : Subfield (VFType (M := M)), ∃ H, E ≤ H ∧ ImmediateHenselianExtension Valued.v E H)
    (f : VFType (M := M) → VFType (M := M)) (A B : Set M)
    (hA : A ⊆ {x | iVF x}) (hB : B ⊆ {x | iVF x})
    (hf : S.Definable LRV (partialUnaryGraph A f))
    (hbij : Set.BijOn f {x | x.val ∈ A} {y | y.val ∈ B}) :
    ∃ U : Set (Fin 1 → M), S.Definable LRV U ∧ U ⊆ {z | z 0 ∈ A} ∧
      ({z : Fin 1 → M | z 0 ∈ A} \ U).Finite ∧
      ∀ a : VFType (M := M), vfValues (![a] : Fin 1 → VFType (M := M)) ∈ U →
        ∃ (r : Values.Gamma (M := M)) (t : CanonicalRV.RVSort M), t ≠ 0 ∧
          Values.GammaDefinable (insert a.val S) {r} ∧ DefinableClosureAt (insert a.val S) .rv t.val ∧
          rvPairwiseGammaLaw A f a t r := by
  obtain ⟨F, G, hF, hG, hFG⟩ := unaryPartialBijection_definable_extensions hA hB hbij hf
  have hAd := raw_definable_sorted hc S A .vf (partialUnaryGraph_domain_definable hA hf) hA
  obtain ⟨U, hU, hUA, hfin, hW⟩ := lemma_8_5_canonical h00 hc hκ hs hsmall hv hEP F G hF hG A hAd
    (fun x hx => (hFG x hx).2)
  refine ⟨U, hU, hUA, hfin, fun a ha => ?_⟩
  obtain ⟨r, t, ht, hr, htd, h⟩ := hW a ha
  refine ⟨r, t, ht, hr, htd, h.1, fun x y hx hy => ?_⟩
  simpa only [(hFG x (h.1 x hx)).1, (hFG y (h.1 y hy)).1] using h.2 x y hx hy

end SpecialTransformations.Section8

end
