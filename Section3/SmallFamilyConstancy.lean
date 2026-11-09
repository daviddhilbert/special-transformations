import ACVFQE
import Mathlib
import Section3.GammaSpecialization
import Section3.MixedPolynomialSyntax
import Section3.PolynomialRVMonomial
import Section3.RVLiteralReduction
import Section3.RVSmallPowers

/- Component: MonomialCoefficients -/

namespace SpecialTransformations.Section3.RVMonomial
variable {G Γ α : Type*} [CommGroupWithZero G] [LinearOrderedCommGroupWithZero Γ]

/-- Only nonzero coefficients need bounds. Zero coefficients remain
available in every product, inverse and residue-operation branch. -/
def CoefficientBounded (v : G →*₀ Γ) (D : Set α) (c : α → G) : Prop :=
  ∃ lo hi : Γˣ, ∀ a ∈ D, c a ≠ 0 → (lo : Γ) ≤ v (c a) ∧ v (c a) ≤ hi

theorem coefficientBounded_const (v : G →*₀ Γ) (D : Set α) (c : G) :
    CoefficientBounded v D (fun _ => c) := by
  by_cases hc : c = 0
  · exact ⟨1,1,fun a ha h => False.elim (h hc)⟩
  · let u : Γˣ := Units.mk0 (v c) ((map_ne_zero v).mpr hc)
    exact ⟨u,u,fun a ha h => ⟨le_rfl,le_rfl⟩⟩

theorem CoefficientBounded.mul {v : G →*₀ Γ} {D : Set α} {c d : α → G}
    (hc : CoefficientBounded v D c) (hd : CoefficientBounded v D d) :
    CoefficientBounded v D (fun a => c a * d a) := by
  obtain ⟨cl,ch,hc⟩ := hc
  obtain ⟨dl,dh,hd⟩ := hd
  refine ⟨cl*dl,ch*dh,?_⟩
  intro a ha hn
  have hcn : c a ≠ 0 := left_ne_zero_of_mul hn
  have hdn : d a ≠ 0 := right_ne_zero_of_mul hn
  obtain ⟨hc0,hc1⟩ := hc a ha hcn
  obtain ⟨hd0,hd1⟩ := hd a ha hdn
  simp only [map_mul,Units.val_mul]
  constructor <;> gcongr

theorem CoefficientBounded.inv {v : G →*₀ Γ} {D : Set α} {c : α → G}
    (hc : CoefficientBounded v D c) : CoefficientBounded v D (fun a => (c a)⁻¹) := by
  obtain ⟨lo,hi,hc⟩ := hc
  refine ⟨hi⁻¹,lo⁻¹,?_⟩
  intro a ha hn
  change (c a)⁻¹ ≠ 0 at hn
  have hcn : c a ≠ 0 := fun hz => hn (by rw [hz,inv_zero])
  obtain ⟨hc0,hc1⟩ := hc a ha hcn
  have hv : 0 < v (c a) := pos_iff_ne_zero.mpr ((map_ne_zero v).mpr hcn)
  have hl : 0 < (lo : Γ) := pos_iff_ne_zero.mpr (Units.ne_zero lo)
  have hh : 0 < (hi : Γ) := pos_iff_ne_zero.mpr (Units.ne_zero hi)
  simp only [map_inv₀,Units.val_inv_eq_inv_val]
  exact ⟨(inv_le_inv₀ hh hv).mpr hc1,(inv_le_inv₀ hv hl).mpr hc0⟩

theorem coefficientBounded_of_zero_or_one (v : G →*₀ Γ) (D : Set α) (c : α → G)
    (hc : ∀ a ∈ D, c a = 0 ∨ v (c a) = 1) : CoefficientBounded v D c := by
  refine ⟨1,1,?_⟩
  intro a ha hn
  rw [(hc a ha).resolve_left hn]
  exact ⟨le_rfl,le_rfl⟩

end SpecialTransformations.Section3.RVMonomial

/- Component: MonomialSeparation -/


namespace SpecialTransformations.Section3.RVMonomial
variable {G Γ α : Type*} [CommGroupWithZero G] [LinearOrderedCommGroupWithZero Γ]

theorem negative_exponent_bound (v : G →*₀ Γ) (D : Set α) (c : α → G)
    (hc : CoefficientBounded v D c) (e : ℤ) (he : e < 0) :
    ∃ r : Γˣ, ∀ x : Γ, 0 < x → x < r →
      ∀ a ∈ D, c a ≠ 0 → 1 < x ^ e * v (c a) := by
  obtain ⟨lo,hi,hc⟩ := hc
  let r : Γˣ := min 1 lo
  refine ⟨r,?_⟩
  intro x hx hxr a ha hca
  have hr1 : (r : Γ) ≤ 1 := min_le_left (1 : Γˣ) lo
  have hrl : (r : Γ) ≤ lo := min_le_right (1 : Γˣ) lo
  have hxl : x < lo := lt_of_lt_of_le hxr hrl
  have hsmall : 1 < x⁻¹ * (lo : Γ) := by
    calc
      1 = x⁻¹*x := (inv_mul_cancel₀ (ne_of_gt hx)).symm
      _ < x⁻¹*lo := mul_lt_mul_of_pos_left hxl (inv_pos.mpr hx)
  exact one_lt_negative_zpow_mul hx (le_trans hxr.le hr1) he (hc a ha hca).1 hsmall

theorem positive_exponent_bound (v : G →*₀ Γ) (D : Set α) (c : α → G)
    (hc : CoefficientBounded v D c) (e : ℤ) (he : 0 < e) :
    ∃ r : Γˣ, ∀ x : Γ, 0 < x → x < r →
      ∀ a ∈ D, c a ≠ 0 → x ^ e * v (c a) < 1 := by
  obtain ⟨lo,hi,hc⟩ := hc
  let r : Γˣ := min 1 hi⁻¹
  refine ⟨r,?_⟩
  intro x hx hxr a ha hca
  have hr1 : (r : Γ) ≤ 1 := min_le_left (1 : Γˣ) hi⁻¹
  have hrh' : (r : Γ) ≤ ((hi⁻¹ : Γˣ) : Γ) := min_le_right (1 : Γˣ) hi⁻¹
  have hrh : (r : Γ) ≤ (hi : Γ)⁻¹ := by
    simpa only [Units.val_inv_eq_inv_val] using hrh'
  have hxh : x < (hi : Γ)⁻¹ := lt_of_lt_of_le hxr hrh
  have hhi : 0 < (hi : Γ) := pos_iff_ne_zero.mpr (Units.ne_zero hi)
  have hsmall : x * (hi : Γ) < 1 := by
    calc
      x*hi < (hi : Γ)⁻¹*hi := mul_lt_mul_of_pos_right hxh hhi
      _ = 1 := inv_mul_cancel₀ (Units.ne_zero hi)
  exact positive_zpow_mul_lt_one hx (le_trans hxr.le hr1) he (hc a ha hca).2 hsmall

/-- Nonzero homogeneous terms with a nonzero exponent eventually leave
the residue subset, uniformly over every bounded coefficient family. -/
theorem nonzero_exponent_separation (v : G →*₀ Γ) (D : Set α) (c : α → G)
    (hc : CoefficientBounded v D c) (e : ℤ) (he : e ≠ 0) :
    ∃ r : Γˣ, ∀ x : Γ, 0 < x → x < r →
      ∀ a ∈ D, c a ≠ 0 → x ^ e * v (c a) ≠ 1 := by
  rcases lt_or_gt_of_ne he with he | he
  · obtain ⟨r,hr⟩ := negative_exponent_bound v D c hc e he
    exact ⟨r,fun x hx hs a ha hn => ne_of_gt (hr x hx hs a ha hn)⟩
  · obtain ⟨r,hr⟩ := positive_exponent_bound v D c hc e he
    exact ⟨r,fun x hx hs a ha hn => ne_of_lt (hr x hx hs a ha hn)⟩

end SpecialTransformations.Section3.RVMonomial

/- Component: SmallRVMonomials -/



set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.RVMonomial
open RVOperations
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

abbrev AbsoluteValueGroup (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF] :=
  MonoidWithZeroHom.ValueGroup₀ (.ofClass (Values.presentationValuation (M := M)))

/-- A common small punctured VF ball for every member of the output box.
The radius belongs to the actual restricted value group. -/
def SmallUniform {α : Type} (D : Set α) (P : VFType (M := M) → α → Prop) : Prop :=
  ∃ r : (AbsoluteValueGroup M)ˣ, ∀ x : VFType (M := M), x ≠ 0 →
    (Values.presentationValuation (M := M)).restrict x < r.val → ∀ y ∈ D, P x y

theorem SmallUniform.of_forall {α : Type} {D : Set α} {P : VFType (M := M) → α → Prop}
    (hP : ∀ x, x ≠ 0 → ∀ y ∈ D, P x y) : SmallUniform D P :=
  ⟨1,fun x hx _ y hy => hP x hx y hy⟩

theorem SmallUniform.and {α : Type} {D : Set α} {P Q : VFType (M := M) → α → Prop}
    (hP : SmallUniform D P) (hQ : SmallUniform D Q) : SmallUniform D (fun x y => P x y ∧ Q x y) := by
  obtain ⟨r,hr⟩ := hP
  obtain ⟨s,hs⟩ := hQ
  refine ⟨min r s,?_⟩
  intro x hx hsmall y hy
  have hmr : ((min r s : (AbsoluteValueGroup M)ˣ) : AbsoluteValueGroup M) ≤ r := min_le_left r s
  have hms : ((min r s : (AbsoluteValueGroup M)ˣ) : AbsoluteValueGroup M) ≤ s := min_le_right r s
  exact ⟨hr x hx (lt_of_lt_of_le hsmall hmr) y hy,hs x hx (lt_of_lt_of_le hsmall hms) y hy⟩

theorem SmallUniform.mono {α : Type} {D : Set α} {P Q : VFType (M := M) → α → Prop}
    (hP : SmallUniform D P) (hPQ : ∀ x, x ≠ 0 → ∀ y ∈ D, P x y → Q x y) : SmallUniform D Q := by
  obtain ⟨r,hr⟩ := hP
  exact ⟨r,fun x hx hs y hy => hPQ x hx y hy (hr x hx hs y hy)⟩

def Homogeneous {α : Type} (D : Set α)
    (f : VFType (M := M) → α → CanonicalRV.RVSort M) : Prop :=
  ∃ e : ℤ, ∃ c : α → CanonicalRV.RVSort M,
    CoefficientBounded (absoluteHom (M := M)) D c ∧
      SmallUniform D (fun x y => f x y = CanonicalRV.encodedRv x ^ e * c y)

theorem Homogeneous.congr {α : Type} {D : Set α}
    {f g : VFType (M := M) → α → CanonicalRV.RVSort M}
    (hf : Homogeneous D f) (he : ∀ x y, f x y = g x y) : Homogeneous D g := by
  have hfg : f = g := funext (fun x => funext (he x))
  rw [← hfg]
  exact hf

theorem homogeneous_const {α : Type} (D : Set α) (c : CanonicalRV.RVSort M) :
    Homogeneous D (fun _ _ => c) := by
  refine ⟨0,fun _ => c,coefficientBounded_const absoluteHom D c,?_⟩
  exact SmallUniform.of_forall (fun _ _ _ _ => by rw [zpow_zero,one_mul])

theorem homogeneous_coefficient {α : Type} (D : Set α) (c : α → CanonicalRV.RVSort M)
    (hc : CoefficientBounded absoluteHom D c) : Homogeneous D (fun _ y => c y) := by
  refine ⟨0,c,hc,?_⟩
  exact SmallUniform.of_forall (fun _ _ _ _ => by rw [zpow_zero,one_mul])

theorem Homogeneous.mul {α : Type} {D : Set α}
    {f g : VFType (M := M) → α → CanonicalRV.RVSort M}
    (hf : Homogeneous D f) (hg : Homogeneous D g) : Homogeneous D (fun x y => f x y * g x y) := by
  obtain ⟨e,c,hc,hf⟩ := hf
  obtain ⟨d,b,hb,hg⟩ := hg
  refine ⟨e+d,fun y => c y*b y,hc.mul hb,?_⟩
  apply (hf.and hg).mono
  intro x hx y hy hfg
  dsimp only
  rw [hfg.1,hfg.2,zpow_add₀ ((rv_ne_zero x).mpr hx)]
  ac_rfl

theorem Homogeneous.inv {α : Type} {D : Set α}
    {f : VFType (M := M) → α → CanonicalRV.RVSort M}
    (hf : Homogeneous D f) : Homogeneous D (fun x y => (f x y)⁻¹) := by
  obtain ⟨e,c,hc,hf⟩ := hf
  refine ⟨-e,fun y => (c y)⁻¹,hc.inv,?_⟩
  apply hf.mono
  intro x hx y hy he
  dsimp only
  rw [he,mul_inv_rev,zpow_neg]
  exact mul_comm _ _

theorem homogeneous_polynomial {α : Type} (D : Set α)
    (p : Polynomial (VFType (M := M))) :
    Homogeneous D (fun x _ => CanonicalRV.encodedRv (p.eval x)) := by
  let v := Values.presentationValuation (M := M)
  letI : Valued (VFType (M := M)) (Values.presentationType (M := M)) := Valued.mk' v
  have hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y :=
    Values.presentation_compatible
  obtain ⟨m,c,hc⟩ := polynomial hv p
  refine ⟨m,fun _ => CanonicalRV.encodedRv c,
    coefficientBounded_const absoluteHom D (CanonicalRV.encodedRv c),?_⟩
  obtain ⟨r,hr⟩ := Valued.mem_nhds.mp hc
  refine ⟨r,?_⟩
  intro x hx hs y hy
  have he := hr (show v.restrict (x-0) < r.val by simpa only [sub_zero] using hs)
  simpa only [Set.mem_setOf_eq,zpow_natCast] using he

theorem nonzero_exponent_outside_residue {α : Type} (D : Set α)
    (c : α → CanonicalRV.RVSort M) (hc : CoefficientBounded absoluteHom D c)
    (e : ℤ) (he : e ≠ 0) :
    SmallUniform D (fun x y => c y ≠ 0 →
      ¬ ValuedModelMap.inK (CanonicalRV.encodedRv x ^ e * c y)) := by
  obtain ⟨r,hr⟩ := nonzero_exponent_separation absoluteHom D c hc e he
  refine ⟨r,?_⟩
  intro x hx hs y hy hcy
  have hrv : CanonicalRV.encodedRv x ≠ 0 := (rv_ne_zero x).mpr hx
  have hv : 0 < absoluteHom (CanonicalRV.encodedRv x) :=
    pos_iff_ne_zero.mpr ((map_ne_zero absoluteHom).mpr hrv)
  apply not_inK_of_absolute_ne_one _ (mul_ne_zero (zpow_ne_zero _ hrv) hcy)
  rw [map_mul,map_zpow₀]
  apply hr _ hv ?_ y hy hcy
  simpa only [absolute_rv] using hs

end SpecialTransformations.Section3.RVMonomial

/- Component: ResidueRVMonomials -/

set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.RVMonomial
open RVOperations
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem Homogeneous.negK {α : Type} {D : Set α}
    {f : VFType (M := M) → α → CanonicalRV.RVSort M}
    (hf : Homogeneous D f) : Homogeneous D (fun x y => ValuedModelMap.negK (f x y)) := by
  obtain ⟨e,c,hc,hf⟩ := hf
  by_cases he : e = 0
  · subst e
    let d (y : α) := ValuedModelMap.negK (c y)
    have hd : CoefficientBounded absoluteHom D d :=
      coefficientBounded_of_zero_or_one absoluteHom D d
        (fun y _ => (inK_iff _).mp (negK_inK (c y)))
    refine ⟨0,d,hd,?_⟩
    apply hf.mono
    intro x hx y hy hxy
    dsimp only
    simpa only [zpow_zero,one_mul] using congrArg ValuedModelMap.negK hxy
  · have hs := nonzero_exponent_outside_residue D c hc e he
    refine ⟨0,fun _ => 0,coefficientBounded_const absoluteHom D 0,?_⟩
    apply (hf.and hs).mono
    intro x hx y hy hxy
    dsimp only
    simp only [zpow_zero,mul_zero]
    rw [hxy.1]
    by_cases hcy : c y = 0
    · rw [hcy,mul_zero,← zeroRV_eq,ValuedModelMap.negK_zero]
    · exact (ValuedModelMap.negK_junk _ (hxy.2 hcy)).trans zeroRV_eq

noncomputable def addCoefficient {α : Type} (e d : ℤ)
    (c b : α → CanonicalRV.RVSort M) (y : α) : CanonicalRV.RVSort M :=
  if (e ≠ 0 ∧ c y ≠ 0) ∨ (d ≠ 0 ∧ b y ≠ 0) then 0
  else ValuedModelMap.addK (if e = 0 then c y else 0) (if d = 0 then b y else 0)

theorem Homogeneous.addK {α : Type} {D : Set α}
    {f g : VFType (M := M) → α → CanonicalRV.RVSort M}
    (hf : Homogeneous D f) (hg : Homogeneous D g) :
    Homogeneous D (fun x y => ValuedModelMap.addK (f x y) (g x y)) := by
  obtain ⟨e,c,hc,hf⟩ := hf
  obtain ⟨d,b,hb,hg⟩ := hg
  have hcoef : CoefficientBounded absoluteHom D (addCoefficient e d c b) := by
    apply coefficientBounded_of_zero_or_one
    intro y hy
    unfold addCoefficient
    split_ifs <;> first
      | exact Or.inl rfl
      | exact (inK_iff _).mp (addK_inK _ _)
  have hs1 : SmallUniform D (fun x y => e ≠ 0 → c y ≠ 0 →
      ¬ ValuedModelMap.inK (CanonicalRV.encodedRv x ^ e * c y)) := by
    by_cases he : e = 0
    · exact SmallUniform.of_forall (fun x hx y hy hne => False.elim (hne he))
    · apply (nonzero_exponent_outside_residue D c hc e he).mono
      exact fun x hx y hy hh _ => hh
  have hs2 : SmallUniform D (fun x y => d ≠ 0 → b y ≠ 0 →
      ¬ ValuedModelMap.inK (CanonicalRV.encodedRv x ^ d * b y)) := by
    by_cases hd : d = 0
    · exact SmallUniform.of_forall (fun x hx y hy hne => False.elim (hne hd))
    · apply (nonzero_exponent_outside_residue D b hb d hd).mono
      exact fun x hx y hy hh _ => hh
  refine ⟨0,addCoefficient e d c b,hcoef,?_⟩
  apply ((hf.and hg).and (hs1.and hs2)).mono
  intro x hx y hy hh
  dsimp only
  simp only [zpow_zero,one_mul]
  rw [hh.1.1,hh.1.2]
  by_cases h1 : e ≠ 0 ∧ c y ≠ 0
  · rw [addCoefficient,if_pos (Or.inl h1)]
    exact (ValuedModelMap.addK_junk _ _ (Or.inl (hh.2.1 h1.1 h1.2))).trans zeroRV_eq
  · by_cases h2 : d ≠ 0 ∧ b y ≠ 0
    · rw [addCoefficient,if_pos (Or.inr h2)]
      exact (ValuedModelMap.addK_junk _ _ (Or.inr (hh.2.2 h2.1 h2.2))).trans zeroRV_eq
    · have heq : CanonicalRV.encodedRv x ^ e * c y = if e = 0 then c y else 0 := by
        by_cases he : e = 0
        · simp [he]
        · have hcy : c y = 0 := by
            by_contra hcy
            exact h1 ⟨he,hcy⟩
          simp only [he,if_false,hcy,mul_zero]
      have hdq : CanonicalRV.encodedRv x ^ d * b y = if d = 0 then b y else 0 := by
        by_cases hd : d = 0
        · simp [hd]
        · have hby : b y = 0 := by
            by_contra hby
            exact h2 ⟨hd,hby⟩
          simp only [hd,if_false,hby,mul_zero]
      rw [addCoefficient,if_neg (not_or_intro h1 h2),heq,hdq]

end SpecialTransformations.Section3.RVMonomial

/- Component: RVTermHomogeneity -/


set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.RVMonomial
open RVOperations MixedPolynomialSyntax
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {A : Set M} {m : ℕ}

noncomputable def termValue (p : Parameters A) (t : LRV.Term (Fin p.length ⊕ Fin (m+1)))
    (ht : TmSort p.sorts (contextSort (m := m)) t = some .rv)
    (x : VFType (M := M)) (ys : Fin m → CanonicalRV.RVSort M) : CanonicalRV.RVSort M :=
  ⟨t.realize (Sum.elim p.values (Fin.cons x.val (fun i => (ys i).val))),by
    have hvars : ∀ i, sortEval (contextSort (m := m) i)
        ((Fin.cons x.val (fun j => (ys j).val) : Fin (m+1) → M) i) := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact x.property
      · exact (ys j).property
    exact CanonicalStructure.term_sort hM p.sorts (contextSort (m := m)) p.values
      (Fin.cons x.val (fun i => (ys i).val)) p.sorted hvars t ht⟩

private theorem eval_fn0 {β : Type} (f : Fn 0) (ts : Fin 0 → LRV.Term β) (v : β → M) :
    (Term.func f ts).realize v = Structure.funMap (L := LRV) f Fin.elim0 := by
  change Structure.funMap (L := LRV) f (fun i => (ts i).realize v) = _
  congr 1
  funext i
  exact i.elim0

private theorem eval_fn1 {β : Type} (f : Fn 1) (ts : Fin 1 → LRV.Term β) (v : β → M) :
    (Term.func f ts).realize v = Structure.funMap (L := LRV) f ![(ts 0).realize v] := by
  change Structure.funMap (L := LRV) f (fun i => (ts i).realize v) = _
  congr 1
  funext i
  fin_cases i
  rfl

private theorem eval_fn2 {β : Type} (f : Fn 2) (ts : Fin 2 → LRV.Term β) (v : β → M) :
    (Term.func f ts).realize v = Structure.funMap (L := LRV) f ![(ts 0).realize v,(ts 1).realize v] := by
  change Structure.funMap (L := LRV) f (fun i => (ts i).realize v) = _
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Every well-sorted RV term is a homogeneous monomial in the small VF
variable with a uniformly bounded coefficient depending only on the RV box.
This is semantic; it does not assert the printed syntactic normal form2.4. -/
theorem term_homogeneous (p : Parameters A) (D : Set (Fin m → CanonicalRV.RVSort M))
    (hvars : ∀ i : Fin m, CoefficientBounded absoluteHom D (fun ys => ys i))
    (t : LRV.Term (Fin p.length ⊕ Fin (m+1)))
    (ht : TmSort p.sorts (contextSort (m := m)) t = some .rv) :
    Homogeneous D (termValue p t ht) := by
  induction t with
  | var i =>
    cases i with
    | inl i =>
      have hi : p.sorts i = .rv := Option.some.inj ht
      have hr : iRV (p.values i) := by
        have hh := p.sorted i
        rw [hi] at hh
        exact hh
      apply (homogeneous_const D (⟨p.values i,hr⟩ : CanonicalRV.RVSort M)).congr
      intro x ys
      rfl
    | inr i =>
      cases i using Fin.cases with
      | zero => cases ht
      | succ j =>
        apply (homogeneous_coefficient D (fun ys => ys j) (hvars j)).congr
        intro x ys
        rfl
  | func f ts ih =>
    obtain ⟨harg,hres⟩ := (tmSort_func_iff p.sorts (contextSort (m := m)) f ts).mp ht
    cases f with
    | vfZero => cases hres
    | vfOne => cases hres
    | vfAdd => cases hres
    | vfMul => cases hres
    | vfNeg => cases hres
    | rvZero =>
      apply (homogeneous_const D (0 : CanonicalRV.RVSort M)).congr
      intro x ys
      apply Subtype.ext
      change (0 : CanonicalRV.RVSort M).val = (Term.func Fn.rvZero ts).realize _
      rw [zero_val,eval_fn0]
      rfl
    | rvOne =>
      apply (homogeneous_const D (1 : CanonicalRV.RVSort M)).congr
      intro x ys
      apply Subtype.ext
      change (1 : CanonicalRV.RVSort M).val = (Term.func Fn.rvOne ts).realize _
      rw [one_val,eval_fn0]
      rfl
    | rvMul =>
      apply ((ih 0 (harg 0)).mul (ih 1 (harg 1))).congr
      intro x ys
      apply Subtype.ext
      change (termValue p (ts 0) (harg 0) x ys * termValue p (ts 1) (harg 1) x ys).val =
        (Term.func Fn.rvMul ts).realize _
      rw [mul_val,eval_fn2]
      rfl
    | rvInv =>
      apply (ih 0 (harg 0)).inv.congr
      intro x ys
      apply Subtype.ext
      change ((termValue p (ts 0) (harg 0) x ys)⁻¹).val = (Term.func Fn.rvInv ts).realize _
      rw [inv_val,eval_fn1]
      rfl
    | kAdd =>
      apply ((ih 0 (harg 0)).addK (ih 1 (harg 1))).congr
      intro x ys
      apply Subtype.ext
      change iKAdd ((ts 0).realize _) ((ts 1).realize _) = (Term.func Fn.kAdd ts).realize _
      rw [eval_fn2]
      rfl
    | kNeg =>
      apply (ih 0 (harg 0)).negK.congr
      intro x ys
      apply Subtype.ext
      change TrivCase.iKNeg ((ts 0).realize _) = (Term.func Fn.kNeg ts).realize _
      rw [eval_fn1]
      rfl
    | rvMap =>
      let E : Subfield (VFType (M := M)) := ⊤
      have hp (i : Fin p.length) (h : iVF (p.values i)) : (⟨p.values i,h⟩ : VFType (M := M)) ∈ E :=
        Set.mem_univ _
      let q := MixedPolynomialSyntax.toPolynomial p E hp (ts 0)
      apply (homogeneous_polynomial D (q.map E.subtype)).congr
      intro x ys
      apply Subtype.ext
      change iRv (((q.map E.subtype).eval x).val) = (Term.func Fn.rvMap ts).realize _
      rw [eval_fn1]
      change iRv (((q.map E.subtype).eval x).val) =
        iRv ((ts 0).realize (Sum.elim p.values (Fin.cons x.val (fun i => (ys i).val))))
      rw [MixedPolynomialSyntax.realizes p E hp (ts 0) (harg 0) x (fun i => (ys i).val)]
      simp only [Polynomial.eval_map,q]

end SpecialTransformations.Section3.RVMonomial

/- Component: MonomialEquality -/

set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.RVMonomial
open RVOperations
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def Independent {α : Type} (D : Set α) (R : VFType (M := M) → α → Prop) : Prop :=
  ∃ P : α → Prop, SmallUniform D (fun x y => R x y ↔ P y)

theorem independent_coefficient {α : Type} (D : Set α) (P : α → Prop) :
    Independent (M := M) D (fun _ y => P y) :=
  ⟨P,SmallUniform.of_forall (fun _ _ _ _ => Iff.rfl)⟩

theorem Independent.congr {α : Type} {D : Set α}
    {P Q : VFType (M := M) → α → Prop} (hp : Independent D P)
    (he : ∀ x y, P x y ↔ Q x y) : Independent D Q := by
  obtain ⟨p,hp⟩ := hp
  refine ⟨p,?_⟩
  apply hp.mono
  exact fun x hx y hy hh => (he x y).symm.trans hh

theorem Independent.imp {α : Type} {D : Set α}
    {P Q : VFType (M := M) → α → Prop} (hp : Independent D P) (hq : Independent D Q) :
    Independent D (fun x y => P x y → Q x y) := by
  obtain ⟨p,hp⟩ := hp
  obtain ⟨q,hq⟩ := hq
  refine ⟨fun y => p y → q y,?_⟩
  apply (hp.and hq).mono
  exact fun x hx y hy h => imp_congr h.1 h.2

theorem monomial_div {G : Type*} [CommGroupWithZero G]
    (x a b : G) (hx : x ≠ 0) (e d : ℤ) :
    x ^ (e-d) * (a/b) = (x^e*a)/(x^d*b) := by
  simp only [zpow_sub₀ hx,div_eq_mul_inv,mul_inv_rev]
  ac_rfl

theorem Homogeneous.equal_independent {α : Type} {D : Set α}
    {f g : VFType (M := M) → α → CanonicalRV.RVSort M}
    (hf : Homogeneous D f) (hg : Homogeneous D g) :
    Independent D (fun x y => f x y = g x y) := by
  obtain ⟨e,c,hc,hf⟩ := hf
  obtain ⟨d,b,hb,hg⟩ := hg
  by_cases hed : e = d
  · subst d
    refine ⟨fun y => c y = b y,?_⟩
    apply (hf.and hg).mono
    intro x hx y hy hh
    dsimp only
    rw [hh.1,hh.2]
    have hn := zpow_ne_zero e ((rv_ne_zero x).mpr hx)
    exact ⟨fun h => mul_left_cancel₀ hn h,fun h => congrArg (fun a => CanonicalRV.encodedRv x ^ e*a) h⟩
  · have hn : e-d ≠ 0 := by omega
    have hcb : CoefficientBounded absoluteHom D (fun y => c y/b y) := by
      simpa only [div_eq_mul_inv] using hc.mul hb.inv
    have hs := nonzero_exponent_outside_residue D (fun y => c y/b y) hcb (e-d) hn
    refine ⟨fun y => c y = 0 ∧ b y = 0,?_⟩
    apply ((hf.and hg).and hs).mono
    intro x hx y hy hh
    dsimp only
    rw [hh.1.1,hh.1.2]
    have hrv := (rv_ne_zero x).mpr hx
    constructor
    · intro heq
      by_cases hcy : c y = 0
      · rw [hcy,mul_zero] at heq
        exact ⟨hcy,(mul_eq_zero.mp heq.symm).resolve_left (zpow_ne_zero _ hrv)⟩
      · by_cases hby : b y = 0
        · rw [hby,mul_zero] at heq
          exact False.elim (hcy ((mul_eq_zero.mp heq).resolve_left (zpow_ne_zero _ hrv)))
        · have hratio : CanonicalRV.encodedRv x ^ (e-d) * (c y/b y) = 1 := by
            rw [monomial_div _ _ _ hrv,heq,div_self (mul_ne_zero (zpow_ne_zero _ hrv) hby)]
          have hnot := hh.2 (div_ne_zero hcy hby)
          apply False.elim
          apply hnot
          rw [hratio]
          exact (inK_iff _).mpr (Or.inr (map_one absoluteHom))
    · rintro ⟨hcy,hby⟩
      rw [hcy,hby,mul_zero,mul_zero]

theorem Homogeneous.units_independent {α : Type} {D : Set α}
    {f : VFType (M := M) → α → CanonicalRV.RVSort M} (hf : Homogeneous D f) :
    Independent D (fun x y => iUnits (f x y).val) := by
  obtain ⟨e,c,hc,hf⟩ := hf
  by_cases he : e = 0
  · subst e
    refine ⟨fun y => iUnits (c y).val,?_⟩
    apply hf.mono
    intro x hx y hy hh
    dsimp only
    rw [hh,zpow_zero,one_mul]
  · have hs := nonzero_exponent_outside_residue D c hc e he
    refine ⟨fun _ => False,?_⟩
    apply (hf.and hs).mono
    intro x hx y hy hh
    dsimp only
    rw [iff_false,hh.1]
    intro hu
    by_cases hcy : c y = 0
    · rw [hcy,mul_zero,zero_val] at hu
      exact ValuedModelMap.units_ne_zero hu rfl
    · exact hh.2 hcy (Or.inl hu)

end SpecialTransformations.Section3.RVMonomial

/- Component: MonomialOrder -/

set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.RVMonomial
open RVOperations
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem larger_exponent_smaller_absolute {α : Type} (D : Set α)
    (c b : α → CanonicalRV.RVSort M)
    (hc : CoefficientBounded absoluteHom D c) (hb : CoefficientBounded absoluteHom D b)
    (e d : ℤ) (hed : d < e) :
    SmallUniform D (fun x y => c y ≠ 0 → b y ≠ 0 →
      absoluteHom (CanonicalRV.encodedRv x ^ e*c y) <
        absoluteHom (CanonicalRV.encodedRv x ^ d*b y)) := by
  have hcb : CoefficientBounded absoluteHom D (fun y => c y/b y) := by
    simpa only [div_eq_mul_inv] using hc.mul hb.inv
  obtain ⟨r,hr⟩ := positive_exponent_bound absoluteHom D (fun y => c y/b y) hcb (e-d)
    (sub_pos.mpr hed)
  refine ⟨r,?_⟩
  intro x hx hs y hy hcy hby
  have hrv := (rv_ne_zero x).mpr hx
  have hv : 0 < absoluteHom (CanonicalRV.encodedRv x) :=
    pos_iff_ne_zero.mpr ((map_ne_zero absoluteHom).mpr hrv)
  have hquot : absoluteHom ((CanonicalRV.encodedRv x ^ e*c y)/
      (CanonicalRV.encodedRv x ^ d*b y)) < 1 := by
    rw [← monomial_div _ _ _ hrv,map_mul,map_zpow₀]
    apply hr _ hv ?_ y hy (div_ne_zero hcy hby)
    simpa only [absolute_rv] using hs
  have hden : 0 < absoluteHom (CanonicalRV.encodedRv x ^ d*b y) :=
    pos_iff_ne_zero.mpr ((map_ne_zero absoluteHom).mpr (mul_ne_zero (zpow_ne_zero _ hrv) hby))
  apply (div_lt_one₀ hden).mp
  simpa only [map_div₀] using hquot

theorem Homogeneous.absolute_le_independent {α : Type} {D : Set α}
    {f g : VFType (M := M) → α → CanonicalRV.RVSort M}
    (hf : Homogeneous D f) (hg : Homogeneous D g) :
    Independent D (fun x y => absoluteHom (f x y) ≤ absoluteHom (g x y)) := by
  obtain ⟨e,c,hc,hf⟩ := hf
  obtain ⟨d,b,hb,hg⟩ := hg
  by_cases hed : e = d
  · subst d
    refine ⟨fun y => absoluteHom (c y) ≤ absoluteHom (b y),?_⟩
    apply (hf.and hg).mono
    intro x hx y hy hh
    dsimp only
    rw [hh.1,hh.2,map_mul,map_mul,map_zpow₀]
    have hv : 0 < absoluteHom (CanonicalRV.encodedRv x) :=
      pos_iff_ne_zero.mpr ((map_ne_zero absoluteHom).mpr ((rv_ne_zero x).mpr hx))
    exact mul_le_mul_iff_right₀ (zpow_pos hv e)
  · rcases lt_or_gt_of_ne hed with hed | hed
    · have hs := larger_exponent_smaller_absolute D b c hb hc d e hed
      refine ⟨fun y => c y = 0,?_⟩
      apply ((hf.and hg).and hs).mono
      intro x hx y hy hh
      dsimp only
      rw [hh.1.1,hh.1.2]
      by_cases hcy : c y = 0
      · exact iff_of_true (by rw [hcy,mul_zero,map_zero]; exact zero_le) hcy
      · by_cases hby : b y = 0
        · have hn : 0 < absoluteHom (CanonicalRV.encodedRv x ^ e*c y) :=
            pos_iff_ne_zero.mpr ((map_ne_zero absoluteHom).mpr
              (mul_ne_zero (zpow_ne_zero _ ((rv_ne_zero x).mpr hx)) hcy))
          exact iff_of_false (by rw [hby,mul_zero,map_zero]; exact not_le_of_gt hn) hcy
        · exact iff_of_false (not_le_of_gt (hh.2 hby hcy)) hcy
    · have hs := larger_exponent_smaller_absolute D c b hc hb e d hed
      refine ⟨fun y => c y = 0 ∨ b y ≠ 0,?_⟩
      apply ((hf.and hg).and hs).mono
      intro x hx y hy hh
      dsimp only
      rw [hh.1.1,hh.1.2]
      by_cases hcy : c y = 0
      · exact iff_of_true (by rw [hcy,mul_zero,map_zero]; exact zero_le) (Or.inl hcy)
      · by_cases hby : b y = 0
        · have hn : 0 < absoluteHom (CanonicalRV.encodedRv x ^ e*c y) :=
            pos_iff_ne_zero.mpr ((map_ne_zero absoluteHom).mpr
              (mul_ne_zero (zpow_ne_zero _ ((rv_ne_zero x).mpr hx)) hcy))
          exact iff_of_false (by rw [hby,mul_zero,map_zero]; exact not_le_of_gt hn)
            (not_or_intro hcy (not_not.mpr hby))
        · exact iff_of_true (hh.2 hcy hby).le (Or.inr hby)

theorem raw_le_iff_absolute (a b : CanonicalRV.RVSort M) :
    iLe a.val b.val ↔ absoluteHom b ≤ absoluteHom a :=
  Values.valueEquiv_rv_le Values.presentationValuation Values.presentation_compatible a b

theorem Homogeneous.le_independent {α : Type} {D : Set α}
    {f g : VFType (M := M) → α → CanonicalRV.RVSort M}
    (hf : Homogeneous D f) (hg : Homogeneous D g) :
    Independent D (fun x y => iLe (f x y).val (g x y).val) := by
  apply (hg.absolute_le_independent hf).congr
  exact fun x y => (raw_le_iff_absolute _ _).symm

end SpecialTransformations.Section3.RVMonomial

/- Component: QFSmallConstancy -/



set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.RVMonomial
open RVOperations MixedPolynomialSyntax
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {A : Set M} {m : ℕ}

private theorem assignment_sorted (x : VFType (M := M)) (ys : Fin m → CanonicalRV.RVSort M) :
    ∀ i, sortEval (contextSort (m := m) i)
      ((Fin.cons x.val (fun j => (ys j).val) : Fin (m+1) → M) i) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact x.property
  · exact (ys j).property

private theorem realize_rel1 (p : Parameters A) (R : Rel 1)
    (ts : Fin 1 → LRV.Term (Fin p.length ⊕ Fin (m+1)))
    (x : VFType (M := M)) (ys : Fin m → CanonicalRV.RVSort M) :
    (BoundedFormula.rel R ts).Realize p.values (Fin.cons x.val (fun j => (ys j).val)) ↔
      Structure.RelMap (L := LRV) R
        ![(ts 0).realize (Sum.elim p.values (Fin.cons x.val (fun j => (ys j).val)))] := by
  change Structure.RelMap (L := LRV) R _ ↔ _
  have he : (fun i => (ts i).realize (Sum.elim p.values (Fin.cons x.val (fun j => (ys j).val)))) =
      (![(ts 0).realize (Sum.elim p.values (Fin.cons x.val (fun j => (ys j).val)))] : Fin 1 → M) := by
    funext i
    fin_cases i
    rfl
  rw [he]

theorem rv_equal_independent (p : Parameters A) (D : Set (Fin m → CanonicalRV.RVSort M))
    (hvars : ∀ i : Fin m, CoefficientBounded absoluteHom D (fun ys => ys i))
    (t u : LRV.Term (Fin p.length ⊕ Fin (m+1)))
    (ht : TmSort p.sorts (contextSort (m := m)) t = some .rv)
    (hu : TmSort p.sorts (contextSort (m := m)) u = some .rv) :
    Independent D (fun x ys => t.realize (Sum.elim p.values (Fin.cons x.val (fun j => (ys j).val))) =
      u.realize (Sum.elim p.values (Fin.cons x.val (fun j => (ys j).val)))) := by
  apply ((term_homogeneous p D hvars t ht).equal_independent
    (term_homogeneous p D hvars u hu)).congr
  exact fun x ys => Subtype.ext_iff

/-- Quantifier-free truth is uniformly independent of a sufficiently
small nonzero VF coordinate on any fixed bounded RV box. This uses semantic
term homogeneity, without assuming Definition2.4's syntactic normal form. -/
theorem qf_independent (p : Parameters A) (D : Set (Fin m → CanonicalRV.RVSort M))
    (hvars : ∀ i : Fin m, CoefficientBounded absoluteHom D (fun ys => ys i))
    (φ : LRV.BoundedFormula (Fin p.length) (m+1)) (hqf : φ.IsQF)
    (hws : WellSorted p.sorts (contextSort (m := m)) φ) :
    Independent D (fun x ys => φ.Realize p.values (Fin.cons x.val (fun j => (ys j).val))) := by
  induction hqf with
  | falsum => exact independent_coefficient D (fun _ => False)
  | of_isAtomic ha =>
    cases ha with
    | equal t u =>
      cases hws with
      | @equal _ _ _ _ σ ht hu =>
        cases σ with
        | rv => exact rv_equal_independent p D hvars t u ht hu
        | vf =>
          let a : LRV.Term (Fin p.length ⊕ Fin (m+1)) :=
            .func Fn.rvMap ![.func Fn.vfAdd ![t,.func Fn.vfNeg ![u] ] ]
          let b : LRV.Term (Fin p.length ⊕ Fin (m+1)) := .func Fn.rvZero Fin.elim0
          have hta : TmSort p.sorts (contextSort (m := m)) a = some .rv := by
            apply tmSort_func p.sorts (contextSort (m := m)) Fn.rvMap
            intro i; fin_cases i
            apply tmSort_func p.sorts (contextSort (m := m)) Fn.vfAdd
            intro j; fin_cases j
            · exact ht
            · apply tmSort_func p.sorts (contextSort (m := m)) Fn.vfNeg
              intro k; fin_cases k; exact hu
          have htb : TmSort p.sorts (contextSort (m := m)) b = some .rv := by
            apply tmSort_func p.sorts (contextSort (m := m)) Fn.rvZero
            intro i; exact i.elim0
          apply (rv_equal_independent p D hvars a b hta htb).congr
          intro x ys
          exact (realize_rvEquality p.sorts (contextSort (m := m)) p.values
            (Fin.cons x.val (fun j => (ys j).val)) p.sorted (assignment_sorted x ys) t u ht hu).symm
    | rel R ts =>
      cases hws with
      | rel _ _ _ hts =>
        cases R with
        | memUnits =>
          apply ((term_homogeneous p D hvars (ts 0) (hts 0)).units_independent).congr
          exact fun x ys => (realize_rel1 p Rel.memUnits ts x ys).symm
        | rvLe =>
          apply ((term_homogeneous p D hvars (ts 0) (hts 0)).le_independent
            (term_homogeneous p D hvars (ts 1) (hts 1))).congr
          intro x ys
          change iLe ((ts 0).realize _) ((ts 1).realize _) ↔ Structure.RelMap (L := LRV) Rel.rvLe _
          have he : (fun i => (ts i).realize (Sum.elim p.values (Fin.cons x.val (fun j => (ys j).val)))) =
              (![(ts 0).realize (Sum.elim p.values (Fin.cons x.val (fun j => (ys j).val))),
                 (ts 1).realize (Sum.elim p.values (Fin.cons x.val (fun j => (ys j).val)))] : Fin 2 → M) := by
            funext i; fin_cases i <;> rfl
          rw [he]
          rfl
        | memVF =>
          refine ⟨fun _ => True,SmallUniform.of_forall ?_⟩
          intro x hx ys hy
          change Structure.RelMap (L := LRV) Rel.memVF
            (fun i => (ts i).realize (Sum.elim p.values (Fin.cons x.val (fun j => (ys j).val)))) ↔ True
          have he : (fun i => (ts i).realize (Sum.elim p.values (Fin.cons x.val (fun j => (ys j).val)))) =
              (![(ts 0).realize (Sum.elim p.values (Fin.cons x.val (fun j => (ys j).val)))] : Fin 1 → M) := by
            funext i; fin_cases i; rfl
          rw [he]
          apply iff_true_intro
          exact CanonicalStructure.term_sort hM p.sorts (contextSort (m := m)) p.values
            (Fin.cons x.val (fun j => (ys j).val)) p.sorted (assignment_sorted x ys) (ts 0) (hts 0)
        | memRV =>
          refine ⟨fun _ => True,SmallUniform.of_forall ?_⟩
          intro x hx ys hy
          change Structure.RelMap (L := LRV) Rel.memRV
            (fun i => (ts i).realize (Sum.elim p.values (Fin.cons x.val (fun j => (ys j).val)))) ↔ True
          have he : (fun i => (ts i).realize (Sum.elim p.values (Fin.cons x.val (fun j => (ys j).val)))) =
              (![(ts 0).realize (Sum.elim p.values (Fin.cons x.val (fun j => (ys j).val)))] : Fin 1 → M) := by
            funext i; fin_cases i; rfl
          rw [he]
          apply iff_true_intro
          exact CanonicalStructure.term_sort hM p.sorts (contextSort (m := m)) p.values
            (Fin.cons x.val (fun j => (ys j).val)) p.sorted (assignment_sorted x ys) (ts 0) (hts 0)
  | @imp φ ψ hφ hψ ihφ ihψ =>
    cases hws with
    | imp _ hwφ hwψ => exact (ihφ hwφ).imp (ihψ hwψ)

end SpecialTransformations.Section3.RVMonomial

/- Component: SmallFamilyConstancy -/



set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3
namespace RVMonomial
open RVOperations MixedPolynomialSyntax
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {m : ℕ}

/-- Full sorted graph on the punctured VF domain. Its value at VF zero
is irrelevant and contributes no points to the defining relation. -/
def puncturedGraph (f : VFType (M := M) → Set (Fin m → CanonicalRV.RVSort M)) :
    Set (Fin (m+1) → M) :=
  {z | ∃ x : VFType (M := M), x ≠ 0 ∧ ∃ ys : Fin m → CanonicalRV.RVSort M,
    Fin.cons x.val (fun i => (ys i).val) = z ∧ ys ∈ f x}

theorem mem_puncturedGraph (f : VFType (M := M) → Set (Fin m → CanonicalRV.RVSort M))
    (x : VFType (M := M)) (ys : Fin m → CanonicalRV.RVSort M) :
    Fin.cons x.val (fun i => (ys i).val) ∈ puncturedGraph f ↔ x ≠ 0 ∧ ys ∈ f x := by
  constructor
  · rintro ⟨z,hz,ws,he,hws⟩
    have hzx : z = x := Subtype.ext (congrFun he 0)
    have hwy : ws = ys := funext (fun i => Subtype.ext (congrFun he i.succ))
    subst z
    subst ws
    exact ⟨hz,hws⟩
  · rintro ⟨hx,hy⟩
    exact ⟨x,hx,ys,rfl,hy⟩

/-- The absolute-value version of3.17. Only the nonzero output coordinates
need bounds, so absorbing-zero RV coordinates and empty output tuples work. -/
theorem lemma_3_17_absolute (S : Set M)
    (f : VFType (M := M) → Set (Fin m → CanonicalRV.RVSort M))
    (hdef : DefinableOver S (contextSort (m := m)) (puncturedGraph f))
    (lo hi : (AbsoluteValueGroup M)ˣ)
    (hb : ∀ x : VFType (M := M), x ≠ 0 → ∀ ys ∈ f x, ∀ i, ys i ≠ 0 →
      (lo : AbsoluteValueGroup M) ≤ absoluteHom (ys i) ∧ absoluteHom (ys i) ≤ hi) :
    ∃ r : (AbsoluteValueGroup M)ˣ, ∀ x z : VFType (M := M), x ≠ 0 → z ≠ 0 →
      Values.presentationValuation.restrict x < r.val → Values.presentationValuation.restrict z < r.val →
        f x = f z := by
  obtain ⟨p,φ,hφ,hgraph⟩ := hdef
  obtain ⟨ψ,hq,hw,heq⟩ := theorem_2_3_quantifier_elimination
    (Fin p.length) p.sorts (m+1) (contextSort (m := m)) φ hφ
  let D : Set (Fin m → CanonicalRV.RVSort M) :=
    {ys | ∀ i, ys i ≠ 0 → (lo : AbsoluteValueGroup M) ≤ absoluteHom (ys i) ∧ absoluteHom (ys i) ≤ hi}
  have hvars (i : Fin m) : CoefficientBounded absoluteHom D (fun ys => ys i) :=
    ⟨lo,hi,fun ys hy hn => hy i hn⟩
  have hψ (x : VFType (M := M)) (ys : Fin m → CanonicalRV.RVSort M) (hx : x ≠ 0) :
      ψ.Realize p.values (Fin.cons x.val (fun i => (ys i).val)) ↔ ys ∈ f x := by
    have hs : ∀ i, sortEval (contextSort (m := m) i)
        ((Fin.cons x.val (fun j => (ys j).val) : Fin (m+1) → M) i) := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact x.property
      · exact (ys j).property
    have hg := Set.ext_iff.mp hgraph (Fin.cons x.val (fun i => (ys i).val))
    exact (heq M hM p.values _ p.sorted hs).symm.trans
      ((and_iff_right hs).symm.trans (hg.symm.trans
        ((mem_puncturedGraph f x ys).trans (and_iff_right hx))))
  obtain ⟨P,r,hr⟩ := qf_independent p D hvars ψ hq hw
  refine ⟨r,?_⟩
  intro x z hx hz hsx hsz
  ext ys
  by_cases hy : ys ∈ D
  · exact (hψ x ys hx).symm.trans ((hr x hx hsx ys hy).trans
      ((hr z hz hsz ys hy).symm.trans (hψ z ys hz)))
  · exact iff_of_false (fun h => hy (hb x hx ys h)) (fun h => hy (hb z hz ys h))

end RVMonomial

open RVMonomial RVOperations MixedPolynomialSyntax
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {m : ℕ}

/-- Lemma3.17 with actual Gamma bounds and thresholds in the paper's
reversed value order. Every larger threshold also gives constancy. -/
theorem lemma_3_17 (S : Set M)
    (f : VFType (M := M) → Set (Fin m → CanonicalRV.RVSort M))
    (hdef : DefinableOver S (contextSort (m := m)) (puncturedGraph f))
    (lo hi : Values.Gamma (M := M))
    (hb : ∀ x : VFType (M := M), x ≠ 0 → ∀ ys ∈ f x, ∀ i,
      (ys i).val ≠ iRVZero → lo.val ≤ Values.vrv (ys i) ∧ Values.vrv (ys i) ≤ hi.val) :
    ∃ δ : Values.Gamma (M := M), ∀ ε : Values.Gamma (M := M), δ ≤ ε →
      ∀ x z : VFType (M := M), x ≠ 0 → z ≠ 0 →
        ε.val < Values.vfValueHom x → ε.val < Values.vfValueHom z → f x = f z := by
  let v := Values.presentationValuation (M := M)
  let hv := Values.presentation_compatible (M := M)
  let e := Values.gammaUnitsEquiv v hv
  have hba : ∀ x : VFType (M := M), x ≠ 0 → ∀ ys ∈ f x, ∀ i, ys i ≠ 0 →
      ((e hi : (AbsoluteValueGroup M)ˣ) : AbsoluteValueGroup M) ≤ absoluteHom (ys i) ∧
        absoluteHom (ys i) ≤ (e lo : (AbsoluteValueGroup M)ˣ) := by
    intro x hx ys hy i hn
    have hn' : (ys i).val ≠ iRVZero := fun he => hn (Subtype.ext (he.trans zero_val.symm))
    have hh := hb x hx ys hy i hn'
    exact ⟨hh.2,hh.1⟩
  obtain ⟨r,hr⟩ := lemma_3_17_absolute S f hdef (e hi) (e lo) hba
  let δ := e.symm r
  have hδ : Values.valueEquiv v hv δ.val = (r : AbsoluteValueGroup M) :=
    congrArg Units.val (e.apply_symm_apply r)
  refine ⟨δ,?_⟩
  intro ε hδε x z hx hz hsx hsz
  have hδε' : δ.val ≤ ε.val := hδε
  have hsmall (w : VFType (M := M)) (hw : ε.val < Values.vfValueHom w) : v.restrict w < r.val := by
    have hh := lt_of_le_of_lt hδε' hw
    change Values.valueEquiv v hv (Values.vfValueHom w) < Values.valueEquiv v hv δ.val at hh
    rw [hδ] at hh
    change Values.valueEquiv v hv (Values.vrv (CanonicalRV.encodedRv w)) < (r : AbsoluteValueGroup M) at hh
    rw [Values.valueEquiv_apply_vf] at hh
    exact hh
  exact hr x z hx hz (hsmall x hsx) (hsmall z hsz)

namespace GammaParameters
/-- Full Gamma-base version: temporary real names occur only inside the
proof of definability, not in the constancy statement or its hypotheses. -/
theorem lemma_3_17_gamma_base (B : Base (M := M))
    (f : VFType (M := M) → Set (Fin m → CanonicalRV.RVSort M))
    (hdef : DefinableOverBase B (contextSort (m := m)) (puncturedGraph f))
    (lo hi : Values.Gamma (M := M))
    (hb : ∀ x : VFType (M := M), x ≠ 0 → ∀ ys ∈ f x, ∀ i,
      (ys i).val ≠ iRVZero → lo.val ≤ Values.vrv (ys i) ∧ Values.vrv (ys i) ≤ hi.val) :
    ∃ δ : Values.Gamma (M := M), ∀ ε : Values.Gamma (M := M), δ ≤ ε →
      ∀ x z : VFType (M := M), x ≠ 0 → z ≠ 0 →
        ε.val < Values.vfValueHom x → ε.val < Values.vfValueHom z → f x = f z := by
  obtain ⟨k,t,hd⟩ := hdef.specialize
  exact lemma_3_17 (B.real ∪ Set.range (rawTuple t)) f hd lo hi hb
end GammaParameters
end SpecialTransformations.Section3
