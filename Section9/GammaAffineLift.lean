import Section9.AffineLift
import Section9.AffineTailHeadFormula
import Section9.GammaRawRelations
import Section9.GammaLiftGluing

/-! Gamma counterpart of `exists_affineLift_of_headLift`. The raw theorem
determines the affine lift by an explicit formula in the head lift `F`, the
representatives `a b`, the scalars `D c` and the tail coordinates; the
formula is a real relation (`affineTailHeadCodes`). Hence the affine lift has
a Gamma graph whenever its inputs do. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput
  gammaPointCode gammaPointSort vfAt)

namespace SpecialTransformations.Section9.GammaLift

variable {M Γ : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : Base (M := M)}
variable [LinearOrderedCommGroupWithZero Γ]
local notation "VF" => VFType (M := M)

/-- A VF-valued map on a mixed domain with a Gamma graph. -/
def VFMapGamma {S : Set M} {n a m : ℕ} {A : DefSet (rawMixedSpace (M := M) n a) S}
    (f : Map A (DefSet.univ (rawVFSpace (M := M) m) S)) (B : Base (M := M)) : Prop :=
  GammaGraphDefinable B (fun (p : Point (M := M) n a) (z : Point (M := M) m 0) =>
    ∃ x : A, x.val = p ∧ (f x).val = z.1)

/-- Pairing of two Gamma relations into a concatenated point. -/
theorem gamma_pair_graph {n m u w u' w' : ℕ}
    {r : Point (M := M) n m → Point (M := M) u w → Prop}
    {s : Point (M := M) n m → Point (M := M) u' w' → Prop}
    (hr : GammaGraphDefinable B r) (hs : GammaGraphDefinable B s) :
    GammaGraphDefinable B (fun p (y : Point (M := M) (u + u') (w + w')) =>
      r p (y.1 ∘ Fin.castAdd u', y.2 ∘ Fin.castAdd w') ∧ s p (y.1 ∘ Fin.natAdd u, y.2 ∘ Fin.natAdd w)) := by
  have L := gammaLogicInput B
  have h₁ := L.comp_graph hr (L.swap_graph (gamma_coordinate_graph (B := B) (n := u + u') (m := w + w')
    (Fin.castAdd u') (Fin.castAdd w')))
  have h₂ := L.comp_graph hs (L.swap_graph (gamma_coordinate_graph (B := B) (n := u + u') (m := w + w')
    (Fin.natAdd u) (Fin.natAdd w)))
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr
    (SpecialTransformations.Section5.GammaGraphDefinable.inter h₁ h₂)
  intro p y
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, ⟨z', hz', rfl⟩⟩
    exact ⟨hz, hz'⟩
  · rintro ⟨hz, hz'⟩
    exact ⟨⟨_, hz, rfl⟩, ⟨_, hz', rfl⟩⟩

variable (m : ℕ)

/-- The packed input point of the affine tail formula: `a b x D c`. -/
abbrev AffineInput := Point (M := M) ((((m + m) + m) + 1) + 1) ((((0 + 0) + 0) + 0) + 0)

variable {m}

def affA (w : AffineInput (M := M) m) : Fin m → VF := fun i =>
  w.1 (Fin.castAdd 1 (Fin.castAdd 1 (Fin.castAdd m (Fin.castAdd m i))))
def affB (w : AffineInput (M := M) m) : Fin m → VF := fun i =>
  w.1 (Fin.castAdd 1 (Fin.castAdd 1 (Fin.castAdd m (Fin.natAdd m i))))
def affX (w : AffineInput (M := M) m) : Fin m → VF := fun i =>
  w.1 (Fin.castAdd 1 (Fin.castAdd 1 (Fin.natAdd (m + m) i)))
def affD (w : AffineInput (M := M) m) : VF := w.1 (Fin.castAdd 1 (Fin.natAdd ((m + m) + m) 0))
def affC (w : AffineInput (M := M) m) : VF := w.1 (Fin.natAdd (((m + m) + m) + 1) 0)

/-- The affine tail formula is a real relation. -/
theorem gamma_affine_tail_relation (hc : CanonicalStructure.IsCanonical (M := M)) (j : Fin m) :
    GammaGraphDefinable B (fun (w : AffineInput (M := M) m) (y : Point (M := M) m 0) =>
      (fun i => (affineHeadInputs (affA w) (affB w) (affX w) y.1 (affD w) (affC w) i).val) ∈
        affineTailHeadCodes j) := by
  let K := (((m + m) + m) + 1) + 1
  let R := (((0 + 0) + 0) + 0) + 0
  let σ : AffineHeadCode m → Fin ((K + R) + (m + 0)) := fun i =>
    match i with
    | .inl (k, i) => (![Fin.castAdd (m + 0) (Fin.castAdd R (Fin.castAdd 1 (Fin.castAdd 1 (Fin.castAdd m (Fin.castAdd m i))))),
        Fin.castAdd (m + 0) (Fin.castAdd R (Fin.castAdd 1 (Fin.castAdd 1 (Fin.castAdd m (Fin.natAdd m i))))),
        Fin.castAdd (m + 0) (Fin.castAdd R (Fin.castAdd 1 (Fin.castAdd 1 (Fin.natAdd (m + m) i)))),
        Fin.natAdd (K + R) (Fin.castAdd 0 i)] : Fin 4 → Fin ((K + R) + (m + 0))) k
    | .inr k => (![Fin.castAdd (m + 0) (Fin.castAdd R (Fin.castAdd 1 (Fin.natAdd ((m + m) + m) 0))),
        Fin.castAdd (m + 0) (Fin.castAdd R (Fin.natAdd (((m + m) + m) + 1) 0))] :
        Fin 2 → Fin ((K + R) + (m + 0))) k
  apply gamma_graph_of_raw hc _ {z | z ∘ σ ∈ affineTailHeadCodes j}
    ((affineTailHeadCodes_definable B.real j).preimage_comp σ)
  intro w y
  change _ ↔ Fin.append (gammaPointCode w) (gammaPointCode y) ∘ σ ∈ affineTailHeadCodes j
  apply Iff.of_eq
  congr 1
  funext i
  rcases i with ⟨k, i⟩ | k
  · fin_cases k
    · simp [σ, affineHeadInputs, affA, affB, affX, gammaPointCode, vfAt, Fin.append_left, Fin.append_right]
    · simp [σ, affineHeadInputs, affA, affB, affX, gammaPointCode, vfAt, Fin.append_left, Fin.append_right]
    · simp [σ, affineHeadInputs, affA, affB, affX, gammaPointCode, vfAt, Fin.append_left, Fin.append_right]
    · change (y.1 i).val = Fin.append (gammaPointCode w) (gammaPointCode y) (Fin.natAdd (K + R) (Fin.castAdd 0 i))
      rw [Fin.append_right]
      unfold gammaPointCode
      rw [Fin.append_left]
      rfl
  · fin_cases k <;>
      simp [σ, affineHeadInputs, affD, affC, gammaPointCode, vfAt, Fin.append_left, Fin.append_right]

theorem fin_append_comp_castAdd {α : Type*} {n m : ℕ} (a : Fin n → α) (b : Fin m → α) :
    Fin.append a b ∘ Fin.castAdd m = a := funext (Fin.append_left a b)

theorem fin_append_comp_natAdd {α : Type*} {n m : ℕ} (a : Fin n → α) (b : Fin m → α) :
    Fin.append a b ∘ Fin.natAdd n = b := funext (Fin.append_right a b)

theorem fin_append_castAdd_natAdd {α : Type*} {n m : ℕ} (y : Fin (n + m) → α) :
    Fin.append (y ∘ Fin.castAdd m) (y ∘ Fin.natAdd n) = y := by
  funext i
  cases i using Fin.addCases <;> simp

variable {k : ℕ}

theorem gamma_affineLift_of_headLift (hc : CanonicalStructure.IsCanonical (M := M))
    (v : Valuation VF Γ) (hv : ∀ a b : VF, VFValued.predV a b ↔ v a ≤ v b)
    {S : Set M} (U V : RVFiniteObject (M := M) S (k + m))
    (hU : (rvHeadVolume U.obj (productLeft k m)).FiniteFibres)
    (hV : (rvHeadVolume V.obj (productLeft k m)).FiniteFibres)
    (hUΓ : RVMapGamma U.obj.volume B)
    (F : Map (rvLift (rvFiniteHead U (productLeft k m) hU).obj)
      (rvLift (rvFiniteHead V (productLeft k m) hV).obj)) (hF : Function.Bijective F)
    (hFΓ : MixedMapGamma F B)
    (a b : Map (rvLift (rvFiniteHead U (productLeft k m) hU).obj)
      (DefSet.univ (rawVFSpace (M := M) m) S))
    (D c : Map (rvLift (rvFiniteHead U (productLeft k m) hU).obj)
      (DefSet.univ (rawVFSpace (M := M) 1) S)) (j : Fin m)
    (haΓ : VFMapGamma a B) (hbΓ : VFMapGamma b B) (hDΓ : VFMapGamma D B) (hcΓ : VFMapGamma c B)
    (ha : ∀ p i, (a p).val i ≠ 0) (hb : ∀ p i, (b p).val i ≠ 0)
    (haRV : ∀ p, tupleRV (a p).val = U.obj.value
      (liftLabelMap (rvFiniteHead U (productLeft k m) hU).obj p) ∘ productRight k m)
    (hbRV : ∀ p, tupleRV (b p).val = V.obj.value
      (liftLabelMap (rvFiniteHead V (productLeft k m) hV).obj (F p)) ∘ productRight k m) :
    ∃ G : Map (rvLift U.obj) (rvLift V.obj), Function.Bijective G ∧ MixedMapGamma G B ∧
      ∀ p : rvLift U.obj,
        let x := rvLiftHeadSelect U (productLeft k m) hU p
        (G p).val = (productTuple (F x).val.1
          (affineTail (a x).val (b x).val
            (affineTailSlopesForHead v (a x).val (b x).val j ((D x).val 0) ((c x).val 0))
            (p.val.1 ∘ productRight k m)), (F x).val.2) := by
  obtain ⟨G, hG, hform⟩ := exists_affineLift_of_headLift v hv U V hU hV F hF a b D c j ha hb haRV hbRV
  refine ⟨G, hG, ?_, hform⟩
  have L := gammaLogicInput B
  let l : Fin k → Fin (k + m) := productLeft k m
  let r : Fin m → Fin (k + m) := productRight k m
  let U₁ := (rvFiniteHead U (productLeft k m) hU).obj
  let hs := rvLiftHeadSelect U (productLeft k m) hU
  have Hs := L.restrict_graph (lift_gamma U.obj hUΓ)
    (gamma_coordinate_graph (B := B) (n := k + m) (m := U.obj.arity) (u := k) (w := U.obj.arity) l id)
  -- composition with head selection, for any map on the head lift
  have hcomp : ∀ {u w : ℕ} (g : rvLift U₁ → Point (M := M) u w) (p : Point (M := M) (k + m) U.obj.arity)
      (z : Point (M := M) u w),
      (∃ x', (p ∈ (rvLift U.obj).carrier ∧ x' = (p.1 ∘ l, p.2 ∘ id)) ∧
        ∃ y : rvLift U₁, y.val = x' ∧ g y = z) ↔
      ∃ x : rvLift U.obj, x.val = p ∧ g (hs x) = z := by
    intro u w g p z
    constructor
    · rintro ⟨x', ⟨hp, rfl⟩, y, hy, hz⟩
      refine ⟨⟨p, hp⟩, rfl, ?_⟩
      have : hs ⟨p, hp⟩ = y := Subtype.ext (by rw [hy]; rfl)
      rw [this]
      exact hz
    · rintro ⟨x, rfl, hz⟩
      exact ⟨_, ⟨x.property, rfl⟩, hs x, rfl, hz⟩
  have hvf : ∀ {u : ℕ} (f : Map (rvLift U₁) (DefSet.univ (rawVFSpace (M := M) u) S)) (y : rvLift U₁)
      (z : Point (M := M) u 0), (f y).val = z.1 ↔ (((f y).val, Fin.elim0) : Point (M := M) u 0) = z := by
    intro u f y z
    constructor
    · intro h
      exact Prod.ext h (funext (fun i => Fin.elim0 i))
    · intro h
      exact congrArg Prod.fst h
  have Fp := L.comp_graph Hs hFΓ
  have Ap := L.comp_graph Hs haΓ
  have Bp := L.comp_graph Hs hbΓ
  have Dp := L.comp_graph Hs hDΓ
  have Cp := L.comp_graph Hs hcΓ
  have Tl := gamma_coordinate_graph (B := B) (n := k + m) (m := U.obj.arity) (u := m) (w := 0) r Fin.elim0
  have W := gamma_pair_graph (gamma_pair_graph (gamma_pair_graph (gamma_pair_graph Ap Bp) Tl) Dp) Cp
  have Tp := L.comp_graph W (gamma_affine_tail_relation (B := B) hc j)
  have P := gamma_pair_graph Fp Tp
  have Fin' := L.comp_graph P (gamma_coordinate_graph (B := B) (n := k + m) (m := V.obj.arity + 0)
    (u := k + m) (w := V.obj.arity) id (Fin.castAdd 0))
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr Fin'
  intro p q
  constructor
  · rintro ⟨y, ⟨hFy, w, hW, hΨ⟩, rfl⟩
    obtain ⟨x, rfl, hFx⟩ := (hcomp (fun t => (F t).val) _ _).mp hFy
    obtain ⟨⟨⟨⟨hA, hB⟩, hT⟩, hD⟩, hC⟩ := hW
    obtain ⟨xa, hxa, hA'⟩ := (hcomp (fun t => (((a t).val, Fin.elim0) : Point (M := M) m 0)) _ _).mp
      (by obtain ⟨x', hx', y', hy', h⟩ := hA; exact ⟨x', hx', y', hy', (hvf a y' _).mp h⟩)
    obtain ⟨xb, hxb, hB'⟩ := (hcomp (fun t => (((b t).val, Fin.elim0) : Point (M := M) m 0)) _ _).mp
      (by obtain ⟨x', hx', y', hy', h⟩ := hB; exact ⟨x', hx', y', hy', (hvf b y' _).mp h⟩)
    obtain ⟨xd, hxd, hD'⟩ := (hcomp (fun t => (((D t).val, Fin.elim0) : Point (M := M) 1 0)) _ _).mp
      (by obtain ⟨x', hx', y', hy', h⟩ := hD; exact ⟨x', hx', y', hy', (hvf D y' _).mp h⟩)
    obtain ⟨xc, hxc, hC'⟩ := (hcomp (fun t => (((c t).val, Fin.elim0) : Point (M := M) 1 0)) _ _).mp
      (by obtain ⟨x', hx', y', hy', h⟩ := hC; exact ⟨x', hx', y', hy', (hvf c y' _).mp h⟩)
    have ea : x = xa := (Subtype.ext hxa).symm
    have eb : x = xb := (Subtype.ext hxb).symm
    have ed : x = xd := (Subtype.ext hxd).symm
    have ec : x = xc := (Subtype.ext hxc).symm
    subst ea eb ed ec
    refine ⟨x, rfl, ?_⟩
    have hAw : affA w = (a (hs x)).val := by
      have := congrArg Prod.fst hA'
      funext i
      exact (congrFun this i).symm
    have hBw : affB w = (b (hs x)).val := by
      have := congrArg Prod.fst hB'
      funext i
      exact (congrFun this i).symm
    have hXw : affX w = x.val.1 ∘ r := by
      have := congrArg Prod.fst hT
      funext i
      exact congrFun this i
    have hDw : affD w = (D (hs x)).val 0 := by
      have := congrArg Prod.fst hD'
      exact (congrFun this 0).symm
    have hCw : affC w = (c (hs x)).val 0 := by
      have := congrArg Prod.fst hC'
      exact (congrFun this 0).symm
    rw [hAw, hBw, hXw, hDw, hCw] at hΨ
    have hΨ' := (mem_affineTailHeadCodes_iff v hv j _ _ _ _ _ _ (ha (hs x)) (hb (hs x))).mp hΨ
    rw [hform x]
    refine Prod.ext ?_ ?_
    · change productTuple (F (hs x)).val.1 _ = y.1 ∘ id
      rw [productTuple_eq_append, hΨ']
      have h1 := congrArg Prod.fst hFx
      change (F (hs x)).val.1 = y.1 ∘ Fin.castAdd m at h1
      rw [h1]
      exact fin_append_castAdd_natAdd y.1
    · have h2 := congrArg Prod.snd hFx
      exact h2
  · rintro ⟨x, rfl, rfl⟩
    let hx := hs x
    let tl : Fin m → VF := affineTail (a hx).val (b hx).val
      (affineTailSlopesForHead v (a hx).val (b hx).val j ((D hx).val 0) ((c hx).val 0)) (x.val.1 ∘ r)
    let y : Point (M := M) (k + m) (V.obj.arity + 0) :=
      (Fin.append (F hx).val.1 tl, Fin.append (F hx).val.2 Fin.elim0)
    let w : AffineInput (M := M) m :=
      (Fin.append (Fin.append (Fin.append (Fin.append (a hx).val (b hx).val) (x.val.1 ∘ r))
        (D hx).val) (c hx).val, fun i => Fin.elim0 i)
    refine ⟨y, ⟨?_, w, ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · refine (hcomp (fun t => (F t).val) _ _).mpr ⟨x, rfl, ?_⟩
      exact Prod.ext (fin_append_comp_castAdd _ _).symm (fin_append_comp_castAdd _ _).symm
    · refine ⟨_, ⟨x.property, rfl⟩, hx, rfl, ?_⟩
      simp [w, fin_append_comp_castAdd]
    · refine ⟨_, ⟨x.property, rfl⟩, hx, rfl, ?_⟩
      simp [w, fin_append_comp_castAdd, fin_append_comp_natAdd]
    · refine Prod.ext ?_ (funext (fun i => Fin.elim0 i))
      simp [w, fin_append_comp_castAdd, fin_append_comp_natAdd, r]
    · refine ⟨_, ⟨x.property, rfl⟩, hx, rfl, ?_⟩
      simp [w, fin_append_comp_castAdd, fin_append_comp_natAdd]
    · refine ⟨_, ⟨x.property, rfl⟩, hx, rfl, ?_⟩
      simp [w, fin_append_comp_natAdd]
    · have hA : affA w = (a hx).val := by funext i; simp only [affA, w, Fin.append_left]
      have hB : affB w = (b hx).val := by funext i; simp only [affB, w, Fin.append_left, Fin.append_right]
      have hX : affX w = x.val.1 ∘ r := by funext i; simp only [affX, w, Fin.append_left, Fin.append_right, Function.comp_apply]
      have hD : affD w = (D hx).val 0 := by simp only [affD, w, Fin.append_left, Fin.append_right]
      have hC : affC w = (c hx).val 0 := by simp only [affC, w, Fin.append_right]
      change (fun i => (affineHeadInputs (affA w) (affB w) (affX w) (y.1 ∘ Fin.natAdd k) (affD w) (affC w) i).val) ∈
        affineTailHeadCodes j
      rw [hA, hB, hX, hD, hC]
      refine (mem_affineTailHeadCodes_iff v hv j _ _ _ _ _ _ (ha hx) (hb hx)).mpr ?_
      exact (fin_append_comp_natAdd _ _).symm
    · rw [hform x]
      refine Prod.ext ?_ ?_
      · change productTuple (F hx).val.1 tl = Fin.append (F hx).val.1 tl
        exact productTuple_eq_append _ _
      · exact (fin_append_comp_castAdd _ _).symm

end SpecialTransformations.Section9.GammaLift
