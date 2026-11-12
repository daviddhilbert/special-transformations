module

public import Section3.BallFibreConstancy
public import Section3.ClosedCosetChoice
public import Section3.DefinableCosets
public import Section3.EncodedBallGeometry
public import Section3.GammaBaseFiniteExceptions
public import Section3.GammaBaseTools
public import Section3.GammaProjection
public import Section3.GammaRealMap
public import Section3.GeneralBallCenters
public import Section3.ProfileComposition

@[expose] public section

/- Full quotient-profile selection over real/Gamma bases. This module
reuses checked additive-coset exceptions, closed-ball centers and the full
mixed-family Lemma 3.13. Its internal raw syntax proofs adapt the existing
DefinableCosets, ClosedClassCodes and ProfileComposition constructions. -/

/- Component: GammaDefinableCosets -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.DefinableCosets
variable {M : Type} [sM : LRV.Structure M]

def differenceTuple (z : Fin 2 → M) : Fin 1 → M :=
  fun _ => iVFAdd (z 0) (iVFNeg (z 1))

/-- The raw primitive-function composition, before any change of model.
This follows relation_raw_definable's existing subtraction-map proof. -/
theorem differenceTuple_raw_definable (S : Set M) :
    S.DefinableMap LRV (differenceTuple (M := M)) := by
  have hn : S.DefinableFun LRV (fun z : Fin 2 → M => iVFNeg (z 1)) := by
    have hf : S.DefinableFun LRV (Structure.funMap (L := LRV) Fn.vfNeg) :=
      Set.DefinableFun.of_empty (@Set.DefinableFun.fun_symbol M LRV sM 1 Fn.vfNeg)
    have hg : S.DefinableMap LRV (fun z : Fin 2 → M => ![z 1]) := by
      intro i
      fin_cases i
      exact Set.DefinableFun.proj LRV
    exact hf.comp hg
  have hd : S.DefinableFun LRV (fun z : Fin 2 → M => iVFAdd (z 0) (iVFNeg (z 1))) := by
    have hf : S.DefinableFun LRV (Structure.funMap (L := LRV) Fn.vfAdd) :=
      Set.DefinableFun.of_empty (@Set.DefinableFun.fun_symbol M LRV sM 2 Fn.vfAdd)
    have hg : S.DefinableMap LRV (fun z : Fin 2 → M => ![z 0,iVFNeg (z 1)]) := by
      intro i
      fin_cases i
      · exact Set.DefinableFun.proj LRV
      · exact hn
    exact hf.comp hg
  exact fun _ => hd

variable [hM : M ⊨ Axioms.ACVF]

/-- The full actual-coset kernel is definable over the same genuine
real/Gamma base as the subgroup's VF point set. -/
theorem relation_definable_gamma_base (B : GammaParameters.Base (M := M))
    (A : Set M) (hA : GammaParameters.DefinableAtBase B .vf A) :
    GammaParameters.DefinableOverBase B (fun _ => .vf) (relation A) := by
  let N := CanonicalStructure.normalize (M := M)
  letI := sM
  let F : (Fin 2 → M) → (Fin 1 → M) := @differenceTuple M N
  have hF := @differenceTuple_raw_definable M N B.real
  have h := hA.preimage_real_map (fun _ : Fin 2 => .vf) F hF
  convert h using 1
  all_goals try rfl
  ext z
  have he (hs : ∀ i : Fin 2, iVF (z i)) :
      F z 0 = iVFAdd (z 0) (iVFNeg (z 1)) := difference_normalize (z 0) (z 1) (hs 0) (hs 1)
  constructor
  · rintro ⟨h0,h1,hd⟩
    have hs : ∀ i : Fin 2, iVF (z i) := by
      intro i
      fin_cases i
      · exact h0
      · exact h1
    refine ⟨?_,hs⟩
    change F z 0 ∈ A
    rw [he hs]
    exact hd
  · rintro ⟨hd,hs⟩
    refine ⟨hs 0,hs 1,?_⟩
    change F z 0 ∈ A at hd
    rwa [he hs] at hd

end SpecialTransformations.Section3.DefinableCosets

/- Component: GammaProfileVariation -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem DefinableOverBase.sdiff {B : Base (M := M)} {n : ℕ}
    {sn : Fin n → SortTag} {A C : Set (Fin n → M)}
    (hA : DefinableOverBase B sn A) (hC : DefinableOverBase B sn C) :
    DefinableOverBase B sn (A \ C) := by
  convert hA.inter hC.compl using 1
  all_goals try rfl
  ext z
  change (z ∈ A ∧ z ∉ C) ↔ z ∈ A ∧ z ∈ sortedUniverse sn ∧ z ∉ C
  exact ⟨fun h => ⟨h.1,hA.proper z h.1,h.2⟩,fun h => ⟨h.1,h.2.2⟩⟩

/-- Universal quantification of one correctly sorted real coordinate,
with the full Gamma parameter support retained over exactly B. -/
theorem DefinableOverBase.forall_last {B : Base (M := M)} {n : ℕ}
    {sn : Fin (n+1) → SortTag} {A : Set (Fin (n+1) → M)}
    (hA : DefinableOverBase B sn A) :
    DefinableOverBase B (sn ∘ Fin.castSucc) {z | z ∈ sortedUniverse (sn ∘ Fin.castSucc) ∧
      ∀ x, sortEval (sn (Fin.last n)) x → Fin.snoc z x ∈ A} := by
  have hh := (hA.compl.image_real Fin.castSucc).compl
  convert hh using 1
  ext z
  change (z ∈ sortedUniverse (sn ∘ Fin.castSucc) ∧
      ∀ x, sortEval (sn (Fin.last n)) x → Fin.snoc z x ∈ A) ↔
    z ∈ sortedUniverse (sn ∘ Fin.castSucc) ∧
      z ∉ (fun w : Fin (n+1) → M => w ∘ Fin.castSucc) '' (sortedUniverse sn \ A)
  constructor
  · rintro ⟨hz,hall⟩
    refine ⟨hz,?_⟩
    rintro ⟨w,⟨hw,hn⟩,he⟩
    have hwEq : w = Fin.snoc z (w (Fin.last n)) := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last]
      · rw [Fin.snoc_castSucc]
        exact congrFun he j
    have hmem := hall (w (Fin.last n)) (hw (Fin.last n))
    rw [← hwEq] at hmem
    exact hn hmem
  · rintro ⟨hz,hn⟩
    refine ⟨hz,?_⟩
    intro x hx
    by_contra hnot
    have hws : Fin.snoc z x ∈ sortedUniverse sn := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.snoc_last] using hx
      · simpa only [Fin.snoc_castSucc,Function.comp_apply] using hz j
    apply hn
    refine ⟨Fin.snoc z x,⟨hws,hnot⟩,?_⟩
    funext i
    simp only [Function.comp_apply,Fin.snoc_castSucc]

end SpecialTransformations.Section3.GammaParameters

namespace SpecialTransformations.Section3.ProfileVariation
open GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {m : ℕ}

def pairSort : Fin (m+2) → SortTag := Fin.cases .vf (Fin.cases .vf (fun _ => .rv))

def leftIndex : Fin (m+1) → Fin (m+2) := Fin.cases 0 (fun i => i.succ.succ)
def rightIndex : Fin (m+1) → Fin (m+2) := Fin.cases 1 (fun i => i.succ.succ)

def pairs (f : VFType (M := M) → Set (Fin m → M)) : Set (Fin 2 → M) :=
  {z | ∃ x y : VFType (M := M), x.val = z 0 ∧ y.val = z 1 ∧ f x ≠ f y}

theorem left_tuple (x y : VFType (M := M)) (ys : Fin m → M) :
    Fin.cons x.val (Fin.cons y.val ys) ∘ leftIndex = Fin.cons x.val ys := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem right_tuple (x y : VFType (M := M)) (ys : Fin m → M) :
    Fin.cons x.val (Fin.cons y.val ys) ∘ rightIndex = Fin.cons y.val ys := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem pair_tuple_sorted (x y : VFType (M := M)) (ys : Fin m → M)
    (hys : ∀ i, iRV (ys i)) :
    Fin.cons x.val (Fin.cons y.val ys) ∈ sortedUniverse pairSort := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact x.property
  · refine Fin.cases ?_ (fun k => ?_) j
    · exact y.property
    · exact hys k

/-- Inequality of two powerset-valued profiles is first-order definable
over the original Gamma base, by projecting their symmetric difference. -/
theorem pairs_definable_base (B : Base (M := M))
    (f : VFType (M := M) → Set (Fin m → M))
    (hf : ∀ x ys, ys ∈ f x → ∀ i, iRV (ys i))
    (hg : DefinableOverBase B MixedPolynomialSyntax.contextSort (BallFibreConstancy.graph f)) :
    DefinableOverBase B (fun _ => .vf) (pairs f) := by
  let L : Set (Fin (m+2) → M) := {w | w ∘ leftIndex ∈ BallFibreConstancy.graph f ∧
    w ∈ sortedUniverse pairSort}
  let R : Set (Fin (m+2) → M) := {w | w ∘ rightIndex ∈ BallFibreConstancy.graph f ∧
    w ∈ sortedUniverse pairSort}
  have hL : DefinableOverBase B pairSort L := hg.preimage_real pairSort leftIndex
  have hR : DefinableOverBase B pairSort R := hg.preimage_real pairSort rightIndex
  let π : Fin 2 → Fin (m+2) := ![0,1]
  have hp := ((hL.sdiff hR).union (hR.sdiff hL)).image_real π
  have hs : pairSort ∘ π = (fun _ : Fin 2 => SortTag.vf) := by
    funext i
    fin_cases i <;> rfl
  rw [hs] at hp
  convert hp using 1
  ext z
  constructor
  · rintro ⟨x,y,hx,hy,hneq⟩
    have hn : ¬ ∀ ys, ys ∈ f x ↔ ys ∈ f y := fun h => hneq (Set.ext h)
    obtain ⟨ys,hys⟩ := Classical.not_forall.mp hn
    have hRV : ∀ i, iRV (ys i) := by
      by_cases hxys : ys ∈ f x
      · exact hf x ys hxys
      · have hyys : ys ∈ f y := by
          by_contra hny
          exact hys ⟨fun h => False.elim (hxys h),fun h => False.elim (hny h)⟩
        exact hf y ys hyys
    let w : Fin (m+2) → M := Fin.cons x.val (Fin.cons y.val ys)
    have hwSort : w ∈ sortedUniverse pairSort := pair_tuple_sorted x y ys hRV
    have hwL : w ∈ L ↔ ys ∈ f x := by
      change (w ∘ leftIndex ∈ BallFibreConstancy.graph f ∧ w ∈ sortedUniverse pairSort) ↔ _
      rw [and_iff_left hwSort,left_tuple]
      exact BallFibreConstancy.mem_graph f x ys
    have hwR : w ∈ R ↔ ys ∈ f y := by
      change (w ∘ rightIndex ∈ BallFibreConstancy.graph f ∧ w ∈ sortedUniverse pairSort) ↔ _
      rw [and_iff_left hwSort,right_tuple]
      exact BallFibreConstancy.mem_graph f y ys
    have hw : w ∈ (L \ R) ∪ (R \ L) := by
      by_cases hxys : ys ∈ f x
      · left
        refine ⟨hwL.mpr hxys,?_⟩
        intro hyR
        have hyys := hwR.mp hyR
        exact hys ⟨fun _ => hyys,fun _ => hxys⟩
      · have hyys : ys ∈ f y := by
          by_contra hny
          exact hys ⟨fun h => False.elim (hxys h),fun h => False.elim (hny h)⟩
        exact Or.inr ⟨hwR.mpr hyys,fun hw' => hxys (hwL.mp hw')⟩
    refine ⟨w,hw,?_⟩
    funext i
    fin_cases i
    · exact hx
    · exact hy
  · rintro ⟨w,hw,he⟩
    have hwSort : w ∈ sortedUniverse pairSort := by
      rcases hw with hw | hw
      · exact hw.1.2
      · exact hw.1.2
    let x : VFType (M := M) := ⟨w 0,hwSort 0⟩
    let y : VFType (M := M) := ⟨w 1,hwSort 1⟩
    let ys : Fin m → M := Fin.tail (Fin.tail w)
    have hleft : w ∘ leftIndex = Fin.cons x.val ys := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    have hright : w ∘ rightIndex = Fin.cons y.val ys := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    have hwL : w ∈ L ↔ ys ∈ f x := by
      change (w ∘ leftIndex ∈ BallFibreConstancy.graph f ∧ w ∈ sortedUniverse pairSort) ↔ _
      rw [and_iff_left hwSort,hleft]
      exact BallFibreConstancy.mem_graph f x ys
    have hwR : w ∈ R ↔ ys ∈ f y := by
      change (w ∘ rightIndex ∈ BallFibreConstancy.graph f ∧ w ∈ sortedUniverse pairSort) ↔ _
      rw [and_iff_left hwSort,hright]
      exact BallFibreConstancy.mem_graph f y ys
    refine ⟨x,y,congrFun he 0,congrFun he 1,?_⟩
    intro hxy
    have hLR : w ∈ L ↔ w ∈ R := by
      rw [hwL,hwR,hxy]
    rcases hw with hw | hw
    · exact hw.2 (hLR.mp hw.1)
    · exact hw.2 (hLR.mpr hw.1)

end SpecialTransformations.Section3.ProfileVariation

/- Component: GammaBallClassCodes -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.BallClassCodes
open GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

def classBody (E : Set (Fin 2 → M)) (r : M) : Set M := {x | ![x,r] ∈ E}

def classEquality (D : (Fin n → M) → Set M) (E : Set (Fin 2 → M)) : Set (Fin (n+1) → M) :=
  {z | z ∈ sortedUniverse (fun _ => .vf) ∧ D (Fin.init z) = classBody E (z (Fin.last n))}

/-- Equality of a real-coded point set with an equivalence class is
definable by its complete quantified membership kernel over the same B. -/
theorem classEquality_definable_base (B : Base (M := M))
    (D : (Fin n → M) → Set M) (E : Set (Fin 2 → M))
    (hD : DefinableOverBase B (fun _ : Fin (n+1) => .vf)
      {z | z (Fin.last n) ∈ D (Fin.init z)})
    (hE : DefinableOverBase B (fun _ => .vf) E) :
    DefinableOverBase B (fun _ => .vf) (classEquality D E) := by
  let iD : Fin (n+1) → Fin (n+2) :=
    Fin.snoc (fun j : Fin n => j.castSucc.castSucc) (Fin.last (n+1))
  let iE : Fin 2 → Fin (n+2) := ![Fin.last (n+1),(Fin.last n).castSucc]
  let U : Set (Fin (n+2) → M) := sortedUniverse (fun _ => SortTag.vf)
  let L : Set (Fin (n+2) → M) := {w |
    (w ∘ iD) (Fin.last n) ∈ D (Fin.init (w ∘ iD)) ∧ w ∈ U}
  let R : Set (Fin (n+2) → M) := {w | w ∘ iE ∈ E ∧ w ∈ U}
  have hL : DefinableOverBase B (fun _ => .vf) L := hD.preimage_real (fun _ => .vf) iD
  have hR : DefinableOverBase B (fun _ => .vf) R := hE.preimage_real (fun _ => .vf) iE
  let F : Set (Fin (n+2) → M) := ((U \ L) ∪ R) ∩ ((U \ R) ∪ L)
  have hF : DefinableOverBase B (fun _ => .vf) F :=
    (hL.compl.union hR).inter (hR.compl.union hL)
  have hPoint (z : Fin (n+1) → M) (hz : z ∈ sortedUniverse (fun _ => .vf))
      (x : M) (hx : iVF x) :
      Fin.snoc z x ∈ F ↔ (x ∈ D (Fin.init z) ↔ ![x,z (Fin.last n)] ∈ E) := by
    let w : Fin (n+2) → M := Fin.snoc z x
    have hw : w ∈ U := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [w,Fin.snoc_last,sortEval,iVF] using hx
      · simpa only [w,Fin.snoc_castSucc] using hz j
    have hd : w ∘ iD = Fin.snoc (Fin.init z) x := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Function.comp_apply,iD,w,Fin.snoc_last]
      · simp only [Function.comp_apply,iD,w,Fin.snoc_castSucc,Fin.init]
    have he : w ∘ iE = ![x,z (Fin.last n)] := by
      funext i
      fin_cases i
      · change w (Fin.last (n+1)) = x
        simp only [w,Fin.snoc_last]
      · change w (Fin.last n).castSucc = z (Fin.last n)
        simp only [w,Fin.snoc_castSucc]
    have hl : w ∈ L ↔ x ∈ D (Fin.init z) := by
      change ((w ∘ iD) (Fin.last n) ∈ D (Fin.init (w ∘ iD)) ∧ w ∈ U) ↔ _
      rw [and_iff_left hw,hd]
      simp only [Fin.snoc_last,Fin.init_snoc]
    have hr : w ∈ R ↔ ![x,z (Fin.last n)] ∈ E := by
      change (w ∘ iE ∈ E ∧ w ∈ U) ↔ _
      rw [and_iff_left hw,he]
    change (((w ∈ U ∧ w ∉ L) ∨ w ∈ R) ∧ ((w ∈ U ∧ w ∉ R) ∨ w ∈ L)) ↔ _
    simp only [hw,true_and,hl,hr]
    tauto
  have hDVF (q : Fin n → M) (x : M) (hx : x ∈ D q) : iVF x := by
    let w : Fin (n+1) → M := Fin.snoc q x
    have hm : w (Fin.last n) ∈ D (Fin.init w) := by
      simpa only [w,Fin.snoc_last,Fin.init_snoc] using hx
    have hh := hD.proper w hm (Fin.last n)
    simpa only [w,Fin.snoc_last,sortEval,iVF] using hh
  have hh := hF.forall_last
  convert hh using 1
  all_goals try rfl
  ext z
  change (z ∈ sortedUniverse (fun _ => .vf) ∧ D (Fin.init z) = classBody E (z (Fin.last n))) ↔
    z ∈ sortedUniverse (fun _ => .vf) ∧ ∀ x, iVF x → Fin.snoc z x ∈ F
  constructor
  · rintro ⟨hz,he⟩
    refine ⟨hz,?_⟩
    intro x hx
    apply (hPoint z hz x hx).mpr
    exact Set.ext_iff.mp he x
  · rintro ⟨hz,hall⟩
    refine ⟨hz,?_⟩
    ext x
    by_cases hx : iVF x
    · exact (hPoint z hz x hx).mp (hall x hx)
    · exact iff_of_false (fun hd => hx (hDVF (Fin.init z) x hd))
        (fun he => hx (hE.proper ![x,z (Fin.last n)] he 0))

def classCodes (D : (Fin n → M) → Set M) (E : Set (Fin 2 → M)) : Set (Fin n → M) :=
  {q | q ∈ sortedUniverse (fun _ => .vf) ∧ ∃ r, iVF r ∧ D q = classBody E r}

theorem classCodes_definable_base (B : Base (M := M))
    (D : (Fin n → M) → Set M) (E : Set (Fin 2 → M))
    (hD : DefinableOverBase B (fun _ : Fin (n+1) => .vf)
      {z | z (Fin.last n) ∈ D (Fin.init z)})
    (hE : DefinableOverBase B (fun _ => .vf) E) :
    DefinableOverBase B (fun _ => .vf) (classCodes D E) := by
  have hp := (classEquality_definable_base B D E hD hE).image_real Fin.castSucc
  convert hp using 1
  all_goals try rfl
  ext q
  constructor
  · rintro ⟨hq,r,hr,he⟩
    let w : Fin (n+1) → M := Fin.snoc q r
    have hws : w ∈ sortedUniverse (fun _ => .vf) := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [w,Fin.snoc_last,sortEval,iVF] using hr
      · simpa only [w,Fin.snoc_castSucc] using hq j
    refine ⟨w,⟨hws,?_⟩,?_⟩
    · simpa only [w,Fin.init_snoc,Fin.snoc_last] using he
    · funext i
      simp only [w,Function.comp_apply,Fin.snoc_castSucc]
  · rintro ⟨w,⟨hw,he⟩,hp⟩
    have hi : Fin.init w = q := hp
    refine ⟨?_,w (Fin.last n),hw (Fin.last n),?_⟩
    · intro i
      rw [← congrFun hp i]
      exact hw i.castSucc
    · rwa [hi] at he

def variationCodes {m : ℕ} (D : (Fin n → M) → Set M)
    (f : VFType (M := M) → Set (Fin m → M)) : Set (Fin n → M) :=
  {q | ∃ x y : VFType (M := M), x.val ∈ D q ∧ y.val ∈ D q ∧ f x ≠ f y}

theorem variationCodes_definable_base (B : Base (M := M))
    (D : (Fin n → M) → Set M)
    (hD : DefinableOverBase B (fun _ : Fin (n+1) => .vf)
      {z | z (Fin.last n) ∈ D (Fin.init z)})
    {m : ℕ} (f : VFType (M := M) → Set (Fin m → M))
    (hf : ∀ x ys, ys ∈ f x → ∀ i, iRV (ys i))
    (hg : DefinableOverBase B MixedPolynomialSyntax.contextSort (BallFibreConstancy.graph f)) :
    DefinableOverBase B (fun _ => .vf) (variationCodes D f) := by
  let iq : Fin n → Fin (n+2) := fun i => i.castSucc.castSucc
  let iy : Fin (n+1) → Fin (n+2) := Fin.snoc iq (Fin.last (n+1))
  let ip : Fin 2 → Fin (n+2) := ![(Fin.last n).castSucc,Fin.last (n+1)]
  have hxD := hD.preimage_real (fun _ : Fin (n+2) => .vf) Fin.castSucc
  have hyD := hD.preimage_real (fun _ : Fin (n+2) => .vf) iy
  have hp := (ProfileVariation.pairs_definable_base B f hf hg).preimage_real
    (fun _ : Fin (n+2) => .vf) ip
  let H : Set (Fin (n+2) → M) := {w |
    w (Fin.last n).castSucc ∈ D (Fin.init (Fin.init w)) ∧
    w (Fin.last (n+1)) ∈ D (Fin.init (Fin.init w)) ∧
    w ∘ ip ∈ ProfileVariation.pairs f ∧ w ∈ sortedUniverse (fun _ => .vf)}
  have hH : DefinableOverBase B (fun _ => .vf) H := by
    convert (hxD.inter hyD).inter hp using 1
    ext w
    have hi : Fin.init (w ∘ iy) = Fin.init (Fin.init w) := by
      funext i
      simp only [Fin.init,Function.comp_apply,iy,Fin.snoc_castSucc,iq]
    have hl : (w ∘ iy) (Fin.last n) = w (Fin.last (n+1)) := by
      simp only [Function.comp_apply,iy,Fin.snoc_last]
    change _ ↔ (((w ∘ Fin.castSucc) (Fin.last n) ∈ D (Fin.init (w ∘ Fin.castSucc)) ∧
      w ∈ sortedUniverse (fun _ => .vf)) ∧
      ((w ∘ iy) (Fin.last n) ∈ D (Fin.init (w ∘ iy)) ∧ w ∈ sortedUniverse (fun _ => .vf))) ∧
      (w ∘ ip ∈ ProfileVariation.pairs f ∧ w ∈ sortedUniverse (fun _ => .vf))
    rw [hi,hl]
    change (w (Fin.last n).castSucc ∈ D (Fin.init (Fin.init w)) ∧
      w (Fin.last (n+1)) ∈ D (Fin.init (Fin.init w)) ∧
      w ∘ ip ∈ ProfileVariation.pairs f ∧ w ∈ sortedUniverse (fun _ => .vf)) ↔
      ((w (Fin.last n).castSucc ∈ D (Fin.init (Fin.init w)) ∧ w ∈ sortedUniverse (fun _ => .vf)) ∧
      (w (Fin.last (n+1)) ∈ D (Fin.init (Fin.init w)) ∧ w ∈ sortedUniverse (fun _ => .vf))) ∧
      (w ∘ ip ∈ ProfileVariation.pairs f ∧ w ∈ sortedUniverse (fun _ => .vf))
    tauto
  have hproj := hH.image_real iq
  convert hproj using 1
  all_goals try rfl
  ext q
  constructor
  · rintro ⟨x,y,hx,hy,hneq⟩
    let zx : Fin (n+1) → M := Fin.snoc q x.val
    have hm : zx (Fin.last n) ∈ D (Fin.init zx) := by
      simpa only [zx,Fin.snoc_last,Fin.init_snoc] using hx
    have hq (i : Fin n) : iVF (q i) := by
      have hs := hD.proper zx hm i.castSucc
      simpa only [zx,Fin.snoc_castSucc,sortEval,iVF] using hs
    let w : Fin (n+2) → M := Fin.snoc (Fin.snoc q x.val) y.val
    have hwq : Fin.init (Fin.init w) = q := by simp only [w,Fin.init_snoc]
    have hwx : w (Fin.last n).castSucc = x.val := by simp only [w,Fin.snoc_castSucc,Fin.snoc_last]
    have hwy : w (Fin.last (n+1)) = y.val := by simp only [w,Fin.snoc_last]
    have hws : w ∈ sortedUniverse (fun _ => .vf) := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [w,Fin.snoc_last,sortEval,iVF] using y.property
      · refine Fin.lastCases ?_ (fun k => ?_) j
        · simpa only [w,Fin.snoc_castSucc,Fin.snoc_last,sortEval,iVF] using x.property
        · simpa only [w,Fin.snoc_castSucc,sortEval,iVF] using hq k
    have hwp : w ∘ ip ∈ ProfileVariation.pairs f := by
      refine ⟨x,y,?_,?_,hneq⟩
      · change x.val = w (Fin.last n).castSucc
        exact hwx.symm
      · change y.val = w (Fin.last (n+1))
        exact hwy.symm
    refine ⟨w,⟨?_,?_,hwp,hws⟩,?_⟩
    · rwa [hwq,hwx]
    · rwa [hwq,hwy]
    · funext i
      simp only [w,Function.comp_apply,iq,Fin.snoc_castSucc]
  · rintro ⟨w,⟨hx,hy,⟨x,y,hxv,hyv,hneq⟩,_⟩,he⟩
    have hi : Fin.init (Fin.init w) = q := he
    refine ⟨x,y,?_,?_,hneq⟩
    · rw [hxv]
      change w (Fin.last n).castSucc ∈ D q
      rwa [hi] at hx
    · rw [hyv]
      change w (Fin.last (n+1)) ∈ D q
      rwa [hi] at hy

end SpecialTransformations.Section3.BallClassCodes

/- Component: GammaProfileComposition -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.ProfileComposition
open GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {m : ℕ}

/-- Profile substitution along a partial VF center relation retains the
complete graph over the same real/Gamma base. -/
theorem compose_definable_base (B : Base (M := M)) (K : Set (Fin 2 → M))
    (U : Set (Fin (m+1) → M))
    (hK : DefinableOverBase B (fun _ => .vf) K)
    (hU : DefinableOverBase B MixedPolynomialSyntax.contextSort U) :
    DefinableOverBase B MixedPolynomialSyntax.contextSort (compose K U) := by
  let ip : Fin 2 → Fin (m+2) := ![0,1]
  have hL := hK.preimage_real (ProfileVariation.pairSort (m := m)) ip
  have hR := hU.preimage_real (ProfileVariation.pairSort (m := m)) ProfileVariation.rightIndex
  have hX := (hL.inter hR).image_real ProfileVariation.leftIndex
  have hsort : ProfileVariation.pairSort ∘ ProfileVariation.leftIndex =
      MixedPolynomialSyntax.contextSort (m := m) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  rw [hsort] at hX
  have hdom := hK.image_real (fun _ : Fin 1 => (0 : Fin 2))
  have hdomU := hdom.preimage_real (MixedPolynomialSyntax.contextSort (m := m))
    (fun _ : Fin 1 => (0 : Fin (m+1)))
  have hnone := hdomU.compl.inter hU
  convert hX.union hnone using 1
  all_goals try rfl
  ext z
  have hsome :
      (∃ c, ![z 0,c] ∈ K ∧ Fin.cons c (Fin.tail z) ∈ U) ↔
        z ∈ (fun w : Fin (m+2) → M => w ∘ ProfileVariation.leftIndex) ''
          ({w | w ∘ ip ∈ K ∧ w ∈ sortedUniverse ProfileVariation.pairSort} ∩
           {w | w ∘ ProfileVariation.rightIndex ∈ U ∧ w ∈ sortedUniverse ProfileVariation.pairSort}) := by
    constructor
    · rintro ⟨c,hc,hu⟩
      let w : Fin (m+2) → M := Fin.cons (z 0) (Fin.cons c (Fin.tail z))
      have hp : w ∘ ip = ![z 0,c] := by funext i; fin_cases i <;> rfl
      have hr : w ∘ ProfileVariation.rightIndex = Fin.cons c (Fin.tail z) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      have hl : w ∘ ProfileVariation.leftIndex = z := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      have hw : w ∈ sortedUniverse ProfileVariation.pairSort := by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hK.proper _ hc 0
        · refine Fin.cases ?_ (fun k => ?_) j
          · exact hK.proper _ hc 1
          · exact hU.proper _ hu k.succ
      exact ⟨w,⟨⟨hp.symm ▸ hc,hw⟩,⟨hr.symm ▸ hu,hw⟩⟩,hl⟩
    · rintro ⟨w,⟨⟨hk,_⟩,⟨hu,_⟩⟩,he⟩
      have hp : w ∘ ip = ![z 0,w 1] := by
        funext i
        fin_cases i
        · exact congrFun he 0
        · rfl
      have hr : w ∘ ProfileVariation.rightIndex = Fin.cons (w 1) (Fin.tail z) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · exact congrFun he j.succ
      exact ⟨w 1,hp ▸ hk,hr ▸ hu⟩
  have hdomain :
      ((fun _ : Fin 1 => z 0) ∈ (fun w : Fin 2 → M => fun _ : Fin 1 => w 0) '' K) ↔
        z 0 ∈ domain K := by
    constructor
    · rintro ⟨w,hw,he⟩
      refine ⟨w 1,?_⟩
      have hwEq : w = ![z 0,w 1] := by
        funext i
        fin_cases i
        · exact congrFun he 0
        · rfl
      exact hwEq ▸ hw
    · rintro ⟨c,hc⟩
      exact ⟨![z 0,c],hc,rfl⟩
  change ((∃ c, ![z 0,c] ∈ K ∧ Fin.cons c (Fin.tail z) ∈ U) ∨
    (z 0 ∉ domain K ∧ z ∈ U)) ↔ _
  rw [hsome]
  change _ ↔ _ ∨ ((z ∈ sortedUniverse MixedPolynomialSyntax.contextSort ∧
    ¬ ((fun _ : Fin 1 => z 0) ∈ (fun w : Fin 2 → M => fun _ : Fin 1 => w 0) '' K ∧
      z ∈ sortedUniverse MixedPolynomialSyntax.contextSort)) ∧ z ∈ U)
  rw [hdomain]
  have hz : z ∈ U → z ∈ sortedUniverse MixedPolynomialSyntax.contextSort := hU.proper z
  tauto

end SpecialTransformations.Section3.ProfileComposition

/- Component: GammaBallCenterKernel -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.BallClassCodes
open GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

def centerKernel (D : (Fin n → M) → Set M) (C : Set (Fin (n+1) → M)) : Set (Fin 2 → M) :=
  {z | ∃ q, z 0 ∈ D q ∧ Fin.snoc q (z 1) ∈ C}

/-- Quantifying real ball codes yields a full point/center relation,
without naming any code or representative in the parameter base. -/
theorem centerKernel_definable_base (B : Base (M := M))
    (D : (Fin n → M) → Set M) (C : Set (Fin (n+1) → M))
    (hD : DefinableOverBase B (fun _ : Fin (n+1) => .vf)
      {z | z (Fin.last n) ∈ D (Fin.init z)})
    (hC : DefinableOverBase B (fun _ => .vf) C) :
    DefinableOverBase B (fun _ => .vf) (centerKernel D C) := by
  let iC : Fin (n+1) → Fin (n+2) :=
    Fin.snoc (fun j : Fin n => j.castSucc.castSucc) (Fin.last (n+1))
  let ip : Fin 2 → Fin (n+2) := ![(Fin.last n).castSucc,Fin.last (n+1)]
  have hL := hD.preimage_real (fun _ : Fin (n+2) => .vf) Fin.castSucc
  have hR := hC.preimage_real (fun _ : Fin (n+2) => .vf) iC
  have h := (hL.inter hR).image_real ip
  convert h using 1
  all_goals try rfl
  ext z
  constructor
  · rintro ⟨q,hx,hc⟩
    let zx : Fin (n+1) → M := Fin.snoc q (z 0)
    have hzx : zx (Fin.last n) ∈ D (Fin.init zx) := by
      simpa only [zx,Fin.snoc_last,Fin.init_snoc] using hx
    let zc : Fin (n+1) → M := Fin.snoc q (z 1)
    have hzc : zc ∈ C := hc
    let w : Fin (n+2) → M := Fin.snoc zx (z 1)
    have hl : w ∘ Fin.castSucc = zx := by
      funext i
      simp only [w,Function.comp_apply,Fin.snoc_castSucc]
    have hr : w ∘ iC = zc := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [w,iC,zc,Function.comp_apply,Fin.snoc_last]
      · simp only [w,iC,zx,zc,Function.comp_apply,Fin.snoc_castSucc]
    have hw : w ∈ sortedUniverse (fun _ => .vf) := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [w,Fin.snoc_last,zc] using hC.proper zc hzc (Fin.last n)
      · simpa only [w,Fin.snoc_castSucc] using hD.proper zx hzx j
    refine ⟨w,⟨⟨?_,hw⟩,⟨?_,hw⟩⟩,?_⟩
    · rw [hl]
      exact hzx
    · rwa [hr]
    · funext i
      fin_cases i
      · change w (Fin.last n).castSucc = z 0
        simp only [w,Fin.snoc_castSucc,zx,Fin.snoc_last]
      · change w (Fin.last (n+1)) = z 1
        simp only [w,Fin.snoc_last]
  · rintro ⟨w,⟨⟨hd,_⟩,⟨hc,_⟩⟩,he⟩
    let q : Fin n → M := Fin.init (Fin.init w)
    have hr : w ∘ iC = Fin.snoc q (z 1) := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have hy : w (Fin.last (n+1)) = z 1 := congrFun he 1
        simpa only [Function.comp_apply,iC,Fin.snoc_last] using hy
      · simp only [Function.comp_apply,iC,Fin.snoc_castSucc,q,Fin.init]
    refine ⟨q,?_,?_⟩
    · have hx : w (Fin.last n).castSucc = z 0 := congrFun he 0
      rw [← hx]
      exact hd
    · rwa [← hr]

end SpecialTransformations.Section3.BallClassCodes

/- Component: CosetBallGeometry -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.BallImaginaries
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem underlying_subset_vf (D : Ball M) : underlying D ⊆ {x | iVF x} := by
  obtain ⟨t,ht⟩ := Quotient.exists_rep D
  cases t with
  | inl C =>
    obtain ⟨q,hq⟩ := Quotient.exists_rep C
    rw [← ht,← hq]
    exact fun x hx => hx.2.1
  | inr O =>
    rw [← ht]
    exact OpenBallCodes.underlying_subset_vf O

/-- The paper's encoded balls have actual VF radius representatives, so
they belong to the two-chart quotient, including its two degeneracies. -/
theorem isBall_coded {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (B : Set M) (hB : IsBall B) :
    ∃ D : Ball M, {x : VFType (M := M) | x.val ∈ B} =
      {x : VFType (M := M) | x.val ∈ underlying D} := by
  rcases hB with hB | ⟨a, t, ha, ht, ht0, hB⟩ | (⟨a, t, ha, ht, ht0, hB⟩ | ⟨a, ha, hB⟩)
  · obtain ⟨D,hD⟩ := universe_coded (M := M)
    refine ⟨D,?_⟩
    rw [hD]
    ext x
    change x.val ∈ B ↔ True
    rw [hB]
    exact iff_true_intro x.property
  · let a' : VFType (M := M) := ⟨a, ha⟩
    obtain ⟨b, hb⟩ := CanonicalRV.encodedRv_surjective (⟨t, ht⟩ : CanonicalRV.RVSort M)
    have hb' : iRv b.val = t := congrArg Subtype.val hb
    obtain ⟨D,hD⟩ := closed_disc_coded v hv a' b
    refine ⟨D,?_⟩
    rw [hD]
    apply Set.ext
    intro (x : VFType (M := M))
    change x.val ∈ B ↔ v (x - a') ≤ v b
    rw [hB]
    change (iVF x.val ∧ iLe t (iRv (iVFAdd x.val (iVFNeg a)))) ↔ _
    rw [and_iff_right x.property]
    have hd : (x - a').val = iVFAdd x.val (iVFNeg a) := by rw [sub_eq_add_neg]; rfl
    have he := hv (x - a') b
    change iLe (iRv b.val) (iRv (x - a').val) ↔ _ at he
    rw [hb', hd] at he
    exact he
  · let a' : VFType (M := M) := ⟨a, ha⟩
    obtain ⟨b, hb⟩ := CanonicalRV.encodedRv_surjective (⟨t, ht⟩ : CanonicalRV.RVSort M)
    have hb' : iRv b.val = t := congrArg Subtype.val hb
    have hb0 : b ≠ 0 := by
      intro he
      exact ht0 (hb'.symm.trans ((CanonicalRV.encodedRv_zero_iff b).mpr he))
    have hvb : v b ≠ 0 := (map_ne_zero v).mpr hb0
    obtain ⟨D,hD⟩ := open_disc_coded v hv a' b hb0
    refine ⟨D,?_⟩
    rw [hD]
    apply Set.ext
    intro (x : VFType (M := M))
    change x.val ∈ B ↔ v (x-a') < v b
    rw [hB]
    change (iVF x.val ∧ iLe t (iRv (iVFAdd x.val (iVFNeg a))) ∧
      ¬ iLe (iRv (iVFAdd x.val (iVFNeg a))) t) ↔ v (x - a') < v b
    rw [and_iff_right x.property]
    have hd : (x - a').val = iVFAdd x.val (iVFNeg a) := by rw [sub_eq_add_neg]; rfl
    have hle := hv (x - a') b
    have hge := hv b (x - a')
    change iLe (iRv b.val) (iRv (x - a').val) ↔ _ at hle
    change iLe (iRv (x - a').val) (iRv b.val) ↔ _ at hge
    rw [hb', hd] at hle hge
    rw [hle, hge, lt_iff_le_not_ge]
  · let a' : VFType (M := M) := ⟨a, ha⟩
    obtain ⟨D,hD⟩ := closed_disc_coded v hv a' 0
    refine ⟨D,?_⟩
    rw [hD,map_zero,ValOneEC.closedBall_zero_radius]
    apply Set.ext
    intro (x : VFType (M := M))
    change x.val ∈ B ↔ x = a'
    rw [hB]
    change (iVF x.val ∧ x.val = a) ↔ x = a'
    rw [and_iff_right x.property]
    constructor
    · intro he
      exact Subtype.ext he
    · intro he
      exact congrArg Subtype.val he

/-- Translating an actual ball stays in the same two-chart universe.
The translating point is proof data, not a new definability parameter. -/
theorem translate_coded {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (D : Ball M) (c : VFType (M := M)) :
    ∃ E : Ball M, {x : VFType (M := M) | (x-c).val ∈ underlying D} =
      {x : VFType (M := M) | x.val ∈ underlying E} := by
  obtain ⟨t,ht⟩ := Quotient.exists_rep D
  cases t with
  | inl C =>
    obtain ⟨q,hq⟩ := Quotient.exists_rep C
    have hD : {x : VFType (M := M) | x.val ∈ underlying D} = ClosedBallCodes.ball q.val := by
      rw [← ht,← hq]
      rfl
    by_cases hz : q.val 2 = iVFZero
    · obtain ⟨E,hE⟩ := universe_coded (M := M)
      refine ⟨E,?_⟩
      rw [hE]
      ext x
      change (x-c) ∈ {y : VFType (M := M) | y.val ∈ underlying D} ↔ True
      rw [hD,ClosedBallCodes.ball_eq_univ q.val q.property hz]
      exact iff_true_intro (Set.mem_univ _)
    · let a : VFType (M := M) := ⟨q.val 0,q.property 0⟩
      let r : VFType (M := M) := ⟨q.val 1,q.property 1⟩
      have hc : ClosedBallCodes.ball q.val = ValOneEC.closedBall v a (v r) :=
        ClosedBallCodes.ball_eq_closed v hv q.val q.property hz
      obtain ⟨E,hE⟩ := closed_disc_coded v hv (a+c) r
      refine ⟨E,?_⟩
      rw [hE]
      ext x
      change (x-c) ∈ {y : VFType (M := M) | y.val ∈ underlying D} ↔ _
      rw [hD,hc]
      change v ((x-c)-a) ≤ v r ↔ v (x-(a+c)) ≤ v r
      have hd : (x-c)-a = x-(a+c) := by ring
      rw [hd]
  | inr O =>
    obtain ⟨q,hq⟩ := Quotient.exists_rep O
    have hD : {x : VFType (M := M) | x.val ∈ underlying D} = OpenBallCodes.ball q.val := by
      rw [← ht,← hq]
      rfl
    let a : VFType (M := M) := ⟨q.val 0,q.property.1 0⟩
    let r : VFType (M := M) := ⟨q.val 1,q.property.1 1⟩
    have hc : OpenBallCodes.ball q.val = ValOneEC.openBall v a (v r) :=
      OpenBallCodes.ball_eq_open v hv q.val q.property
    obtain ⟨E,hE⟩ := open_disc_coded v hv (a+c) r (OpenBallCodes.radius_ne_zero q.val q.property)
    refine ⟨E,?_⟩
    rw [hE]
    ext x
    change (x-c) ∈ {y : VFType (M := M) | y.val ∈ underlying D} ↔ _
    rw [hD,hc]
    change v ((x-c)-a) < v r ↔ v (x-(a+c)) < v r
    have hd : (x-c)-a = x-(a+c) := by ring
    rw [hd]

/-- Every actual additive coset of a ball subgroup is represented by
one actual ball; equality is equality of its entire raw VF point set. -/
theorem additive_coset_coded (H : AddSubgroup (VFType (M := M)))
    (hH : IsBall (Subtype.val '' (H : Set (VFType (M := M)))))
    (d : VFType (M := M) ⧸ H) :
    ∃ D : Ball M, underlying D =
      Subtype.val '' {x : VFType (M := M) | QuotientAddGroup.mk' H x = d} := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨D,hD⟩ := isBall_coded v hv _ hH
  obtain ⟨c,hc⟩ := QuotientAddGroup.mk'_surjective H d
  obtain ⟨E,hE⟩ := translate_coded v hv D c
  refine ⟨E,?_⟩
  have he (x : VFType (M := M)) : x.val ∈ underlying E ↔ QuotientAddGroup.mk' H x = d := by
    have hsub : (x-c).val ∈ underlying D ↔ x-c ∈ H := by
      have hh := Set.ext_iff.mp hD (x-c)
      change (x-c).val ∈ Subtype.val '' (H : Set (VFType (M := M))) ↔
        (x-c).val ∈ underlying D at hh
      exact hh.symm.trans ⟨fun ⟨y,hy,hyx⟩ => (Subtype.ext hyx : y=x-c) ▸ hy,
        fun hx => ⟨x-c,hx,rfl⟩⟩
    have hh := Set.ext_iff.mp hE x
    change (x-c).val ∈ underlying D ↔ x.val ∈ underlying E at hh
    apply hh.symm.trans
    apply hsub.trans
    rw [← hc]
    exact QuotientAddGroup.eq_iff_sub_mem.symm
  ext a
  constructor
  · intro ha
    let x : VFType (M := M) := ⟨a,underlying_subset_vf E ha⟩
    exact ⟨x,(he x).mp ha,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    exact (he x).mpr hx

/-- The closed alternative stays in the closed chart under translation,
including whole-field and singleton cosets. -/
theorem closed_additive_coset_coded (H : AddSubgroup (VFType (M := M)))
    (hclosed : ∃ C : ClosedBallCodes.ClosedBall M,
      ClosedBallCodes.underlying C = Subtype.val '' (H : Set (VFType (M := M))))
    (d : VFType (M := M) ⧸ H) :
    ∃ C : ClosedBallCodes.ClosedBall M, ClosedBallCodes.underlying C =
      Subtype.val '' {x : VFType (M := M) | QuotientAddGroup.mk' H x = d} := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨C,hC⟩ := hclosed
  obtain ⟨t,ht⟩ := Quotient.exists_rep C
  have htH : ClosedBallCodes.rawBall t.val = Subtype.val '' (H : Set (VFType (M := M))) :=
    (congrArg ClosedBallCodes.underlying ht).trans hC
  have hball := ClosedCosetChoice.closed_cosets_of_code v hv H t htH d
  obtain ⟨q,hq,hqEq⟩ := ClosedBallCodes.exists_code_of_closed v hv _ hball
  refine ⟨Quotient.mk _ (⟨q,hq⟩ : ClosedBallCodes.Code M),?_⟩
  change ClosedBallCodes.rawBall q = _
  ext a
  constructor
  · intro ha
    let x : VFType (M := M) := ⟨a,ha.2.1⟩
    have hh := Set.ext_iff.mp hqEq x
    change QuotientAddGroup.mk' H x = d ↔ x.val ∈ ClosedBallCodes.rawBall q at hh
    exact ⟨x,hh.mpr ha,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    have hh := Set.ext_iff.mp hqEq x
    change QuotientAddGroup.mk' H x = d ↔ x.val ∈ ClosedBallCodes.rawBall q at hh
    exact hh.mp hx

end SpecialTransformations.Section3.BallImaginaries

/- Component: CosetBallFamilies -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.CosetBallFamilies
open GammaParameters BallClassCodes
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {m n : ℕ}

def cosetBody (H : AddSubgroup (VFType (M := M))) (d : VFType (M := M) ⧸ H) : Set M :=
  Subtype.val '' {x : VFType (M := M) | QuotientAddGroup.mk' H x = d}

def badClasses (H : AddSubgroup (VFType (M := M)))
    (f : VFType (M := M) → Set (Fin m → M)) : Set (VFType (M := M) ⧸ H) :=
  {d | ∃ x y, QuotientAddGroup.mk' H x = d ∧ QuotientAddGroup.mk' H y = d ∧ f x ≠ f y}

def exceptionalBalls (H : AddSubgroup (VFType (M := M)))
    (f : VFType (M := M) → Set (Fin m → M)) : Set (BallImaginaries.Ball M) :=
  BallImaginaries.underlying ⁻¹' (cosetBody H '' badClasses H f)

theorem mem_cosetBody (H : AddSubgroup (VFType (M := M))) (d : VFType (M := M) ⧸ H)
    (x : VFType (M := M)) : x.val ∈ cosetBody H d ↔ QuotientAddGroup.mk' H x = d :=
  ⟨fun ⟨y,hy,he⟩ => (Subtype.ext he : y=x) ▸ hy,fun hx => ⟨x,hx,rfl⟩⟩

theorem classBody_eq_cosetBody (H : AddSubgroup (VFType (M := M)))
    (r : VFType (M := M)) :
    classBody (DefinableCosets.relation (Subtype.val '' (H : Set (VFType (M := M))))) r.val =
      cosetBody H (QuotientAddGroup.mk' H r) := by
  ext a
  constructor
  · intro ha
    let x : VFType (M := M) := ⟨a,ha.1⟩
    exact ⟨x,(DefinableCosets.mem_relation H x r).mp ha,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    exact (DefinableCosets.mem_relation H x r).mpr hx

theorem exceptionalBalls_finite (H : AddSubgroup (VFType (M := M)))
    (f : VFType (M := M) → Set (Fin m → M)) (hf : (badClasses H f).Finite) :
    (exceptionalBalls H f).Finite :=
  (hf.image (cosetBody H)).preimage BallImaginaries.underlying_injective.injOn

/-- A code represents an exceptional class exactly when it represents
some entire coset and contains a pair of unequal profile values. -/
theorem exceptional_class_iff (H : AddSubgroup (VFType (M := M)))
    (f : VFType (M := M) → Set (Fin m → M)) (D : (Fin n → M) → Set M) (q : Fin n → M) :
    (∃ d ∈ badClasses H f, cosetBody H d = D q) ↔
      (∃ r : VFType (M := M), D q = classBody
        (DefinableCosets.relation (Subtype.val '' (H : Set (VFType (M := M))))) r.val) ∧
      q ∈ variationCodes D f := by
  constructor
  · rintro ⟨d,⟨x,y,hx,hy,hneq⟩,he⟩
    obtain ⟨r,hr⟩ := QuotientAddGroup.mk'_surjective H d
    refine ⟨⟨r,?_⟩,x,y,?_,?_,hneq⟩
    · rw [classBody_eq_cosetBody,hr]
      exact he.symm
    · rw [← he]
      exact (mem_cosetBody H d x).mpr hx
    · rw [← he]
      exact (mem_cosetBody H d y).mpr hy
  · rintro ⟨⟨r,hr⟩,x,y,hx,hy,hneq⟩
    rw [classBody_eq_cosetBody] at hr
    refine ⟨QuotientAddGroup.mk' H r,⟨x,y,?_,?_,hneq⟩,hr.symm⟩
    · apply (mem_cosetBody H _ x).mp
      rwa [← hr]
    · apply (mem_cosetBody H _ y).mp
      rwa [← hr]

theorem closed_membership_definable_base (B : Base (M := M)) :
    DefinableOverBase B (fun _ : Fin 4 => .vf)
      {z | z (Fin.last 3) ∈ ClosedBallCodes.rawBall (Fin.init z)} := by
  apply real_definableOverBase B
  let p : Parameters B.real := ⟨0,Fin.elim0,(fun _ => .vf),(fun i => i.elim0),(fun i => i.elim0)⟩
  have hG : SpecialTransformations.Section3.DefinableOver B.real (fun _ : Fin 4 => .vf)
      {z | (∀ i, iVF (z i)) ∧ ClosedBallCodes.body.Realize Fin.elim0 z} :=
    ⟨p,ClosedBallCodes.body,ClosedBallCodes.body_sorted,rfl⟩
  convert hG using 1
  ext z
  have ht : ClosedBallCodes.tuple (Fin.init z) (z (Fin.last 3)) = z := by
    funext i
    fin_cases i <;> rfl
  change ((∀ j, iVF (Fin.init z j)) ∧ iVF (z (Fin.last 3)) ∧
    ClosedBallCodes.body.Realize Fin.elim0 (ClosedBallCodes.tuple (Fin.init z) (z (Fin.last 3)))) ↔
    (∀ i, iVF (z i)) ∧ ClosedBallCodes.body.Realize Fin.elim0 z
  rw [ht]
  constructor
  · rintro ⟨hq,hx,hb⟩
    refine ⟨?_,hb⟩
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact hx
    · exact hq j
  · rintro ⟨hs,hb⟩
    exact ⟨fun j => hs j.castSucc,hs (Fin.last 3),hb⟩

/-- Both chart preimages of the entire exceptional family are definable
over B. Equality of whole point sets removes all coset representatives. -/
theorem exceptionalBalls_definable_base (B : Base (M := M))
    (H : AddSubgroup (VFType (M := M)))
    (hH : DefinableAtBase B .vf (Subtype.val '' (H : Set (VFType (M := M)))))
    (f : VFType (M := M) → Set (Fin m → M))
    (hf : ∀ x ys, ys ∈ f x → ∀ i, iRV (ys i))
    (hg : DefinableOverBase B MixedPolynomialSyntax.contextSort (BallFibreConstancy.graph f)) :
    BallImaginaries.FamilyDefinableBase B (exceptionalBalls H f) := by
  let E := DefinableCosets.relation (Subtype.val '' (H : Set (VFType (M := M))))
  have hE := DefinableCosets.relation_definable_gamma_base B _ hH
  have hC := closed_membership_definable_base B
  have hO := real_definableOverBase B _ _ (OpenBallCodes.membership_definable B.real)
  constructor
  · have h := (classCodes_definable_base B ClosedBallCodes.rawBall E hC hE).inter
      (variationCodes_definable_base B ClosedBallCodes.rawBall hC f hf hg)
    convert h using 1
    ext q
    constructor
    · rintro ⟨hq,d,hd,he⟩
      have hh : ∃ d ∈ badClasses H f, cosetBody H d = ClosedBallCodes.rawBall q := ⟨d,hd,he⟩
      obtain ⟨⟨r,hr⟩,hv⟩ := (exceptional_class_iff H f ClosedBallCodes.rawBall q).mp hh
      exact ⟨⟨hq,r.val,r.property,hr⟩,hv⟩
    · rintro ⟨⟨hq,r,hr,he⟩,hv⟩
      have hh := (exceptional_class_iff H f ClosedBallCodes.rawBall q).mpr ⟨⟨⟨r,hr⟩,he⟩,hv⟩
      exact ⟨hq,hh⟩
  · have h := (classCodes_definable_base B OpenBallCodes.rawBall E hO hE).inter
      (variationCodes_definable_base B OpenBallCodes.rawBall hO f hf hg)
    convert h using 1
    ext q
    constructor
    · rintro ⟨hq,d,hd,he⟩
      have hh : ∃ d ∈ badClasses H f, cosetBody H d = OpenBallCodes.rawBall q := ⟨d,hd,he⟩
      obtain ⟨⟨r,hr⟩,hv⟩ := (exceptional_class_iff H f OpenBallCodes.rawBall q).mp hh
      exact ⟨⟨hq.1,r.val,r.property,hr⟩,hv⟩
    · rintro ⟨⟨hq,r,hr,he⟩,hv⟩
      let r' : VFType (M := M) := ⟨r,hr⟩
      have hre : r ∈ classBody E r := (DefinableCosets.mem_relation H r' r').mpr rfl
      have hrB : r ∈ OpenBallCodes.rawBall q := he.symm ▸ hre
      have hh := (exceptional_class_iff H f OpenBallCodes.rawBall q).mpr ⟨⟨r',he⟩,hv⟩
      exact ⟨hrB.1,hh⟩

end SpecialTransformations.Section3.CosetBallFamilies

/- Component: BallCenterRelation -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.BallImaginaries
open GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def centerRelation (A : Set (Ball M)) (c : A → M) : Set (Fin 2 → M) :=
  {z | ∃ D : A, z 0 ∈ underlying D.val ∧ c D = z 1}

/-- The two full chart graphs define one partial center relation on VF,
including agreement when the charts represent the same actual ball. -/
theorem centerRelation_definable_base (B : Base (M := M))
    (A : Set (Ball M)) (c : A → M) (hc : CenterDefinableBase B A c) :
    DefinableOverBase B (fun _ => .vf) (centerRelation A c) := by
  have hC := BallClassCodes.centerKernel_definable_base B ClosedBallCodes.rawBall _
    (CosetBallFamilies.closed_membership_definable_base B) hc.1
  have hO := BallClassCodes.centerKernel_definable_base B OpenBallCodes.rawBall _
    (real_definableOverBase B _ _ (OpenBallCodes.membership_definable B.real)) hc.2
  convert hC.union hO using 1
  ext z
  constructor
  · rintro ⟨D,hx,hd⟩
    rcases family_cases A D with ⟨C,hC⟩ | ⟨O,hO⟩
    · obtain ⟨q,hq⟩ := Quotient.exists_rep C.val
      left
      refine ⟨q.val,?_,q,?_,C,hq,?_⟩
      · have he : ClosedBallCodes.rawBall q.val = underlying D.val :=
          (congrArg ClosedBallCodes.underlying hq).trans (congrArg underlying hC)
        rwa [he]
      · simp only [Fin.init_snoc]
      · simpa only [Fin.snoc_last] using (congrArg c (Subtype.ext hC)).trans hd
    · obtain ⟨q,hq⟩ := Quotient.exists_rep O.val
      right
      refine ⟨q.val,?_,q,?_,O,hq,?_⟩
      · have he : OpenBallCodes.rawBall q.val = underlying D.val :=
          (congrArg OpenBallCodes.underlying hq).trans (congrArg underlying hO)
        rwa [he]
      · simp only [Fin.init_snoc]
      · simpa only [Fin.snoc_last] using (congrArg c (Subtype.ext hO)).trans hd
  · rintro (⟨q,hx,u,hu,C,hC,hc⟩ | ⟨q,hx,u,hu,O,hO,hc⟩)
    · let D : A := ⟨ofClosed C.val,C.property⟩
      refine ⟨D,?_,?_⟩
      · have hqu : u.val = q := by simpa only [Fin.init_snoc] using hu
        have he : ClosedBallCodes.rawBall q = underlying D.val := by
          rw [← hqu]
          exact congrArg ClosedBallCodes.underlying hC
        rwa [← he]
      · simpa only [Fin.snoc_last] using hc
    · let D : A := ⟨ofOpen O.val,O.property⟩
      refine ⟨D,?_,?_⟩
      · have hqu : u.val = q := by simpa only [Fin.init_snoc] using hu
        have he : OpenBallCodes.rawBall q = underlying D.val := by
          rw [← hqu]
          exact congrArg OpenBallCodes.underlying hO
        rwa [← he]
      · simpa only [Fin.snoc_last] using hc

end SpecialTransformations.Section3.BallImaginaries

/- Component: ClosedFamilyCenters -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.BallImaginaries
open GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- A finite family consisting of actual closed balls has a common
finite real-base hitting set, with no saturation or generation premise. -/
theorem centers_of_closed_family (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (A : Set (Ball M)) (hA : A.Finite)
    (hdef : FamilyDefinableBase B A)
    (hclosed : ∀ D : A, ∃ C : ClosedBallCodes.ClosedBall M, ofClosed C = D.val) :
    ∃ f : A → M, (∀ D, f D ∈ underlying D.val) ∧ CenterDefinableBase B A f := by
  obtain ⟨c,hcMem,hcDef⟩ := lemma_3_10_gamma_base h00 B (closedFamily A)
    (closedFamily_finite A hA) hdef.1
  obtain ⟨hcd,hcf⟩ := closed_center_image_definable B (closedFamily A)
    (closedFamily_finite A hA) c hcDef
  have halg : ∀ D : A, ∃ x : VFType (M := M), AlgebraicAtBase B .vf x.val ∧ x.val ∈ underlying D.val := by
    intro D
    obtain ⟨C,hC⟩ := hclosed D
    have hCA : ofClosed C ∈ A := hC.symm ▸ D.property
    let C' : closedFamily A := ⟨C,hCA⟩
    let x : VFType (M := M) := ⟨c C',hcd.proper _ (Set.mem_range_self C')⟩
    refine ⟨x,⟨Set.range c,hcd,hcf,Set.mem_range_self C'⟩,?_⟩
    rw [← hC]
    exact hcMem C'
  letI : Fintype A := hA.fintype
  obtain ⟨R,hR,hhit⟩ := finite_hitting_set_of_algebraic_points B
    (fun D : A => underlying D.val) halg
  exact ⟨familyMean R A,familyMean_mem h00 A R hhit,familyMean_definable_base h00 B A hdef R hR⟩

end SpecialTransformations.Section3.BallImaginaries

/- Component: CosetProfileChoice -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.CosetProfileChoice
open GammaParameters CosetBallFamilies
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {m : ℕ}

/-- The quotient-selection argument consumes a proved center function on
the entire actual exceptional ball family. Final paper theorems below
construct this data from 3.10 or 3.13 rather than assuming choice. -/
theorem choose_profile_of_centers (B : Base (M := M))
    (H : AddSubgroup (VFType (M := M)))
    (f : VFType (M := M) → Set (Fin m → M))
    (hf : ∀ x ys, ys ∈ f x → ∀ i, iRV (ys i))
    (hg : DefinableOverBase B MixedPolynomialSyntax.contextSort (BallFibreConstancy.graph f))
    (hcodes : ∀ d ∈ badClasses H f, ∃ D : BallImaginaries.Ball M,
      BallImaginaries.underlying D = cosetBody H d)
    (c : exceptionalBalls H f → M)
    (hcMem : ∀ D, c D ∈ BallImaginaries.underlying D.val)
    (hcDef : BallImaginaries.CenterDefinableBase B (exceptionalBalls H f) c) :
    ∃ G : (VFType (M := M) ⧸ H) → Set (Fin m → M),
      (∀ d ys, ys ∈ G d → ∀ i, iRV (ys i)) ∧
      DefinableOverBase B MixedPolynomialSyntax.contextSort
        (BallFibreConstancy.graph (fun x => G (QuotientAddGroup.mk' H x))) ∧
      ∀ d, ∃ x : VFType (M := M), QuotientAddGroup.mk' H x = d ∧ f x = G d := by
  let A := exceptionalBalls H f
  let K := BallImaginaries.centerRelation A c
  have hK : DefinableOverBase B (fun _ => .vf) K :=
    BallImaginaries.centerRelation_definable_base B A c hcDef
  have hpoint (D : A) (x : VFType (M := M)) :
      ∃ d ∈ badClasses H f, cosetBody H d = BallImaginaries.underlying D.val ∧
        (x.val ∈ BallImaginaries.underlying D.val ↔ QuotientAddGroup.mk' H x = d) := by
    obtain ⟨d,hd,he⟩ := D.property
    refine ⟨d,hd,he,?_⟩
    rw [← he]
    exact mem_cosetBody H d x
  have hfun (x : VFType (M := M)) (u v : M) (hu : ![x.val,u] ∈ K) (hv : ![x.val,v] ∈ K) : u=v := by
    obtain ⟨D,hxD,hDu⟩ := hu
    obtain ⟨E,hxE,hEv⟩ := hv
    obtain ⟨d,hd,hD,hxd⟩ := hpoint D x
    obtain ⟨e,he,hE,hxe⟩ := hpoint E x
    have hde : d=e := ((hxd.mp hxD).symm.trans (hxe.mp hxE))
    have hDE : D=E := Subtype.ext (BallImaginaries.underlying_injective (by rw [← hD,← hE,hde]))
    exact hDu.symm.trans ((congrArg c hDE).trans hEv)
  have hsome (x : VFType (M := M)) (hx : QuotientAddGroup.mk' H x ∈ badClasses H f) :
      ∃ C : VFType (M := M), ![x.val,C.val] ∈ K ∧ QuotientAddGroup.mk' H C = QuotientAddGroup.mk' H x := by
    obtain ⟨D,hD⟩ := hcodes _ hx
    let D' : A := ⟨D,QuotientAddGroup.mk' H x,hx,hD.symm⟩
    let C : VFType (M := M) := ⟨c D',BallImaginaries.underlying_subset_vf D (hcMem D')⟩
    refine ⟨C,⟨D',?_,rfl⟩,?_⟩
    · change x.val ∈ BallImaginaries.underlying D
      rw [hD]
      exact (mem_cosetBody H _ x).mpr rfl
    · apply (mem_cosetBody H _ C).mp
      rw [← hD]
      exact hcMem D'
  have hnone (x : VFType (M := M)) (hx : QuotientAddGroup.mk' H x ∉ badClasses H f) :
      ∀ t, ![x.val,t] ∉ K := by
    rintro t ⟨D,hxD,_⟩
    obtain ⟨d,hd,he,hxd⟩ := hpoint D x
    exact hx ((hxd.mp hxD).symm ▸ hd)
  let U := BallFibreConstancy.graph f
  let V := ProfileComposition.compose K U
  let g := ProfileComposition.profile V
  have hV : DefinableOverBase B MixedPolynomialSyntax.contextSort V :=
    ProfileComposition.compose_definable_base B K U hK hg
  have hgGraph : BallFibreConstancy.graph g = V :=
    ProfileComposition.graph_profile V (fun z hz => hV.proper z hz 0)
  have hprofile (x : VFType (M := M)) : ProfileComposition.profile U x = f x := by
    ext ys
    change (∃ y : VFType (M := M), y.val = x.val ∧ ys ∈ f y) ↔ ys ∈ f x
    exact ⟨fun ⟨y,hy,hmem⟩ => (Subtype.ext hy : y=x) ▸ hmem,fun h => ⟨x,rfl,h⟩⟩
  have hat (x : VFType (M := M)) :
      (QuotientAddGroup.mk' H x ∉ badClasses H f → g x = f x) ∧
      (∀ C : VFType (M := M), ![x.val,C.val] ∈ K → g x = f C) := by
    constructor
    · intro hx
      exact (ProfileComposition.at_none K U x (hnone x hx)).trans (hprofile x)
    · intro C hC
      exact (ProfileComposition.at_some K U x C hC (fun t ht => hfun x t C.val ht hC)).trans (hprofile C)
  have hrow (x y : VFType (M := M)) (hxy : QuotientAddGroup.mk' H x = QuotientAddGroup.mk' H y) :
      ∀ t, ![x.val,t] ∈ K ↔ ![y.val,t] ∈ K := by
    intro t
    have hh (x y : VFType (M := M)) (he : QuotientAddGroup.mk' H x = QuotientAddGroup.mk' H y)
        (hx : ![x.val,t] ∈ K) : ![y.val,t] ∈ K := by
      obtain ⟨D,hxD,hc⟩ := hx
      obtain ⟨d,hd,hD,hxd⟩ := hpoint D x
      refine ⟨D,?_,hc⟩
      rw [← hD]
      exact (mem_cosetBody H d y).mpr (he.symm.trans (hxd.mp hxD))
    exact ⟨hh x y hxy,hh y x hxy.symm⟩
  have hconstant (x y : VFType (M := M)) (hxy : QuotientAddGroup.mk' H x = QuotientAddGroup.mk' H y) : g x = g y := by
    by_cases hx : QuotientAddGroup.mk' H x ∈ badClasses H f
    · obtain ⟨C,hCx,_⟩ := hsome x hx
      exact (hat x).2 C hCx |>.trans ((hat y).2 C ((hrow x y hxy C.val).mp hCx)).symm
    · have hy : QuotientAddGroup.mk' H y ∉ badClasses H f := hxy ▸ hx
      have hfxy : f x = f y := by
        by_contra hn
        exact hx ⟨x,y,rfl,hxy.symm,hn⟩
      exact ((hat x).1 hx).trans (hfxy.trans ((hat y).1 hy).symm)
  let G : (VFType (M := M) ⧸ H) → Set (Fin m → M) :=
    fun d => g (Classical.choose (QuotientAddGroup.mk'_surjective H d))
  have hG (x : VFType (M := M)) : G (QuotientAddGroup.mk' H x) = g x :=
    hconstant _ x (Classical.choose_spec (QuotientAddGroup.mk'_surjective H (QuotientAddGroup.mk' H x)))
  refine ⟨G,?_,?_,?_⟩
  · intro d ys hys i
    obtain ⟨x,rfl⟩ := QuotientAddGroup.mk'_surjective H d
    rw [hG] at hys
    exact hV.proper (Fin.cons x.val ys) hys i.succ
  · have he : (fun x : VFType (M := M) => G (QuotientAddGroup.mk' H x)) = g := funext hG
    rw [he,hgGraph]
    exact hV
  · intro d
    obtain ⟨x,rfl⟩ := QuotientAddGroup.mk'_surjective H d
    rw [hG]
    by_cases hx : QuotientAddGroup.mk' H x ∈ badClasses H f
    · obtain ⟨C,hC,hCx⟩ := hsome x hx
      exact ⟨C,hCx,((hat x).2 C hC).symm⟩
    · exact ⟨x,rfl,((hat x).1 hx).symm⟩

end SpecialTransformations.Section3.CosetProfileChoice

/- Component: GeneralCosetChoice -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.CosetProfileChoice
open GammaParameters CosetBallFamilies
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {m : ℕ}

/-- Full closed-ball alternative of Lemma 3.18(2), over the original
real/Gamma base, without saturation or additional representatives. -/
theorem lemma_3_18_2_closed_gamma_base (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (H : AddSubgroup (VFType (M := M)))
    (hH : DefinableAtBase B .vf (Subtype.val '' (H : Set (VFType (M := M)))))
    (hclosed : ∃ C : ClosedBallCodes.ClosedBall M,
      ClosedBallCodes.underlying C = Subtype.val '' (H : Set (VFType (M := M))))
    (f : VFType (M := M) → Set (Fin m → M))
    (hf : ∀ x ys, ys ∈ f x → ∀ i, iRV (ys i))
    (hg : DefinableOverBase B MixedPolynomialSyntax.contextSort (BallFibreConstancy.graph f)) :
    ∃ G : (VFType (M := M) ⧸ H) → Set (Fin m → M),
      (∀ d ys, ys ∈ G d → ∀ i, iRV (ys i)) ∧
      DefinableOverBase B MixedPolynomialSyntax.contextSort
        (BallFibreConstancy.graph (fun x => G (QuotientAddGroup.mk' H x))) ∧
      ∀ d, ∃ x : VFType (M := M), QuotientAddGroup.mk' H x = d ∧ f x = G d := by
  let A := exceptionalBalls H f
  have hAfin : A.Finite := exceptionalBalls_finite H f (lemma_3_18_1_gamma_base h00 B H hH f hf hg)
  have hAdef := exceptionalBalls_definable_base B H hH f hf hg
  have hAllClosed (D : A) : ∃ C : ClosedBallCodes.ClosedBall M, BallImaginaries.ofClosed C = D.val := by
    obtain ⟨d,hd,hD⟩ := D.property
    obtain ⟨C,hC⟩ := BallImaginaries.closed_additive_coset_coded H hclosed d
    refine ⟨C,BallImaginaries.underlying_injective ?_⟩
    exact hC.trans hD
  obtain ⟨c,hcMem,hcDef⟩ := BallImaginaries.centers_of_closed_family h00 B A hAfin hAdef hAllClosed
  apply choose_profile_of_centers B H f hf hg ?_ c hcMem hcDef
  intro d hd
  obtain ⟨C,hC⟩ := BallImaginaries.closed_additive_coset_coded H hclosed d
  exact ⟨BallImaginaries.ofClosed C,hC⟩

/-- The (VF,Gamma)-generated alternative of Lemma 3.18(2). Its center
function is constructed by the proved full Lemma 3.13 on the finite actual
exceptional ball family. All finite RV output arities are retained. -/
theorem lemma_3_18_2_generated {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    (H : AddSubgroup (VFType (M := M)))
    (hH : DefinableAtBase B .vf (Subtype.val '' (H : Set (VFType (M := M)))))
    (f : VFType (M := M) → Set (Fin m → M))
    (hf : ∀ x ys, ys ∈ f x → ∀ i, iRV (ys i))
    (hg : DefinableOverBase B MixedPolynomialSyntax.contextSort (BallFibreConstancy.graph f)) :
    ∃ G : (VFType (M := M) ⧸ H) → Set (Fin m → M),
      (∀ d ys, ys ∈ G d → ∀ i, iRV (ys i)) ∧
      DefinableOverBase B MixedPolynomialSyntax.contextSort
        (BallFibreConstancy.graph (fun x => G (QuotientAddGroup.mk' H x))) ∧
      ∀ d, ∃ x : VFType (M := M), QuotientAddGroup.mk' H x = d ∧ f x = G d := by
  let A := exceptionalBalls H f
  have hAfin : A.Finite := exceptionalBalls_finite H f (lemma_3_18_1_gamma_base h00 B H hH f hf hg)
  have hAdef := exceptionalBalls_definable_base B H hH f hf hg
  obtain ⟨c,hcMem,hcDef⟩ := BallImaginaries.lemma_3_13 hκ hs h00 B hsmall hB A hAfin hAdef
  apply choose_profile_of_centers B H f hf hg ?_ c hcMem hcDef
  intro d hd
  exact BallImaginaries.additive_coset_coded H (additive_subgroup_isBall_gamma_base h00 B H hH) d

end SpecialTransformations.Section3.CosetProfileChoice
