import Section5.GammaInvariantLogic
import Section5.GammaLift
import Section4.VFDimensionRank
import Section5.Surjectivity

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section5

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

private theorem rank_union_gamma_codes {d n : ℕ} (S : Set M)
    (t : Fin d → GammaParameters.Code (M := M)) (p : Fin n → VF (M := M)) :
    @vfTupleTrdeg M N hN (S ∪ Set.range (GammaParameters.rawTuple t)) n p =
      @vfTupleTrdeg M N hN S n p := by
  letI : LRV.Structure M := N
  letI : M ⊨ Axioms.ACVF := hN
  have ht : ∀ x ∈ Set.range (@GammaParameters.rawTuple M sM d t), iRV x := by
    rintro _ ⟨i, rfl⟩
    exact (t i).val.property
  let q : Fin n → VFType (M := M) := p
  exact congrArg (fun E : Subfield (VFType (M := M)) =>
    relativeTrdeg E (tupleField E q) (le_tupleField E q))
    (vfParameterField_union_rv S _ ht)

theorem finiteRVFibres_of_gammaIso {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    {n m k l : ℕ} {A : Set (Point (M := M) n m)} {D : Set (Point (M := M) k l)}
    (e : GammaIso B A D)
    (hRank : ∀ p ∈ A, @vfTupleTrdeg M N hN B.real n p.1 ≤ (k : Cardinal))
    (hfin : ∀ x : Fin n → VF (M := M), {t : Fin m → RV (M := M) | (x, t) ∈ A}.Finite) :
    ∀ x : Fin k → VF (M := M), {t : Fin l → RV (M := M) | (x, t) ∈ D}.Finite := by
  obtain ⟨d, t, hg⟩ := e.graph.real_specialize
  let T := B.real ∪ Set.range (GammaParameters.rawTuple t)
  let P := pointSpace (M := M) n m
  let Q := pointSpace (M := M) k l
  have hA : SetDefinable P T A := by
    have h := @Space.RelationDefinable.exists_right LRV M N P Q _ _ hg
    convert h using 1
    ext p
    exact ⟨fun hp => ⟨(e.equiv ⟨p, hp⟩).val, ⟨p, hp⟩, rfl, rfl⟩,
      fun ⟨_, a, ha, _⟩ => ha ▸ a.property⟩
  have hD : SetDefinable Q T D := by
    have hg' := @Space.RelationDefinable.swap LRV M N P Q _ _ hg
    have h := @Space.RelationDefinable.exists_right LRV M N Q P _ _ hg'
    convert h using 1
    ext q
    constructor
    · intro hq
      let a := e.equiv.symm ⟨q, hq⟩
      exact ⟨a.val, a, rfl, congrArg Subtype.val (e.equiv.apply_symm_apply ⟨q, hq⟩)⟩
    · rintro ⟨_, a, _, he⟩
      exact he ▸ (e.equiv a).property
  let A' : PresentedSet P T := PresentedSet.mk A hA
  let D' : PresentedSet Q T := PresentedSet.mk D hD
  let f : Map A' D' := Map.mk e.equiv hg
  let g := rawPointMap A'
  let g' := Map.toImage g
  have hg' : Function.Bijective g' := ⟨
    fun _ _ he => Subtype.ext (congrArg (fun z : Map.image g => z.val) he),
    fun ⟨_, a, ha⟩ => ⟨a, Subtype.ext ha⟩⟩
  have hGA : carrier (Map.image g) = A := by
    ext p
    exact ⟨fun ⟨a, ha⟩ => ha ▸ a.property, fun hp => ⟨⟨p, hp⟩, rfl⟩⟩
  have hsmallT : Cardinal.mk T < κ := small_union_range hκ B.real hsmall
    (GammaParameters.rawTuple t)
  let r := Map.comp f (Map.inverse g' hg')
  have hr : Function.Bijective r := e.equiv.bijective.comp (Equiv.ofBijective g' hg').symm.bijective
  have hRank' (p : Map.image g) : @vfTupleTrdeg M N hN T n p.val.1 ≤ (k : Cardinal) := by
    rw [rank_union_gamma_codes B.real t]
    exact hRank p.val (hGA ▸ p.property)
  let Δ := @Section4.gammaSpace M sM hM
  have hΔ : @Space.RVCoded M N Δ := @gammaSpace_rvCoded M sM hM
  let hsN := hs.normalize
  have hd := @vfDim_le_of_point_trdeg M N hN κ hsN T hsmallT Δ n m (Map.image g) k hRank'
  have hfin' : ∀ x : Fin n → VF (M := M),
      {t : Fin m → RV (M := M) | (x, t) ∈ carrier (Map.image g)}.Finite := by
    rwa [hGA]
  let O : normalizedVFFiniteObject Δ T k := by
    letI : LRV.Structure M := N
    exact ⟨⟨⟨(n, m), DefinableGeometry.Map.image g⟩, hd⟩, hfin'⟩
  exact finite_fibres_of_presentation hκ hs hsmallT Δ hΔ k O D' r hr

end SpecialTransformations.Section5
