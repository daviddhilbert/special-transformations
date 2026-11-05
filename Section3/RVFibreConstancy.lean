import Section3.MixedRootFree
import Section3.BallGeometry
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.RVFibreConstancy
open MixedPolynomialSyntax
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {m : ℕ}

def domain (B : Set M) : Set (VFType (M := M)) := {x | iRv x.val ∈ B}

def graph (B : Set M) (f : domain B → Fin m → M) : Set (Fin (m + 1) → M) :=
  {z | ∃ a : domain B, a.val.val = z 0 ∧ f a = Fin.tail z}

omit hM in
theorem mem_graph (B : Set M) (f : domain B → Fin m → M) (a : domain B) :
    Fin.cons a.val.val (f a) ∈ graph B f := ⟨a, rfl, rfl⟩

/-- Corollary 3.12, strengthened to all ACVF models. A full original-base
sorted graph suffices. The finite obstacle set is uniform in all RV outputs;
no saturation, characteristic-zero or definable-choice premise is needed. -/
theorem corollary_3_12 (S B : Set M) (f : domain B → Fin m → M)
    (hf : ∀ a i, iRV (f a i))
    (hgraph : DefinableOver S contextSort (graph B f)) :
    {t : M | t ∈ B ∧ ∃ a b : domain B,
      iRv a.val.val = t ∧ iRv b.val.val = t ∧ f a ≠ f b}.Finite := by
  obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨R, hR, hRdef, hO, hC⟩ := mixed_finite_definable_obstacles v hv S (graph B f) hgraph
  have hfin : (iRv '' (Subtype.val '' (R : Set (VFType (M := M))))).Finite :=
    (R.finite_toSet.image Subtype.val).image iRv
  apply hfin.subset
  rintro t ⟨htB, a, b, ha, hb, hne⟩
  by_contra hnot
  by_cases ht0 : t = iRVZero
  · have ha0 : a.val = (0 : VFType (M := M)) :=
      (CanonicalRV.encodedRv_zero_iff a.val).mp (ha.trans ht0)
    have hb0 : b.val = (0 : VFType (M := M)) :=
      (CanonicalRV.encodedRv_zero_iff b.val).mp (hb.trans ht0)
    exact hne (congrArg f (Subtype.ext (ha0.trans hb0.symm)))
  · let c : VFType (M := M) := a.val
    have hc0 : c ≠ 0 := by
      intro he
      exact ht0 (ha.symm.trans ((CanonicalRV.encodedRv_zero_iff c).mpr he))
    let ρ : Balls.Radius Γ := ↑(OrderDual.toDual (v c))
    have hball : Balls.rvFibre (CanonicalRV.encodedRv c) = Balls.openDisc v c ρ :=
      Balls.rvFibre_eq_openDisc v hv c hc0
    have hmem (x : VFType (M := M)) (hx : iRv x.val = t) : x ∈ Balls.openDisc v c ρ := by
      rw [← hball]
      change iRv x.val = iRv c.val
      exact hx.trans ha.symm
    have havoid : ∀ r ∈ R, r ∉ Balls.openDisc v c ρ := by
      intro r hr hrd
      rw [← hball] at hrd
      have he : iRv r.val = t := hrd.trans ha
      exact hnot ⟨r.val, ⟨r, hr, rfl⟩, he⟩
    have he := (hO c ρ havoid a.val (hmem a.val ha) b.val (hmem b.val hb) (f a) (hf a)).mp
      (mem_graph B f a)
    obtain ⟨b', hbb', hfb'⟩ := he
    have hEq : b' = b := Subtype.ext (Subtype.ext hbb')
    have hfb : f b = f a := by simpa only [hEq, Fin.tail_cons] using hfb'
    exact hne hfb.symm

end SpecialTransformations.Section3.RVFibreConstancy

namespace SpecialTransformations.Section3
export RVFibreConstancy (corollary_3_12)
end SpecialTransformations.Section3
