import Section3.RVUnaryLift
import Section3.FiniteBallBasis
import Section3.RadialBalls
import Section3.ValueQuotient
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Away from finitely many RV classes, an RV-definable set is radial on
each value fibre. The basis centers are not adjoined as S parameters. -/
theorem rv_set_finite_angular_exceptions (S A : Set M) (hA : DefinableAt S .rv A) :
    ∃ T : Set M, T.Finite ∧ (∀ t ∈ T, iRV t) ∧
      ∀ t u : CanonicalRV.RVSort M, Values.vrv t = Values.vrv u →
        t.val ∉ T → u.val ∉ T → (t.val ∈ A ↔ u.val ∈ A) := by
  obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  let U : Set M := {x | iVF x ∧ iRv x ∈ A}
  have hU : DefinableAt S .vf U := hA.rv_preimage
  obtain ⟨F, hF, hdet⟩ := BooleanCombinations.finite_basis hU.isBoolComb_balls
  let z : M := (0 : VFType (M := M)).val
  let τ (B : F) : M := if h : z ∈ B.val then iRVZero else
    Classical.choose (ball_avoiding_zero_rv v hv B.val (hF B.val B.property) h)
  have hτ (B : F) (hz : z ∉ B.val) :
      iRV (τ B) ∧ ∀ x : VFType (M := M), x.val ∈ B.val → iRv x.val = τ B := by
    dsimp only [τ]
    rw [dif_neg hz]
    exact Classical.choose_spec (ball_avoiding_zero_rv v hv B.val (hF B.val B.property) hz)
  let T := Set.range τ
  have hT : T.Finite := Set.finite_range τ
  have hTRV : ∀ t ∈ T, iRV t := by
    rintro t ⟨B, rfl⟩
    by_cases hz : z ∈ B.val
    · simp only [τ, dif_pos hz]
      exact rv_zero_mem hM
    · exact (hτ B hz).1
  refine ⟨T, hT, hTRV, ?_⟩
  intro t u htu ht hu
  obtain ⟨x, hx⟩ := CanonicalRV.encodedRv_surjective t
  obtain ⟨y, hy⟩ := CanonicalRV.encodedRv_surjective u
  have hx' : iRv x.val = t.val := congrArg Subtype.val hx
  have hy' : iRv y.val = u.val := congrArg Subtype.val hy
  have hvxy : v x = v y := (Values.vf_value_eq_iff v hv x y).mp (by rw [hx, hy]; exact htu)
  have hpattern : ∀ B ∈ F, x.val ∈ B ↔ y.val ∈ B := by
    intro B hB
    by_cases hz : z ∈ B
    · exact ball_zero_radial v hv B (hF B hB) hz x y hvxy
    · have hxB : x.val ∉ B := by
        intro hxB
        have hc := (hτ ⟨B, hB⟩ hz).2 x hxB
        exact ht ⟨⟨B, hB⟩, hc.symm.trans hx'⟩
      have hyB : y.val ∉ B := by
        intro hyB
        have hc := (hτ ⟨B, hB⟩ hz).2 y hyB
        exact hu ⟨⟨B, hB⟩, hc.symm.trans hy'⟩
      exact iff_of_false hxB hyB
  have he := hdet x.val y.val hpattern
  change (iVF x.val ∧ iRv x.val ∈ A) ↔ (iVF y.val ∧ iRv y.val ∈ A) at he
  rw [and_iff_right x.property, and_iff_right y.property, hx', hy'] at he
  exact he

end SpecialTransformations.Section3
