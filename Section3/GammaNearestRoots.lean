module

public import Section3.GammaProjection
public import Section3.GammaRealRestriction
public import Section3.GammaSupport
public import Section3.NearestPairs

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Nearest-root selection preserves a genuinely imaginary base. The
containing ball is not a parameter; the distance relation uses only R. -/
theorem nearest_definable_gamma_base (B : Base (M := M)) (R A : Set M)
    (hR : DefinableAt B.real .vf R) (hA : DefinableAtBase B .vf A) :
    DefinableAtBase B .vf
      (@NearestRootSyntax.nearest M (CanonicalStructure.normalize (M := M)) R A) := by
  let P := NearestRootSyntax.normalizedPairs R
  let D : Set (Fin 2 → M) := {z | z 1 ∈ A ∧ z ∈ P}
  have hP := NearestRootSyntax.normalizedPairs_definable B.real R hR
  have hD : DefinableOverBase B (fun _ : Fin 2 => .vf) D :=
    hA.inter_real_preimage (fun _ : Fin 2 => .vf) P hP (fun _ : Fin 1 => 1)
  have hp := hD.image_real (fun _ : Fin 1 => (0 : Fin 2))
  have he : ((fun w : Fin 2 → M => w ∘ (fun _ : Fin 1 => (0 : Fin 2))) '' D) =
      {z : Fin 1 → M | z 0 ∈ @NearestRootSyntax.nearest M
        (CanonicalStructure.normalize (M := M)) R A} := by
    ext z
    constructor
    · rintro ⟨w,hw,he⟩
      have h0 : w 0 = z 0 := congrFun he 0
      change z 0 ∈ @NearestRootSyntax.nearest M (CanonicalStructure.normalize (M := M)) R A
      rw [← h0]
      exact ⟨hw.2.1,w 1,hw.1,hw.2.2.2⟩
    · rintro ⟨hr,a,ha,hnear⟩
      refine ⟨![z 0,a],?_,?_⟩
      · exact ⟨ha,hr,hA.proper a ha,hnear⟩
      · funext i
        fin_cases i
        rfl
  change DefinableOverBase B (fun _ : Fin 1 => .vf) _
  rw [← he]
  exact hp

end SpecialTransformations.Section3.GammaParameters
