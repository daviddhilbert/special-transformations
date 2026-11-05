import Mathlib
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
namespace SpecialTransformations.Section3
variable {K : Type} [Field K]

noncomputable def relativeTrdeg (E F : Subfield K) (h : E ≤ F) : Cardinal :=
  letI := (Subfield.inclusion h).toAlgebra
  Algebra.trdeg E F

theorem relativeTrdeg_eq_of_algebraic (E F G : Subfield K) (hEF : E ≤ F) (hFG : F ≤ G)
    (halg : ∀ x ∈ G, IsAlgebraic F x) :
    relativeTrdeg E F hEF = relativeTrdeg E G (hEF.trans hFG) := by
  letI := (Subfield.inclusion hEF).toAlgebra
  letI := (Subfield.inclusion hFG).toAlgebra
  letI := (Subfield.inclusion (hEF.trans hFG)).toAlgebra
  letI : IsScalarTower E F G := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let i : G →ₐ[F] K := { G.subtype with commutes' := fun _ => rfl }
  haveI : Algebra.IsAlgebraic F G :=
    ⟨fun x => (isAlgebraic_algHom_iff i Subtype.val_injective).mp (halg x.val x.property)⟩
  change Algebra.trdeg E F = Algebra.trdeg E G
  have h := trdeg_add_eq E F (A := G)
  simpa only [trdeg_eq_zero, add_zero] using h

end SpecialTransformations.Section3
