import Section3.NormalizationReduct
import Section3.TupleCompactness
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.ModelTheory
namespace SpecialTransformations.Section3
variable {M : Type} [sM : LRV.Structure M]

theorem Saturated.normalize {κ : Cardinal} (hs : Saturated M κ) :
    @Saturated M (CanonicalStructure.normalize (M := M)) κ := by
  intro α v hsmall n p hp
  let N := CanonicalStructure.normalize (M := M)
  letI := sM
  let S := Set.range v
  have hS : Cardinal.mk S < κ := (Cardinal.mk_range_le (f := v)).trans_lt hsmall
  have hdef (φ : LRV.BoundedFormula α n) : S.Definable LRV
      {x : Fin n → M | @BoundedFormula.Realize LRV M N α n φ v x} := by
    exact (normalization_definableReduct (M := M)).formula S φ (fun _ => v) (fun x => x)
      (fun a => LRV.definableFun_const (Fin n) (Set.mem_range_self a))
      (fun _ => Set.DefinableFun.proj LRV)
  choose θ hθ using fun φ => raw_definable_formula_tuple (hdef φ)
  let q := θ '' p
  let back (ψ : LRV.BoundedFormula S n) : LRV.BoundedFormula α n :=
    if h : ψ ∈ q then Classical.choose h else .falsum
  have hback (ψ : LRV.BoundedFormula S n) (hψ : ψ ∈ q) :
      back ψ ∈ p ∧ θ (back ψ) = ψ := by
    dsimp only [back]
    rw [dif_pos hψ]
    exact Classical.choose_spec hψ
  have hq : FinitelySatisfiable (Subtype.val : S → M) q := by
    intro l hl
    have hlist : ∀ φ ∈ l.map back, φ ∈ p := by
      intro φ hφ
      obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hφ
      exact (hback ψ (hl ψ hψ)).1
    obtain ⟨x, hx⟩ := hp (l.map back) hlist
    refine ⟨x, ?_⟩
    intro ψ hψ
    have hx' := (hθ (back ψ) x).mpr (hx (back ψ) (List.mem_map.mpr ⟨ψ, hψ, rfl⟩))
    rwa [(hback ψ (hl ψ hψ)).2] at hx'
  obtain ⟨x, hx⟩ := hs S Subtype.val hS q hq
  refine ⟨x, ?_⟩
  intro φ hφ
  exact (hθ φ x).mp (hx (θ φ) (Set.mem_image_of_mem θ hφ))

end SpecialTransformations.Section3
