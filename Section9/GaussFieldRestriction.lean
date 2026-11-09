import Section9.GaussDerivative

/-! The Gauss bound survives restriction to a graph field containing
the coefficient field and the chosen tuple. -/

open MvPolynomial

namespace SpecialTransformations.Section9

variable {K Γ ι : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

def graphCoefficientEquiv (E L : Subfield K) (h : E ≤ L) : E.comap L.subtype ≃+* E where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, h x.property⟩, x.property⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv x := Subtype.ext rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem isGaussEvaluation_comap_subfield (v : Valuation K Γ) (E L : Subfield K) (h : E ≤ L)
    (x : ι → L) (hGauss : IsGaussEvaluation (E := E) v (L.subtype ∘ x)) :
    IsGaussEvaluation (E := E.comap L.subtype) (v.comap L.subtype) x := by
  let e := graphCoefficientEquiv E L h
  let g := L.subtype
  intro P d hd
  let Q := P.map e.toRingHom
  have hQ : d ∈ Q.support := by
    rw [mem_support_iff, coeff_map]
    exact fun h => (mem_support_iff.mp hd) (e.injective (h.trans (map_zero e).symm))
  have he : g.comp (aeval x).toRingHom = (aeval (g ∘ x)).toRingHom.comp (map e.toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_C, map_C]
      rfl
    · intro i
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X,
        map_X, Function.comp_apply]
  have heval : g (aeval x P) = aeval (g ∘ x) Q := RingHom.congr_fun he P
  have hc : Q.coeff d = e (P.coeff d) := coeff_map _ _ _
  have hv := hGauss Q d hQ
  rw [hc, ← heval] at hv
  exact hv

end SpecialTransformations.Section9
