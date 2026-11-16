module

public import Section4.DefinableGeometry

@[expose] public section

/-! Logical closure for an open-chart certificate with scale and
coefficient variables. The arithmetic tests are interpreted in the
residue field before using this lemma. -/

open FirstOrder FirstOrder.Language

namespace SpecialTransformations.Section9

variable {L : Language} {M : Type} [L.Structure M] {S : Set M}
variable {α β γ : Type} [Finite γ]

def rawResidueChartCertificate
    (C : Set (α ⊕ γ → M)) (V : Set (β → M))
    (P Q D R : Set (β ⊕ γ → M)) : Set (α ⊕ β → M) :=
  {w | w ∘ Sum.inr ∈ V ∧
    (∃ z : γ → M, Sum.elim (w ∘ Sum.inr) z ∈ D) ∧
    ∀ z : γ → M,
      (Sum.elim (w ∘ Sum.inl) z ∈ C →
        Sum.elim (w ∘ Sum.inr) z ∈ P ∧
        (Sum.elim (w ∘ Sum.inr) z ∈ D →
          Sum.elim (w ∘ Sum.inr) z ∈ Q ∧ Sum.elim (w ∘ Sum.inr) z ∈ R)) ∧
      (Sum.elim (w ∘ Sum.inr) z ∈ P ∧ Sum.elim (w ∘ Sum.inr) z ∈ Q →
        Sum.elim (w ∘ Sum.inl) z ∈ C)}

theorem rawResidueChartCertificate_definable
    {C : Set (α ⊕ γ → M)} {V : Set (β → M)} {P Q D R : Set (β ⊕ γ → M)}
    (hC : S.Definable L C) (hV : S.Definable L V) (hP : S.Definable L P)
    (hQ : S.Definable L Q) (hD : S.Definable L D) (hR : S.Definable L R) :
    S.Definable L (rawResidueChartCertificate C V P Q D R) := by
  let i : α ⊕ γ → (α ⊕ β) ⊕ γ := Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr
  let j : β ⊕ γ → (α ⊕ β) ⊕ γ := Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr
  let hC' := hC.preimage_comp i
  let hP' := hP.preimage_comp j
  let hQ' := hQ.preimage_comp j
  let hD' := hD.preimage_comp j
  let hR' := hR.preimage_comp j
  have h := (hV.preimage_comp (Sum.inr : β → α ⊕ β)).inter
    (hD'.exists_of_finite.inter
      ((hC'.himp (hP'.inter (hD'.himp (hQ'.inter hR')))).inter
        ((hP'.inter hQ').himp hC')).forall_of_finite)
  convert h using 1
  ext w
  have hi (u : γ → M) : Sum.elim w u ∘ i = Sum.elim (w ∘ Sum.inl) u := by
    funext z
    cases z <;> rfl
  have hj (u : γ → M) : Sum.elim w u ∘ j = Sum.elim (w ∘ Sum.inr) u := by
    funext z
    cases z <;> rfl
  simp [rawResidueChartCertificate, hi, hj]

theorem rawResidueChartCertificate_projection_definable {C : Set (α ⊕ γ → M)}
    {V : Set (β → M)} {P Q D R : Set (β ⊕ γ → M)} [Finite β]
    (hC : S.Definable L C) (hV : S.Definable L V) (hP : S.Definable L P)
    (hQ : S.Definable L Q) (hD : S.Definable L D) (hR : S.Definable L R) :
    S.Definable L {a | ∃ c : β → M, Sum.elim a c ∈ rawResidueChartCertificate C V P Q D R} :=
  (rawResidueChartCertificate_definable hC hV hP hQ hD hR).exists_of_finite

end SpecialTransformations.Section9
