import Section3.AngularPattern
import Section3.InfiniteValueFibres
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.Values
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def fibre (A : Set M) (γ : Gamma (M := M)) : Set (CanonicalRV.RVSort M) :=
  {t | vrv t = γ.val ∧ t.val ∈ A}

def finiteNonemptyValues (A : Set M) : Set (Gamma (M := M)) :=
  {γ | (fibre A γ).Nonempty ∧ (fibre A γ).Finite}

/-- The finite-value fibres that are nonempty and finite form a finite set.
The original S occurs only in A's definability; no value representatives
or Boolean-basis centers are added as named parameters. -/
theorem finite_nonempty_values_finite (h00 : M ⊨ Axioms.ACVF00)
    (S A : Set M) (hA : DefinableAt S .rv A) : (finiteNonemptyValues A).Finite := by
  obtain ⟨T, hT, hTRV, hpattern⟩ := rv_set_finite_angular_exceptions S A hA
  let T' : Set (CanonicalRV.RVSort M) := {t | t.val ∈ T}
  have hT' : T'.Finite := hT.preimage Subtype.val_injective.injOn
  have hvals : (vrv '' T').Finite := hT'.image vrv
  have hsub : Subtype.val '' finiteNonemptyValues A ⊆ vrv '' T' := by
    rintro γ ⟨g, ⟨hne, hfin⟩, rfl⟩
    by_contra hnot
    obtain ⟨t, htγ, htA⟩ := hne
    have htT : t.val ∉ T := fun h => hnot ⟨t, h, htγ⟩
    have hginf := infinite_gamma_fibre h00 g
    have hremove : ({t : CanonicalRV.RVSort M | vrv t = g.val} \ fibre A g).Nonempty :=
      (hginf.sdiff hfin).nonempty
    obtain ⟨u, huγ, huA⟩ := hremove
    have huT : u.val ∉ T := fun h => hnot ⟨u, h, huγ⟩
    have huA' : u.val ∉ A := fun h => huA ⟨huγ, h⟩
    exact huA' ((hpattern t u (htγ.trans huγ.symm) htT huT).mp htA)
  exact (hvals.subset hsub).of_finite_image Subtype.val_injective.injOn

/-- A fixed natural bound on every finite non-infinity fibre. This bound
will make finite nonempty fibres definable using first-order counting. -/
theorem finite_value_fibres_uniform_bound (h00 : M ⊨ Axioms.ACVF00)
    (S A : Set M) (hA : DefinableAt S .rv A) :
    ∃ N : ℕ, ∀ γ : Gamma (M := M), (fibre A γ).Finite → (fibre A γ).ncard ≤ N := by
  obtain ⟨T, hT, hTRV, hpattern⟩ := rv_set_finite_angular_exceptions S A hA
  let T' : Set (CanonicalRV.RVSort M) := {t | t.val ∈ T}
  have hT' : T'.Finite := hT.preimage Subtype.val_injective.injOn
  refine ⟨T'.ncard, ?_⟩
  intro γ hfin
  have hsub : fibre A γ ⊆ T' := by
    intro t ht
    by_contra htT
    have hginf := infinite_gamma_fibre h00 γ
    have hremove := (hginf.sdiff (hfin.union hT')).nonempty
    obtain ⟨u, huγ, hu⟩ := hremove
    have huA : u.val ∉ A := fun h => hu (Or.inl ⟨huγ, h⟩)
    have huT : u.val ∉ T := fun h => hu (Or.inr h)
    exact huA ((hpattern t u (ht.1.trans huγ.symm) htT huT).mp ht.2)
  exact Set.ncard_le_ncard hsub hT'

end SpecialTransformations.Section3.Values
