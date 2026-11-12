module

public import Section3.GammaCodeDefinability
public import Section3.GammaParameters
public import Section3.DefinableMeans
public import Section3.CanonicalContext
public import Section3.GammaBaseVFAlgebraicity
public import Section3.FiniteAlgebraicCover

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Use the actual normalized-model barycentre; no equality of two field
structures or two Gamma quotient types is asserted. -/
noncomputable def normalizedMean (F : Finset (VFType (M := M))) : M :=
  (@Barycentre.mean M (CanonicalStructure.normalize (M := M))
    (CanonicalStructure.normalized_model hM) F).val

noncomputable def rowFinset {S : Set M} {k : ℕ} (Q : Relation S k 1 (fun _ => .vf))
    (E : Finset (VFType (M := M))) (a : Fin k → M) : Finset (VFType (M := M)) :=
  E.filter (fun x => (a,fun _ : Fin 1 => x.val) ∈ Q.carrier)

/-- Restricting every row to one finite real-base cover gives a uniform
bound without assuming finiteness of the other Gamma fibres. -/
theorem finite_intersection_mean_definableWith (h00 : M ⊨ Axioms.ACVF00)
    {S : Set M} {k : ℕ} (Q : Relation S k 1 (fun _ => .vf))
    (E : Finset (VFType (M := M)))
    (hE : DefinableAt S .vf (Subtype.val '' (E : Set (VFType (M := M)))))
    (γ : Fin k → Values.Gamma (M := M)) :
    DefinableWith S γ (fun _ : Fin 1 => .vf)
      {z | z 0 = normalizedMean (rowFinset Q E (rawTuple (representatives γ)))} := by
  let U := Q.carrier
  let G := rowFinset Q E
  let V : Set M := Subtype.val '' (E : Set (VFType (M := M)))
  let N := CanonicalStructure.normalize (M := M)
  letI := sM
  have hN : @Theory.Model LRV M N Axioms.ACVF := CanonicalStructure.normalized_model hM
  have h00N : @Theory.Model LRV M N Axioms.ACVF00 := normalized_model00 h00
  have hEd := ((definableAt_iff_normalized_raw S .vf _).mp hE).1
  have hQd := Q.definable
  have hGd : @RawClosure.Tuple.RelationDefinable M N k S
      (@Barycentre.finiteFibreRelation M N k G) := by
    letI := N
    have he := hEd.preimage_comp (Sum.inr : Fin 1 → Fin k ⊕ Fin 1)
    change S.Definable LRV {z : Fin k ⊕ Fin 1 → M |
      (z ∘ Sum.inl,z (.inr 0)) ∈ @Barycentre.finiteFibreRelation M N k G}
    convert hQd.inter he using 1
    ext z
    change (∃ x ∈ G (z ∘ Sum.inl), x.val = z (.inr 0)) ↔
      ((z ∘ Sum.inl,z ∘ Sum.inr) ∈ U ∧
        z (.inr 0) ∈ V)
    constructor
    · rintro ⟨x,hx,hv⟩
      obtain ⟨hxE,hxQ⟩ := Finset.mem_filter.mp hx
      have ht : (fun _ : Fin 1 => x.val) = z ∘ Sum.inr := by
        funext i; fin_cases i; exact hv
      exact ⟨ht ▸ hxQ,x,hxE,hv⟩
    · rintro ⟨hxQ,x,hxE,hv⟩
      have ht : (fun _ : Fin 1 => x.val) = z ∘ Sum.inr := by
        funext i; fin_cases i; exact hv
      exact ⟨x,Finset.mem_filter.mpr ⟨hxE,ht.symm ▸ hxQ⟩,hv⟩
  let g (a : Fin k → M) : M := normalizedMean (G a)
  have hg : @Set.DefinableFun M LRV N (Fin k) S g :=
    @Barycentre.mean_definable M N hN k h00N S G hGd E.card
      (fun a => Finset.card_filter_le _ _)
  have hp := proper_normalized_definable (M := M) S (n := k)
  have hv := ((definableAt_iff_normalized_raw S .vf {x | iVF x}).mp
    (definableAt_sort S .vf)).1
  let P : Relation S k 1 (fun _ => .vf) :=
    { carrier := {p | Proper p.1 ∧ iVF (p.2 0) ∧ g p.1 = p.2 0}
      definable := by
        letI := N
        have hi : S.DefinableMap LRV (fun z : Fin k ⊕ Fin 1 → M => z ∘ Sum.inl) :=
          fun i => Set.DefinableFun.proj LRV
        have he := (hg.comp hi).ofPred_eq
          (Set.DefinableFun.proj (L := LRV) (A := S) (i := Sum.inr 0))
        have hproper := hp.preimage_comp (Sum.inl : Fin k → Fin k ⊕ Fin 1)
        have hsort := hv.preimage_comp (Sum.inr : Fin 1 → Fin k ⊕ Fin 1)
        convert hproper.inter (hsort.inter he) using 1
        ext z
        rfl
      proper := by
        intro p hp
        refine ⟨hp.1,?_⟩
        intro i; fin_cases i; exact hp.2.1
      invariant := by
        intro t u htu b
        have hG : G (rawTuple t) = G (rawTuple u) := by
          apply Finset.ext
          intro x
          simp only [G,rowFinset,Finset.mem_filter]
          exact and_congr Iff.rfl (Q.invariant t u htu (fun _ => x.val))
        change (Proper (rawTuple t) ∧ iVF (b 0) ∧ g (rawTuple t) = b 0) ↔
          (Proper (rawTuple u) ∧ iVF (b 0) ∧ g (rawTuple u) = b 0)
        simp only [rawTuple_proper,true_and]
        exact and_congr Iff.rfl (by rw [show g (rawTuple t) = g (rawTuple u) from congrArg normalizedMean hG]) }
  refine ⟨P,?_⟩
  ext z
  change (Proper (rawTuple (representatives γ)) ∧ iVF (z 0) ∧
    g (rawTuple (representatives γ)) = z 0) ↔ z 0 = g (rawTuple (representatives γ))
  simp only [rawTuple_proper,true_and]
  have hsort : iVF (g (rawTuple (representatives γ))) :=
    (@Barycentre.mean M N hN (G (rawTuple (representatives γ)))).property
  exact ⟨fun h => h.2.symm,fun h => ⟨h.symm ▸ hsort,h.symm⟩⟩

/-- The mean of a finite Gamma-base definable VF set is definable over the
same base. The finite real-base cover is constructed, not assumed. -/
theorem finite_mean_definable_base (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
    (F : Finset (VFType (M := M)))
    (hF : DefinableAtBase B .vf (Subtype.val '' (F : Set (VFType (M := M))))) :
    DefinableClosureAtBase B .vf (normalizedMean F) := by
  let A : Set M := Subtype.val '' (F : Set (VFType (M := M)))
  have hAf : A.Finite := F.finite_toSet.image Subtype.val
  have hAcl : ∀ x ∈ A, SpecialTransformations.Section3.AlgebraicAt B.real .vf x := by
    rintro x ⟨a,ha,rfl⟩
    exact (algebraic_vf_iff_real B a).mp ⟨A,hF,hAf,a,ha,rfl⟩
  obtain ⟨E,hEd,hEf,hFE⟩ := finite_definable_cover hAf hAcl
  let E' : Set (VFType (M := M)) := Subtype.val ⁻¹' E
  have hEf' : E'.Finite := hEf.preimage Subtype.val_injective.injOn
  let R := hEf'.toFinset
  have hRE : Subtype.val '' (R : Set (VFType (M := M))) = E := by
    ext x
    constructor
    · rintro ⟨r,hr,rfl⟩
      exact hEf'.mem_toFinset.mp hr
    · intro hx
      let r : VFType (M := M) := ⟨x,hEd.2 hx⟩
      exact ⟨r,hEf'.mem_toFinset.mpr hx,rfl⟩
  have hRd : DefinableAt B.real .vf (Subtype.val '' (R : Set (VFType (M := M)))) := hRE.symm ▸ hEd
  obtain ⟨k,γ,hγ,Q,hQA⟩ := hF
  have hrow : rowFinset Q R (rawTuple (representatives γ)) = F := by
    apply Finset.ext
    intro x
    have hQx : (rawTuple (representatives γ),fun _ : Fin 1 => x.val) ∈ Q.carrier ↔ x.val ∈ A :=
      Set.ext_iff.mp hQA (fun _ => x.val)
    constructor
    · intro hx
      obtain ⟨_,hxQ⟩ := Finset.mem_filter.mp hx
      obtain ⟨y,hy,he⟩ := hQx.mp hxQ
      exact (Subtype.ext he : y = x) ▸ hy
    · intro hx
      have hxA : x.val ∈ A := ⟨x,hx,rfl⟩
      exact Finset.mem_filter.mpr ⟨hEf'.mem_toFinset.mpr (hFE hxA),hQx.mpr hxA⟩
  have hm := finite_intersection_mean_definableWith h00 Q R hRd γ
  rw [hrow] at hm
  exact ⟨k,γ,hγ,hm⟩

end SpecialTransformations.Section3.GammaParameters
