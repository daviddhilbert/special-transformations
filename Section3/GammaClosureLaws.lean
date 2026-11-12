module

public import Section3.GammaBaseTools
public import Section3.GammaProjection

@[expose] public section

/- Component: BaseTupleOperations -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem DefinableOverBase.finite_iInter {B : Base (M := M)} {n : ℕ}
    {sn : Fin n → SortTag} {ι : Type} (s : Finset ι) (F : ι → Set (Fin n → M))
    (hF : ∀ i ∈ s, DefinableOverBase B sn (F i)) :
    DefinableOverBase B sn {z | z ∈ sortedUniverse sn ∧ ∀ i ∈ s, z ∈ F i} := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    convert real_definableOverBase B sn (sortedUniverse sn) (sortedUniverse_definable B.real sn) using 1
    ext z
    simp
  | @insert a s ha ih =>
    have h := (hF a (Finset.mem_insert_self a s)).inter
      (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))
    convert h using 1
    ext z
    simp only [Set.mem_setOf_eq,Set.mem_inter_iff,Finset.mem_insert,forall_eq_or_imp]
    tauto

/-- A finite tuple of actual definable names is definable over the same
imaginary base, with all Gamma supports retained by finite intersections. -/
theorem tuple_singleton_definable_base (B : Base (M := M)) {n : ℕ}
    (sn : Fin n → SortTag) (a : Fin n → M)
    (ha : ∀ i, DefinableClosureAtBase B (sn i) (a i)) :
    DefinableOverBase B sn {a} := by
  let F (i : Fin n) : Set (Fin n → M) := {z | z i = a i ∧ z ∈ sortedUniverse sn}
  have hF (i : Fin n) : DefinableOverBase B sn (F i) :=
    (ha i).preimage_real sn (fun _ : Fin 1 => i)
  have h := DefinableOverBase.finite_iInter Finset.univ F (fun i _ => hF i)
  have hsa (i : Fin n) : sortEval (sn i) (a i) := (ha i).proper (a i) (Set.mem_singleton (a i))
  convert h using 1
  ext z
  change z = a ↔ z ∈ sortedUniverse sn ∧ ∀ i ∈ Finset.univ, z ∈ F i
  constructor
  · rintro rfl
    exact ⟨hsa,fun _ _ => ⟨rfl,hsa⟩⟩
  · rintro ⟨_,hz⟩
    exact funext (fun i => (hz i (Finset.mem_univ i)).1)

theorem gamma_fibre_tuple_definable_base (B : Base (M := M)) {k : ℕ}
    (γ : Fin k → Values.Gamma (M := M))
    (hγ : ∀ i, GammaDefinableClosureAtBase B (γ i)) :
    DefinableOverBase B (fun _ : Fin k => .rv)
      {c | ∀ i, c i ∈ Values.gammaPullback {γ i}} := by
  let F (i : Fin k) : Set (Fin k → M) :=
    {c | c i ∈ Values.gammaPullback {γ i} ∧ c ∈ sortedUniverse (fun _ => .rv)}
  have hF (i : Fin k) : DefinableOverBase B (fun _ => .rv) (F i) :=
    (hγ i).preimage_real (fun _ => .rv) (fun _ : Fin 1 => i)
  have h := DefinableOverBase.finite_iInter Finset.univ F (fun i _ => hF i)
  convert h using 1
  ext c
  change (∀ i, c i ∈ Values.gammaPullback {γ i}) ↔
    c ∈ sortedUniverse (fun _ => .rv) ∧ ∀ i ∈ Finset.univ, c ∈ F i
  constructor
  · intro hc
    have hs (i : Fin k) : iRV (c i) := (hc i).choose
    exact ⟨hs,fun i _ => ⟨hc i,hs⟩⟩
  · rintro ⟨_,hc⟩
    exact fun i => (hc i (Finset.mem_univ i)).1

end SpecialTransformations.Section3.GammaParameters

/- Component: GammaDefinableParameterElimination -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem Relation.finite_real_support {S : Set M} {k n : ℕ} {sn : Fin n → SortTag}
    (Q : Relation S k n sn) :
    ∃ F : Finset M, (F : Set M) ⊆ S ∧
      ∃ R : Relation (F : Set M) k n sn, R.carrier = Q.carrier := by
  have hd := Q.definable
  letI := CanonicalStructure.normalize (M := M)
  obtain ⟨F,hFS,hF⟩ := Set.definable_iff_finitely_definable.mp hd
  letI := sM
  exact ⟨F,hFS,⟨Q.carrier,hF,Q.proper,Q.invariant⟩,rfl⟩

/-- Transitivity for genuine imaginary parameters. Each real name is
replaced by its singleton and each Gamma name by its entire value fibre;
finite support is promoted before these relations are composed. -/
theorem DefinableOverBase.eliminate_definable_params {B C : Base (M := M)}
    {n : ℕ} {sn : Fin n → SortTag} {U : Set (Fin n → M)}
    (hU : DefinableOverBase C sn U)
    (hreal : ∀ c ∈ C.real, ∃ σ, DefinableClosureAtBase B σ c)
    (hgamma : ∀ γ ∈ C.gamma, GammaDefinableClosureAtBase B γ) :
    DefinableOverBase B sn U := by
  obtain ⟨k,γ,hγ,Q,rfl⟩ := hU
  obtain ⟨F,hFC,R,hRQ⟩ := Q.finite_real_support
  let eF : F ≃ Fin F.card := F.equivFin
  let a : Fin F.card → M := fun i => (eF.symm i).val
  have haF (i : Fin F.card) : a i ∈ (F : Set M) := (eF.symm i).property
  have hFa : (F : Set M) ⊆ Set.range a := by
    intro c hc
    exact ⟨eF ⟨c,hc⟩,congrArg Subtype.val (eF.symm_apply_apply ⟨c,hc⟩)⟩
  have haC (i : Fin F.card) : a i ∈ C.real := hFC (haF i)
  choose sa hsa using fun i => hreal (a i) (haC i)
  let R' := R.monoReal (show (F : Set M) ⊆ B.real ∪ Set.range a from
    fun c hc => Or.inr (hFa hc))
  obtain ⟨H,hHd,hHi,hHa⟩ := promote_gamma_relation B.real a R'
  let e : Fin F.card ⊕ (Fin k ⊕ Fin n) ≃ Fin (F.card + (k+n)) :=
    (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv
  let ip : Fin F.card → Fin (F.card + (k+n)) := fun i => e (.inl i)
  let ig : Fin k → Fin (F.card + (k+n)) := fun i => e (.inr (.inl i))
  let io : Fin n → Fin (F.card + (k+n)) := fun i => e (.inr (.inr i))
  let st : Fin (F.card + (k+n)) → SortTag :=
    Sum.elim sa (Sum.elim (fun _ => .rv) sn) ∘ e.symm
  let G : Set (Fin (F.card + (k+n)) → M) :=
    {z | (z ∘ ip,z ∘ ig,z ∘ io) ∈ H ∧ z ∈ sortedUniverse st}
  have hG : SpecialTransformations.Section3.DefinableOver B.real st G := by
    have hraw := @Set.Definable.preimage_comp M B.real LRV
      (CanonicalStructure.normalize (M := M))
      (Fin F.card ⊕ (Fin k ⊕ Fin n)) (Fin (F.card + (k+n))) e _ hHd
    have hs := (definableOver_iff_normalized_raw B.real st (sortedUniverse st)).mp
      (sortedUniverse_definable B.real st)
    apply (definableOver_iff_normalized_raw B.real st G).mpr
    refine ⟨?_,fun z hz => hz.2⟩
    letI := CanonicalStructure.normalize (M := M)
    convert hraw.inter hs.1 using 1
    ext z
    rfl
  have hA := (tuple_singleton_definable_base B sa a hsa).preimage_real st ip
  have hC := (gamma_fibre_tuple_definable_base B γ (fun i => hgamma (γ i) (hγ i))).preimage_real st ig
  have hfull := ((real_definableOverBase B st G hG).inter hA).inter hC
  have him := hfull.image_real io
  have hst : st ∘ io = sn := by
    funext i
    simp only [st,io,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inr]
  rw [hst] at him
  convert him using 1
  ext b
  change b ∈ Q.fibre γ ↔ ∃ z,
    ((z ∈ G ∧ (z ∘ ip ∈ ({a} : Set (Fin F.card → M)) ∧ z ∈ sortedUniverse st)) ∧
      ((∀ i, (z ∘ ig) i ∈ Values.gammaPullback {γ i}) ∧ z ∈ sortedUniverse st)) ∧
      z ∘ io = b
  constructor
  · intro hb
    let c := rawTuple (representatives γ)
    have hc : Proper c := rawTuple_proper (representatives γ)
    let z := Sum.elim a (Sum.elim c b) ∘ e.symm
    have hzA : z ∘ ip = a := by
      funext i
      simp only [z,ip,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inl]
    have hzC : z ∘ ig = c := by
      funext i
      simp only [z,ig,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inr,Sum.elim_inl]
    have hzB : z ∘ io = b := by
      funext i
      simp only [z,io,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inr]
    have hzs : z ∈ sortedUniverse st := by
      intro i
      change sortEval (Sum.elim sa (Sum.elim (fun _ => .rv) sn) (e.symm i))
        (Sum.elim a (Sum.elim c b) (e.symm i))
      cases hidx : e.symm i with
      | inl j => exact (hsa j).proper (a j) (Set.mem_singleton (a j))
      | inr j =>
        cases j with
        | inl j => exact (hc j).1
        | inr j => exact Q.fibre_proper γ b hb j
    have hQa : (c,b) ∈ R'.carrier := by
      change (c,b) ∈ R.carrier
      rw [hRQ]
      exact hb
    have hzH : (z ∘ ip,z ∘ ig,z ∘ io) ∈ H := by
      rw [hzA,hzC,hzB]
      exact (hHa c b hc).mpr hQa
    refine ⟨z,⟨⟨⟨hzH,hzs⟩,by rw [hzA]; exact ⟨rfl,hzs⟩⟩,?_⟩,hzB⟩
    refine ⟨?_,hzs⟩
    intro i
    rw [hzC]
    exact ⟨raw_rv (representative (γ i)),raw_ne_zero (representative (γ i)),
      representative_value (γ i)⟩
  · rintro ⟨z,⟨⟨hzG,ha,_⟩,hγz,_⟩,hzb⟩
    have hza : z ∘ ip = a := ha
    have hpc : Proper (z ∘ ig) := fun i => ⟨(hγz i).choose,(hγz i).choose_spec.choose⟩
    let t := ofRaw (z ∘ ig) hpc
    have ht : values t = γ := by
      funext i
      obtain ⟨hr,h0,hval⟩ := hγz i
      exact hval
    have hzH := hzG.1
    rw [hza,hzb] at hzH
    have hR := (hHa (z ∘ ig) b hpc).mp hzH
    have hQ : (z ∘ ig,b) ∈ Q.carrier := by
      change (z ∘ ig,b) ∈ R.carrier at hR
      rwa [hRQ] at hR
    exact (Q.mem_fibre_iff t γ ht b).mpr hQ

end SpecialTransformations.Section3.GammaParameters

/- Component: GammaClosureLaws -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem gamma_name_definable (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ B.gamma) : GammaDefinableClosureAtBase B γ := by
  let R : Relation B.real 1 1 (fun _ => .rv) :=
    { carrier := {p | Same p.1 p.2}
      definable := same_normalized_definable B.real
      proper := fun p hp => ⟨hp.proper_left,fun i => (hp.proper_right i).1⟩
      invariant := by
        intro t u htu b
        by_cases hb : Proper b
        · let v := ofRaw b hb
          have hv : rawTuple v = b := rfl
          change Same (rawTuple t) b ↔ Same (rawTuple u) b
          rw [← hv,same_codes_iff,same_codes_iff,htu]
        · exact iff_of_false (fun h => hb h.proper_right) (fun h => hb h.proper_right) }
  refine ⟨1,![γ],(fun i => by fin_cases i; exact hγ),R,?_⟩
  ext z
  change Same (rawTuple (representatives ![γ])) z ↔ z 0 ∈ Values.gammaPullback {γ}
  constructor
  · intro hz
    have h := hz 0
    let u : Code (M := M) := ⟨⟨z 0,h.2.1.1⟩,h.2.1.2⟩
    have hv : value (representative γ) = value u := (value_eq_iff _ _).mpr h.2.2
    exact ⟨h.2.1.1,h.2.1.2,hv.symm.trans (representative_value γ)⟩
  · rintro ⟨hr,h0,hv⟩
    let u : Code (M := M) := ⟨⟨z 0,hr⟩,h0⟩
    have he : value (representative γ) = value u := (representative_value γ).trans hv.symm
    intro i
    fin_cases i
    exact ⟨⟨raw_rv (representative γ),raw_ne_zero (representative γ)⟩,
      ⟨hr,h0⟩,(value_eq_iff _ _).mp he⟩

theorem subset_closureBase (B : Base (M := M)) :
    B.real ⊆ (closureBase B).real ∧ B.gamma ⊆ (closureBase B).gamma := by
  constructor
  · intro b hb
    rcases TypedModelMap.sort_cover (M := M) b with hv | hr
    · exact ⟨.vf,real_definableAtBase B .vf {b} (definableClosureAt_of_mem hb hv)⟩
    · exact ⟨.rv,real_definableAtBase B .rv {b} (definableClosureAt_of_mem hb hr)⟩
  · exact fun γ hγ => gamma_name_definable B γ hγ

theorem closureBase_mono {B C : Base (M := M)}
    (hr : B.real ⊆ C.real) (hγ : B.gamma ⊆ C.gamma) :
    (closureBase B).real ⊆ (closureBase C).real ∧
      (closureBase B).gamma ⊆ (closureBase C).gamma := by
  constructor
  · rintro b ⟨σ,hb⟩
    exact ⟨σ,hb.mono hr hγ⟩
  · exact fun γ h => h.mono hr hγ

theorem DefinableOverBase.closureBase_iff (B : Base (M := M)) {n : ℕ}
    (sn : Fin n → SortTag) (U : Set (Fin n → M)) :
    DefinableOverBase (closureBase B) sn U ↔ DefinableOverBase B sn U := by
  constructor
  · intro hU
    exact hU.eliminate_definable_params (fun _ h => h) (fun _ h => h)
  · intro hU
    exact hU.mono (subset_closureBase B).1 (subset_closureBase B).2

theorem DefinableAtBase.closureBase_iff (B : Base (M := M))
    (σ : SortTag) (U : Set M) :
    DefinableAtBase (closureBase B) σ U ↔ DefinableAtBase B σ U :=
  DefinableOverBase.closureBase_iff B (fun _ : Fin 1 => σ) {z | z 0 ∈ U}

theorem AlgebraicAtBase.closureBase_iff (B : Base (M := M)) (σ : SortTag) (b : M) :
    AlgebraicAtBase (closureBase B) σ b ↔ AlgebraicAtBase B σ b := by
  constructor
  · rintro ⟨U,hU,hfin,hb⟩
    exact ⟨U,(DefinableAtBase.closureBase_iff B σ U).mp hU,hfin,hb⟩
  · rintro ⟨U,hU,hfin,hb⟩
    exact ⟨U,(DefinableAtBase.closureBase_iff B σ U).mpr hU,hfin,hb⟩

theorem GammaAlgebraicAtBase.closureBase_iff (B : Base (M := M))
    (γ : Values.Gamma (M := M)) :
    GammaAlgebraicAtBase (closureBase B) γ ↔ GammaAlgebraicAtBase B γ := by
  constructor
  · rintro ⟨U,hU,hfin,hγ⟩
    exact ⟨U,(DefinableAtBase.closureBase_iff B .rv _).mp hU,hfin,hγ⟩
  · rintro ⟨U,hU,hfin,hγ⟩
    exact ⟨U,(DefinableAtBase.closureBase_iff B .rv _).mpr hU,hfin,hγ⟩

theorem closureBase_idempotent (B : Base (M := M)) :
    closureBase (closureBase B) = closureBase B := by
  have hr : (closureBase (closureBase B)).real = (closureBase B).real := by
    ext b
    exact exists_congr (fun σ => DefinableAtBase.closureBase_iff B σ {b})
  have hg : (closureBase (closureBase B)).gamma = (closureBase B).gamma := by
    ext γ
    exact DefinableAtBase.closureBase_iff B .rv (Values.gammaPullback {γ})
  cases hC : closureBase (closureBase B)
  cases hB : closureBase B
  simp_all only [Base.mk.injEq,true_and]

end SpecialTransformations.Section3.GammaParameters
