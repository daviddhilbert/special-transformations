module

public import Section6.HenselianElimination
public import Section6.ExpandedLiterals
public import Section6.ExtraSortSemantics
public import Section6.NativeImageTransport

@[expose] public section

/-! Conversion of VF-quantifier-free formulas to the RV fragment in
models that admit a native ACVF envelope. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Milestone0.LRV FirstOrder.Language.sum

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Section6.ExpandedLiterals

open RVTermSupport RVAbstraction ExpandedLogic

variable {E : _root_.FirstOrder.Language.{0, 0}} {V R : Type}
variable {M U : Type} [(Expanded E).Structure M] [LRV.Structure M] [LRV.Structure U]
variable [(LHom.sumInl : LRV →ᴸ Expanded E).IsExpansionOn M] [hU : U ⊨ Axioms.ACVF]

private theorem native_fun (j : M ↪[LRV] U) {k : ℕ} (f : Fn k) (x : Fin k → M) :
    j (Structure.funMap (L := Expanded E) (.inl f) x) =
      Structure.funMap (L := LRV) f (j ∘ x) := by
  have he := (LHom.sumInl : LRV →ᴸ Expanded E).map_onFunction f x
  exact (congrArg j he).trans (j.map_fun f x)

private theorem term_sorted_in_native (j : M ↪[LRV] U)
    (hM : M ⊨ HenselianTheory.expanded E) {I : Type} (s : I → SortTag)
    (a : I → M) (ha : ∀ i, tagEval (E := E) (s i) (a i))
    (t : (Expanded E).Term I) {σ : SortTag} (ht : termSort s t = some σ) :
    tagEval (E := E) σ (t.realize a) := by
  induction t generalizing σ with
  | var i => exact Option.some.inj ht ▸ ha i
  | func f ts ih =>
    obtain ⟨hts, hf⟩ := (termSort_func s f ts).mp ht
    subst σ
    cases f with
    | inl f =>
      apply (NativeImageTransport.sorts_preserved j _ _).mp
      change sortEval (Fn.resSort f) (j (Structure.funMap (L := Expanded E) (.inl f)
        (fun i => (ts i).realize a)))
      rw [native_fun j f]
      exact CanonicalStructure.function_sort hU f _
        (fun i => (NativeImageTransport.sorts_preserved j _ _).mpr (ih i (hts i)))
    | inr f =>
      exact (ExtraSortSemantics.laws_of_henselian_model hM).functions f _
        (fun i => ih i (hts i))

private theorem map_singleton_tuple (f : M → U) (a : M) :
    f ∘ ![a] = ![f a] := by
  funext i
  fin_cases i
  rfl

private theorem map_pair_tuple (f : M → U) (a b : M) :
    f ∘ ![a, b] = ![f a, f b] := by
  funext i
  fin_cases i <;> rfl

private theorem native_vf_eq (j : M ↪[LRV] U) (a b : M)
    (ha : tagEval (E := E) .vf a) (hb : tagEval (E := E) .vf b) :
    a = b ↔
      Structure.funMap (L := Expanded E) (.inl Fn.rvMap)
        ![Structure.funMap (L := Expanded E) (.inl Fn.vfAdd)
          ![a, Structure.funMap (L := Expanded E) (.inl Fn.vfNeg) ![b] ] ] =
      Structure.funMap (L := Expanded E) (.inl Fn.rvZero) Fin.elim0 := by
  let x : VFType (M := U) := ⟨j a, (NativeImageTransport.sorts_preserved j .vf a).mpr ha⟩
  let y : VFType (M := U) := ⟨j b, (NativeImageTransport.sorts_preserved j .vf b).mpr hb⟩
  have h₀ : a = b ↔ x = y := by
    rw [Subtype.ext_iff]
    exact j.injective.eq_iff.symm
  have h₁ : x = y ↔ iRv (x - y).val = iRVZero :=
    ((CanonicalRV.encodedRv_zero_iff (x - y)).trans sub_eq_zero).symm
  refine h₀.trans (h₁.trans ?_)
  rw [← j.injective.eq_iff]
  rw [native_fun (E := E) j .rvMap, native_fun (E := E) j .rvZero,
    map_singleton_tuple]
  rw [show j ∘ (Fin.elim0 : Fin 0 → M) = (Fin.elim0 : Fin 0 → U) from
    Subsingleton.elim _ _]
  rw [native_fun (E := E) j .vfAdd, map_pair_tuple,
    native_fun (E := E) j .vfNeg, map_singleton_tuple] <;> rfl

private theorem realize_func0 {I M : Type} [(Expanded E).Structure M]
    (f : (Expanded E).Functions 0) (v : I → M) :
    (Term.func f Fin.elim0 : (Expanded E).Term I).realize v =
      Structure.funMap f (Fin.elim0 : Fin 0 → M) := by
  change Structure.funMap f _ = _
  congr 1
  exact Subsingleton.elim _ _

private theorem realize_func1 {I M : Type} [(Expanded E).Structure M]
    (f : (Expanded E).Functions 1) (t : (Expanded E).Term I) (v : I → M) :
    (Term.func f ![t]).realize v = Structure.funMap f ![t.realize v] := by
  change Structure.funMap f _ = _
  congr 1
  funext i
  fin_cases i
  rfl

private theorem realize_func2 {I M : Type} [(Expanded E).Structure M]
    (f : (Expanded E).Functions 2) (t u : (Expanded E).Term I) (v : I → M) :
    (Term.func f ![t, u]).realize v = Structure.funMap f ![t.realize v, u.realize v] := by
  change Structure.funMap f _ = _
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem rvEquality_realize_in_native (j : M ↪[LRV] U)
    (hM : M ⊨ HenselianTheory.expanded E) {n : ℕ}
    (t u : (Expanded E).Term ((V ⊕ R) ⊕ Fin n))
    (ht : termSort sourceSort t = some .vf) (hu : termSort sourceSort u = some .vf)
    (v : V → M) (r : R → M) (x : Fin n → M)
    (hv : ∀ i, tagEval (E := E) .vf (v i))
    (hr : ∀ i, tagEval (E := E) .rv (r i)) (hx : ∀ i, tagEval (E := E) .rv (x i)) :
    (BoundedFormula.equal t u).Realize (Sum.elim v r) x ↔ (rvEquality t u).Realize (Sum.elim v r) x := by
  let a := Sum.elim (Sum.elim v r) x
  have ha : ∀ i, tagEval (E := E) (sourceSort i) (a i) := by
    rintro ((i | i) | i)
    · exact hv i
    · exact hr i
    · exact hx i
  have ht' := term_sorted_in_native j hM sourceSort a ha t ht
  have hu' := term_sorted_in_native j hM sourceSort a ha u hu
  have hh := native_vf_eq j (t.realize a) (u.realize a) ht' hu'
  simp only [rvEquality, rvTerm, BoundedFormula.Realize, realize_func0, realize_func1, realize_func2]
  exact hh

end SpecialTransformations.Section6.ExpandedLiterals

namespace SpecialTransformations.Section6.HenselianElimination

open RVTermSupport RVAbstraction ExpandedLogic ExpandedLiterals

variable {E : _root_.FirstOrder.Language.{0, 0}} {V R : Type}

private theorem normalize_fragment (hEnv : UniformNormalizedElimination.NativeEnvelopes E)
    {n : ℕ} (φ : (Expanded E).BoundedFormula (V ⊕ R) n)
    (hQ : IsVFQF φ) (hS : WellSorted (Sum.elim (fun _ => .vf) (fun _ => .rv)) (fun _ => .rv) φ) :
    ∃ ψ : (Expanded E).BoundedFormula (V ⊕ R) n, Fragment ψ ∧
      ∀ (M : (HenselianTheory.expanded E).ModelType.{0,0,0})
        (v : V → M) (r : R → M) (x : Fin n → M),
        (∀ i, tagEval (E := E) .vf (v i)) → (∀ i, tagEval (E := E) .rv (r i)) →
        (∀ i, tagEval (E := E) .rv (x i)) →
        (φ.Realize (Sum.elim v r) x ↔ ψ.Realize (Sum.elim v r) x) := by
  induction hQ with
  | falsum => exact ⟨⊥, .falsum, fun _ _ _ _ _ _ _ => Iff.rfl⟩
  | atomic h =>
    cases h with
    | equal t u =>
      cases hS with
      | @equal _ _ σ _ _ ht hu =>
        cases σ with
        | rv =>
          exact ⟨.equal t u, .equal t u ht hu, fun _ _ _ _ _ _ _ => Iff.rfl⟩
        | vf =>
          refine ⟨rvEquality t u, rvEquality_fragment t u ht hu, ?_⟩
          intro M v r x hv hr hx
          letI := (LHom.sumInl : LRV →ᴸ Expanded E).reduct M
          obtain ⟨h00, hc, j, hj⟩ := hEnv M (inferInstance : M ⊨ HenselianTheory.expanded E)
          exact rvEquality_realize_in_native j inferInstance t u ht hu v r x hv hr hx
    | rel ρ ts =>
      cases hS with
      | rel ρ ts hs =>
        have htag {d : ℕ} (s : SortTag) (t : (Expanded E).Term ((V ⊕ R) ⊕ Fin d))
            (ht : termSort sourceSort t = some s)
            (M : (HenselianTheory.expanded E).ModelType.{0,0,0})
            (v : V → M) (r : R → M) (x : Fin d → M)
            (hv : ∀ i, tagEval (E := E) .vf (v i))
            (hr : ∀ i, tagEval (E := E) .rv (r i))
            (hx : ∀ i, tagEval (E := E) .rv (x i)) :
            tagEval (E := E) s (t.realize (Sum.elim (Sum.elim v r) x)) := by
          letI := (LHom.sumInl : LRV →ᴸ Expanded E).reduct M
          obtain ⟨h00, hc, j, hj⟩ := hEnv M (inferInstance : M ⊨ HenselianTheory.expanded E)
          apply term_sorted_in_native j inferInstance sourceSort _ _ t ht
          rintro ((i | i) | i)
          · exact hv i
          · exact hr i
          · exact hx i
        cases ρ with
        | inr ρ =>
          exact ⟨.rel (.inr ρ) ts, .rel (.inr ρ) ts hs, fun _ _ _ _ _ _ _ => Iff.rfl⟩
        | inl ρ =>
          cases ρ with
          | memVF =>
            refine ⟨⊥ ⟹ ⊥, .imp .falsum .falsum, ?_⟩
            intro M v r x hv hr hx
            have ht := htag .vf (ts 0) (hs 0) M v r x hv hr hx
            have hts : ts = ![ts 0] := by funext i; fin_cases i; rfl
            rw [hts]
            change (Relations.boundedFormula₁ (L := Expanded E) (.inl .memVF) (ts 0)).Realize
              (Sum.elim v r) x ↔ (False → False)
            rw [BoundedFormula.realize_rel₁]
            exact ⟨fun _ h => h, fun _ => ht⟩
          | memRV =>
            refine ⟨⊥ ⟹ ⊥, .imp .falsum .falsum, ?_⟩
            intro M v r x hv hr hx
            have ht := htag .rv (ts 0) (hs 0) M v r x hv hr hx
            have hts : ts = ![ts 0] := by funext i; fin_cases i; rfl
            rw [hts]
            change (Relations.boundedFormula₁ (L := Expanded E) (.inl .memRV) (ts 0)).Realize
              (Sum.elim v r) x ↔ (False → False)
            rw [BoundedFormula.realize_rel₁]
            exact ⟨fun _ h => h, fun _ => ht⟩
          | memUnits =>
            exact ⟨.rel (.inl .memUnits) ts, .rel (.inl ⟨.memUnits, fun _ => rfl⟩) ts hs,
              fun _ _ _ _ _ _ _ => Iff.rfl⟩
          | rvLe =>
            exact ⟨.rel (.inl .rvLe) ts, .rel (.inl ⟨.rvLe, fun _ => rfl⟩) ts hs,
              fun _ _ _ _ _ _ _ => Iff.rfl⟩
  | imp _ _ ih₁ ih₂ =>
    cases hS with
    | imp h₁ h₂ =>
      obtain ⟨ψ₁, hψ₁, he₁⟩ := ih₁ h₁
      obtain ⟨ψ₂, hψ₂, he₂⟩ := ih₂ h₂
      refine ⟨ψ₁.imp ψ₂, .imp hψ₁ hψ₂, ?_⟩
      intro M v r x hv hr hx
      exact imp_congr (he₁ M v r x hv hr hx) (he₂ M v r x hv hr hx)
  | @all_rv n φ hφ ih =>
    generalize heq : ExpandedLogic.allSorted .rv φ = θ at hS
    cases hS with
    | falsum | equal | rel | imp => cases heq
    | @all _ _ s ψ h =>
      have hφψ : φ = ψ := by
        unfold ExpandedLogic.allSorted at heq
        injection heq with _ hb
        exact (BoundedFormula.imp.inj hb).2
      subst ψ
      have hs : s = .rv := by
        cases s with
        | rv => rfl
        | vf =>
          unfold ExpandedLogic.allSorted ExpandedLogic.guardAtom ExpandedLogic.sortRelation at heq
          cases heq
      subst s
      have he : Fin.snoc (α := fun _ => SortTag) (fun _ : Fin n => .rv) .rv = fun _ => .rv := by
        funext i
        cases i using Fin.lastCases <;> simp
      rw [he] at h
      obtain ⟨ψ, hψ, hEq⟩ := ih h
      refine ⟨ExpandedLogic.allSorted .rv ψ, .all hψ, ?_⟩
      intro M v r x hv hr hx
      simp only [ExpandedLogic.allSorted_realize]
      exact forall_congr' fun a => imp_congr_right fun ha =>
        hEq M v r (Fin.snoc x a) hv hr (by simpa only [he] using sorted_snoc hx ha)

theorem rvLiteralNormalForm_of_nativeEnvelopes (hEnv : UniformNormalizedElimination.NativeEnvelopes E) :
    RVLiteralNormalForm E := by
  intro V R _ _ φ hS hQ
  obtain ⟨ψ, hψ, he⟩ := normalize_fragment hEnv φ hQ hS
  exact ⟨ψ, hψ, fun M v r hv hr => he M v r default hv hr (fun i => i.elim0)⟩

end SpecialTransformations.Section6.HenselianElimination
