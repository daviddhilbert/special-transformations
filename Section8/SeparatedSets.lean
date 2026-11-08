import Section8.UnaryBalls

/-! Lemma 8.1: a uniformly separated definable subset of a finite VF power
is finite. This follows the paper's induction, using definable coordinate
projections and actual unary fibres. -/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace SpecialTransformations.Section8

variable {M : Type} [sM : LRV.Structure M]

private theorem headImage_definable {S : Set M} {n : ℕ} {A : Set (Fin (n + 1) → M)}
    (hA : S.Definable LRV A) : S.Definable₁ LRV ((fun z => z 0) '' A) := by
  change S.Definable LRV {u : Fin 1 → M | u 0 ∈ (fun z => z 0) '' A}
  convert hA.image_comp (fun _ : Fin 1 => (0 : Fin (n + 1))) using 1
  ext u
  constructor
  · rintro ⟨x, hx, he⟩
    exact ⟨x, hx, funext (fun i => by fin_cases i; exact he)⟩
  · rintro ⟨x, hx, he⟩
    exact ⟨x, hx, congrFun he 0⟩

private theorem tailFibre_definable {S : Set M} {n : ℕ} {A : Set (Fin (n + 1) → M)}
    (hA : S.Definable LRV A) (a : M) :
    (insert a S).Definable LRV {t | Fin.cons a t ∈ A} := by
  apply (hA.mono (Set.subset_insert a S)).preimage_map
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.cons_zero] using
      LRV.definableFun_const (Fin n) (Set.mem_insert a S)
  · simpa only [Fin.cons_succ] using
      (Set.DefinableFun.proj (L := LRV) (A := insert a S) (i := j))

private theorem headFibre_definable {S : Set M} {n : ℕ} {A : Set (Fin (n + 1) → M)}
    (hA : S.Definable LRV A) (t : Fin n → M) :
    (S ∪ Set.range t).Definable₁ LRV {a | Fin.cons a t ∈ A} := by
  change (S ∪ Set.range t).Definable LRV {u : Fin 1 → M | Fin.cons (u 0) t ∈ A}
  apply (hA.mono Set.subset_union_left).preimage_map
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.cons_zero] using
      (Set.DefinableFun.proj (L := LRV) (A := S ∪ Set.range t) (i := (0 : Fin 1)))
  · simpa only [Fin.cons_succ] using
      (LRV.definableFun_const (M := M) (Fin 1)
        (Or.inr (Set.mem_range_self j) : t j ∈ S ∪ Set.range t))

variable [hM : M ⊨ Axioms.ACVF]

section CompatibleValuation

variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ]
variable (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (hc : CanonicalStructure.IsCanonical (M := M))

include hv hc in
private theorem unary_finite_of_ball_unique {S A : Set M} (hA : S.Definable₁ LRV A)
    (hVF : A ⊆ {x | iVF x}) {r : M} (hr : iVF r) (hr0 : r ≠ iVFZero)
    (huniq : ∀ x ∈ A, ∀ y ∈ A, y ∈ rawOpenBall x r → x = y) : A.Finite := by
  by_contra hInf
  obtain ⟨a, ha, s, hs, hs0, hsub⟩ :=
    infinite_definable_contains_small_ball hv (raw_definable_sorted hc S A .vf hA hVF) hInf hr hr0
  apply rawOpenBall_infinite hv (hVF ha) hs hs0
  apply Set.Subsingleton.finite
  intro x hx y hy
  exact huniq x (hsub hx).1 y (hsub hy).1
    (rawOpenBall_recentre Valued.v hv (hsub hx).2 (hsub hy).2)

include hv hc in
theorem finite_of_uniformBall_unique {n : ℕ} {S : Set M} {A : Set (Fin n → M)}
    (hA : S.Definable LRV A) (hVF : ∀ x ∈ A, ∀ i, iVF (x i))
    {r : M} (hr : iVF r) (hr0 : r ≠ iVFZero)
    (huniq : ∀ x ∈ A, ∀ y ∈ A, y ∈ uniformBall x r → x = y) : A.Finite := by
  induction n generalizing S with
  | zero =>
    apply Set.Subsingleton.finite
    intro x _ y _
    funext i
    exact i.elim0
  | succ n ih =>
    let P := (fun z : Fin (n + 1) → M => z 0) '' A
    have hP : S.Definable₁ LRV P := headImage_definable hA
    have hPVF : P ⊆ {a | iVF a} := by
      rintro _ ⟨z, hz, rfl⟩
      exact hVF z hz 0
    by_cases hPfin : P.Finite
    · let F (a : M) : Set (Fin n → M) := {t | Fin.cons a t ∈ A}
      have hFfin (a : M) (ha : a ∈ P) : (F a).Finite := by
        apply ih (tailFibre_definable hA a) (fun t ht i => by
          simpa only [Fin.cons_succ] using hVF (Fin.cons a t) ht i.succ)
        intro t ht u hu htu
        have he : (Fin.cons a t : Fin (n + 1) → M) = Fin.cons a u := huniq _ ht _ hu
          (fun i => Fin.cases
            (by simpa only [Fin.cons_zero] using rawOpenBall_self Valued.v hv (hPVF ha) hr hr0)
            (fun j => by simpa only [Fin.cons_succ] using htu j) i)
        exact (Fin.cons_inj.mp he).2
      let prepend (a : M) (t : Fin n → M) : Fin (n + 1) → M := Fin.cons a t
      let G (a : M) : Set (Fin (n + 1) → M) := prepend a '' F a
      have hUnion : (⋃ a ∈ P, G a).Finite :=
        hPfin.biUnion (fun a ha => (hFfin a ha).image (prepend a))
      apply hUnion.subset
      intro z hz
      exact Set.mem_biUnion (Set.mem_image_of_mem _ hz)
        ⟨Fin.tail z, by simpa only [F, Set.mem_setOf_eq, Fin.cons_self_tail] using hz,
          Fin.cons_self_tail z⟩
    · exfalso
      obtain ⟨a, ha, s, hs, hs0, hsub⟩ := infinite_definable_contains_small_ball hv
        (raw_definable_sorted hc S P .vf hP hPVF) hPfin hr hr0
      let B := rawOpenBall a s
      let T := insert a (insert s S)
      let C := Fin.tail '' (A ∩ {z | z 0 ∈ B})
      have hB : T.Definable₁ LRV B :=
        rawOpenBall_definable (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      have hC : T.Definable LRV C :=
        ((hA.mono (fun _ hx => Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hx))).inter
          (hB.preimage_comp (fun _ : Fin 1 => (0 : Fin (n + 1))))).image_comp Fin.succ
      have hCfin : C.Finite := by
        apply ih hC
        · rintro _ ⟨x, ⟨hx, _⟩, rfl⟩ i
          exact hVF x hx i.succ
        · rintro _ ⟨x, ⟨hx, hxb⟩, rfl⟩ _ ⟨y, ⟨hy, hyb⟩, rfl⟩ hxy
          have hhead := rawOpenBall_recentre Valued.v hv (hsub hxb).2 (hsub hyb).2
          exact congrArg Fin.tail (huniq x hx y hy (fun i => Fin.cases hhead (fun j => hxy j) i))
      let F (t : Fin n → M) : Set M := {b | Fin.cons b t ∈ A}
      have hFfin (t : Fin n → M) : (F t).Finite := by
        apply unary_finite_of_ball_unique hv hc (headFibre_definable hA t)
          (fun b hb => by
            change iVF b
            simpa only [Fin.cons_zero] using hVF (Fin.cons b t) hb 0) hr hr0
        intro b hb c hc' hbc
        have he : (Fin.cons b t : Fin (n + 1) → M) = Fin.cons c t := huniq _ hb _ hc'
          (fun i => Fin.cases
            (by simpa only [Fin.cons_zero] using hbc)
            (fun j => by simpa only [Fin.cons_succ] using
              rawOpenBall_self Valued.v hv (hVF (Fin.cons b t) hb j.succ) hr hr0) i)
        exact (Fin.cons_inj.mp he).1
      apply rawOpenBall_infinite hv (hPVF ha) hs hs0
      apply (hCfin.biUnion (fun t _ => hFfin t)).subset
      intro b hb
      obtain ⟨z, hz, hzb⟩ := (hsub hb).1
      change z 0 = b at hzb
      have hzbB : z 0 ∈ B := by rwa [hzb]
      refine Set.mem_biUnion ⟨z, ⟨hz, hzbB⟩, rfl⟩ ?_
      change Fin.cons b (Fin.tail z) ∈ A
      rwa [← hzb, Fin.cons_self_tail]

end CompatibleValuation

/-- Lemma 8.1 over the released language, with no saturation or extra
characteristic assumption needed. The existential radius is an ordinary
value, represented by any nonzero VF element of that value. -/
theorem lemma_8_1 {S : Set M} {n : ℕ} (A : Set (Fin n → M))
    (hA : DefinableOver S (fun _ => .vf) A)
    (hsep : ∃ r : M, iVF r ∧ r ≠ iVFZero ∧
      A.Pairwise (fun a b => Disjoint (uniformBall a r) (uniformBall b r))) : A.Finite := by
  obtain ⟨r, hr, hr0, hsep⟩ := hsep
  let N := @CanonicalStructure.normalize M sM
  letI := sM
  have hN : @Theory.Model LRV M N Axioms.ACVF := CanonicalStructure.normalized_model hM
  have hcan : @CanonicalStructure.IsCanonical M N := CanonicalStructure.normalize_isCanonical
  have hAN : @DefinableOver M N S n (fun _ => .vf) A :=
    (definableOver_normalize_iff S (fun _ => .vf) A).mpr hA
  have hrN : @iVF M N r := (CanonicalStructure.sortEval_normalize .vf r).mpr hr
  have hzN : @iVFZero M N = @iVFZero M sM := CanonicalStructure.sortZero_normalize .vf
  have hball (a : Fin n → M) : @uniformBall M N n a r = @uniformBall M sM n a r :=
    uniformBall_normalize a r
  letI := N
  letI := hN
  obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  letI : Valued (VFType (M := M)) Γ := Valued.mk' v
  have hVF : ∀ x ∈ A, ∀ i, iVF (x i) := by
    obtain ⟨p, φ, hw, he⟩ := hAN
    intro x hx
    exact (he ▸ hx).1
  apply finite_of_uniformBall_unique hv hcan
    hAN.raw_definable hVF hrN (hzN.symm ▸ hr0)
  intro x hx y hy hxy
  by_contra hne
  apply Set.disjoint_left.mp (hsep hx hy hne) (hball x ▸ hxy)
  rw [← hball y]
  exact fun i => rawOpenBall_self v hv (hVF y hy i) hrN (hzN.symm ▸ hr0)

end SpecialTransformations.Section8
