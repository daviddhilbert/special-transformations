import Section5.GeneralExistence
import Section5.PolynomialExpression

/-! Polynomial instances of the definable-map preparation theorem. The
existing Section 4 finite ring expression is reused in the released LRV
language, with every coefficient kept over the original parameter base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

namespace SpecialTransformations.Section5

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m k : ℕ}

def mvPolynomialTerm (p : MvPolynomial (Fin n) (VF (M := M))) :=
  Section3.RingSyntax.ofRingTerm
    (FirstOrder.Ring.termOfFreeCommRing (PolynomialExpression.expression p))

def mvPolynomialCode (p : MvPolynomial (Fin n) (VF (M := M))) (z : Fin n ⊕ Fin m → M) : M :=
  @Term.realize LRV M (CanonicalStructure.normalize (M := M)) (Fin p.support.card ⊕ Fin n)
    (Sum.elim (fun i => (p.coeff (PolynomialExpression.enumeration p i).val).val)
      (fun i => z (.inl i))) (mvPolynomialTerm p)

theorem mvPolynomialCode_eq (p : MvPolynomial (Fin n) (VF (M := M)))
    (z : Fin n ⊕ Fin m → M) (x : Fin n → VF (M := M))
    (hx : ∀ i, z (.inl i) = (x i).val) :
    mvPolynomialCode p z = (MvPolynomial.eval x p).val := by
  unfold mvPolynomialCode
  simp_rw [hx]
  have hn := CanonicalStructure.term_normalize hM (fun _ => .vf) (fun _ => .vf)
    (fun i => (p.coeff (PolynomialExpression.enumeration p i).val).val)
    (fun i => (x i).val)
    (fun i => (p.coeff (PolynomialExpression.enumeration p i).val).property)
    (fun i => (x i).property) (mvPolynomialTerm p) (Section3.RingSyntax.sorted _)
  refine hn.trans ?_
  let cs := fun i : Fin p.support.card => p.coeff (PolynomialExpression.enumeration p i).val
  have he : (fun a => ((Sum.elim cs x) a).val) =
      Sum.elim (fun i => (p.coeff (PolynomialExpression.enumeration p i).val).val)
        (fun i => (x i).val) := by
    funext a
    cases a <;> rfl
  have ht := congrArg (fun v : Fin p.support.card ⊕ Fin n → M =>
    @Term.realize LRV M sM _ v (mvPolynomialTerm p)) he.symm
  have hr : @Term.realize LRV M sM _ (fun a => ((Sum.elim cs x) a).val) (mvPolynomialTerm p) =
      (FreeCommRing.lift (Sum.elim cs x) (PolynomialExpression.expression p)).val := by
    unfold mvPolynomialTerm
    rw [Section3.RingSyntax.realizes, FirstOrder.Ring.realize_termOfFreeCommRing]
  exact ht.trans (hr.trans (congrArg (fun y : VF (M := M) => y.val)
    (PolynomialExpression.expression_eval p (RingHom.id _) x)))

theorem mvPolynomialCode_definable (p : MvPolynomial (Fin n) (VF (M := M)))
    (hc : ∀ d, (p.coeff d).val ∈ S) : RawFun S (Fin n ⊕ Fin m) (mvPolynomialCode p) := by
  let g : (Fin n ⊕ Fin m → M) → Fin p.support.card ⊕ Fin n → M :=
    fun z => Sum.elim (fun i => (p.coeff (PolynomialExpression.enumeration p i).val).val)
      (fun i => z (.inl i))
  let t := @mvPolynomialTerm M sM hM n p
  let N := @CanonicalStructure.normalize M sM
  letI := N
  have ht : (∅ : Set M).DefinableFun LRV
      (fun z => @Term.realize LRV M N _ z t) :=
    t.definableFun_realize (M := M)
  have hg : ∀ i, @Set.DefinableFun M LRV N (Fin n ⊕ Fin m) S (fun z => g z i) := by
    intro i
    cases i with
    | inl i => exact LRV.definableFun_const _ (hc _)
    | inr i => exact Set.DefinableFun.proj LRV
  exact @Set.DefinableFun.comp M LRV N (Fin p.support.card ⊕ Fin n)
    (Fin n ⊕ Fin m) S _ inferInstance g hg ht.of_empty

def mvPolynomialTupleMap (A : DefSet (M := M) S n m)
    (p : Fin k → MvPolynomial (Fin n) (VF (M := M)))
    (hc : ∀ i d, ((p i).coeff d).val ∈ S) :
    Map A (PresentedSet.univ (pointSpace (M := M) k 0) S) :=
  Map.ofCodes A (fun a => (fun i => MvPolynomial.eval (vfAt a) (p i), Fin.elim0))
    (fun z => Sum.elim (fun i => mvPolynomialCode (p i) z) Fin.elim0)
    (by
      intro i
      cases i with
      | inl i => exact mvPolynomialCode_definable (p i) (hc i)
      | inr i => exact i.elim0)
    (by
      intro c
      refine ⟨?_, fun i => i.elim0⟩
      intro i
      change iVF (mvPolynomialCode (p i) c.val)
      rw [mvPolynomialCode_eq (p i) c.val (vfAt (pDecode (pointSpace n m) c)) (fun _ => rfl)]
      exact (MvPolynomial.eval (vfAt (pDecode (pointSpace n m) c)) (p i)).property)
    (by
      intro c
      refine Prod.ext ?_ (Subsingleton.elim _ _)
      funext i
      apply Subtype.ext
      exact mvPolynomialCode_eq (p i) c.val (vfAt (pDecode (pointSpace n m) c)) (fun _ => rfl))

theorem theorem_5_5_finite {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (h00 : M ⊨ Axioms.ACVF00) (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (hObstacles : ∀ N, UniformVerticalObstacles v S N)
    {A₀ : DefSet (M := M) S n 0} {A : DefSet (M := M) S n m}
    (τ : SpecialBijection A₀ A) (p : Fin k → MvPolynomial (Fin n) (VF (M := M)))
    (hc : ∀ i d, ((p i).coeff d).val ∈ S) :
    ∃ r : ℕ, ∃ B : DefSet (M := M) S n r, ∃ T : SpecialBijection A B,
      (τ.chain.append T.chain).Alternating none ∧ IsRVPullback (carrier B) ∧
        ∀ b c : B, SameRV b.val c.val → ∀ i,
          rv (MvPolynomial.eval (vfAt (τ.inverseMap (T.inverseMap b)).val) (p i)) =
          rv (MvPolynomial.eval (vfAt (τ.inverseMap (T.inverseMap c)).val) (p i)) := by
  let f := Map.comp (mvPolynomialTupleMap A₀ p hc) τ.inverseMap
  obtain ⟨r, B, T, hTa, hB, hf⟩ := map_preparation h00 v hv hObstacles τ f
  refine ⟨r, B, T, hTa, hB, ?_⟩
  intro b c he i
  exact ((sameRV_iff _ _).mp (hf b c he)).1 i

theorem theorem_5_5 {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (h00 : M ⊨ Axioms.ACVF00) (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (hObstacles : ∀ N, UniformVerticalObstacles v S N)
    {A₀ : DefSet (M := M) S n 0} {A : DefSet (M := M) S n m}
    (τ : SpecialBijection A₀ A) (p : MvPolynomial (Fin n) (VF (M := M)))
    (hc : ∀ d, (p.coeff d).val ∈ S) :
    ∃ r : ℕ, ∃ B : DefSet (M := M) S n r, ∃ T : SpecialBijection A B,
      (τ.chain.append T.chain).Alternating none ∧ IsRVPullback (carrier B) ∧
        ∀ b c : B, SameRV b.val c.val →
          rv (MvPolynomial.eval (vfAt (τ.inverseMap (T.inverseMap b)).val) p) =
          rv (MvPolynomial.eval (vfAt (τ.inverseMap (T.inverseMap c)).val) p) := by
  obtain ⟨r, B, T, hTa, hB, hf⟩ := theorem_5_5_finite h00 v hv hObstacles τ
    (fun _ : Fin 1 => p) (fun _ => hc)
  exact ⟨r, B, T, hTa, hB, fun b c he => hf b c he 0⟩

/-- The RV-polydisc instance in the precise form used by Theorem 5.4.
The presented source records definability of the supplied RV fibre. -/
theorem theorem_5_4 {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (h00 : M ⊨ Axioms.ACVF00) (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (hObstacles : ∀ N, UniformVerticalObstacles v S N)
    {A₀ : DefSet (M := M) S n 0} {A : DefSet (M := M) S n m}
    (u : Fin n → RV (M := M))
    (_hFibre : carrier A₀ = {p | ∀ i, rv (vfAt p i) = u i})
    (τ : SpecialBijection A₀ A) (p : MvPolynomial (Fin n) (VF (M := M)))
    (hc : ∀ d, (p.coeff d).val ∈ S) :
    ∃ r : ℕ, ∃ B : DefSet (M := M) S n r, ∃ T : SpecialBijection A B,
      (τ.chain.append T.chain).Alternating none ∧
        ∀ b c : B, SameRV b.val c.val →
          rv (MvPolynomial.eval (vfAt (τ.inverseMap (T.inverseMap b)).val) p) =
          rv (MvPolynomial.eval (vfAt (τ.inverseMap (T.inverseMap c)).val) p) := by
  obtain ⟨r, B, T, hTa, _, hf⟩ := theorem_5_5 h00 v hv hObstacles τ p hc
  exact ⟨r, B, T, hTa, hf⟩

end SpecialTransformations.Section5
