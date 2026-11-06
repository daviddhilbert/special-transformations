import Section5.UnaryRelations

/-!
# Unary definable maps with RV targets

The graph is prepared uniformly in both its original RV coordinates and
its output coordinates. Its domain and its value then descend together.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section5

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m k : ℕ}

theorem isRVPullback_zeroVF (A : Set (Point (M := M) 0 m)) : IsRVPullback A := by
  apply (isRVPullback_iff _).mpr
  intro p hp q he
  have hlabels := ((sameRV_iff _ _).mp he).2
  have hpq : p = q := Prod.ext (Subsingleton.elim _ _) hlabels
  exact hpq ▸ hp

theorem corollary_5_6_zeroVF (A : DefSet (M := M) S 0 m) : IsDeformedRVPullback A :=
  ⟨m, A, ⟨SpecialBijection.refl A⟩, isRVPullback_zeroVF (carrier A)⟩

theorem unary_relation_preparation_at_boundary (h00 : M ⊨ Axioms.ACVF00)
    (U : Set (Fin (k + 1) → M)) (hU : Section3.DefinableOver S Section3.MixedPolynomialSyntax.contextSort U)
    (A : DefSet (M := M) S 1 m) (hA : IsRVPullback (carrier A))
    (previous : Option Bool)
    (hTag : previous = some false → ∃ j, Tagged (carrier A) 0 j) :
    ∃ r : ℕ, ∃ B : DefSet (M := M) S 1 r, ∃ T : SpecialBijection A B,
      T.chain.Alternating previous ∧ IsRVPullback (carrier B) ∧ RelationContractible U T := by
  obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨Q, _, hQ, hO, _⟩ := Section3.mixed_finite_definable_obstacles v hv S U hU
  let R₀ := obstacleFamily S m Q hQ
  let R := R₀.restrict A (Set.subset_univ _)
  obtain ⟨r, B, W, hW, hz⟩ := R.centralize_boundary h00 Q.card
    (R₀.restrict_bound A (Set.subset_univ _) Q.card (obstacleFamily_bound S m Q hQ)) previous hTag
  let T : SpecialBijection A B := ⟨W, W.alternating_none previous hW⟩
  have hB := T.preserves_pullback hA
  refine ⟨r, B, T, hW, hB, ?_⟩
  apply relation_contractible_of_zero_obstacles v hv U Q hO T hB
  intro a ha
  exact hz a ⟨ha, a.property⟩

def attachRV (p : Point (M := M) n m) (t : Fin k → RV (M := M)) :
    Point (M := M) n (m + k) := (p.1, Fin.append p.2 t)

def attachRVCodes (z : (Fin n ⊕ Fin m) ⊕ (Fin 0 ⊕ Fin k) → M) : Fin n ⊕ Fin (m + k) → M :=
  Sum.elim (fun i => z (.inl (.inl i)))
    (Fin.append (fun i => z (.inl (.inr i))) (fun i => z (.inr (.inr i))))

def attachRVMap (A : DefSet (M := M) S n m) (D : DefSet (M := M) S 0 k) :
    Map (PresentedSet.prod A D) (PresentedSet.univ (pointSpace n (m + k)) S) :=
  Map.ofCodes (M := M) (sM := sM)
    (P := spaceProd (pointSpace n m) (pointSpace 0 k)) (Q := pointSpace n (m + k))
    (PresentedSet.prod A D) (fun p => attachRV p.1 p.2.2) (attachRVCodes (m := m) (k := k))
    (by
      intro i
      cases i with
      | inl i =>
        simpa [attachRVCodes] using
          rawProj S (.inl (.inl i) : (Fin n ⊕ Fin m) ⊕ (Fin 0 ⊕ Fin k))
      | inr i =>
        cases i using Fin.addCases with
        | left i =>
          simpa [attachRVCodes] using
            rawProj S (.inl (.inr i) : (Fin n ⊕ Fin m) ⊕ (Fin 0 ⊕ Fin k))
        | right i =>
          simpa [attachRVCodes] using
            rawProj S (.inr (.inr i) : (Fin n ⊕ Fin m) ⊕ (Fin 0 ⊕ Fin k)))
    (by
      intro c
      refine ⟨c.property.1.1, ?_⟩
      intro i
      cases i using Fin.addCases with
      | left i => simpa [attachRVCodes] using c.property.1.2 i
      | right i => simpa [attachRVCodes] using c.property.2.2 i)
    (by
      intro c
      refine Prod.ext rfl ?_
      funext i
      cases i using Fin.addCases <;> apply Subtype.ext <;> simp [attachRVCodes, attachRV])

def rvGraph {A : DefSet (M := M) S n m} {D : DefSet (M := M) S 0 k} (f : Map A D) :
    DefSet (M := M) S n (m + k) :=
  Map.image (Map.comp (attachRVMap A D) (Map.pair (Map.id A) f))

theorem mem_rvGraph {A : DefSet (M := M) S n m} {D : DefSet (M := M) S 0 k}
    (f : Map A D) (p : Point (M := M) n m) (t : Fin k → RV (M := M)) :
    attachRV p t ∈ carrier (rvGraph f) ↔ ∃ a : A, a.val = p ∧ (f a).val.2 = t := by
  change (∃ a : A, attachRV a.val (f a).val.2 = attachRV p t) ↔ _
  constructor
  · rintro ⟨a, he⟩
    have hv := congrArg Prod.fst he
    have ht : a.val.2 = p.2 := by
      funext i
      simpa only [attachRV, Fin.append_left] using
        congrArg (fun z : Point (M := M) n (m + k) => z.2 (Fin.castAdd k i)) he
    have hf : (f a).val.2 = t := by
      funext i
      simpa only [attachRV, Fin.append_right] using
        congrArg (fun z : Point (M := M) n (m + k) => z.2 (Fin.natAdd m i)) he
    exact ⟨a, Prod.ext hv ht, hf⟩
  · rintro ⟨a, rfl, he⟩
    exact ⟨a, by rw [he]⟩

theorem unaryPoint_eq_of (p q : Point (M := M) 1 m)
    (hv : vfAt p 0 = vfAt q 0) (ht : p.2 = q.2) : p = q := by
  refine Prod.ext ?_ ht
  funext i
  fin_cases i
  exact hv

theorem rvGraph_transfer {A : DefSet (M := M) S 1 m} {D : DefSet (M := M) S 0 k}
    (f : Map A D) {l : ℕ} {E : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}
    (hAE : carrier A ⊆ carrier E) (T : SpecialBijection E B)
    (hT : RelationContractible (rawUnarySet (rvGraph f)) T)
    (a : A) (b : B)
    (he : SameRV (T.toMap ⟨a.val, hAE a.property⟩).val b.val) :
    ∃ d : A, d.val = (T.inverseMap b).val ∧ (f d).val.2 = (f a).val.2 := by
  let aE : E := ⟨a.val, hAE a.property⟩
  let ys : Fin (m + k) → M := fun i => (Fin.append a.val.2 (f a).val.2 i).val
  have hys : ∀ i, iRV (ys i) := fun i => (Fin.append a.val.2 (f a).val.2 i).property
  have hh := hT (T.toMap aE) b he ys hys
  rw [T.inverse_apply] at hh
  have haG : rawUnaryValues (attachRV a.val (f a).val.2) ∈ rawUnarySet (rvGraph f) :=
    (mem_rawUnarySet_values _ _).mpr ((mem_rvGraph f _ _).mpr ⟨a, rfl, rfl⟩)
  have hlabels : (T.inverseMap b).val.2 = a.val.2 := by
    have h := ((sameRV_iff _ _).mp (T.inverse_contractible (T.toMap aE) b he)).2
    rw [T.inverse_apply] at h
    exact h.symm
  have hdG : rawUnaryValues (attachRV (T.inverseMap b).val (f a).val.2) ∈ rawUnarySet (rvGraph f) := by
    change (Fin.cons (vfAt (T.inverseMap b).val 0).val
      (fun i => (Fin.append (T.inverseMap b).val.2 (f a).val.2 i).val) : Fin ((m + k) + 1) → M) ∈
        rawUnarySet (rvGraph f)
    rw [hlabels]
    exact hh.mp haG
  exact (mem_rvGraph f _ _).mp ((mem_rawUnarySet_values _ _).mp hdG)

/-- Unary definable-map preparation, including an arbitrary initial chain.
The target can be any finite RV tuple space. -/
theorem unary_rvMap_preparation_at_boundary (h00 : M ⊨ Axioms.ACVF00)
    {A : DefSet (M := M) S 1 m} {D : DefSet (M := M) S 0 k} (previous : Option Bool)
    (hTag : previous = some false → ∃ j, Tagged (carrier A) 0 j) (f : Map A D) :
    ∃ r : ℕ, ∃ B : DefSet (M := M) S 1 r, ∃ V : SpecialBijection A B,
      V.chain.Alternating previous ∧ IsRVPullback (carrier B) ∧
        ∀ b c : B, SameRV b.val c.val →
          (f (V.inverseMap b)).val.2 = (f (V.inverseMap c)).val.2 := by
  let E : DefSet (M := M) S 1 m := PresentedSet.mk (hull (carrier A)) (hull_definable A)
  have hAE : carrier A ⊆ carrier E := subset_hull _
  obtain ⟨r, C, T, hT, hC, hRel⟩ := unary_relation_preparation_at_boundary h00
    (rawUnarySet (rvGraph f)) (rawUnarySet_definable _) E (hull_idem _)
    previous (fun h => by
      obtain ⟨j, hj⟩ := hTag h
      exact ⟨j, tagged_hull hj⟩)
  obtain ⟨B, V, hV, hBC, hImage, hcomm⟩ := T.restrict_at A hAE previous hT
  have hB : IsRVPullback (carrier B) := by
    apply (isRVPullback_iff _).mpr
    intro p hp q hpq
    have hq := (isRVPullback_iff _).mp hC p (hBC hp) q hpq
    have hp' : ∃ a : A, (T.toMap ⟨a.val, hAE a.property⟩).val = p := by
      change p ∈ {c | ∃ a : A, (T.toMap ⟨a.val, hAE a.property⟩).val = c}
      exact hImage ▸ hp
    obtain ⟨a, ha⟩ := hp'
    have he : SameRV (T.toMap ⟨a.val, hAE a.property⟩).val (⟨q, hq⟩ : C).val := by
      change SameRV _ q
      rw [ha]
      exact hpq
    obtain ⟨d, hd, _⟩ := rvGraph_transfer f hAE T hRel a ⟨q, hq⟩ he
    have hmap : (T.toMap ⟨d.val, hAE d.property⟩).val = q := by
      have heq : (⟨d.val, hAE d.property⟩ : E) = T.inverseMap ⟨q, hq⟩ := Subtype.ext hd
      rw [heq, T.apply_inverse]
    have hh : q ∈ {c | ∃ a : A, (T.toMap ⟨a.val, hAE a.property⟩).val = c} := ⟨d, hmap⟩
    exact hImage.symm ▸ hh
  refine ⟨r, B, V, hV, hB, ?_⟩
  intro b c he
  let x := V.inverseMap b
  let y := V.inverseMap c
  have hx : (T.toMap ⟨x.val, hAE x.property⟩).val = b.val := by
    rw [← hcomm x]
    exact congrArg Subtype.val (V.apply_inverse b)
  have hy : (T.toMap ⟨y.val, hAE y.property⟩).val = c.val := by
    rw [← hcomm y]
    exact congrArg Subtype.val (V.apply_inverse c)
  have hxy : SameRV (T.toMap ⟨x.val, hAE x.property⟩).val
      (T.toMap ⟨y.val, hAE y.property⟩).val := by rw [hx, hy]; exact he
  obtain ⟨d, hd, hf⟩ := rvGraph_transfer f hAE T hRel x
    (T.toMap ⟨y.val, hAE y.property⟩) hxy
  rw [T.inverse_apply] at hd
  have hdy : d = y := Subtype.ext hd
  exact (hdy ▸ hf).symm

theorem unary_rvMap_preparation (h00 : M ⊨ Axioms.ACVF00)
    {a : ℕ} {A₀ : DefSet (M := M) S 1 a} {A : DefSet (M := M) S 1 m}
    {D : DefSet (M := M) S 0 k} (τ : SpecialBijection A₀ A) (f : Map A D) :
    ∃ r : ℕ, ∃ B : DefSet (M := M) S 1 r, ∃ V : SpecialBijection A B,
      (τ.chain.append V.chain).Alternating none ∧ IsRVPullback (carrier B) ∧
        ∀ b c : B, SameRV b.val c.val →
          (f (V.inverseMap b)).val.2 = (f (V.inverseMap c)).val.2 := by
  obtain ⟨r, B, V, hV, hB, hf⟩ := unary_rvMap_preparation_at_boundary h00 (τ.chain.lastKind none)
    (fun h => τ.chain.lastKind_tagged none (by intro he; cases he) h) f
  exact ⟨r, B, V, τ.chain.append_alternating V.chain none τ.alternating hV, hB, hf⟩

def flattenKeyMap {u v : ℕ} (D : PresentedSet (keySpace (M := M) u v) S) :
    Map D (PresentedSet.univ (pointSpace 0 (u + v)) S) :=
  Map.ofCodes (M := M) (sM := sM) (P := keySpace u v) (Q := pointSpace 0 (u + v))
    D (fun p => (Fin.elim0, Fin.append p.1 p.2))
    (fun z => Sum.elim Fin.elim0 (Fin.append (z ∘ Sum.inl) (z ∘ Sum.inr)))
    (by
      intro i
      cases i with
      | inl i => exact i.elim0
      | inr i =>
        cases i using Fin.addCases with
        | left i =>
          simpa only [Sum.elim_inr, Fin.append_left, Function.comp_apply, Sum.elim_inl] using
            rawProj S (.inl i : Fin u ⊕ Fin v)
        | right i =>
          simpa only [Sum.elim_inr, Fin.append_right, Function.comp_apply] using
            rawProj S (.inr i : Fin u ⊕ Fin v))
    (by
      intro c
      refine ⟨fun i => i.elim0, ?_⟩
      intro i
      cases i using Fin.addCases with
      | left i => simpa only [Sum.elim_inr, Fin.append_left, Function.comp_apply, Sum.elim_inl] using c.property.1 i
      | right i => simpa only [Sum.elim_inr, Fin.append_right, Function.comp_apply] using c.property.2 i)
    (by
      intro c
      refine Prod.ext (Subsingleton.elim _ _) ?_
      funext i
      cases i using Fin.addCases <;> apply Subtype.ext <;> simp)

/-- Every definable map on a unary mixed domain admits a contractible
refinement with an RV-pullback source. The output may have any finite
number of VF and RV coordinates. -/
theorem unary_map_preparation_at_boundary (h00 : M ⊨ Axioms.ACVF00)
    {u v : ℕ} {A : DefSet (M := M) S 1 m} {D : DefSet (M := M) S u v} (previous : Option Bool)
    (hTag : previous = some false → ∃ j, Tagged (carrier A) 0 j) (f : Map A D) :
    ∃ r : ℕ, ∃ B : DefSet (M := M) S 1 r, ∃ V : SpecialBijection A B,
      V.chain.Alternating previous ∧ IsRVPullback (carrier B) ∧
        Contractible (fun b : B => f (V.inverseMap b)) := by
  let g := Map.comp (flattenKeyMap (PresentedSet.univ (keySpace u v) S)) (Map.comp (keyMap D) f)
  obtain ⟨r, B, V, hV, hB, hg⟩ := unary_rvMap_preparation_at_boundary h00 previous hTag g
  refine ⟨r, B, V, hV, hB, ?_⟩
  intro b c he
  have hh := hg b c he
  change Fin.append (key (f (V.inverseMap b)).val).1 (key (f (V.inverseMap b)).val).2 =
    Fin.append (key (f (V.inverseMap c)).val).1 (key (f (V.inverseMap c)).val).2 at hh
  apply Prod.ext
  · funext i
    simpa only [Fin.append_left] using congrFun hh (Fin.castAdd v i)
  · funext i
    simpa only [Fin.append_right] using congrFun hh (Fin.natAdd u i)

theorem unary_map_preparation (h00 : M ⊨ Axioms.ACVF00)
    {a u v : ℕ} {A₀ : DefSet (M := M) S 1 a} {A : DefSet (M := M) S 1 m}
    {D : DefSet (M := M) S u v} (τ : SpecialBijection A₀ A) (f : Map A D) :
    ∃ r : ℕ, ∃ B : DefSet (M := M) S 1 r, ∃ V : SpecialBijection A B,
      (τ.chain.append V.chain).Alternating none ∧ IsRVPullback (carrier B) ∧
        Contractible (fun b : B => f (V.inverseMap b)) := by
  obtain ⟨r, B, V, hV, hB, hf⟩ := unary_map_preparation_at_boundary h00 (τ.chain.lastKind none)
    (fun h => τ.chain.lastKind_tagged none (by intro he; cases he) h) f
  exact ⟨r, B, V, τ.chain.append_alternating V.chain none τ.alternating hV, hB, hf⟩

theorem zero_map_preparation_at_boundary {u v : ℕ} (A : DefSet (M := M) S 0 m)
    {D : DefSet (M := M) S u v} (previous : Option Bool) (f : Map A D) :
    ∃ r : ℕ, ∃ B : DefSet (M := M) S 0 r, ∃ V : SpecialBijection A B,
      V.chain.Alternating previous ∧ IsRVPullback (carrier B) ∧
        Contractible (fun b : B => f (V.inverseMap b)) := by
  refine ⟨m, A, SpecialBijection.refl A, trivial, isRVPullback_zeroVF _, ?_⟩
  intro b c he
  have hbc : b = c := Subtype.ext (Prod.ext (Subsingleton.elim _ _) (((sameRV_iff _ _).mp he).2))
  subst c
  rfl

end SpecialTransformations.Section5
