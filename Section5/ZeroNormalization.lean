import Section5.GammaRestriction

/-!
# Nonzero active loci for Definition 5.1

The zero RV fibre is a singleton, and its centripetal map is the identity.
Deleting it from the active locus therefore changes neither the map nor its
image. The resulting focus has exactly the printed C-sharp codomain. This
normalization uses no new parameters and also preserves original-base Gamma
graphs. It is a choice of locus, not a second absorbing RV point or an erratum.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Section5

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}

/-- The retained tag, not merely its valuation, is different from rv(0). -/
def nonzeroTag (k : Fin m) : Set (Point (M := M) n m) :=
  {p | p.2 k ≠ rv (0 : VF (M := M))}

theorem nonzeroTag_pullback (k : Fin m) :
    IsRVPullback (nonzeroTag (M := M) (n := n) k) := by
  apply (isRVPullback_iff _).mpr
  intro p hp q he
  have ht := ((sameRV_iff _ _).mp he).2
  change q.2 k ≠ rv (0 : VF (M := M))
  rw [← ht]
  exact hp

theorem nonzeroTag_definable (k : Fin m) :
    SetDefinable (pointSpace (M := M) n m) S (nonzeroTag k) := by
  have hd := setDefinable (PresentedSet.univ (pointSpace (M := M) n m) S)
  have hz := rvConstant_definable (S := S) (α := Fin n ⊕ Fin m)
    (0 : VF (M := M)) (zeroCode_definable S)
  have hp := rawProj (M := M) S (Sum.inr k : Fin n ⊕ Fin m)
  have hi := @Set.DefinableFun.ofPred_eq M LRV (CanonicalStructure.normalize (M := M))
    (Fin n ⊕ Fin m) S _ _ hp hz
  have hc := @Set.Definable.compl M S LRV (CanonicalStructure.normalize (M := M)) _ _ hi
  have ht := @Set.Definable.inter M S LRV (CanonicalStructure.normalize (M := M))
    (Fin n ⊕ Fin m) _ _ hd hc
  change @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin n ⊕ Fin m)
    {z | ∃ hz : z ∈ pDomain (pointSpace n m),
      (pDecode (pointSpace n m) ⟨z, hz⟩).2 k ≠ rv (0 : VF (M := M))}
  convert ht using 1
  ext z
  constructor
  · rintro ⟨hz, hp⟩
    exact ⟨⟨hz, Set.mem_univ _⟩, fun he => hp (Subtype.ext he)⟩
  · rintro ⟨⟨hz, _⟩, hp⟩
    exact ⟨hz, fun he => hp (congrArg Subtype.val he)⟩

/-- Projection away from the changed VF coordinate, with every RV tag retained.
The strict comparison uses the paper's order, directly through iLe. -/
def printedSharp (C : Set (Point (M := M) n m)) (j : Fin n) (k : Fin m) :
    Set (Point (M := M) n m) :=
  {q | ∃ p ∈ C, erase j p = erase j q ∧ ¬ iLe (rv (vfAt q j)).val (p.2 k).val}

def printedTarget (A C : Set (Point (M := M) n m)) (j : Fin n) (k : Fin m) :
    Set (Point (M := M) n m) := printedSharp C j k ∪ (hull A \ C)

namespace Focus

variable {A : DefSet (M := M) S n m} {j : Fin n} {k : Fin m}

/-- The union in the paper is genuinely disjoint: a strict new RV value
cannot satisfy the old hull's retained tag equality. -/
theorem printedSharp_disjoint_hull (D : Focus A j k) :
    Disjoint (printedSharp D.locus j k) (hull (carrier A)) := by
  apply Set.disjoint_left.mpr
  intro q hq hh
  obtain ⟨p, _, he, hs⟩ := hq
  have ht := congrArg (fun r : Point (M := M) n m => r.2) he
  change p.2 = q.2 at ht
  have htag := tagged_hull D.tagged q hh
  have heq : p.2 k = rv (vfAt q j) := (congrFun ht k).trans htag
  rw [heq] at hs
  exact hs (RVCalc.le_refl_rv hM (rv (vfAt q j)).property)

theorem printedTarget_disjoint (D : Focus A j k) :
    Disjoint (printedSharp D.locus j k) (hull (carrier A) \ D.locus) :=
  D.printedSharp_disjoint_hull.mono_right Set.sdiff_subset

def withoutZero (D : Focus A j k) : Focus A j k where
  tagged := D.tagged
  locus := D.locus ∩ nonzeroTag k
  locus_pullback := isRVPullback_inter D.locus_pullback (nonzeroTag_pullback k)
  locus_subset := fun _ hp => D.locus_subset hp.1
  center := D.center
  independent p hp q hq he := D.independent p ⟨hp.1, hp.2.1⟩ q ⟨hq.1, hq.2.1⟩ he
  center_mem p hp := ⟨D.center_mem p ⟨hp.1, hp.2.1⟩, hp.2.2⟩
  locus_definable := SetDefinable.inter _ D.locus_definable (nonzeroTag_definable k)
  center_graph := by
    have hn := SetDefinable.left_relation (pointSpace (M := M) n m) (Section4.vfSpace 1)
      (nonzeroTag_definable (S := S) k)
    apply RelationDefinable.congr _ _ (RelationDefinable.inter _ _ D.center_graph hn)
    intro p z
    exact ⟨fun ⟨⟨⟨ha, hc⟩, hz⟩, hn⟩ => ⟨⟨ha, hc, hn⟩, hz⟩,
      fun ⟨⟨ha, hc, hn⟩, hz⟩ => ⟨⟨⟨ha, hc⟩, hz⟩, hn⟩⟩

theorem withoutZero_nonzero (D : Focus A j k) (p : Point (M := M) n m)
    (hp : p ∈ D.withoutZero.locus) : p.2 k ≠ rv (0 : VF (M := M)) := hp.2

theorem withoutZero_eta (D : Focus A j k) (p : Point (M := M) n m)
    (hp : p ∈ carrier A) : D.withoutZero.toFocusGeometry.eta p = D.toFocusGeometry.eta p := by
  by_cases hc : p ∈ D.locus
  · by_cases hn : p ∈ nonzeroTag k
    · simp [FocusGeometry.eta, withoutZero, hc, hn]
    · have ht : p.2 k = rv (0 : VF (M := M)) := not_not.mp hn
      have hx : vfAt p j = 0 := (rv_eq_zero_iff _).mp ((D.tagged p hp).symm.trans ht)
      have hz : D.center p = 0 := (rv_eq_zero_iff _).mp
        ((D.toFocusGeometry.center_sameRV p ⟨hp, hc⟩).trans ((D.tagged p hp).symm.trans ht))
      have hr : replace j p (vfAt p j - D.center p) = p := by
        rw [hz, sub_zero]
        exact Prod.ext (Function.update_eq_self j p.1) rfl
      simp only [FocusGeometry.eta, withoutZero, Set.mem_inter_iff, hc, hn,
        and_false, if_false, if_true]
      change p = replace j p (vfAt p j - D.center p)
      exact hr.symm
  · simp [FocusGeometry.eta, withoutZero, hc]

theorem withoutZero_image (D : Focus A j k) : D.withoutZero.etaImage = D.etaImage := by
  apply PresentedSet.eq_of_carrier_eq
  change carrier D.withoutZero.etaImage = carrier D.etaImage
  rw [etaImage_carrier, etaImage_carrier]
  exact Set.image_congr (fun p hp => D.withoutZero_eta p hp)

/-- Every nonzero active locus has the printed C-sharp codomain. -/
theorem eta_printedTarget (D : Focus A j k)
    (hn : ∀ p ∈ D.locus, p.2 k ≠ rv (0 : VF (M := M)))
    (p : Point (M := M) n m) (hp : p ∈ carrier A) :
    D.toFocusGeometry.eta p ∈ printedTarget (carrier A) D.locus j k := by
  by_cases hc : p ∈ D.locus
  · left
    refine ⟨p, hc, (D.toFocusGeometry.erase_eta p).symm, ?_⟩
    rw [D.tagged p hp]
    apply D.toFocusGeometry.eta_target_strict p ⟨hp, hc⟩
    intro hz
    apply hn p hc
    simpa [hz] using D.tagged p hp
  · right
    rw [FocusGeometry.eta, if_neg hc]
    exact ⟨subset_hull _ hp, hc⟩

/-- Zero-coordinate points belong to the inactive part hull(A) minus the new
locus; they are not required to satisfy an impossible strict comparison. -/
theorem withoutZero_printedTarget (D : Focus A j k) (p : Point (M := M) n m)
    (hp : p ∈ carrier A) : D.withoutZero.toFocusGeometry.eta p ∈
      printedTarget (carrier A) D.withoutZero.locus j k :=
  D.withoutZero.eta_printedTarget D.withoutZero_nonzero p hp

end Focus

theorem GammaFocusDefinable.withoutZero {B : Section3.GammaParameters.Base (M := M)}
    (hΓ : GammaLogicInput B) {A : DefSet (M := M) S n m} {j : Fin n} {k : Fin m}
    (D : Focus A j k) (hD : GammaFocusDefinable B D) : GammaFocusDefinable B D.withoutZero := by
  have hn := hΓ.real_set (nonzeroTag (M := M) (n := n) k)
    (nonzeroTag_definable (S := B.real) k)
  refine ⟨hΓ.inter hD.1 hn, ?_⟩
  apply GammaGraphDefinable.congr (hΓ.restrict_graph hn hD.2)
  intro p z
  exact ⟨fun ⟨hn, ⟨ha, hc⟩, hz⟩ => ⟨⟨ha, hc, hn⟩, hz⟩,
    fun ⟨⟨ha, hc, hn⟩, hz⟩ => ⟨hn, ⟨ha, hc⟩, hz⟩⟩

namespace Primitive

variable {l : ℕ} {A : DefSet (M := M) S n m} {C : DefSet (M := M) S n l}

/-- Every active centripetal locus excludes the zero retained tag. -/
def NonzeroLoci : Primitive S n A C → Prop
  | .canonical _ => True
  | @centripetal _ _ _ _ _ _ _ _ k D => ∀ p ∈ D.locus, p.2 k ≠ rv (0 : VF (M := M))

def withoutZero : Primitive S n A C → Primitive S n A C
  | .canonical A => .canonical A
  | .centripetal D => D.withoutZero_image ▸ (.centripetal D.withoutZero)

private theorem cast_value {C' : DefSet (M := M) S n l} (he : C = C')
    (p : Primitive S n A C) (a : A) :
    ((he ▸ p).toMap a).val = (p.toMap a).val := by cases he; rfl

private theorem cast_kind {C' : DefSet (M := M) S n l} (he : C = C')
    (p : Primitive S n A C) : (he ▸ p).kind = p.kind := by cases he; rfl

private theorem cast_length {C' : DefSet (M := M) S n l} (he : C = C')
    (p : Primitive S n A C) : (he ▸ p).length = p.length := by cases he; rfl

private theorem cast_nonzero {C' : DefSet (M := M) S n l} (he : C = C')
    (p : Primitive S n A C) : (he ▸ p).NonzeroLoci ↔ p.NonzeroLoci := by cases he; rfl

theorem withoutZero_nonzero (p : Primitive S n A C) : p.withoutZero.NonzeroLoci := by
  cases p with
  | canonical A => trivial
  | centripetal D =>
    exact (cast_nonzero D.withoutZero_image (.centripetal D.withoutZero)).mpr
      D.withoutZero_nonzero

theorem withoutZero_kind (p : Primitive S n A C) : p.withoutZero.kind = p.kind := by
  cases p with
  | canonical A => rfl
  | centripetal D => exact cast_kind D.withoutZero_image (.centripetal D.withoutZero)

theorem withoutZero_length (p : Primitive S n A C) : p.withoutZero.length = p.length := by
  cases p with
  | canonical A => rfl
  | centripetal D => exact cast_length D.withoutZero_image (.centripetal D.withoutZero)

theorem withoutZero_toMap (p : Primitive S n A C) : p.withoutZero.toMap = p.toMap := by
  apply Map.ext
  intro a
  apply Subtype.ext
  cases p with
  | canonical A => rfl
  | centripetal D =>
    exact (cast_value D.withoutZero_image (.centripetal D.withoutZero) a).trans
      (D.withoutZero_eta a.val a.property)

private theorem cast_gamma {C' : DefSet (M := M) S n l} (he : C = C')
    (p : Primitive S n A C) (B : Section3.GammaParameters.Base (M := M)) :
    GammaPrimitiveDefinable B (he ▸ p) ↔ GammaPrimitiveDefinable B p := by cases he; rfl

theorem withoutZero_gamma (p : Primitive S n A C)
    {B : Section3.GammaParameters.Base (M := M)} (hΓ : GammaLogicInput B)
    (hp : GammaPrimitiveDefinable B p) : GammaPrimitiveDefinable B p.withoutZero := by
  cases p with
  | canonical A => exact hp
  | centripetal D =>
    exact (cast_gamma D.withoutZero_image (.centripetal D.withoutZero) B).mpr
      ⟨hp.1, GammaFocusDefinable.withoutZero hΓ D hp.2⟩

end Primitive

namespace Chain

variable {a b : ℕ} {A : DefSet (M := M) S n a} {C : DefSet (M := M) S n b}

def NonzeroLoci {a₁ b₁ : ℕ} {X : DefSet (M := M) S n a₁}
    {Y : DefSet (M := M) S n b₁} : Chain S n X Y → Prop
  | .nil _ => True
  | .cons p tail => p.NonzeroLoci ∧ tail.NonzeroLoci

def withoutZero {a₁ b₁ : ℕ} {X : DefSet (M := M) S n a₁}
    {Y : DefSet (M := M) S n b₁} : Chain S n X Y → Chain S n X Y
  | .nil A => .nil A
  | .cons p tail => .cons p.withoutZero tail.withoutZero

theorem withoutZero_nonzero (T : Chain S n A C) : T.withoutZero.NonzeroLoci := by
  induction T with
  | nil _ => trivial
  | cons p tail ih => exact ⟨p.withoutZero_nonzero, ih⟩

theorem withoutZero_toMap (T : Chain S n A C) : T.withoutZero.toMap = T.toMap := by
  induction T with
  | nil _ => rfl
  | cons p tail ih =>
    change Map.comp tail.withoutZero.toMap p.withoutZero.toMap = Map.comp tail.toMap p.toMap
    rw [ih, p.withoutZero_toMap]

theorem withoutZero_length (T : Chain S n A C) : T.withoutZero.length = T.length := by
  induction T with
  | nil _ => rfl
  | cons p tail ih => exact congrArg₂ (· + ·) p.withoutZero_length ih

theorem withoutZero_alternating (T : Chain S n A C) (previous : Option Bool) :
    T.withoutZero.Alternating previous ↔ T.Alternating previous := by
  induction T generalizing previous with
  | nil _ => rfl
  | cons p tail ih =>
    rw [withoutZero, cons_alternating_iff, cons_alternating_iff, p.withoutZero_kind, ih]

theorem withoutZero_gamma (T : Chain S n A C)
    {B : Section3.GammaParameters.Base (M := M)} (hΓ : GammaLogicInput B)
    (hT : GammaChainDefinable B T) : GammaChainDefinable B T.withoutZero := by
  induction T with
  | nil _ => exact hT
  | cons p tail ih => exact ⟨p.withoutZero_gamma hΓ hT.1, ih hT.2⟩

end Chain

namespace SpecialBijection

variable {l : ℕ} {A : DefSet (M := M) S n m} {C : DefSet (M := M) S n l}

def withoutZero (T : SpecialBijection A C) : SpecialBijection A C :=
  ⟨T.chain.withoutZero, (T.chain.withoutZero_alternating none).mpr T.alternating⟩

theorem withoutZero_nonzero (T : SpecialBijection A C) : T.withoutZero.chain.NonzeroLoci :=
  T.chain.withoutZero_nonzero

theorem withoutZero_toMap (T : SpecialBijection A C) : T.withoutZero.toMap = T.toMap :=
  T.chain.withoutZero_toMap

theorem withoutZero_inverseMap (T : SpecialBijection A C) :
    T.withoutZero.inverseMap = T.inverseMap := by
  apply Map.ext
  intro c
  apply T.bijective.1
  have hleft : T.toMap (T.withoutZero.inverseMap c) = c := by
    rw [← T.withoutZero_toMap]
    exact T.withoutZero.apply_inverse c
  exact hleft.trans (T.apply_inverse c).symm

theorem withoutZero_length (T : SpecialBijection A C) : T.withoutZero.length = T.length :=
  T.chain.withoutZero_length

/-- Same endpoints, same full maps and inverse maps, same length, and an
alternating chain whose active loci all admit the printed strict target. -/
theorem paper_representative (T : SpecialBijection A C) :
    ∃ U : SpecialBijection A C, U.chain.NonzeroLoci ∧ U.toMap = T.toMap ∧
      U.inverseMap = T.inverseMap ∧ U.length = T.length :=
  ⟨T.withoutZero, T.withoutZero_nonzero, T.withoutZero_toMap,
    T.withoutZero_inverseMap, T.withoutZero_length⟩

theorem paper_representative_gamma (T : SpecialBijection A C)
    {B : Section3.GammaParameters.Base (M := M)} (hΓ : GammaLogicInput B)
    (hT : GammaChainDefinable B T.chain) :
    ∃ U : SpecialBijection A C, U.chain.NonzeroLoci ∧ GammaChainDefinable B U.chain ∧
      U.toMap = T.toMap ∧ U.inverseMap = T.inverseMap ∧ U.length = T.length :=
  ⟨T.withoutZero, T.withoutZero_nonzero, T.chain.withoutZero_gamma hΓ hT,
    T.withoutZero_toMap, T.withoutZero_inverseMap, T.withoutZero_length⟩

end SpecialBijection

namespace GammaSpecialBijection

variable {B : Section3.GammaParameters.Base (M := M)} {l : ℕ}
variable {A : Set (Point (M := M) n m)} {C : Set (Point (M := M) n l)}

/-- Normalize without enlarging either the original Gamma base or its internal
real-code presentation. The original source and target presentations are kept. -/
def withoutZero (hΓ : GammaLogicInput B) (T : GammaSpecialBijection B A C) :
    GammaSpecialBijection B A C where
  codes := T.codes
  real_contains := T.real_contains
  source := T.source
  target := T.target
  source_eq := T.source_eq
  target_eq := T.target_eq
  special := T.special.withoutZero
  invariant_graphs := T.special.chain.withoutZero_gamma hΓ T.invariant_graphs

theorem withoutZero_spec (hΓ : GammaLogicInput B) (T : GammaSpecialBijection B A C) :
    (T.withoutZero hΓ).codes = T.codes ∧
    (T.withoutZero hΓ).source = T.source ∧ (T.withoutZero hΓ).target = T.target ∧
    (T.withoutZero hΓ).special.chain.NonzeroLoci ∧
    (T.withoutZero hΓ).special.toMap = T.special.toMap ∧
    (T.withoutZero hΓ).special.inverseMap = T.special.inverseMap ∧
    (T.withoutZero hΓ).special.length = T.special.length :=
  ⟨rfl, rfl, rfl, T.special.withoutZero_nonzero, T.special.withoutZero_toMap,
    T.special.withoutZero_inverseMap, T.special.withoutZero_length⟩

end GammaSpecialBijection
end SpecialTransformations.Section5
