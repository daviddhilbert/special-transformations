module

public import Section5.VerticalConstruction

@[expose] public section

/-!
# Definable indicators for geometric assembly

Membership is encoded by the existing RV values of VF zero and one. No
additional RV point, parameter or language symbol is introduced.
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

abbrev pPreimage (P : PresentedSpace (M := M)) (D : Set (Carrier P)) :=
  @DefinableGeometry.Space.preimage LRV M (CanonicalStructure.normalize (M := M)) P D

theorem oneCode_definable (S : Set M) {α : Type} : RawFun (M := M) S α (fun _ => iVFOne) := by
  let N := @CanonicalStructure.normalize M sM
  have he : @Structure.funMap LRV M N 0 Fn.vfOne Fin.elim0 = @iVFOne M sM :=
    @CanonicalStructure.normalize_fun M sM 0 Fn.vfOne Fin.elim0 (fun i => i.elim0)
  have h := @DefinableConstants.function_symbol M LRV N S 0 Fn.vfOne Fin.elim0 (fun i => i.elim0)
  rw [he] at h
  exact @DefinableConstants.constant M LRV N S _ h α

theorem rvConstant_definable {α : Type} (x : VF (M := M))
    (hx : RawFun S α (fun _ => x.val)) : RawFun S α (fun _ => (rv x).val) := by
  have hf := rvCode_definable (M := M) S (0 : Fin 1)
  have hh := @Set.DefinableFun.comp M LRV (CanonicalStructure.normalize (M := M))
    (Fin 1) α S _ inferInstance (fun _ _ => x.val) (fun _ => hx) hf
  have he : (fun _ : α → M => rvCode x.val) = (fun _ => (rv x).val) :=
    funext (fun _ => rvCode_eq x.val x.property)
  exact he ▸ hh

def membershipCode (D : DefSet (M := M) S n m) (z : Fin n ⊕ Fin m → M) : M :=
  if z ∈ pPreimage (pointSpace n m) (carrier D) then (rv (1 : VF (M := M))).val
  else (rv (0 : VF (M := M))).val

def membershipPoint (D : DefSet (M := M) S n m) (p : Point (M := M) n m) : Point (M := M) 0 1 :=
  (Fin.elim0, ![if p ∈ carrier D then rv (1 : VF (M := M)) else rv (0 : VF (M := M))])

def membershipMap (A D : DefSet (M := M) S n m) :
    Map A (PresentedSet.univ (pointSpace 0 1) S) :=
  Map.ofCodes (M := M) (sM := sM) (P := pointSpace n m) (Q := pointSpace 0 1) A
    (membershipPoint D) (fun z => Sum.elim Fin.elim0 (fun _ => membershipCode D z))
    (by
      intro i
      cases i with
      | inl i => exact i.elim0
      | inr i =>
        fin_cases i
        have hcond := setDefinable D
        have hone := rvConstant_definable (S := S) (α := Fin n ⊕ Fin m) (1 : VF (M := M))
          (oneCode_definable S)
        have hzero := rvConstant_definable (S := S) (α := Fin n ⊕ Fin m) (0 : VF (M := M))
          (zeroCode_definable S)
        letI := @CanonicalStructure.normalize M sM
        exact Set.DefinableFun.ite hcond hone hzero)
    (by
      intro c
      refine ⟨fun i => i.elim0, ?_⟩
      intro i
      fin_cases i
      change iRV (membershipCode D c.val)
      by_cases hc : c.val ∈ pPreimage (pointSpace n m) (carrier D)
      · rw [membershipCode, if_pos hc]
        exact (rv (1 : VF (M := M))).property
      · rw [membershipCode, if_neg hc]
        exact (rv (0 : VF (M := M))).property)
    (by
      intro c
      refine Prod.ext (Subsingleton.elim _ _) ?_
      funext i
      fin_cases i
      apply Subtype.ext
      have hcond : c.val ∈ pPreimage (pointSpace n m) (carrier D) ↔
          pDecode (pointSpace n m) c ∈ carrier D := by
        exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨c.property, h⟩⟩
      change membershipCode D c.val =
        (if pDecode (pointSpace n m) c ∈ carrier D then rv (1 : VF (M := M)) else rv (0 : VF (M := M))).val
      by_cases hc : pDecode (pointSpace n m) c ∈ carrier D
      · simp only [membershipCode, if_pos hc, if_pos (hcond.mpr hc)]
      · simp only [membershipCode, if_neg hc, if_neg (fun h => hc (hcond.mp h))])

theorem rv_zero_ne_one : rv (0 : VF (M := M)) ≠ rv (1 : VF (M := M)) := by
  intro he
  exact one_ne_zero ((rv_eq_zero_iff _).mp he.symm)

theorem membershipMap_iff (A D : DefSet (M := M) S n m) (a : A) :
    (membershipMap A D a).val.2 0 = rv (1 : VF (M := M)) ↔ a.val ∈ carrier D := by
  change (if a.val ∈ carrier D then rv (1 : VF (M := M)) else rv (0 : VF (M := M))) = rv 1 ↔ _
  by_cases ha : a.val ∈ carrier D <;>
    simp [ha, rv_zero_ne_one (M := M)]

theorem membershipMap_eq_iff (A D : DefSet (M := M) S n m) (a b : A) :
    (membershipMap A D a).val.2 0 = (membershipMap A D b).val.2 0 ↔
      (a.val ∈ carrier D ↔ b.val ∈ carrier D) := by
  change (if a.val ∈ carrier D then rv (1 : VF (M := M)) else rv (0 : VF (M := M))) =
    (if b.val ∈ carrier D then rv (1 : VF (M := M)) else rv (0 : VF (M := M))) ↔ _
  by_cases ha : a.val ∈ carrier D <;> by_cases hb : b.val ∈ carrier D <;>
    simp [ha, hb, rv_zero_ne_one (M := M), Ne.symm (rv_zero_ne_one (M := M))]

def constantRVMap (A : DefSet (M := M) S n m) (k : ℕ) :
    Map A (PresentedSet.univ (pointSpace 0 k) S) :=
  Map.ofCodes (M := M) (sM := sM) (P := pointSpace n m) (Q := pointSpace 0 k) A
    (fun _ => (Fin.elim0, fun _ => rv (0 : VF (M := M))))
    (fun _ => Sum.elim Fin.elim0 (fun _ => (rv (0 : VF (M := M))).val))
    (by
      intro i
      cases i with
      | inl i => exact i.elim0
      | inr i => exact rvConstant_definable (0 : VF (M := M)) (zeroCode_definable S))
    (by intro c; exact ⟨fun i => i.elim0, fun _ => (rv (0 : VF (M := M))).property⟩)
    (by intro c; exact Prod.ext (Subsingleton.elim _ _) rfl)

namespace Map

variable {u v : ℕ} {A D : DefSet (M := M) S n m} {B : DefSet (M := M) S u v}

/-- Extend a partial definable map by a specified definable fallback.
The complete graph remains over the original base. -/
def extend (f : Map D B) (g : Map A B) (hDA : carrier D ⊆ carrier A) : Map A B :=
  Map.mk (fun a => if h : a.val ∈ carrier D then f ⟨a.val, h⟩ else g a) (by
    have hnot : SetDefinable (pointSpace n m) S (carrier D)ᶜ :=
      @DefinableGeometry.Space.Definable.compl LRV M (CanonicalStructure.normalize (M := M))
        (pointSpace n m) S (carrier D) (setDefinable D)
    have hleft := SetDefinable.left_relation (pointSpace n m) (pointSpace u v) hnot
    have hh := RelationDefinable.union _ _ (Map.graph_definable f)
      (RelationDefinable.inter _ _ hleft (Map.graph_definable g))
    apply RelationDefinable.congr _ _ hh
    intro p z
    constructor
    · intro hz
      rcases hz with ⟨d, rfl, hd⟩ | ⟨hnot, a, rfl, ha⟩
      · refine ⟨⟨d.val, hDA d.property⟩, rfl, ?_⟩
        rw [dif_pos d.property]
        exact hd
      · refine ⟨a, rfl, ?_⟩
        rw [dif_neg hnot]
        exact ha
    · rintro ⟨a, rfl, hz⟩
      by_cases hd : a.val ∈ carrier D
      · left
        exact ⟨⟨a.val, hd⟩, rfl, by simpa only [dif_pos hd] using hz⟩
      · right
        exact ⟨hd, a, rfl, by simpa only [dif_neg hd] using hz⟩)

theorem extend_apply (f : Map D B) (g : Map A B) (hDA : carrier D ⊆ carrier A) (d : D) :
    Map.extend f g hDA ⟨d.val, hDA d.property⟩ = f d := by
  change (if h : d.val ∈ carrier D then f ⟨d.val, h⟩ else g ⟨d.val, hDA d.property⟩) = f d
  rw [dif_pos d.property]

end Map

namespace Map

variable {P Q R : PresentedSpace (M := M)}
variable {A : PresentedSet P S} {B : PresentedSet Q S} {D : PresentedSet R S}

def imageRepresentative (q : Map A B) (u : Map.image q) : A := Classical.choose u.property

theorem imageRepresentative_spec (q : Map A B) (u : Map.image q) :
    (q (imageRepresentative q u)).val = u.val := Classical.choose_spec u.property

/-- Descend a definable function through a definable map onto its actual
image. Fibre constancy supplies the well-definedness; the graph is an
existential composition of the given full graphs. -/
def descend (q : Map A B) (f : Map A D)
    (hconst : ∀ a b : A, (q a).val = (q b).val → f a = f b) : Map (Map.image q) D :=
  Map.mk (fun u => f (imageRepresentative q u)) (by
    have hr := RelationDefinable.comp _ _ _
      (RelationDefinable.swap _ _ (Map.graph_definable q)) (Map.graph_definable f)
    apply RelationDefinable.congr _ _ hr
    intro u v
    constructor
    · rintro ⟨p, ⟨a, ha, hqa⟩, ⟨b, hb, hfb⟩⟩
      have hab : a = b := Subtype.ext (ha.trans hb.symm)
      subst b
      let c : Map.image q := ⟨u, ⟨a, hqa⟩⟩
      refine ⟨c, rfl, ?_⟩
      have hc : (q (imageRepresentative q c)).val = (q a).val :=
        (imageRepresentative_spec q c).trans hqa.symm
      exact (congrArg Subtype.val (hconst _ a hc)).trans hfb
    · rintro ⟨u, rfl, he⟩
      let a := imageRepresentative q u
      exact ⟨a.val, ⟨a, rfl, imageRepresentative_spec q u⟩, a, rfl, he⟩)

theorem descend_apply (q : Map A B) (f : Map A D)
    (hconst : ∀ a b : A, (q a).val = (q b).val → f a = f b) (a : A) :
    Map.descend q f hconst (Map.toImage q a) = f a :=
  hconst _ a (imageRepresentative_spec q (Map.toImage q a))

theorem descend_unique (q : Map A B) (f : Map A D)
    (hconst : ∀ a b : A, (q a).val = (q b).val → f a = f b)
    (g : Map (Map.image q) D) (hg : ∀ a : A, g (Map.toImage q a) = f a) :
    g = Map.descend q f hconst := by
  apply Map.ext
  intro u
  let a := imageRepresentative q u
  have hu : Map.toImage q a = u := Subtype.ext (imageRepresentative_spec q u)
  rw [← hu, hg, Map.descend_apply]

end Map

def joinRVMap {a b : ℕ} (D : DefSet (M := M) S 0 a) (E : DefSet (M := M) S 0 b) :
    Map (PresentedSet.prod D E) (PresentedSet.univ (pointSpace 0 (a + b)) S) :=
  Map.ofCodes (M := M) (sM := sM) (P := spaceProd (pointSpace 0 a) (pointSpace 0 b))
    (Q := pointSpace 0 (a + b)) (PresentedSet.prod D E)
    (fun p => (Fin.elim0, Fin.append p.1.2 p.2.2))
    (fun z => Sum.elim Fin.elim0
      (Fin.append (fun i => z (.inl (.inr i))) (fun i => z (.inr (.inr i)))))
    (by
      intro i
      cases i with
      | inl i => exact i.elim0
      | inr i =>
        cases i using Fin.addCases with
        | left i =>
          simpa only [Sum.elim_inr, Fin.append_left] using
            rawProj S (.inl (.inr i) : (Fin 0 ⊕ Fin a) ⊕ (Fin 0 ⊕ Fin b))
        | right i =>
          simpa only [Sum.elim_inr, Fin.append_right] using
            rawProj S (.inr (.inr i) : (Fin 0 ⊕ Fin a) ⊕ (Fin 0 ⊕ Fin b)))
    (by
      intro c
      refine ⟨fun i => i.elim0, ?_⟩
      intro i
      cases i using Fin.addCases with
      | left i => simpa only [Function.comp_apply, Sum.elim_inr, Fin.append_left] using c.property.1.2 i
      | right i => simpa only [Function.comp_apply, Sum.elim_inr, Fin.append_right] using c.property.2.2 i)
    (by
      intro c
      refine Prod.ext (Subsingleton.elim _ _) ?_
      funext i
      cases i using Fin.addCases <;> apply Subtype.ext <;> simp)

def pairRVMaps {a b : ℕ} {A : DefSet (M := M) S n m}
    {D : DefSet (M := M) S 0 a} {E : DefSet (M := M) S 0 b} (f : Map A D) (g : Map A E) :
    Map A (PresentedSet.univ (pointSpace 0 (a + b)) S) :=
  Map.comp (joinRVMap D E) (Map.pair f g)

theorem Contractible.refine {l u v : ℕ} {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}
    {D : DefSet (M := M) S u v} {f : A → D} (hf : Contractible f)
    (T : SpecialBijection A B) : Contractible (fun b : B => f (T.inverseMap b)) := by
  intro b c he
  exact hf _ _ (T.inverse_contractible b c he)

theorem pairRVMaps_contractible_left {a b : ℕ} {A : DefSet (M := M) S n m}
    {D : DefSet (M := M) S 0 a} {E : DefSet (M := M) S 0 b} (f : Map A D) (g : Map A E)
    (hfg : Contractible (pairRVMaps f g)) : Contractible f := by
  intro x y he
  have hh := ((sameRV_iff _ _).mp (hfg x y he)).2
  apply (sameRV_iff _ _).mpr
  refine ⟨fun i => i.elim0, ?_⟩
  funext i
  have hv := congrFun hh (Fin.castAdd b i)
  change Fin.append (f x).val.2 (g x).val.2 (Fin.castAdd b i) =
    Fin.append (f y).val.2 (g y).val.2 (Fin.castAdd b i) at hv
  simpa only [Fin.append_left] using hv

theorem pairRVMaps_contractible_right {a b : ℕ} {A : DefSet (M := M) S n m}
    {D : DefSet (M := M) S 0 a} {E : DefSet (M := M) S 0 b} (f : Map A D) (g : Map A E)
    (hfg : Contractible (pairRVMaps f g)) : Contractible g := by
  intro x y he
  have hh := ((sameRV_iff _ _).mp (hfg x y he)).2
  apply (sameRV_iff _ _).mpr
  refine ⟨fun i => i.elim0, ?_⟩
  funext i
  have hv := congrFun hh (Fin.natAdd a i)
  change Fin.append (f x).val.2 (g x).val.2 (Fin.natAdd a i) =
    Fin.append (f y).val.2 (g y).val.2 (Fin.natAdd a i) at hv
  simpa only [Fin.append_right] using hv

theorem pairRVMaps_comp {n' m' a b : ℕ} {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n' m'}
    {D : DefSet (M := M) S 0 a} {E : DefSet (M := M) S 0 b} (f : Map A D) (g : Map A E)
    (h : Map B A) : Map.comp (pairRVMaps f g) h = pairRVMaps (Map.comp f h) (Map.comp g h) := by
  apply Map.ext
  intro x
  apply Subtype.ext
  rfl

def baseImage (A : DefSet (M := M) S (n + 1) m) : DefSet (M := M) S n m :=
  Map.image (dropHeadMap id A)

def baseProjection (A : DefSet (M := M) S (n + 1) m) : Map A (baseImage A) :=
  Map.toImage (dropHeadMap id A)

theorem baseImage_carrier (A : DefSet (M := M) S (n + 1) m) :
    carrier (baseImage A) = dropHead id '' carrier A := by
  ext p
  exact ⟨fun ⟨a, he⟩ => ⟨a.val, a.property, he⟩,
    fun ⟨a, ha, he⟩ => ⟨⟨a, ha⟩, he⟩⟩

theorem mem_baseImage (A : DefSet (M := M) S (n + 1) m) (p : Point (M := M) n m) :
    p ∈ carrier (baseImage A) ↔ ∃ x : VF (M := M), insertHead x p ∈ carrier A := by
  change (∃ a : A, dropHead id a.val = p) ↔ _
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨vfAt a.val 0, ?_⟩
    rw [← ha, insertHead_dropHead]
    exact a.property
  · rintro ⟨x, hx⟩
    exact ⟨⟨insertHead x p, hx⟩, dropHead_insertHead x p⟩

theorem dropHead_image_pullback {A : Set (Point (M := M) (n + 1) m)}
    (hA : IsRVPullback A) : IsRVPullback (dropHead id '' A) := by
  apply (isRVPullback_iff _).mpr
  rintro p ⟨a, ha, rfl⟩ q he
  obtain ⟨hv, ht⟩ := (sameRV_iff _ _).mp he
  let r : Point (M := M) (n + 1) m := (Fin.cons (vfAt a 0) q.1, q.2)
  have har : SameRV a r := by
    apply (sameRV_iff _ _).mpr
    refine ⟨?_, ?_⟩
    · intro i
      cases i using Fin.cases with
      | zero => rfl
      | succ i => exact hv i
    · exact ht
  refine ⟨r, (isRVPullback_iff _).mp hA a ha r har, ?_⟩
  rfl

theorem baseImage_pullback (A : DefSet (M := M) S (n + 1) m) (hA : IsRVPullback (carrier A)) :
    IsRVPullback (carrier (baseImage A)) := by
  exact (congrArg (fun Z : Set (Point (M := M) n m) => IsRVPullback Z) (baseImage_carrier A)).mpr
    (dropHead_image_pullback hA)

theorem baseImage_tagged (A : DefSet (M := M) S (n + 1) m) (j : Fin n) (k : Fin m)
    (hA : Tagged (carrier A) j.succ k) : Tagged (carrier (baseImage A)) j k := by
  have hh : Tagged (dropHead id '' carrier A) j k := by
    rintro p ⟨a, ha, rfl⟩
    exact hA a ha
  exact (congrArg (fun Z : Set (Point (M := M) n m) => Tagged Z j k) (baseImage_carrier A)).mpr hh

theorem replace_zero_insertHead (p : Point (M := M) (n + 1) m) (x : VF (M := M)) :
    replace 0 p x = insertHead x (dropHead id p) := by
  refine Prod.ext ?_ rfl
  funext i
  cases i using Fin.cases <;> simp [replace, insertHead, dropHead, vfAt]

def AllTagged {N : ℕ} (A : DefSet (M := M) S N m) : Prop :=
  ∀ j : Fin N, ∃ k : Fin m, Tagged (carrier A) j k

theorem canonicalImage_allTagged {N : ℕ} (A : DefSet (M := M) S N m) : AllTagged (canonicalImage A) := by
  intro j
  refine ⟨Fin.castAdd m j, ?_⟩
  exact (congrArg (fun Z : Set (Point (M := M) N (N + m)) => Tagged Z j (Fin.castAdd m j))
    (canonicalImage_carrier A)).mpr (canonical_tagged _ _)

theorem Chain.lastKind_allTagged {N a b : ℕ} {A : DefSet (M := M) S N a} {B : DefSet (M := M) S N b}
    (T : Chain S N A B) (previous : Option Bool) (hA : previous = some false → AllTagged A)
    (hT : T.lastKind previous = some false) : AllTagged B := by
  intro j
  exact T.lastKind_tagged_at j previous (fun h => hA h j) hT

theorem baseImage_allTagged (A : DefSet (M := M) S (n + 1) m) (hA : AllTagged A) : AllTagged (baseImage A) := by
  intro j
  obtain ⟨k, hk⟩ := hA j.succ
  exact ⟨k, baseImage_tagged A j k hk⟩

theorem headKey_eq_iff (p q : Point (M := M) (n + 1) m) :
    headKey p = headKey q ↔ TailEq p q ∧ SameRV p q := by
  constructor
  · intro he
    have htail : TailEq p q := fun i => congrFun (congrArg Prod.fst he) i
    have hlabels : p.2 = q.2 := by
      funext i
      simpa only [headKey, Fin.append_right] using
        congrArg (fun z : Point (M := M) n (1 + m) => z.2 (Fin.natAdd 1 i)) he
    have hhead : rv (vfAt p 0) = rv (vfAt q 0) :=
      congrArg (fun z : Point (M := M) n (1 + m) => z.2 (Fin.castAdd m (0 : Fin 1))) he
    refine ⟨htail, (sameRV_iff _ _).mpr ⟨?_, hlabels⟩⟩
    intro i
    cases i using Fin.cases with
    | zero => exact hhead
    | succ i => exact congrArg rv (htail i)
  · rintro ⟨htail, he⟩
    obtain ⟨hv, ht⟩ := (sameRV_iff _ _).mp he
    refine Prod.ext (funext htail) ?_
    change Fin.append (fun _ : Fin 1 => rv (p.1 0)) p.2 =
      Fin.append (fun _ : Fin 1 => rv (q.1 0)) q.2
    rw [hv 0, ht]

def headImage (A : DefSet (M := M) S (n + 1) m) : DefSet (M := M) S n (1 + m) :=
  Map.image (headKeyMap A)

theorem headImage_carrier (A : DefSet (M := M) S (n + 1) m) :
    carrier (headImage A) = headKey '' carrier A := by
  ext p
  constructor
  · rintro ⟨a, he⟩
    exact ⟨a.val, a.property, (headKeyMap_apply A a).symm.trans he⟩
  · rintro ⟨a, ha, he⟩
    exact ⟨⟨a, ha⟩, (headKeyMap_apply A ⟨a, ha⟩).trans he⟩

theorem headKey_image_pullback {A : Set (Point (M := M) (n + 1) m)}
    (hA : IsRVPullback A) : IsRVPullback (headKey '' A) := by
  apply (isRVPullback_iff _).mpr
  rintro p ⟨a, ha, rfl⟩ q he
  obtain ⟨hv, ht⟩ := (sameRV_iff _ _).mp he
  let r : Point (M := M) (n + 1) m :=
    (Fin.cons (vfAt a 0) q.1, fun i => q.2 (Fin.natAdd 1 i))
  have har : SameRV a r := by
    apply (sameRV_iff _ _).mpr
    refine ⟨?_, ?_⟩
    · intro i
      cases i using Fin.cases with
      | zero => rfl
      | succ i => exact hv i
    · funext i
      simpa only [headKey, Fin.append_right, r] using congrFun ht (Fin.natAdd 1 i)
  refine ⟨r, (isRVPullback_iff _).mp hA a ha r har, ?_⟩
  refine Prod.ext rfl ?_
  funext i
  cases i using Fin.addCases with
  | left i =>
    fin_cases i
    exact congrFun ht (Fin.castAdd m (0 : Fin 1))
  | right i => simp only [headKey, Fin.append_right, r]

theorem headImage_pullback (A : DefSet (M := M) S (n + 1) m) (hA : IsRVPullback (carrier A)) :
    IsRVPullback (carrier (headImage A)) := by
  exact (congrArg (fun Z : Set (Point (M := M) n (1 + m)) => IsRVPullback Z) (headImage_carrier A)).mpr
    (headKey_image_pullback hA)

theorem headImage_mono {A B : DefSet (M := M) S (n + 1) m} (hAB : carrier A ⊆ carrier B) :
    carrier (headImage A) ⊆ carrier (headImage B) := by
  intro p hp
  have h := Set.image_mono (f := headKey (M := M)) hAB
  exact (headImage_carrier B).symm ▸ h ((headImage_carrier A) ▸ hp)

theorem headImage_tagged (A : DefSet (M := M) S (n + 1) m) (j : Fin n) (k : Fin m)
    (hA : Tagged (carrier A) j.succ k) :
    Tagged (carrier (headImage A)) j (Fin.natAdd 1 k) := by
  have hh : Tagged (headKey '' carrier A) j (Fin.natAdd 1 k) := by
    rintro p ⟨a, ha, rfl⟩
    simpa only [headKey, Fin.append_right] using hA a ha
  exact (congrArg (fun Z : Set (Point (M := M) n (1 + m)) => Tagged Z j (Fin.natAdd 1 k))
    (headImage_carrier A)).mpr hh

theorem headImage_allTagged (A : DefSet (M := M) S (n + 1) m) (hA : AllTagged A) : AllTagged (headImage A) := by
  intro j
  obtain ⟨k, hk⟩ := hA j.succ
  exact ⟨Fin.natAdd 1 k, headImage_tagged A j k hk⟩

def headDescend {u v : ℕ} {A : DefSet (M := M) S (n + 1) m} {D : DefSet (M := M) S u v}
    (f : Map A D)
    (hconst : ∀ a b : A, SameRV a.val b.val → TailEq a.val b.val → f a = f b) :
    Map (headImage A) D :=
  Map.descend (headKeyMap A) f (fun a b he => by
    have hk : headKey a.val = headKey b.val :=
      (headKeyMap_apply A a).symm.trans (he.trans (headKeyMap_apply A b))
    obtain ⟨ht, hr⟩ := (headKey_eq_iff _ _).mp hk
    exact hconst a b hr ht)

theorem headDescend_apply {u v : ℕ} {A : DefSet (M := M) S (n + 1) m} {D : DefSet (M := M) S u v}
    (f : Map A D)
    (hconst : ∀ a b : A, SameRV a.val b.val → TailEq a.val b.val → f a = f b) (a : A) :
    headDescend f hconst (Map.toImage (headKeyMap A) a) = f a :=
  Map.descend_apply _ _ _ a

namespace SpecialBijection

variable {l : ℕ} {A D : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}

/-- Restrict an already constructed chain once the domain predicate is
constant on its inverse RV fibres. The restriction is itself a genuine
special bijection, with the same boundary alternation. -/
theorem restrict_prepared_at (T : SpecialBijection A B) (hB : IsRVPullback (carrier B))
    (hDA : carrier D ⊆ carrier A) (previous : Option Bool) (hT : T.chain.Alternating previous)
    (hconst : ∀ b c : B, SameRV b.val c.val →
      ((T.inverseMap b).val ∈ carrier D ↔ (T.inverseMap c).val ∈ carrier D)) :
    ∃ E : DefSet (M := M) S n l, ∃ U : SpecialBijection D E,
      U.chain.Alternating previous ∧ IsRVPullback (carrier E) := by
  obtain ⟨E, U, hU, hEB, hImage, _⟩ := T.restrict_at D hDA previous hT
  refine ⟨E, U, hU, (isRVPullback_iff _).mpr ?_⟩
  intro p hp q hpq
  have hqB := (isRVPullback_iff _).mp hB p (hEB hp) q hpq
  let b : B := ⟨p, hEB hp⟩
  let c : B := ⟨q, hqB⟩
  have hpImage : ∃ a : D, (T.toMap ⟨a.val, hDA a.property⟩).val = p := by
    change p ∈ {z | ∃ a : D, (T.toMap ⟨a.val, hDA a.property⟩).val = z}
    exact hImage ▸ hp
  obtain ⟨a, ha⟩ := hpImage
  have hbD : (T.inverseMap b).val ∈ carrier D := by
    have heq : T.toMap ⟨a.val, hDA a.property⟩ = b := Subtype.ext ha
    rw [← heq, T.inverse_apply]
    exact a.property
  have hcD := (hconst b c hpq).mp hbD
  have hqImage : q ∈ {z | ∃ a : D, (T.toMap ⟨a.val, hDA a.property⟩).val = z} := by
    refine ⟨⟨(T.inverseMap c).val, hcD⟩, ?_⟩
    have heq : (⟨(T.inverseMap c).val, hDA hcD⟩ : A) = T.inverseMap c := Subtype.ext rfl
    rw [heq, T.apply_inverse]
  exact hImage.symm ▸ hqImage

theorem restrict_contracted_indicator_at (T : SpecialBijection A B) (hB : IsRVPullback (carrier B))
    (hDA : carrier D ⊆ carrier A) (previous : Option Bool) (hT : T.chain.Alternating previous)
    (hflag : Contractible (fun b : B => membershipMap A D (T.inverseMap b))) :
    ∃ E : DefSet (M := M) S n l, ∃ U : SpecialBijection D E,
      U.chain.Alternating previous ∧ IsRVPullback (carrier E) := by
  apply T.restrict_prepared_at hB hDA previous hT
  intro b c he
  have hh := congrFun (((sameRV_iff _ _).mp (hflag b c he)).2) 0
  exact (membershipMap_eq_iff A D (T.inverseMap b) (T.inverseMap c)).mp hh

end SpecialBijection

end SpecialTransformations.Section5

namespace SpecialTransformations.Section5

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m l k : ℕ}
variable {A : DefSet (M := M) S (n + 1) m} {B : DefSet (M := M) S (n + 1) l}

def VerticalRelationContractible (U : Set (Point (M := M) (n + 1) k))
    (T : SpecialBijection A B) : Prop :=
  ∀ b c : B, SameRV b.val c.val → TailEq b.val c.val → ∀ ys : Fin k → RV (M := M),
    (((T.inverseMap b).val.1, ys) ∈ U ↔ ((T.inverseMap c).val.1, ys) ∈ U)

/-- Root-free constancy on the actual inverse head slices. The root-free
family interface is earlier-section input; the slice geometry is derived
from the constructed compatible chain. -/
theorem vertical_relation_of_zero_obstacles {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (U : Set (Point (M := M) (n + 1) k)) (R : VerticalRootFamily A)
    (hO : ∀ (p : Point (M := M) n m) (a : VF (M := M)) (r : Section3.Balls.OpenRadius Γ),
      (∀ x ∈ Section3.Balls.openDisc v a r, insertHead x p ∈ carrier A) →
      (∀ x ∈ R.fibre p, x ∉ Section3.Balls.openDisc v a r) →
      ∀ x ∈ Section3.Balls.openDisc v a r, ∀ y ∈ Section3.Balls.openDisc v a r,
      ∀ ys : Fin k → RV (M := M),
        (((insertHead x p).1, ys) ∈ U ↔ ((insertHead y p).1, ys) ∈ U))
    (T : SpecialBijection A B) (hT : T.chain.HeadCompatible) (hB : IsRVPullback (carrier B))
    (hz : ∀ a : A, a.val ∈ carrier R.set → vfAt (T.toMap a).val 0 = 0) :
    VerticalRelationContractible U T := by
  intro b c hbc htail ys
  obtain ⟨hrv, hlabels⟩ := (sameRV_iff _ _).mp hbc
  by_cases hb : vfAt b.val 0 = 0
  · have hc : vfAt c.val 0 = 0 := (rv_eq_zero_iff _).mp ((hrv 0).symm.trans (congrArg rv hb))
    have he : b = c := by
      apply Subtype.ext
      refine Prod.ext ?_ hlabels
      funext i
      cases i using Fin.cases with
      | zero => exact hb.trans hc.symm
      | succ i => exact htail i
    subst c
    rfl
  · obtain ⟨he, _⟩ := T.compatible_inverse_slice v hv hT hB b hb
    let a₀ := T.inverseMap b
    let p := dropHead id a₀.val
    let centre := vfAt a₀.val 0
    have hrad : v (vfAt b.val 0) ≠ 0 := (map_ne_zero v).mpr hb
    let ρ : Section3.Balls.OpenRadius Γ := Section3.Balls.openRadius (v (vfAt b.val 0)) hrad
    have hmem (x : VF (M := M)) (hx : x ∈ Section3.Balls.openDisc v centre ρ) :
        insertHead x p ∈ T.inverseSlice b := by
      rw [he]
      refine ⟨?_, (fun _ => rfl), rfl⟩
      change v (x - centre) < v (vfAt b.val 0)
      simpa only [ρ, Section3.Balls.openDisc_openRadius,
        Set.mem_ofPred_eq] using hx
    have hball : ∀ x ∈ Section3.Balls.openDisc v centre ρ, insertHead x p ∈ carrier A := by
      intro x hx
      obtain ⟨a, ha, _, _⟩ := hmem x hx
      exact ha ▸ a.property
    have havoid : ∀ x ∈ R.fibre p, x ∉ Section3.Balls.openDisc v centre ρ := by
      intro x hx hxd
      obtain ⟨a, ha, hrv, _⟩ := hmem x hxd
      have hroot : a.val ∈ carrier R.set := ha.symm ▸ (R.mem_fibre p x).mp hx
      have hzero := hz a hroot
      have hh := ((sameRV_iff _ _).mp hrv).1 0
      change rv (vfAt (T.toMap a).val 0) = rv (vfAt b.val 0) at hh
      exact hb ((rv_eq_zero_iff _).mp (hh.symm.trans (congrArg rv hzero)))
    have hcF : (T.inverseMap c).val ∈ T.inverseSlice b :=
      ⟨T.inverseMap c, rfl, by rw [T.apply_inverse]; exact hbc.symm,
        by rw [T.apply_inverse]; intro i; exact (htail i).symm⟩
    rw [he] at hcF
    have hy : vfAt (T.inverseMap c).val 0 ∈ Section3.Balls.openDisc v centre ρ := by
      simpa only [ρ, Section3.Balls.openDisc_openRadius,
        Set.mem_ofPred_eq] using hcF.1
    have hpC : dropHead id (T.inverseMap c).val = p := Prod.ext (funext hcF.2.1) hcF.2.2
    have hOrigB : insertHead centre p = a₀.val := insertHead_dropHead a₀.val
    have hOrigC : insertHead (vfAt (T.inverseMap c).val 0) p = (T.inverseMap c).val := by
      rw [← hpC, insertHead_dropHead]
    have hh := hO p centre ρ hball havoid centre (Section3.Balls.centre_mem_openDisc v centre ρ)
      (vfAt (T.inverseMap c).val 0) hy ys
    rw [hOrigB, hOrigC] at hh
    exact hh

end SpecialTransformations.Section5
