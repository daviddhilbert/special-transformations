import Section5.Geometry
import Section4.Spaces
import Section4.CodeMaps
import Section4.DefinableCategory
import Section3.FiniteBarycentricCode
import Section3.PolynomialRVConstant

noncomputable section

/- Expose the finite tuple carriers and indices to elaboration. This local
transparency setting does not change the imported definitions or proof terms. -/
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval

/-!
# The geometric part of a focus map

Definition 5.1, with the targeted coordinate and the retained RV label
explicit. This module separates the elementary injectivity argument from
definability. Definable focus data are added in Focus; this geometric
structure alone is not called a definable special bijection.
-/

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Section5

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {n m : ℕ}

noncomputable def replace (j : Fin n) (p : Point (M := M) n m) (a : VF (M := M)) :
    Point (M := M) n m := (Function.update p.1 j a, p.2)

noncomputable def erase (j : Fin n) (p : Point (M := M) n m) : Point (M := M) n m :=
  replace j p 0

def Tagged (A : Set (Point (M := M) n m)) (j : Fin n) (k : Fin m) : Prop :=
  ∀ p ∈ A, p.2 k = rv (p.1 j)

theorem canonical_tagged (A : Set (Point (M := M) n m)) (j : Fin n) :
    Tagged (canonical '' A) j (Fin.castAdd m j) := by
  rintro _ ⟨p, hp, rfl⟩
  exact canonical_new p j

theorem tagged_hull {A : Set (Point (M := M) n m)} {j : Fin n} {k : Fin m}
    (hA : Tagged A j k) : Tagged (hull A) j k := by
  rintro p ⟨q, hq, he⟩
  obtain ⟨hv, hr⟩ := (sameRV_iff q p).mp he
  exact (congrFun hr k).symm.trans ((hA q hq).trans (hv j))

structure FocusGeometry (A : Set (Point (M := M) n m)) (j : Fin n) (k : Fin m) where
  tagged : Tagged A j k
  locus : Set (Point (M := M) n m)
  locus_pullback : IsRVPullback locus
  locus_subset : locus ⊆ hull A
  center : Point (M := M) n m → VF (M := M)
  independent : ∀ p ∈ A ∩ locus, ∀ q ∈ A ∩ locus,
    erase j p = erase j q → center p = center q
  center_mem : ∀ p ∈ A ∩ locus, replace j p (center p) ∈ locus

namespace FocusGeometry

variable {A : Set (Point (M := M) n m)} {j : Fin n} {k : Fin m}

noncomputable def eta (D : FocusGeometry A j k) (p : Point (M := M) n m) :
    Point (M := M) n m := if p ∈ D.locus then replace j p (p.1 j - D.center p) else p

@[simp] theorem eta_labels (D : FocusGeometry A j k) (p : Point (M := M) n m) :
    (D.eta p).2 = p.2 := by
  classical
  by_cases h : p ∈ D.locus <;> simp [eta, replace, h]

theorem eta_other (D : FocusGeometry A j k) (p : Point (M := M) n m)
    (i : Fin n) (hi : i ≠ j) : (D.eta p).1 i = p.1 i := by
  classical
  by_cases h : p ∈ D.locus <;> simp [eta, replace, h, hi]

theorem erase_eta (D : FocusGeometry A j k) (p : Point (M := M) n m) :
    erase j (D.eta p) = erase j p := by
  classical
  refine Prod.ext ?_ ?_
  swap
  · exact D.eta_labels p
  funext i
  by_cases hi : i = j
  · subst i; simp [erase, replace]
  · simpa [erase, replace, hi] using D.eta_other p i hi

theorem center_sameRV (D : FocusGeometry A j k) (p : Point (M := M) n m)
    (hp : p ∈ A ∩ D.locus) : rv (D.center p) = rv (p.1 j) := by
  have hf := tagged_hull D.tagged (replace j p (D.center p))
    (D.locus_subset (D.center_mem p hp))
  have ha := D.tagged p hp.1
  simpa [replace] using hf.symm.trans ha

/-- Injectivity follows from the locus, focus and retained-label conditions.
It is not supplied as an extra field of the special-bijection data. -/
theorem eta_injOn (D : FocusGeometry A j k) : Set.InjOn D.eta A := by
  classical
  intro p hp q hq he
  have hr : p.2 = q.2 := (D.eta_labels p).symm.trans
    ((congrArg Prod.snd he).trans (D.eta_labels q))
  have ho (i : Fin n) (hi : i ≠ j) : p.1 i = q.1 i :=
    (D.eta_other p i hi).symm.trans
      ((congrArg (fun z => z.1 i) he).trans (D.eta_other q i hi))
  have hrv : SameRV p q := by
    apply (sameRV_iff p q).mpr
    refine ⟨fun i => ?_, hr⟩
    by_cases hi : i = j
    · subst i
      exact (D.tagged p hp).symm.trans ((congrFun hr k).trans (D.tagged q hq))
    · rw [ho i hi]
  have hm := mem_iff_sameRV D.locus_pullback hrv
  by_cases hpc : p ∈ D.locus
  · have hqc := hm.mp hpc
    have herase : erase j p = erase j q := (D.erase_eta p).symm.trans
      ((congrArg (erase j) he).trans (D.erase_eta q))
    have hc := D.independent p ⟨hp, hpc⟩ q ⟨hq, hqc⟩ herase
    have hj : p.1 j - D.center p = q.1 j - D.center q := by
      simpa [eta, replace, hpc, hqc] using congrArg (fun z => z.1 j) he
    apply Prod.ext _ hr
    funext i
    by_cases hi : i = j
    · subst i; rw [hc] at hj; exact sub_left_inj.mp hj
    · exact ho i hi
  · have hqc : q ∉ D.locus := fun h => hpc (hm.mpr h)
    simpa [eta, hpc, hqc] using he

end FocusGeometry
end SpecialTransformations.Section5

/-!
# Original-base definability of the Section 5 coordinate maps

The presentations are Section 4's real-sort presentations in the normalized
released language. They refer to the original base set S. Normalization
agrees with every sorted operation, and does not add parameters.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false


open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section5

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

abbrev PresentedSpace := @DefinableGeometry.Space LRV M (CanonicalStructure.normalize (M := M))

abbrev pointSpace (n m : ℕ) : PresentedSpace (M := M) :=
  @DefinableGeometry.Space.prod LRV M (CanonicalStructure.normalize (M := M))
    (Section4.vfSpace n) (Section4.rvSpace m)

abbrev keySpace (n m : ℕ) : PresentedSpace (M := M) :=
  @DefinableGeometry.Space.prod LRV M (CanonicalStructure.normalize (M := M))
    (Section4.rvSpace n) (Section4.rvSpace m)

abbrev PresentedSet (P : PresentedSpace (M := M)) (S : Set M) :=
  @DefinableGeometry.DefSet LRV M (CanonicalStructure.normalize (M := M)) P S

abbrev spaceProd (P Q : PresentedSpace (M := M)) : PresentedSpace (M := M) :=
  @DefinableGeometry.Space.prod LRV M (CanonicalStructure.normalize (M := M)) P Q

abbrev Carrier (P : PresentedSpace (M := M)) :=
  @DefinableGeometry.Space.Carrier LRV M (CanonicalStructure.normalize (M := M)) P

abbrev SetDefinable (P : PresentedSpace (M := M)) (S : Set M) (A : Set (Carrier P)) :=
  @DefinableGeometry.Space.Definable LRV M (CanonicalStructure.normalize (M := M)) P S A

abbrev RelationDefinable (P Q : PresentedSpace (M := M)) (S : Set M)
    (r : Carrier P → Carrier Q → Prop) :=
  @DefinableGeometry.Space.RelationDefinable LRV M (CanonicalStructure.normalize (M := M)) P Q S r

abbrev DefSet (S : Set M) (n m : ℕ) := PresentedSet (pointSpace (M := M) n m) S

abbrev carrier {P : PresentedSpace (M := M)} {S : Set M} (A : PresentedSet P S) :=
  @DefinableGeometry.DefSet.carrier LRV M (CanonicalStructure.normalize (M := M)) P S A

abbrev setDefinable {P : PresentedSpace (M := M)} {S : Set M} (A : PresentedSet P S) :=
  @DefinableGeometry.DefSet.definable LRV M (CanonicalStructure.normalize (M := M)) P S A

abbrev Map {P Q : PresentedSpace (M := M)} {S : Set M}
    (A : PresentedSet P S) (B : PresentedSet Q S) :=
  @DefinableGeometry.Map LRV M (CanonicalStructure.normalize (M := M)) P Q S A B

namespace PresentedSet
abbrev mk := @DefinableGeometry.DefSet.mk LRV M (CanonicalStructure.normalize (M := M))
abbrev univ := @DefinableGeometry.DefSet.univ LRV M (CanonicalStructure.normalize (M := M))
abbrev prod := @DefinableGeometry.DefSet.prod LRV M (CanonicalStructure.normalize (M := M))
end PresentedSet

namespace Map
abbrev mk := @DefinableGeometry.Map.mk LRV M (CanonicalStructure.normalize (M := M))
abbrev ofCodes := @DefinableGeometry.Map.ofCodes LRV M (CanonicalStructure.normalize (M := M))
abbrev id := @DefinableGeometry.Map.id LRV M (CanonicalStructure.normalize (M := M))
abbrev comp := @DefinableGeometry.Map.comp LRV M (CanonicalStructure.normalize (M := M))
abbrev pair := @DefinableGeometry.Map.pair LRV M (CanonicalStructure.normalize (M := M))
abbrev image := @DefinableGeometry.Map.image LRV M (CanonicalStructure.normalize (M := M))
abbrev toImage := @DefinableGeometry.Map.toImage LRV M (CanonicalStructure.normalize (M := M))
abbrev inverse := @DefinableGeometry.Map.inverse LRV M (CanonicalStructure.normalize (M := M))
abbrev inclusion := @DefinableGeometry.Map.inclusion LRV M (CanonicalStructure.normalize (M := M))
abbrev ext := @DefinableGeometry.Map.ext LRV M (CanonicalStructure.normalize (M := M))
abbrev inverse_apply := @DefinableGeometry.Map.inverse_apply LRV M (CanonicalStructure.normalize (M := M))
abbrev apply_inverse := @DefinableGeometry.Map.apply_inverse LRV M (CanonicalStructure.normalize (M := M))
abbrev graph_definable := @DefinableGeometry.Map.graph_definable LRV M (CanonicalStructure.normalize (M := M))
abbrev definable_image := @DefinableGeometry.Map.definable_image LRV M (CanonicalStructure.normalize (M := M))
abbrev definable_preimage := @DefinableGeometry.Map.definable_preimage LRV M (CanonicalStructure.normalize (M := M))
end Map

namespace SetDefinable
abbrev inter := @DefinableGeometry.Space.Definable.inter LRV M (CanonicalStructure.normalize (M := M))
abbrev sdiff := @DefinableGeometry.Space.Definable.sdiff LRV M (CanonicalStructure.normalize (M := M))
end SetDefinable

namespace RelationDefinable
abbrev congr := @DefinableGeometry.Space.RelationDefinable.congr LRV M (CanonicalStructure.normalize (M := M))
abbrev swap := @DefinableGeometry.Space.RelationDefinable.swap LRV M (CanonicalStructure.normalize (M := M))
abbrev comp := @DefinableGeometry.Space.RelationDefinable.comp LRV M (CanonicalStructure.normalize (M := M))
abbrev union := @DefinableGeometry.Space.RelationDefinable.union LRV M (CanonicalStructure.normalize (M := M))
end RelationDefinable

abbrev RawFun (S : Set M) (α : Type) (f : (α → M) → M) :=
  @Set.DefinableFun M LRV (CanonicalStructure.normalize (M := M)) α S f

theorem rawProj (S : Set M) {α : Type} (i : α) : RawFun S α (fun z => z i) := by
  letI := CanonicalStructure.normalize (M := M)
  exact Set.DefinableFun.proj LRV

def rvCode (x : M) : M := @iRv M (CanonicalStructure.normalize (M := M)) x
def subCode (x y : M) : M := @iVFAdd M (CanonicalStructure.normalize (M := M)) x
  (@iVFNeg M (CanonicalStructure.normalize (M := M)) y)

private def vfSub (x y : VF (M := M)) : VF (M := M) := x - y

theorem rvCode_eq (x : M) (hx : iVF x) : rvCode x = iRv x := by
  exact CanonicalStructure.normalize_fun Fn.rvMap ![x]
    (by intro i; fin_cases i; exact hx)

theorem subCode_eq (x y : VF (M := M)) : subCode x.val y.val = (x - y).val := by
  have hn := CanonicalStructure.normalize_fun Fn.vfNeg ![y.val]
    (by intro i; fin_cases i; exact y.property)
  have ha := CanonicalStructure.normalize_fun Fn.vfAdd ![x.val, (-y).val]
    (by intro i; fin_cases i; exact x.property; exact (-y).property)
  change @iVFAdd M (CanonicalStructure.normalize (M := M)) x.val
    (@iVFNeg M (CanonicalStructure.normalize (M := M)) y.val) = (x - y).val
  change @iVFNeg M (CanonicalStructure.normalize (M := M)) y.val = (-y).val at hn
  rw [hn]
  exact ha

theorem rvCode_definable (S : Set M) {α : Type} (i : α) :
    RawFun S α (fun z => rvCode (z i)) := by
  let N := CanonicalStructure.normalize (M := M)
  let t : LRV.Term α := Term.func Fn.rvMap (fun _ => Term.var i)
  letI := N
  have ht : (∅ : Set M).DefinableFun LRV (fun z : α → M => @Term.realize LRV M N α z t) :=
    t.definableFun_realize (M := M)
  have he : (fun z : α → M => @Term.realize LRV M N α z t) =
      (fun z : α → M => @iRv M N (z i)) := by
    funext z
    change @Structure.funMap LRV M N 1 Fn.rvMap (fun _ : Fin 1 => z i) =
      @Structure.funMap LRV M N 1 Fn.rvMap ![z i]
    apply congrArg (@Structure.funMap LRV M N 1 Fn.rvMap)
    funext k
    fin_cases k
    rfl
  have hdef : @Set.DefinableFun M LRV N α S (fun z => @iRv M N (z i)) := by
    rw [← he]
    exact ht.of_empty
  exact hdef

theorem subCode_definable (S : Set M) {α : Type} (i j : α) :
    RawFun S α (fun z => subCode (z i) (z j)) := by
  let N := CanonicalStructure.normalize (M := M)
  let t : LRV.Term α := Term.func Fn.vfAdd
    ![Term.var i, Term.func Fn.vfNeg (fun _ => Term.var j)]
  letI := N
  have ht : (∅ : Set M).DefinableFun LRV (fun z : α → M => @Term.realize LRV M N α z t) :=
    t.definableFun_realize (M := M)
  have he : (fun z : α → M => @Term.realize LRV M N α z t) =
      (fun z : α → M => @iVFAdd M N (z i) (@iVFNeg M N (z j))) := by
    funext z
    apply congrArg (@Structure.funMap LRV M N 2 Fn.vfAdd)
    funext k
    fin_cases k
    · rfl
    · apply congrArg (@Structure.funMap LRV M N 1 Fn.vfNeg)
      funext l
      fin_cases l
      rfl
  have hdef : @Set.DefinableFun M LRV N α S
      (fun z => @iVFAdd M N (z i) (@iVFNeg M N (z j))) := by
    rw [← he]
    exact ht.of_empty
  exact hdef

def canonicalCodes {n m : ℕ} (z : Fin n ⊕ Fin m → M) : Fin n ⊕ Fin (n + m) → M :=
  Sum.elim (z ∘ Sum.inl) (Fin.append (fun i => rvCode (z (.inl i))) (z ∘ Sum.inr))

def canonicalMap {n m : ℕ} {S : Set M} (A : DefSet (M := M) S n m) :
    Map A (PresentedSet.univ (pointSpace n (n + m)) S) :=
  Map.ofCodes (M := M) (sM := sM) (P := pointSpace n m) (Q := pointSpace n (n + m)) A
    (@canonical M sM hM n m) (canonicalCodes (M := M) (sM := sM) (n := n) (m := m))
    (by
      intro i
      cases i with
      | inl i => exact rawProj S (Sum.inl i : Fin n ⊕ Fin m)
      | inr i =>
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simpa [canonicalCodes] using rvCode_definable S (Sum.inl j : Fin n ⊕ Fin m)
        · simpa [canonicalCodes] using rawProj S (Sum.inr j : Fin n ⊕ Fin m))
    (by
      intro c
      change (∀ i, iVF (canonicalCodes c.val (.inl i))) ∧
        ∀ i, iRV (canonicalCodes c.val (.inr i))
      refine ⟨c.property.1, ?_⟩
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [canonicalCodes, Sum.elim_inr, Fin.append_left]
        rw [rvCode_eq (sM := sM) (c.val (Sum.inl j)) (by
          simpa [Function.comp_def, sortEval, iVF] using c.property.1 j)]
        exact rv_mem hM (c.property.1 j)
      · simpa [canonicalCodes, Function.comp_def, sortEval, iRV] using c.property.2 j)
    (by
      intro c
      refine Prod.ext ?_ ?_
      · rfl
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · apply Subtype.ext
        simpa [canonicalCodes, canonical, rv] using
          rvCode_eq (sM := sM) (c.val (Sum.inl j)) (by
            simpa [Function.comp_def, sortEval, iVF] using c.property.1 j)
      · simp [canonicalCodes, canonical])

def canonicalImage {n m : ℕ} {S : Set M} (A : DefSet (M := M) S n m) :
    DefSet (M := M) S n (n + m) := Map.image (canonicalMap A)

theorem canonicalImage_carrier {n m : ℕ} {S : Set M} (A : DefSet (M := M) S n m) :
    carrier (canonicalImage A) = canonical '' carrier A := by
  ext p
  exact ⟨fun ⟨a, he⟩ => ⟨a.val, a.property, he⟩,
    fun ⟨a, ha, he⟩ => ⟨⟨a, ha⟩, he⟩⟩

def keyCodes {n m : ℕ} (z : Fin n ⊕ Fin m → M) : Fin n ⊕ Fin m → M :=
  Sum.elim (fun i => rvCode (z (.inl i))) (z ∘ Sum.inr)

def keyMap {n m : ℕ} {S : Set M} (A : DefSet (M := M) S n m) :
    Map A (PresentedSet.univ (keySpace n m) S) :=
  Map.ofCodes (M := M) (sM := sM) (P := pointSpace n m) (Q := keySpace n m) A
    (@key M sM hM n m) (keyCodes (M := M) (sM := sM) (n := n) (m := m))
    (by
      intro i
      cases i with
      | inl i => exact rvCode_definable S (Sum.inl i : Fin n ⊕ Fin m)
      | inr i => exact rawProj S (Sum.inr i : Fin n ⊕ Fin m))
    (by
      intro c
      refine ⟨?_, c.property.2⟩
      intro i
      change iRV (rvCode (c.val (.inl i)))
      rw [rvCode_eq (sM := sM) (c.val (Sum.inl i)) (by
        simpa [Function.comp_def, sortEval, iVF] using c.property.1 i)]
      exact rv_mem hM (c.property.1 i))
    (by
      intro c
      refine Prod.ext ?_ ?_
      swap
      · rfl
      funext i
      exact Subtype.ext (rvCode_eq (sM := sM) _ (c.property.1 i)))

theorem hull_definable {n m : ℕ} {S : Set M} (A : DefSet (M := M) S n m) :
    SetDefinable (pointSpace n m) S (hull (carrier A)) := by
  have h := Map.definable_preimage (keyMap (PresentedSet.univ (pointSpace n m) S))
    (Map.definable_image (keyMap A))
  convert h using 1
  ext p
  constructor
  · rintro ⟨q, hq, he⟩
    exact ⟨⟨p, Set.mem_univ _⟩, rfl, ⟨⟨q, hq⟩, he⟩⟩
  · rintro ⟨p', rfl, q, he⟩
    exact ⟨q.val, q.property, he⟩

end SpecialTransformations.Section5

/-!
# Definable focus maps and centripetal transformations

Definition 5.1 retains the full original-base graphs of the locus and focus.
The focus depends only on the complementary VF coordinates and all RV labels.
Its value outside the actual domain is irrelevant.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false


open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section5

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}

structure Focus (A : DefSet (M := M) S n m) (j : Fin n) (k : Fin m)
    extends FocusGeometry (carrier A) j k where
  locus_definable : SetDefinable (pointSpace n m) S locus
  center_graph : RelationDefinable (pointSpace n m) (Section4.vfSpace 1) S
    (fun p z => p ∈ carrier A ∩ locus ∧ z 0 = center p)

def subtractCodes (j : Fin n)
    (z : ((Fin n ⊕ Fin m) ⊕ Fin 1) → M) : Fin n ⊕ Fin m → M :=
  Sum.elim (fun i => if i = j then subCode (z (.inl (.inl j))) (z (.inr 0))
    else z (.inl (.inl i))) (fun i => z (.inl (.inr i)))

def subtractMap (j : Fin n)
    (A : PresentedSet (spaceProd (pointSpace (M := M) n m) (Section4.vfSpace 1)) S) :
    Map A (PresentedSet.univ (pointSpace n m) S) :=
  Map.ofCodes (M := M) (P := spaceProd (pointSpace n m) (Section4.vfSpace 1))
    (Q := pointSpace n m) A
    (fun p => replace j p.1 (vfSub (p.1.1 j) (p.2 0)))
    (subtractCodes j)
    (by
      intro i
      cases i with
      | inl i =>
        by_cases hi : i = j
        · subst i
          simpa [subtractCodes] using subCode_definable S
            (Sum.inl (Sum.inl j) : (Fin n ⊕ Fin m) ⊕ Fin 1) (Sum.inr 0)
        · simpa [subtractCodes, hi] using
            rawProj S (Sum.inl (Sum.inl i) : (Fin n ⊕ Fin m) ⊕ Fin 1)
      | inr i =>
        exact rawProj S (Sum.inl (Sum.inr i) : (Fin n ⊕ Fin m) ⊕ Fin 1))
    (by
      intro c
      refine ⟨?_, c.property.1.2⟩
      intro i
      by_cases hi : i = j
      · subst i
        simp only [subtractCodes, Sum.elim_inl, if_pos rfl, Function.comp_apply]
        change iVF (subCode (c.val (.inl (.inl j))) (c.val (.inr 0)))
        let x : VF (M := M) := ⟨c.val (.inl (.inl j)), by
          simpa [Function.comp_def, sortEval, iVF] using c.property.1.1 j⟩
        let y : VF (M := M) := ⟨c.val (.inr 0), by
          simpa [Function.comp_def, sortEval, iVF] using c.property.2 0⟩
        have hs : subCode (c.val (.inl (.inl j))) (c.val (.inr 0)) = (x - y).val :=
          subCode_eq x y
        rw [hs]
        exact (x - y).property
      · simpa [subtractCodes, hi] using c.property.1.1 i)
    (by
      intro c
      refine Prod.ext ?_ ?_
      swap
      · rfl
      funext i
      by_cases hi : i = j
      · subst i
        apply Subtype.ext
        simpa [subtractCodes, replace, vfSub] using
          (subCode_eq (⟨c.val (.inl (.inl j)), c.property.1.1 j⟩ : VF (M := M))
            (⟨c.val (.inr 0), c.property.2 0⟩ : VF (M := M)))
      · simp [subtractCodes, replace, hi])

namespace Focus

variable {A : DefSet (M := M) S n m} {j : Fin n} {k : Fin m}

def active (D : Focus A j k) : DefSet (M := M) S n m :=
  PresentedSet.mk (carrier A ∩ D.locus)
    (SetDefinable.inter _ (setDefinable A) D.locus_definable)

def inactive (D : Focus A j k) : DefSet (M := M) S n m :=
  PresentedSet.mk (carrier A \ D.locus)
    (SetDefinable.sdiff _ (setDefinable A) D.locus_definable)

def centerMap (D : Focus A j k) :
    Map D.active (PresentedSet.univ (Section4.vfSpace 1) S) :=
  Map.mk (fun p => ⟨![D.center p.val], Set.mem_univ _⟩)
    (RelationDefinable.congr _ _ D.center_graph (by
    intro p z
    constructor
    · rintro ⟨hp, hz⟩
      refine ⟨⟨p, hp⟩, rfl, ?_⟩
      funext i
      fin_cases i
      exact hz.symm
    · rintro ⟨a, rfl, rfl⟩
      exact ⟨a.property, rfl⟩))

def activeMap (D : Focus A j k) :
    Map D.active (PresentedSet.univ (pointSpace n m) S) :=
  Map.comp (subtractMap j (PresentedSet.prod D.active (PresentedSet.univ (Section4.vfSpace 1) S)))
    (Map.pair (Map.id D.active) D.centerMap)

def inactiveMap (D : Focus A j k) :
    Map D.inactive (PresentedSet.univ (pointSpace n m) S) :=
  Map.inclusion (Set.subset_univ _)

@[simp] theorem activeMap_apply (D : Focus A j k) (p : D.active) :
    (D.activeMap p).val = replace j p.val (vfSub (p.val.1 j) (D.center p.val)) := rfl

@[simp] theorem inactiveMap_apply (D : Focus A j k) (p : D.inactive) :
    (D.inactiveMap p).val = p.val := rfl

noncomputable def etaMap (D : Focus A j k) :
    Map A (PresentedSet.univ (pointSpace n m) S) :=
  Map.mk (fun p => ⟨D.toFocusGeometry.eta p.val, Set.mem_univ _⟩)
    (RelationDefinable.congr _ _
    (RelationDefinable.union _ _ (Map.graph_definable D.activeMap)
      (Map.graph_definable D.inactiveMap)) (by
      intro p q
      constructor
      · rintro (⟨a, rfl, he⟩ | ⟨a, rfl, he⟩)
        · refine ⟨⟨a.val, a.property.1⟩, rfl, ?_⟩
          simpa [FocusGeometry.eta, vfSub, a.property.2] using he
        · refine ⟨⟨a.val, a.property.1⟩, rfl, ?_⟩
          simpa [FocusGeometry.eta, a.property.2] using he
      · rintro ⟨a, rfl, he⟩
        by_cases hc : a.val ∈ D.locus
        · left
          refine ⟨⟨a.val, a.property, hc⟩, rfl, ?_⟩
          simpa [FocusGeometry.eta, vfSub, hc] using he
        · right
          refine ⟨⟨a.val, a.property, hc⟩, rfl, ?_⟩
          simpa [FocusGeometry.eta, hc] using he))

noncomputable def etaImage (D : Focus A j k) : DefSet (M := M) S n m := Map.image D.etaMap

theorem etaMap_injective (D : Focus A j k) : Function.Injective D.etaMap := by
  intro p q he
  exact Subtype.ext (D.toFocusGeometry.eta_injOn p.property q.property
    (congrArg Subtype.val he))

end Focus
end SpecialTransformations.Section5

/-!
# Special bijections with changing RV arities

Definition 5.1: an alternating finite sequence of actual canonical and
centripetal maps. Every primitive has its full graph definable over S.
Injectivity is proved from the primitive constructions. The type retains
both the actual source and target and the index of each targeted coordinate.
-/

set_option backward.isDefEq.respectTransparency false


open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section5

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

inductive Primitive (S : Set M) (n : ℕ) : {m l : ℕ} →
    DefSet (M := M) S n m → DefSet (M := M) S n l → Type where
  | canonical {m : ℕ} (A : DefSet (M := M) S n m) : Primitive S n A (canonicalImage A)
  | centripetal {m : ℕ} {A : DefSet (M := M) S n m} {j : Fin n} {k : Fin m}
      (D : Focus A j k) : Primitive S n A D.etaImage

namespace Primitive

variable {S : Set M} {n m l : ℕ} {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}

noncomputable def toMap : Primitive S n A B → Map A B
  | .canonical A => Map.toImage (canonicalMap A)
  | .centripetal D => Map.toImage D.etaMap

theorem bijective (p : Primitive S n A B) : Function.Bijective p.toMap := by
  cases p with
  | canonical A =>
    constructor
    · intro x y he
      exact Subtype.ext (canonical_injective (congrArg Subtype.val he))
    · rintro ⟨q, a, ha⟩
      exact ⟨a, Subtype.ext ha⟩
  | centripetal D =>
    constructor
    · intro x y he
      apply D.etaMap_injective
      apply Subtype.ext
      exact congrArg (fun z : D.etaImage => z.val) he
    · rintro ⟨q, a, ha⟩
      exact ⟨a, Subtype.ext ha⟩

def length : Primitive S n A B → ℕ
  | .canonical _ => 0
  | .centripetal _ => 1

end Primitive

inductive Chain (S : Set M) (n : ℕ) : {m l : ℕ} →
    DefSet (M := M) S n m → DefSet (M := M) S n l → Type where
  | nil {m : ℕ} (A : DefSet (M := M) S n m) : Chain S n A A
  | cons {m l k : ℕ} {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}
      {C : DefSet (M := M) S n k} (p : Primitive S n A B) (tail : Chain S n B C) : Chain S n A C

namespace Chain

variable {S : Set M} {n m l k : ℕ}
variable {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l} {C : DefSet (M := M) S n k}

noncomputable def toMap {m₁ m₂ : ℕ} {X : DefSet (M := M) S n m₁}
    {Y : DefSet (M := M) S n m₂} : Chain S n X Y → Map X Y
  | .nil A => Map.id A
  | .cons p tail => Map.comp tail.toMap p.toMap

theorem bijective (t : Chain S n A B) : Function.Bijective t.toMap := by
  induction t with
  | nil A => exact Function.bijective_id
  | cons p tail ih => exact ih.comp p.bijective

def length {m₁ m₂ : ℕ} {X : DefSet (M := M) S n m₁}
    {Y : DefSet (M := M) S n m₂} : Chain S n X Y → ℕ
  | .nil _ => 0
  | .cons p tail => p.length + tail.length

/-- `none` permits either initial step. Thereafter `true` means centripetal
and `false` canonical, so both sorts of repeated adjacent step are excluded. -/
def Alternating {m₁ m₂ : ℕ} {X : DefSet (M := M) S n m₁}
    {Y : DefSet (M := M) S n m₂} (previous : Option Bool) : Chain S n X Y → Prop
  | .nil _ => True
  | .cons (.canonical _) tail => previous ≠ some false ∧ tail.Alternating (some false)
  | .cons (.centripetal _) tail => previous ≠ some true ∧ tail.Alternating (some true)

def append {m₁ m₂ m₃ : ℕ} {X : DefSet (M := M) S n m₁}
    {Y : DefSet (M := M) S n m₂} {Z : DefSet (M := M) S n m₃}
    (t : Chain S n X Y) (u : Chain S n Y Z) : Chain S n X Z :=
  match t with
  | .nil _ => u
  | .cons p tail => .cons p (tail.append u)

theorem length_append (t : Chain S n A B) (u : Chain S n B C) :
    (t.append u).length = t.length + u.length := by
  induction t with
  | nil A => simp [append, length]
  | cons p tail ih => simp [append, length, ih, Nat.add_assoc]

end Chain

structure SpecialBijection {S : Set M} {n m l : ℕ}
    (A : DefSet (M := M) S n m) (B : DefSet (M := M) S n l) where
  chain : Chain S n A B
  alternating : chain.Alternating none

namespace SpecialBijection

variable {S : Set M} {n m l k : ℕ}
variable {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l} {C : DefSet (M := M) S n k}

noncomputable def toMap (T : SpecialBijection A B) : Map A B := T.chain.toMap

theorem bijective (T : SpecialBijection A B) : Function.Bijective T.toMap := T.chain.bijective

noncomputable def equiv (T : SpecialBijection A B) : A ≃ B := Equiv.ofBijective T.toMap T.bijective

/-- The inverse, including a single centrifugal transformation, has its full
graph definable over the original base. -/
noncomputable def inverseMap (T : SpecialBijection A B) : Map B A :=
  Map.inverse T.toMap T.bijective

@[simp] theorem inverse_apply (T : SpecialBijection A B) (a : A) :
    T.inverseMap (T.toMap a) = a := Map.inverse_apply T.toMap T.bijective a

@[simp] theorem apply_inverse (T : SpecialBijection A B) (b : B) :
    T.toMap (T.inverseMap b) = b := Map.apply_inverse T.toMap T.bijective b

def length (T : SpecialBijection A B) : ℕ := T.chain.length

def refl (A : DefSet (M := M) S n m) : SpecialBijection A A := ⟨.nil A, trivial⟩

def canonical (A : DefSet (M := M) S n m) : SpecialBijection A (canonicalImage A) :=
  ⟨.cons (.canonical A) (.nil _), by decide, trivial⟩

def centripetal {j : Fin n} {k : Fin m} (D : Focus A j k) : SpecialBijection A D.etaImage :=
  ⟨.cons (.centripetal D) (.nil _), by decide, trivial⟩

def comp (T : SpecialBijection A B) (U : SpecialBijection B C)
    (h : (T.chain.append U.chain).Alternating none) : SpecialBijection A C :=
  ⟨T.chain.append U.chain, h⟩

theorem length_comp (T : SpecialBijection A B) (U : SpecialBijection B C)
    (h : (T.chain.append U.chain).Alternating none) :
    (T.comp U h).length = T.length + U.length := T.chain.length_append U.chain

end SpecialBijection

def IsDeformedRVPullback {S : Set M} {n m : ℕ} (A : DefSet (M := M) S n m) : Prop :=
  ∃ l : ℕ, ∃ B : DefSet (M := M) S n l, Nonempty (SpecialBijection A B) ∧ IsRVPullback (carrier B)

end SpecialTransformations.Section5

/-!
# Unique definable contractions

The paragraph after Remark 5.3. A contractible definable function descends
to the actual images of the mixed RV-key maps. The complete graph remains
definable over S. Representatives are used internally to define the unique
function, and are never adjoined to the parameter base.
-/

set_option backward.isDefEq.respectTransparency false


open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section5

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m n' m' : ℕ}
variable {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n' m'}

def Contractible (f : A → B) : Prop :=
  ∀ a b : A, SameRV a.val b.val → SameRV (f a).val (f b).val

def keyImage (A : DefSet (M := M) S n m) := Map.image (keyMap A)

def toKeyImage (A : DefSet (M := M) S n m) : A → keyImage A :=
  fun a => ⟨key a.val, ⟨a, rfl⟩⟩

noncomputable def keyRepresentative (u : keyImage A) : A := Classical.choose u.property

theorem keyRepresentative_spec (u : keyImage A) : key (keyRepresentative u).val = u.val :=
  Classical.choose_spec u.property

noncomputable def contractionFun (f : A → B) (u : keyImage A) : keyImage B :=
  toKeyImage B (f (keyRepresentative u))

theorem contractionFun_spec (f : A → B) (hf : Contractible f) (a : A) :
    contractionFun f (toKeyImage A a) = toKeyImage B (f a) := by
  apply Subtype.ext
  exact hf _ a (keyRepresentative_spec (toKeyImage A a))

theorem contractionFun_unique (f : A → B) (hf : Contractible f)
    (g : keyImage A → keyImage B)
    (hg : ∀ a : A, g (toKeyImage A a) = toKeyImage B (f a)) : g = contractionFun f := by
  funext u
  have he : toKeyImage A (keyRepresentative u) = u := Subtype.ext (keyRepresentative_spec u)
  rw [← he, hg, contractionFun_spec f hf]

noncomputable def contractionMap (f : Map A B) (hf : Contractible f) :
    Map (keyImage A) (keyImage B) :=
  Map.mk (contractionFun f) (by
    let kf := Map.comp (keyMap B) f
    have hr := RelationDefinable.comp _ _ _
      (RelationDefinable.swap _ _ (Map.graph_definable (keyMap A))) (Map.graph_definable kf)
    apply RelationDefinable.congr _ _ hr
    intro u v
    constructor
    · rintro ⟨p, ⟨a, ha, hka⟩, ⟨b, hb, hfb⟩⟩
      have hab : a = b := Subtype.ext (ha.trans hb.symm)
      subst b
      let c : keyImage A := ⟨u, ⟨a, hka⟩⟩
      refine ⟨c, rfl, ?_⟩
      have hc : c = toKeyImage A a := Subtype.ext hka.symm
      change (contractionFun f c).val = v
      rw [hc, contractionFun_spec f hf]
      exact hfb
    · rintro ⟨u, rfl, he⟩
      let a := keyRepresentative u
      refine ⟨a.val, ⟨a, rfl, keyRepresentative_spec u⟩, a, rfl, ?_⟩
      exact he)

theorem contractionMap_spec (f : Map A B) (hf : Contractible f) (a : A) :
    contractionMap f hf (toKeyImage A a) = toKeyImage B (f a) := contractionFun_spec f hf a

theorem exists_unique_definable_contraction (f : Map A B) (hf : Contractible f) :
    ∃! g : Map (keyImage A) (keyImage B),
      ∀ a : A, g (toKeyImage A a) = toKeyImage B (f a) := by
  refine ⟨contractionMap f hf, contractionMap_spec f hf, ?_⟩
  intro g hg
  apply Map.ext
  intro u
  exact congrFun (contractionFun_unique f hf g hg) u

end SpecialTransformations.Section5

/-!
# The unary polynomial argument: barycentric data control every root factor

This is the algebraic induction used in the base case of Theorem 5.4.
The finite set consists of the polynomial's actual roots. The barycentric
code is the existing, uniformly definable Section 3 construction; the
argument here applies to all field points, not only to members of that
finite set. Assembly into a definable special bijection is separate.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Section5

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- A root outside a centered RV fibre contributes the same linear-factor
leading term at any two points of that fibre. -/
theorem root_factor_rv_eq (c r x y : VFType (M := M))
    (hxy : iRv (x - c).val = iRv (y - c).val)
    (hr : iRv (r - c).val ≠ iRv (x - c).val) :
    iRv (x - r).val = iRv (y - r).val := by
  obtain ⟨Γ, inst, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := inst
  by_cases hx : x - c = 0
  · have hy : y - c = 0 := (CanonicalRV.encodedRv_zero_iff _).mp
      (hxy.symm.trans (by rw [hx]; exact RVCalc.rv_zero_eq hM))
    have he : x = y := (sub_eq_zero.mp hx).trans (sub_eq_zero.mp hy).symm
    rw [he]
  have hclose : v (x - y) < v (x - c) := by
    have hh := (CanonicalRV.encoded_eq_iff_close (y - c).property (x - c).property
      (fun h => hx (Subtype.ext h))).mp hxy.symm
    change ¬ VFValued.predV (x - c) ((y - c) - (x - c)) at hh
    rw [hv, not_le] at hh
    have he : (y - c) - (x - c) = -(x - y) := by abel
    simpa only [he, Valuation.map_neg] using hh
  have hbound : v (x - c) ≤ v (x - r) := by
    apply le_of_not_gt
    intro hlt
    apply hr
    apply Section3.Balls.rv_eq_of_sub_lt v hv (r - c) (x - c) hx
    have he : (r - c) - (x - c) = -(x - r) := by abel
    simpa only [he, Valuation.map_neg] using hlt
  have hxr : x - r ≠ 0 := by
    intro h
    have hpos : 0 < v (x - c) := pos_iff_ne_zero.mpr ((map_ne_zero v).mpr hx)
    rw [h, map_zero] at hbound
    exact (not_le_of_gt hpos) hbound
  symm
  apply Section3.Balls.rv_eq_of_sub_lt v hv (y - r) (x - r) hxr
  have he : (y - r) - (x - r) = -(x - y) := by abel
  rw [he, Valuation.map_neg]
  exact hclose.trans_le hbound

/-- The code depth is bounded by the number of distinct roots. Equality of
the entire code forces equality of the leading terms of all root factors. -/
theorem barycentric_code_controls_factors (h00 : M ⊨ Axioms.ACVF00) (d : ℕ)
    (A : Finset (VFType (M := M))) (hcard : A.card ≤ d)
    (x y : VFType (M := M)) (he : Section3.Barycentre.code d A x =
      Section3.Barycentre.code d A y) :
    ∀ r ∈ A, iRv (x - r).val = iRv (y - r).val := by
  induction d generalizing A x y with
  | zero =>
    have hA : A = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
    simp [hA]
  | succ d ih =>
    intro r hr
    have hhead : iRv (x - Section3.Barycentre.mean A).val =
        iRv (y - Section3.Barycentre.mean A).val := congrFun he 0
    by_cases hsmall : A.card ≤ 1
    · have hA : A = {r} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hr, fun z hz => (Finset.card_le_one_iff.mp hsmall) hz hr⟩
      simpa [hA, Section3.Barycentre.mean] using hhead
    · by_cases hrx : r ∈ Section3.Barycentre.fibre A x
      · have hfib : Section3.Barycentre.fibre A x = Section3.Barycentre.fibre A y := by
          unfold Section3.Barycentre.fibre
          rw [hhead]
        have htail : Section3.Barycentre.code d (Section3.Barycentre.fibre A x) x =
            Section3.Barycentre.code d (Section3.Barycentre.fibre A x) y := by
          have ht := congrArg (fun z : Fin (d + 1) → M => Fin.tail z) he
          change Section3.Barycentre.code d (Section3.Barycentre.fibre A x) x =
            Section3.Barycentre.code d (Section3.Barycentre.fibre A y) y at ht
          rwa [← hfib] at ht
        have hlt := Section3.Barycentre.fibre_card_lt h00 A (by omega)
          (iRv (x - Section3.Barycentre.mean A).val)
        exact ih (Section3.Barycentre.fibre A x) (by change
          (Section3.Barycentre.fibre A x).card < A.card at hlt; omega) x y htail r hrx
      · apply root_factor_rv_eq (Section3.Barycentre.mean A) r x y hhead
        intro h
        exact hrx (Finset.mem_filter.mpr ⟨hr, h⟩)

theorem unary_polynomial_rv_of_barycentric_code (h00 : M ⊨ Axioms.ACVF00)
    (p : Polynomial (VFType (M := M))) (x y : VFType (M := M))
    (he : Section3.Barycentre.code p.roots.toFinset.card p.roots.toFinset x =
      Section3.Barycentre.code p.roots.toFinset.card p.roots.toFinset y) :
    iRv (p.eval x).val = iRv (p.eval y).val := by
  apply Section3.polynomial_rv_eq_of_linear_factors p x y
  intro r hr
  exact barycentric_code_controls_factors h00 p.roots.toFinset.card p.roots.toFinset
    le_rfl x y he r (Multiset.mem_toFinset.mpr hr)

end SpecialTransformations.Section5

#check @SpecialTransformations.Section5.unary_polynomial_rv_of_barycentric_code
#print axioms SpecialTransformations.Section5.unary_polynomial_rv_of_barycentric_code
