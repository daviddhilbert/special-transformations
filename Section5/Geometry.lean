module

public import VFValued
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-!
# RV hulls and canonical maps in the released language

Section 5 preamble and the canonical-map part of Definition 5.1.
The RV carrier is the existing sorted carrier, with its single absorbing
element. Canonical maps attach RV coordinates and retain all earlier labels.
No second language or quotient model is introduced.
-/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace SpecialTransformations.Section5

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

abbrev VF := VFType (M := M)
abbrev RV := {t : M // iRV t}
abbrev Point (n m : ℕ) := (Fin n → VF (M := M)) × (Fin m → RV (M := M))
abbrev Key (n m : ℕ) := (Fin n → RV (M := M)) × (Fin m → RV (M := M))

def rv (x : VF (M := M)) : RV (M := M) := ⟨iRv x.val, rv_mem hM x.property⟩

def key {n m : ℕ} (p : Point (M := M) n m) : Key (M := M) n m :=
  (fun i => rv (p.1 i), p.2)

def SameRV {n m : ℕ} (p q : Point (M := M) n m) : Prop := key p = key q

def hull {n m : ℕ} (A : Set (Point (M := M) n m)) : Set (Point (M := M) n m) :=
  {q | ∃ p ∈ A, SameRV p q}

def IsRVPullback {n m : ℕ} (A : Set (Point (M := M) n m)) : Prop := hull A = A

theorem sameRV_iff {n m : ℕ} (p q : Point (M := M) n m) :
    SameRV p q ↔ (∀ i, rv (p.1 i) = rv (q.1 i)) ∧ p.2 = q.2 := by
  simp only [SameRV, key, Prod.mk.injEq, funext_iff]

theorem subset_hull {n m : ℕ} (A : Set (Point (M := M) n m)) : A ⊆ hull A :=
  fun p hp => ⟨p, hp, rfl⟩

theorem hull_mono {n m : ℕ} {A B : Set (Point (M := M) n m)} (h : A ⊆ B) :
    hull A ⊆ hull B := fun _ ⟨p, hp, he⟩ => ⟨p, h hp, he⟩

theorem hull_idem {n m : ℕ} (A : Set (Point (M := M) n m)) : hull (hull A) = hull A := by
  apply Set.Subset.antisymm _ (subset_hull _)
  rintro q ⟨p, ⟨a, ha, hap⟩, hpq⟩
  exact ⟨a, ha, hap.trans hpq⟩

theorem isRVPullback_iff {n m : ℕ} (A : Set (Point (M := M) n m)) :
    IsRVPullback A ↔ ∀ p ∈ A, ∀ q, SameRV p q → q ∈ A := by
  constructor
  · intro h p hp q he
    rw [← h]
    exact ⟨p, hp, he⟩
  · intro h
    exact Set.Subset.antisymm (by rintro q ⟨p, hp, he⟩; exact h p hp q he) (subset_hull A)

theorem mem_iff_sameRV {n m : ℕ} {A : Set (Point (M := M) n m)}
    (hA : IsRVPullback A) {p q : Point (M := M) n m} (h : SameRV p q) :
    p ∈ A ↔ q ∈ A :=
  ⟨fun hp => (isRVPullback_iff A).mp hA p hp q h,
    fun hq => (isRVPullback_iff A).mp hA q hq p h.symm⟩

/-- The canonical bijection appends all current VF leading terms. -/
def canonical {n m : ℕ} (p : Point (M := M) n m) : Point (M := M) n (n + m) :=
  (p.1, Fin.append (fun i => rv (p.1 i)) p.2)

@[simp] theorem canonical_vf {n m : ℕ} (p : Point (M := M) n m) :
    (canonical p).1 = p.1 := rfl

@[simp] theorem canonical_new {n m : ℕ} (p : Point (M := M) n m) (i : Fin n) :
    (canonical p).2 (Fin.castAdd m i) = rv (p.1 i) := by simp [canonical]

@[simp] theorem canonical_old {n m : ℕ} (p : Point (M := M) n m) (i : Fin m) :
    (canonical p).2 (Fin.natAdd n i) = p.2 i := by simp [canonical]

theorem canonical_injective {n m : ℕ} :
    Function.Injective (canonical (M := M) (n := n) (m := m)) := by
  intro p q he
  refine Prod.ext ?_ ?_
  · exact congrArg (fun z : Point (M := M) n (n + m) => z.1) he
  funext i
  exact (canonical_old p i).symm.trans
    ((congrArg (fun z => z.2 (Fin.natAdd n i)) he).trans (canonical_old q i))

theorem canonical_sameRV_iff {n m : ℕ} (p q : Point (M := M) n m) :
    SameRV (canonical p) (canonical q) ↔ SameRV p q := by
  rw [sameRV_iff, sameRV_iff]
  constructor
  · rintro ⟨hv, hr⟩
    refine ⟨hv, funext (fun i => ?_)⟩
    simpa using congrFun hr (Fin.natAdd n i)
  · rintro ⟨hv, hr⟩
    exact ⟨hv, by simp only [canonical, funext hv, hr]⟩

theorem canonical_image_pullback {n m : ℕ} {A : Set (Point (M := M) n m)}
    (hA : IsRVPullback A) : IsRVPullback (canonical '' A) := by
  apply (isRVPullback_iff _).mpr
  rintro _ ⟨p, hp, rfl⟩ q hq
  let r : Point (M := M) n m := (q.1, fun i => q.2 (Fin.natAdd n i))
  have h := (sameRV_iff (canonical p) q).mp hq
  have hpr : SameRV p r := (sameRV_iff p r).mpr
    ⟨h.1, funext (fun i => by simpa [r] using congrFun h.2 (Fin.natAdd n i))⟩
  have hr : r ∈ A := (isRVPullback_iff A).mp hA p hp r hpr
  refine ⟨r, hr, ?_⟩
  refine Prod.ext ?_ ?_
  · rfl
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have hj := congrFun h.2 (Fin.castAdd m j)
    simpa [canonical, r] using (h.1 j).symm.trans ((canonical_new p j).symm.trans hj)
  · simp [canonical, r]

end SpecialTransformations.Section5

#check @SpecialTransformations.Section5.canonical_image_pullback
#print axioms SpecialTransformations.Section5.canonical_image_pullback
