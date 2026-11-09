import Section8.GammaBalls

/-! Definition 9.1 in the released VF/RV language. The point at infinity
belongs to the auxiliary limit space only. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- The finite VF points and the formal point at infinity of Section 9. -/
abbrev LimitPoint (M : Type) [LRV.Structure M] := Option (VFType (M := M))

/-- Membership of a finite point in a neighbourhood of an extended point.
An infinity neighbourhood is the complement of the closed ball with
opposite radius in the paper's value order. -/
def memLimitBall (b : LimitPoint M) (ε : Values.Gamma (M := M))
    (y : VFType (M := M)) : Prop :=
  match b with
  | some a => ε.val < Values.vfValueHom (y - a)
  | none => Values.vfValueHom y < (ε⁻¹).val

/-- A limit set for a set-valued map. The union in Definition 9.1 can be
taken over all of `L`, since the permitted subcover may be `L` itself. -/
def IsLimitSet {n m : ℕ} (A : Set (Fin n → VFType (M := M)))
    (a : Fin n → VFType (M := M))
    (f : (Fin n → VFType (M := M)) → Set (Fin m → VFType (M := M)))
    (L : Set (Fin m → LimitPoint M)) : Prop :=
  ∀ ε : Values.Gamma (M := M), ∃ δ : Values.Gamma (M := M),
    ∀ x ∈ A \ {a},
      (fun i => (x i).val) ∈ Section8.gammaUniformBall (fun i => (a i).val) δ →
        ∀ y ∈ f x, ∃ b ∈ L, ∀ i, memLimitBall (b i) ε (y i)

/-- Minimality of a limit set is inclusion minimality. -/
def IsMinimalLimitSet {n m : ℕ} (A : Set (Fin n → VFType (M := M)))
    (a : Fin n → VFType (M := M))
    (f : (Fin n → VFType (M := M)) → Set (Fin m → VFType (M := M)))
    (L : Set (Fin m → LimitPoint M)) : Prop :=
  IsLimitSet A a f L ∧ ∀ L' ⊂ L, ¬ IsLimitSet A a f L'

theorem IsLimitSet.mono {n m : ℕ} {A : Set (Fin n → VFType (M := M))}
    {a : Fin n → VFType (M := M)}
    {f : (Fin n → VFType (M := M)) → Set (Fin m → VFType (M := M))}
    {L L' : Set (Fin m → LimitPoint M)} (h : IsLimitSet A a f L)
    (hsub : L ⊆ L') : IsLimitSet A a f L' := by
  intro ε
  obtain ⟨δ, hδ⟩ := h ε
  refine ⟨δ, ?_⟩
  intro x hx hnear y hy
  obtain ⟨b, hb, hball⟩ := hδ x hx hnear y hy
  exact ⟨b, hsub hb, hball⟩

end SpecialTransformations.Section9
