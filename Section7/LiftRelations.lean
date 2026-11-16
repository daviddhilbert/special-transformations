module

public import Section7.GammaPolynomial

@[expose] public section

/-!
# Definition 7.3 on products of VF powers

A relation is a lift when each specified pair of actual RV fibres carries
the graph of a bijection. This is the full-ambient-space instance needed by
Theorem 7.6. Existence and definability of a lift are separate obligations.
The definition does not require the entire RV correspondence to be a function.
-/

namespace SpecialTransformations.Section7

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

def FibreBijection (v : Valuation K Γ) {m n : ℕ}
    (A : Set ((Fin m → K) × (Fin n → K)))
    (t : Fin m → RVCalc.RV v) (s : Fin n → RVCalc.RV v) : Prop :=
  (∀ a ∈ RVFibre v t, ∃! b, b ∈ RVFibre v s ∧ (a, b) ∈ A) ∧
  (∀ b ∈ RVFibre v s, ∃! a, a ∈ RVFibre v t ∧ (a, b) ∈ A)

/-- The Definition 7.3 instance with ambient pullbacks VF^m and VF^n. -/
def IsLift (v : Valuation K Γ) {m n : ℕ}
    (C : Set ((Fin m → RVCalc.RV v) × (Fin n → RVCalc.RV v)))
    (A : Set ((Fin m → K) × (Fin n → K))) : Prop :=
  ∀ u ∈ C, FibreBijection v A u.1 u.2

namespace FibreBijection

variable {v : Valuation K Γ} {m n : ℕ}
    {A : Set ((Fin m → K) × (Fin n → K))}
    {t : Fin m → RVCalc.RV v} {s : Fin n → RVCalc.RV v}

/-- A lift supplies a genuine equivalence of the two RV-polydiscs. -/
noncomputable def equiv (h : FibreBijection v A t s) : RVFibre v t ≃ RVFibre v s where
  toFun a := ⟨Classical.choose (h.1 a.val a.property),
    (Classical.choose_spec (h.1 a.val a.property)).1.1⟩
  invFun b := ⟨Classical.choose (h.2 b.val b.property),
    (Classical.choose_spec (h.2 b.val b.property)).1.1⟩
  left_inv a := by
    apply Subtype.ext
    exact ((Classical.choose_spec (h.2 _
      (Classical.choose_spec (h.1 a.val a.property)).1.1)).2 a.val
        ⟨a.property, (Classical.choose_spec (h.1 a.val a.property)).1.2⟩).symm
  right_inv b := by
    apply Subtype.ext
    exact ((Classical.choose_spec (h.1 _
      (Classical.choose_spec (h.2 b.val b.property)).1.1)).2 b.val
        ⟨b.property, (Classical.choose_spec (h.2 b.val b.property)).1.2⟩).symm

theorem equiv_mem (h : FibreBijection v A t s) (a : RVFibre v t) :
    (a.val, (h.equiv a).val) ∈ A :=
  (Classical.choose_spec (h.1 a.val a.property)).1.2

theorem equiv_graph (h : FibreBijection v A t s)
    (a : RVFibre v t) (b : RVFibre v s) :
    h.equiv a = b ↔ (a.val, b.val) ∈ A := by
  constructor
  · intro he
    rw [← he]
    exact h.equiv_mem a
  · intro hab
    apply Subtype.ext
    exact ((Classical.choose_spec (h.1 a.val a.property)).2 b.val
      ⟨b.property, hab⟩).symm

end FibreBijection

theorem IsLift.restrict {v : Valuation K Γ} {m n : ℕ}
    {C D : Set ((Fin m → RVCalc.RV v) × (Fin n → RVCalc.RV v))}
    {A : Set ((Fin m → K) × (Fin n → K))}
    (h : IsLift v C A) (hDC : D ⊆ C) : IsLift v D A :=
  fun u hu => h u (hDC hu)

/-- Every RV diagonal has the VF diagonal as a lift, including absorbing coordinates. -/
theorem diagonal_isLift (v : Valuation K Γ) (n : ℕ)
    (D : Set (Fin n → RVCalc.RV v)) :
    IsLift v {u | u.1 = u.2 ∧ u.1 ∈ D} {p | p.1 = p.2} := by
  rintro ⟨t, s⟩ ⟨heq, _⟩
  change t = s at heq
  subst s
  constructor
  · intro a ha
    exact ⟨a, ⟨ha, rfl⟩, fun b hb => hb.2.symm⟩
  · intro b hb
    exact ⟨b, ⟨hb, rfl⟩, fun a ha => ha.2⟩

end SpecialTransformations.Section7
