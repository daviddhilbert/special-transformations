import Section3.GammaCodes
import Section3.SortedBoolean
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- A genuine first-order relation with Gamma inputs, represented by its
full invariant preimage on nonzero RV codes. Definability uses the normalized
released LRV structure; no representative is named in the real base S. -/
structure Relation (S : Set M) (k n : ℕ) (sn : Fin n → SortTag) where
  carrier : Set ((Fin k → M) × (Fin n → M))
  definable : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin k ⊕ Fin n)
    {z | (z ∘ Sum.inl,z ∘ Sum.inr) ∈ carrier}
  proper : ∀ p ∈ carrier, Proper p.1 ∧ ∀ i, sortEval (sn i) (p.2 i)
  invariant : ∀ t u : Fin k → Code (M := M), values t = values u →
    ∀ b : Fin n → M, (rawTuple t,b) ∈ carrier ↔ (rawTuple u,b) ∈ carrier

namespace Relation
variable {S : Set M} {k n : ℕ} {sn : Fin n → SortTag}

def fibre (R : Relation S k n sn) (γ : Fin k → Values.Gamma (M := M)) : Set (Fin n → M) :=
  {b | (rawTuple (representatives γ),b) ∈ R.carrier}

theorem row_eq_fibre (R : Relation S k n sn) (t : Fin k → Code (M := M))
    (γ : Fin k → Values.Gamma (M := M)) (ht : values t = γ) :
    {b | (rawTuple t,b) ∈ R.carrier} = R.fibre γ :=
  Set.ext (fun b => R.invariant t (representatives γ) (ht.trans (representatives_values γ).symm) b)

theorem mem_fibre_iff (R : Relation S k n sn) (t : Fin k → Code (M := M))
    (γ : Fin k → Values.Gamma (M := M)) (ht : values t = γ) (b : Fin n → M) :
    b ∈ R.fibre γ ↔ (rawTuple t,b) ∈ R.carrier :=
  (Set.ext_iff.mp (R.row_eq_fibre t γ ht) b).symm

theorem fibre_proper (R : Relation S k n sn) (γ : Fin k → Values.Gamma (M := M)) :
    ∀ b ∈ R.fibre γ, ∀ i, sortEval (sn i) (b i) := fun b hb => (R.proper _ hb).2

theorem full_preimage (R : Relation S k n sn) (t : Fin k → Code (M := M)) (b : Fin n → M) :
    b ∈ R.fibre (values t) ↔ (rawTuple t,b) ∈ R.carrier :=
  R.mem_fibre_iff t (values t) rfl b

end Relation

/-- Definability over a finite tuple of actual Gamma parameters. The
relation has a full first-order invariant preimage, not a chosen section. -/
def DefinableWith (S : Set M) {k n : ℕ} (γ : Fin k → Values.Gamma (M := M))
    (sn : Fin n → SortTag) (A : Set (Fin n → M)) : Prop :=
  ∃ R : Relation S k n sn, R.fibre γ = A

theorem DefinableWith.proper {S : Set M} {k n : ℕ} {γ : Fin k → Values.Gamma (M := M)}
    {sn : Fin n → SortTag} {A : Set (Fin n → M)} (hA : DefinableWith S γ sn A) :
    ∀ b ∈ A, ∀ i, sortEval (sn i) (b i) := by
  obtain ⟨R,rfl⟩ := hA
  exact R.fibre_proper γ

/-- A base in the real sorts together with its genuinely imaginary names. -/
structure Base where
  real : Set M
  gamma : Set (Values.Gamma (M := M))

def DefinableOverBase (B : Base (M := M)) {n : ℕ} (sn : Fin n → SortTag)
    (A : Set (Fin n → M)) : Prop :=
  ∃ k, ∃ γ : Fin k → Values.Gamma (M := M), (∀ i, γ i ∈ B.gamma) ∧ DefinableWith B.real γ sn A

def DefinableAtBase (B : Base (M := M)) (σ : SortTag) (A : Set M) : Prop :=
  DefinableOverBase B (fun _ : Fin 1 => σ) {z | z 0 ∈ A}

def AlgebraicAtBase (B : Base (M := M)) (σ : SortTag) (b : M) : Prop :=
  ∃ A : Set M, DefinableAtBase B σ A ∧ A.Finite ∧ b ∈ A

def DefinableClosureAtBase (B : Base (M := M)) (σ : SortTag) (b : M) : Prop :=
  DefinableAtBase B σ {b}

def GammaDefinableOverBase (B : Base (M := M)) (A : Set (Values.Gamma (M := M))) : Prop :=
  DefinableAtBase B .rv (Values.gammaPullback A)

def GammaAlgebraicAtBase (B : Base (M := M)) (γ : Values.Gamma (M := M)) : Prop :=
  ∃ A : Set (Values.Gamma (M := M)), GammaDefinableOverBase B A ∧ A.Finite ∧ γ ∈ A

def GammaDefinableClosureAtBase (B : Base (M := M)) (γ : Values.Gamma (M := M)) : Prop :=
  GammaDefinableOverBase B {γ}

/-- These are closure definitions, not assertions of the paper's exchange
or generation conclusions. Their algebraic laws are separate obligations. -/
def closureBase (B : Base (M := M)) : Base (M := M) where
  real := {b | ∃ σ, DefinableClosureAtBase B σ b}
  gamma := {γ | GammaDefinableClosureAtBase B γ}

def VFGeneratedBase (B : Base (M := M)) : Prop :=
  ∃ A : Set M, A ⊆ B.real ∧ (∀ a ∈ A, iVF a) ∧ closureBase ⟨A,∅⟩ = B

def VFGammaGeneratedBase (B : Base (M := M)) : Prop :=
  ∃ A : Set M, ∃ G : Set (Values.Gamma (M := M)),
    A ⊆ B.real ∧ G ⊆ B.gamma ∧ (∀ a ∈ A, iVF a) ∧ closureBase ⟨A,G⟩ = B

end SpecialTransformations.Section3.GammaParameters
