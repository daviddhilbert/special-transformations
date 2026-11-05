import Section3.GammaCodeDefinability
import Section3.GammaParameters
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Add unused Gamma coordinates, or repeat existing ones, retaining the
full proper-code guard and global representative invariance. -/
def Relation.precomposeGamma {S : Set M} {k n l : ℕ} {sn : Fin n → SortTag}
    (Q : Relation S k n sn) (π : Fin k → Fin l) : Relation S l n sn where
  carrier := {p | Proper p.1 ∧ (p.1 ∘ π,p.2) ∈ Q.carrier}
  definable := by
    have hp := @Set.Definable.preimage_comp M S LRV (CanonicalStructure.normalize (M := M))
      (Fin l) (Fin l ⊕ Fin n) Sum.inl _ (proper_normalized_definable S)
    have hq := @Set.Definable.preimage_comp M S LRV (CanonicalStructure.normalize (M := M))
      (Fin k ⊕ Fin n) (Fin l ⊕ Fin n) (Sum.map π id) _ Q.definable
    let N := CanonicalStructure.normalize (M := M)
    letI := N
    convert hp.inter hq using 1
    ext z
    rfl
  proper := fun p hp => ⟨hp.1,(Q.proper _ hp.2).2⟩
  invariant := by
    intro t u htu b
    have he : values (t ∘ π) = values (u ∘ π) := funext (fun i => congrFun htu (π i))
    change (Proper (rawTuple t) ∧ (rawTuple (t ∘ π),b) ∈ Q.carrier) ↔
      (Proper (rawTuple u) ∧ (rawTuple (u ∘ π),b) ∈ Q.carrier)
    simp only [rawTuple_proper,true_and]
    exact Q.invariant (t ∘ π) (u ∘ π) he b

theorem DefinableWith.reparam {S : Set M} {k n l : ℕ}
    {γ : Fin k → Values.Gamma (M := M)} {δ : Fin l → Values.Gamma (M := M)}
    {sn : Fin n → SortTag} {A : Set (Fin n → M)} (hA : DefinableWith S γ sn A)
    (π : Fin k → Fin l) (hδ : δ ∘ π = γ) : DefinableWith S δ sn A := by
  obtain ⟨Q,hQA⟩ := hA
  refine ⟨Q.precomposeGamma π,?_⟩
  have hv : values (representatives δ ∘ π) = γ :=
    (congrArg (fun f => f ∘ π) (representatives_values δ)).trans hδ
  ext b
  change (Proper (rawTuple (representatives δ)) ∧
    (rawTuple (representatives δ ∘ π),b) ∈ Q.carrier) ↔ b ∈ A
  rw [and_iff_right (rawTuple_proper (representatives δ))]
  exact (Q.mem_fibre_iff (representatives δ ∘ π) γ hv b).symm.trans (Set.ext_iff.mp hQA b)

def Relation.inter {S : Set M} {k n : ℕ} {sn : Fin n → SortTag}
    (Q R : Relation S k n sn) : Relation S k n sn where
  carrier := Q.carrier ∩ R.carrier
  definable := by
    have hQ := Q.definable
    have hR := R.definable
    let N := CanonicalStructure.normalize (M := M)
    letI := N
    exact hQ.inter hR
  proper := fun p hp => Q.proper p hp.1
  invariant := fun t u htu b => and_congr (Q.invariant t u htu b) (R.invariant t u htu b)

theorem DefinableWith.inter {S : Set M} {k n : ℕ}
    {γ : Fin k → Values.Gamma (M := M)} {sn : Fin n → SortTag}
    {A C : Set (Fin n → M)} (hA : DefinableWith S γ sn A) (hC : DefinableWith S γ sn C) :
    DefinableWith S γ sn (A ∩ C) := by
  obtain ⟨Q,hQA⟩ := hA
  obtain ⟨R,hRC⟩ := hC
  refine ⟨Q.inter R,?_⟩
  ext b
  change (b ∈ Q.fibre γ ∧ b ∈ R.fibre γ) ↔ (b ∈ A ∧ b ∈ C)
  rw [hQA,hRC]

theorem DefinableOverBase.inter {B : Base (M := M)} {n : ℕ} {sn : Fin n → SortTag}
    {A C : Set (Fin n → M)} (hA : DefinableOverBase B sn A) (hC : DefinableOverBase B sn C) :
    DefinableOverBase B sn (A ∩ C) := by
  obtain ⟨k,γ,hγ,hA⟩ := hA
  obtain ⟨l,δ,hδ,hC⟩ := hC
  let e : Fin k ⊕ Fin l ≃ Fin (k+l) := finSumFinEquiv
  let η : Fin (k+l) → Values.Gamma (M := M) := Sum.elim γ δ ∘ e.symm
  let π : Fin k → Fin (k+l) := fun i => e (.inl i)
  let ρ : Fin l → Fin (k+l) := fun i => e (.inr i)
  have hη (i : Fin (k+l)) : η i ∈ B.gamma := by
    change Sum.elim γ δ (e.symm i) ∈ B.gamma
    cases e.symm i with
    | inl j => exact hγ j
    | inr j => exact hδ j
  have hπ : η ∘ π = γ := by
    funext i
    simp only [η,π,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inl]
  have hρ : η ∘ ρ = δ := by
    funext i
    simp only [η,ρ,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inr]
  exact ⟨k+l,η,hη,(hA.reparam π hπ).inter (hC.reparam ρ hρ)⟩

def Relation.monoReal {S T : Set M} {k n : ℕ} {sn : Fin n → SortTag}
    (Q : Relation S k n sn) (hST : S ⊆ T) : Relation T k n sn where
  carrier := Q.carrier
  definable := by
    have hQ := Q.definable
    let N := CanonicalStructure.normalize (M := M)
    letI := N
    exact hQ.mono hST
  proper := Q.proper
  invariant := Q.invariant

theorem DefinableWith.mono_real {S T : Set M} {k n : ℕ}
    {γ : Fin k → Values.Gamma (M := M)} {sn : Fin n → SortTag}
    {A : Set (Fin n → M)} (hA : DefinableWith S γ sn A) (hST : S ⊆ T) :
    DefinableWith T γ sn A := by
  obtain ⟨Q,hQA⟩ := hA
  exact ⟨Q.monoReal hST,hQA⟩

theorem DefinableOverBase.mono {B C : Base (M := M)} {n : ℕ}
    {sn : Fin n → SortTag} {A : Set (Fin n → M)} (hA : DefinableOverBase B sn A)
    (hreal : B.real ⊆ C.real) (hgamma : B.gamma ⊆ C.gamma) : DefinableOverBase C sn A := by
  obtain ⟨k,γ,hγ,hA⟩ := hA
  exact ⟨k,γ,(fun i => hgamma (hγ i)),hA.mono_real hreal⟩

theorem DefinableOverBase.proper {B : Base (M := M)} {n : ℕ}
    {sn : Fin n → SortTag} {A : Set (Fin n → M)} (hA : DefinableOverBase B sn A) :
    ∀ a ∈ A, ∀ i, sortEval (sn i) (a i) := by
  obtain ⟨k,γ,_,hA⟩ := hA
  exact hA.proper

theorem DefinableAtBase.proper {B : Base (M := M)} {σ : SortTag} {A : Set M}
    (hA : DefinableAtBase B σ A) : ∀ a ∈ A, sortEval σ a := by
  intro a ha
  exact DefinableOverBase.proper hA (fun _ => a) ha 0

theorem DefinableAtBase.mono {B C : Base (M := M)} {σ : SortTag} {A : Set M}
    (hA : DefinableAtBase B σ A) (hr : B.real ⊆ C.real) (hγ : B.gamma ⊆ C.gamma) :
    DefinableAtBase C σ A := DefinableOverBase.mono hA hr hγ

theorem AlgebraicAtBase.mono {B C : Base (M := M)} {σ : SortTag} {a : M}
    (ha : AlgebraicAtBase B σ a) (hr : B.real ⊆ C.real) (hγ : B.gamma ⊆ C.gamma) :
    AlgebraicAtBase C σ a := by
  obtain ⟨A,hA,hf,ha⟩ := ha
  exact ⟨A,hA.mono hr hγ,hf,ha⟩

theorem GammaDefinableOverBase.mono {B C : Base (M := M)} {A : Set (Values.Gamma (M := M))}
    (hA : GammaDefinableOverBase B A) (hr : B.real ⊆ C.real) (hγ : B.gamma ⊆ C.gamma) :
    GammaDefinableOverBase C A := DefinableAtBase.mono hA hr hγ

theorem GammaAlgebraicAtBase.mono {B C : Base (M := M)} {a : Values.Gamma (M := M)}
    (ha : GammaAlgebraicAtBase B a) (hr : B.real ⊆ C.real) (hγ : B.gamma ⊆ C.gamma) :
    GammaAlgebraicAtBase C a := by
  obtain ⟨A,hA,hf,ha⟩ := ha
  exact ⟨A,hA.mono hr hγ,hf,ha⟩

end SpecialTransformations.Section3.GammaParameters
