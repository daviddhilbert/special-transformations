import Section3.GammaParameters
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem with_zero_iff (S : Set M) {n : ℕ} (γ : Fin 0 → Values.Gamma (M := M))
    (sn : Fin n → SortTag) (A : Set (Fin n → M)) :
    DefinableWith S γ sn A ↔ SpecialTransformations.Section3.DefinableOver S sn A := by
  constructor
  · rintro ⟨R,rfl⟩
    apply (definableOver_iff_normalized_raw S sn _).mpr
    constructor
    · let idx : Fin 0 ⊕ Fin n → Fin n := Sum.elim Fin.elim0 id
      have h := @Set.Definable.preimage_comp M S LRV (CanonicalStructure.normalize (M := M))
        (Fin 0 ⊕ Fin n) (Fin n) idx _ R.definable
      convert h using 1
      ext b
      change (rawTuple (representatives γ),b) ∈ R.carrier ↔
        ((b ∘ idx) ∘ Sum.inl,(b ∘ idx) ∘ Sum.inr) ∈ R.carrier
      have hi : rawTuple (representatives γ) = (b ∘ idx) ∘ Sum.inl :=
        funext (fun i => i.elim0)
      have ho : (b ∘ idx) ∘ Sum.inr = b := rfl
      rw [hi,ho]
    · exact R.fibre_proper γ
  · intro hA
    have hAN := (definableOver_iff_normalized_raw S sn A).mp hA
    let R : Relation S 0 n sn :=
      { carrier := {p | p.2 ∈ A}
        definable := @Set.Definable.preimage_comp M S LRV (CanonicalStructure.normalize (M := M))
          (Fin n) (Fin 0 ⊕ Fin n) Sum.inr A hAN.1
        proper := fun p hp => ⟨fun i => i.elim0,hAN.2 p.2 hp⟩
        invariant := fun _ _ _ _ => Iff.rfl }
    exact ⟨R,rfl⟩

theorem base_empty_iff (S : Set M) {n : ℕ} (sn : Fin n → SortTag) (A : Set (Fin n → M)) :
    DefinableOverBase (⟨S,∅⟩ : Base (M := M)) sn A ↔
      SpecialTransformations.Section3.DefinableOver S sn A := by
  constructor
  · rintro ⟨k,γ,hγ,hA⟩
    cases k with
    | zero => exact (with_zero_iff S γ sn A).mp hA
    | succ k => exact False.elim (hγ 0)
  · intro hA
    exact ⟨0,Fin.elim0,(fun i => i.elim0),(with_zero_iff S Fin.elim0 sn A).mpr hA⟩

theorem at_base_empty_iff (S : Set M) (σ : SortTag) (A : Set M) :
    DefinableAtBase (⟨S,∅⟩ : Base (M := M)) σ A ↔
      SpecialTransformations.Section3.DefinableAt S σ A := by
  constructor
  · intro hA
    have h := (base_empty_iff S (fun _ : Fin 1 => σ) {z | z 0 ∈ A}).mp hA
    exact ⟨h,fun a ha => ((definableOver_iff_normalized_raw S (fun _ : Fin 1 => σ) _).mp h).2 ![a] ha 0⟩
  · intro hA
    exact (base_empty_iff S (fun _ : Fin 1 => σ) {z | z 0 ∈ A}).mpr hA.1

theorem algebraic_base_empty_iff (S : Set M) (σ : SortTag) (b : M) :
    AlgebraicAtBase (⟨S,∅⟩ : Base (M := M)) σ b ↔
      SpecialTransformations.Section3.AlgebraicAt S σ b := by
  constructor
  · rintro ⟨A,hA,hfin,hb⟩
    exact ⟨A,(at_base_empty_iff S σ A).mp hA,hfin,hb⟩
  · rintro ⟨A,hA,hfin,hb⟩
    exact ⟨A,(at_base_empty_iff S σ A).mpr hA,hfin,hb⟩

theorem dcl_base_empty_iff (S : Set M) (σ : SortTag) (b : M) :
    DefinableClosureAtBase (⟨S,∅⟩ : Base (M := M)) σ b ↔
      SpecialTransformations.Section3.DefinableClosureAt S σ b :=
  at_base_empty_iff S σ {b}

end SpecialTransformations.Section3.GammaParameters
