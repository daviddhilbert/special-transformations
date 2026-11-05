import Section3.GammaDefinability
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
open Values
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Real codes for Gamma elements are all nonzero RV representatives.
There is no chosen section in a parameter base. -/
def Code := {t : CanonicalRV.RVSort M // t.val ≠ iRVZero}

def raw (t : Code (M := M)) : M := t.val.val

def value (t : Code (M := M)) : Gamma (M := M) := gammaOf t.val t.property

theorem raw_rv (t : Code (M := M)) : iRV (raw t) := t.val.property

theorem raw_ne_zero (t : Code (M := M)) : raw t ≠ iRVZero := t.property

theorem raw_injective : Function.Injective (raw (M := M)) := by
  intro t u he
  apply Subtype.ext
  apply Subtype.ext
  exact he

theorem value_surjective : Function.Surjective (value (M := M)) := by
  intro γ
  obtain ⟨t,ht0,htγ⟩ := gamma_has_nonzero_representative γ
  exact ⟨⟨t,ht0⟩,Subtype.ext htγ⟩

theorem value_eq_iff (t u : Code (M := M)) :
    value t = value u ↔ iLe (raw t) (raw u) ∧ iLe (raw u) (raw t) := by
  constructor
  · intro h
    exact (vrv_eq_iff t.val u.val).mp (congrArg Subtype.val h)
  · intro h
    apply Subtype.ext
    exact (vrv_eq_iff t.val u.val).mpr h

/-- Used only inside proofs of surjectivity and descent. Definability of
objects with Gamma parameters must use all codes and their invariance. -/
noncomputable def representative (γ : Gamma (M := M)) : Code (M := M) :=
  Classical.choose (value_surjective γ)

theorem representative_value (γ : Gamma (M := M)) : value (representative γ) = γ :=
  Classical.choose_spec (value_surjective γ)

def rawTuple {n : ℕ} (t : Fin n → Code (M := M)) : Fin n → M := fun i => raw (t i)

def values {n : ℕ} (t : Fin n → Code (M := M)) : Fin n → Gamma (M := M) := fun i => value (t i)

def Proper {n : ℕ} (a : Fin n → M) : Prop := ∀ i, iRV (a i) ∧ a i ≠ iRVZero

theorem rawTuple_proper {n : ℕ} (t : Fin n → Code (M := M)) : Proper (rawTuple t) :=
  fun i => ⟨raw_rv (t i),raw_ne_zero (t i)⟩

def ofRaw {n : ℕ} (a : Fin n → M) (ha : Proper a) : Fin n → Code (M := M) :=
  fun i => ⟨⟨a i,(ha i).1⟩,(ha i).2⟩

theorem rawTuple_ofRaw {n : ℕ} (a : Fin n → M) (ha : Proper a) : rawTuple (ofRaw a ha) = a := rfl

theorem rawTuple_injective {n : ℕ} : Function.Injective (rawTuple (M := M) (n := n)) := by
  intro t u he
  funext i
  exact raw_injective (congrFun he i)

theorem ofRaw_rawTuple {n : ℕ} (t : Fin n → Code (M := M)) :
    ofRaw (rawTuple t) (rawTuple_proper t) = t := rawTuple_injective rfl

noncomputable def representatives {n : ℕ} (γ : Fin n → Gamma (M := M)) : Fin n → Code (M := M) :=
  fun i => representative (γ i)

theorem representatives_values {n : ℕ} (γ : Fin n → Gamma (M := M)) : values (representatives γ) = γ :=
  funext (fun i => representative_value (γ i))

theorem values_surjective {n : ℕ} : Function.Surjective (values (M := M) (n := n)) :=
  fun γ => ⟨representatives γ,representatives_values γ⟩

theorem values_eq_iff {n : ℕ} (t u : Fin n → Code (M := M)) : values t = values u ↔
    ∀ i, iLe (rawTuple t i) (rawTuple u i) ∧ iLe (rawTuple u i) (rawTuple t i) := by
  constructor
  · intro he i
    exact (value_eq_iff (t i) (u i)).mp (congrFun he i)
  · intro h
    exact funext (fun i => (value_eq_iff (t i) (u i)).mpr (h i))

end SpecialTransformations.Section3.GammaParameters
