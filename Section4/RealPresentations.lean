module

public import Section4.CodeMaps
public import Section3.ClosureBridge
public import CanonicalRV

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Real tuple presentations in a fixed LRV structure. The normalized
presentations in `Spaces` give the sorted-language comparison; these
constructors also allow the finite-refinement argument to stay in the
structure in which its definable graph was supplied. -/

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace SpecialTransformations.DefinableGeometry.Space

variable {L : Language} {M : Type} [L.Structure M]

/-- An injectively coded real sort is a presentation. -/
noncomputable def ofEmbedding {X ι : Type} [Finite ι] (code : X → ι → M)
    (hinj : Function.Injective code)
    (hdom : (∅ : Set M).Definable L (Set.range code)) : Space L M where
  Carrier := X
  Index := ι
  finiteIndex := inferInstance
  domain := Set.range code
  domain_definable := hdom
  decode z := Classical.choose z.property
  onto x := by
    refine ⟨⟨code x, Set.mem_range_self x⟩, hinj ?_⟩
    exact Classical.choose_spec (Set.mem_range_self x)
  diagonal_definable := by
    have hl := hdom.preimage_comp (Sum.inl : ι → ι ⊕ ι)
    have hr := hdom.preimage_comp (Sum.inr : ι → ι ⊕ ι)
    have he (i : ι) : (∅ : Set M).Definable L
        {z : ι ⊕ ι → M | z (.inl i) = z (.inr i)} :=
      (Set.DefinableFun.proj L).ofPred_eq (Set.DefinableFun.proj L)
    convert hl.inter (hr.inter (Set.definable_iInter_of_finite he)) using 1
    ext z
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hx, hy, hxy⟩
      refine ⟨hx, hy, ?_⟩
      intro i
      exact (congrFun (Classical.choose_spec hx) i).symm.trans
        ((congrArg (fun x => code x i) hxy).trans (congrFun (Classical.choose_spec hy) i))
    · rintro ⟨hx, hy, he⟩
      exact ⟨hx, hy, hinj ((Classical.choose_spec hx).trans
        ((funext he).trans (Classical.choose_spec hy).symm))⟩

theorem ofEmbedding_decode {X ι : Type} [Finite ι] (code : X → ι → M)
    (hinj : Function.Injective code) (hdom : (∅ : Set M).Definable L (Set.range code))
    (z : (ofEmbedding code hinj hdom).domain) :
    code ((ofEmbedding code hinj hdom).decode z) = z.val :=
  Classical.choose_spec z.property

end SpecialTransformations.DefinableGeometry.Space

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M]

def vfValues {n : ℕ} (x : Fin n → VFType (M := M)) : Fin n → M := fun i => (x i).val
def rvValues {n : ℕ} (x : Fin n → CanonicalRV.RVSort M) : Fin n → M := fun i => (x i).val

theorem vfValues_injective {n : ℕ} : Function.Injective (vfValues (M := M) (n := n)) := by
  intro x y he
  funext i
  exact Subtype.ext (congrFun he i)

theorem rvValues_injective {n : ℕ} : Function.Injective (rvValues (M := M) (n := n)) := by
  intro x y he
  funext i
  exact Subtype.ext (congrFun he i)

private theorem values_range_definable {n : ℕ} (σ : SortTag) :
    (∅ : Set M).Definable LRV
      (Set.range (fun x : Fin n → {z : M // sortEval σ z} => fun i => (x i).val)) := by
  have h (i : Fin n) := (definableAt_sort (∅ : Set M) σ).raw_definable.preimage_comp
    (fun _ : Fin 1 => i)
  convert Set.definable_iInter_of_finite h using 1
  ext z
  simp only [Set.mem_range, Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, rfl⟩ i
    exact (x i).property
  · intro hz
    exact ⟨fun i => ⟨z i, hz i⟩, rfl⟩

noncomputable def rawVFSpace (n : ℕ) : DefinableGeometry.Space LRV M :=
  .ofEmbedding (vfValues (n := n)) vfValues_injective (values_range_definable .vf)

noncomputable def rawRVSpace (n : ℕ) : DefinableGeometry.Space LRV M :=
  .ofEmbedding (rvValues (n := n)) rvValues_injective (values_range_definable .rv)

noncomputable def rawMixedSpace (n r : ℕ) : DefinableGeometry.Space LRV M :=
  (rawVFSpace n).prod (rawRVSpace r)

def mixedValues {n r : ℕ}
    (x : (Fin n → VFType (M := M)) × (Fin r → CanonicalRV.RVSort M)) : Fin n ⊕ Fin r → M :=
  Sum.elim (vfValues x.1) (rvValues x.2)

theorem mixedValues_injective {n r : ℕ} :
    Function.Injective (mixedValues (M := M) (n := n) (r := r)) := by
  intro x y he
  exact Prod.ext (vfValues_injective (funext (fun i => congrFun he (.inl i))))
    (rvValues_injective (funext (fun i => congrFun he (.inr i))))

@[simp] theorem mixedValues_mem_domain {n r : ℕ} (x : (rawMixedSpace (M := M) n r).Carrier) :
    mixedValues x ∈ (rawMixedSpace (M := M) n r).domain :=
  ⟨Set.mem_range_self x.1, Set.mem_range_self x.2⟩

@[simp] theorem mixedValues_decode {n r : ℕ} (z : (rawMixedSpace (M := M) n r).domain) :
    mixedValues ((rawMixedSpace (M := M) n r).decode z) = z.val := by
  funext i
  cases i with
  | inl i => exact congrFun (Classical.choose_spec z.property.1) i
  | inr i => exact congrFun (Classical.choose_spec z.property.2) i

@[simp] theorem decode_mixedValues {n r : ℕ} (x : (rawMixedSpace (M := M) n r).Carrier) :
    (rawMixedSpace (M := M) n r).decode ⟨mixedValues x, mixedValues_mem_domain x⟩ = x :=
  mixedValues_injective (mixedValues_decode _)

end SpecialTransformations.Section4
