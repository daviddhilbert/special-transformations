import Mathlib.ModelTheory.Definability
import Mathlib.ModelTheory.ElementaryMaps
import Mathlib.Data.Finite.Sum

/-!
# Functional closedness and definable closure

Definition 6.1, for arbitrary parameter sets and every finite input/output
arity. Graphs are complete graphs of partial functions, including their
domains. This generic module is specialized to the released LRV language
in `HenselianClosure`; it introduces no second valued-field language.
-/

open FirstOrder FirstOrder.Language
set_option backward.isDefEq.respectTransparency false

namespace SpecialTransformations.Section6

variable {L : Language} {M : Type} [L.Structure M]

/-- Closure under singletons definable over the whole, possibly infinite, base. -/
def DclClosed (X : Set M) : Prop :=
  ∀ b : M, X.Definable₁ L {b} → b ∈ X

/-- The complete graph of a partial map between finite Cartesian powers. -/
def partialGraph {ι κ : Type} (A : Set (ι → M)) (f : A → κ → M) :
    Set ((ι ⊕ κ) → M) :=
  {z | ∃ h : z ∘ Sum.inl ∈ A, f ⟨z ∘ Sum.inl, h⟩ = z ∘ Sum.inr}

/-- Definition 6.1. Both the domain and the full graph are definable over X.
Scalar, mixed-sort and empty tuples are all included. In a sorted
application the domain and graph also contain their sort conditions. -/
def FunctionallyClosed (X : Set M) : Prop :=
  ∀ (ι κ : Type) [Finite ι] [Finite κ] (A : Set (ι → M)) (f : A → κ → M),
    X.Definable L A → X.Definable L (partialGraph A f) →
    ∀ a : A, (∀ i, a.val i ∈ X) → ∀ j, f a j ∈ X

theorem singleton_tuple_coordinates {X : Set M} {ι : Type} [Finite ι]
    {b : ι → M} (hb : X.Definable L {b}) (i : ι) :
    X.Definable₁ L {b i} := by
  change X.Definable L {z : Fin 1 → M | z 0 = b i}
  have h := hb.image_comp (fun _ : Fin 1 => i)
  convert h using 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_image]
  constructor
  · intro hz
    exact ⟨b, rfl, funext (fun j => by
      simpa only [Function.comp_apply, Subsingleton.elim j 0] using hz.symm)⟩
  · rintro ⟨y, rfl, hy⟩
    exact (congrFun hy 0).symm

/-- Evaluating a uniquely defined tuple at parameters already in X yields
a tuple individually definable over X. No definable choice is used. -/
theorem singleton_of_unique_relation {X : Set M} {ι κ : Type}
    [Finite ι] [Finite κ] {R : Set ((ι ⊕ κ) → M)}
    (hR : X.Definable L R) (a : ι → M) (ha : ∀ i, a i ∈ X)
    (b : κ → M) (hb : ∀ y, Sum.elim a y ∈ R ↔ y = b) :
    X.Definable L {b} := by
  let F (y : κ → M) : ι ⊕ κ → M := Sum.elim a y
  have hF : X.DefinableMap L F := by
    intro i
    cases i with
    | inl i => exact L.definableFun_const κ (ha i)
    | inr j => exact Set.DefinableFun.proj L
  convert hR.preimage_map hF using 1
  ext y
  exact (hb y).symm

theorem functionallyClosed_of_dclClosed {X : Set M} (hX : DclClosed (L := L) X) :
    FunctionallyClosed (L := L) X := by
  intro ι κ _ _ A f _ hf a ha j
  have hb : X.Definable L {f a} :=
    singleton_of_unique_relation hf a.val ha (f a) (by
      intro y
      simp only [partialGraph, Set.mem_ofPred_eq, Sum.elim_comp_inl,
        Sum.elim_comp_inr]
      exact ⟨fun ⟨_, he⟩ => he.symm, fun he => ⟨a.property, he.symm⟩⟩)
  exact hX _ (singleton_tuple_coordinates hb j)

theorem dclClosed_of_functionallyClosed {X : Set M}
    (hX : FunctionallyClosed (L := L) X) : DclClosed (L := L) X := by
  intro b hb
  let A : Set (Fin 0 → M) := Set.univ
  let f : A → Fin 1 → M := fun _ _ => b
  have hg : X.Definable L (partialGraph A f) := by
    have hh := hb.preimage_comp (fun _ : Fin 1 => (Sum.inr 0 : Fin 0 ⊕ Fin 1))
    convert hh using 1
    ext z
    simp only [partialGraph, A, f, Set.mem_ofPred_eq, Set.mem_univ,
      Set.mem_preimage, Function.comp_def, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, he⟩
      exact (congrFun he 0).symm
    · intro he
      exact ⟨trivial, funext (fun j => by simpa only [Subsingleton.elim j 0] using he.symm)⟩
  exact hX (Fin 0) (Fin 1) A f Set.definable_univ hg
    ⟨Fin.elim0, Set.mem_univ _⟩ (fun i => i.elim0) 0

theorem functionallyClosed_iff_dclClosed (X : Set M) :
    FunctionallyClosed (L := L) X ↔ DclClosed (L := L) X :=
  ⟨dclClosed_of_functionallyClosed, functionallyClosed_of_dclClosed⟩

/-- A definable singleton is fixed by every elementary self-map fixing its
parameters. This also applies to automorphisms of an algebraic envelope. -/
theorem definable_singleton_fixed {X : Set M} {b : M}
    (hb : X.Definable₁ L {b}) (e : M ↪ₑ[L] M)
    (he : ∀ x ∈ X, e x = x) : e b = b := by
  obtain ⟨φ, hφ⟩ := Set.definable_iff_exists_formula_sum.mp hb
  have hreal (c : M) : φ.Realize (Sum.elim Subtype.val (fun _ : Fin 1 => c)) ↔ c = b := by
    exact (Set.ext_iff.mp hφ (fun _ : Fin 1 => c)).symm
  apply (hreal (e b)).mp
  have hp := (e.map_formula φ (Sum.elim Subtype.val (fun _ : Fin 1 => b))).mpr
    ((hreal b).mpr rfl)
  have hv : e ∘ Sum.elim (Subtype.val : X → M) (fun _ : Fin 1 => b) =
      Sum.elim (Subtype.val : X → M) (fun _ : Fin 1 => e b) := by
    funext i
    cases i with
    | inl x => exact he x.val x.property
    | inr i => rfl
  rwa [hv] at hp

end SpecialTransformations.Section6
