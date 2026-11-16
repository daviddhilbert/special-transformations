module

public import Mathlib.ModelTheory.Ultraproducts
public import Mathlib.ModelTheory.ElementaryMaps
public import Mathlib.Order.Filter.AtTopBot.Finset

@[expose] public section

/-! Elementary amalgamation over tuples of the same complete type. Only
countable saturation is needed after amalgamating the two structures. -/

noncomputable section
open Classical FirstOrder FirstOrder.Language
open scoped Filter

namespace SpecialTransformations.Section6.NativeAmalgamation

variable {L : FirstOrder.Language.{0, 0}} {U V I : Type}
variable [L.Structure U] [L.Structure V] [Nonempty V]
variable (a : I → U) (b : I → V)
variable (ht : ∀ φ : L.Formula I, φ.Realize a ↔ φ.Realize b)
include ht

private theorem finite_diagram (S : Finset {φ : L.Formula U // φ.Realize id}) :
    ∃ f : U → V, f ∘ a = b ∧ ∀ φ ∈ S, φ.val.Realize f := by
  classical
  let ψ : L.Formula U := BoundedFormula.iInf (fun φ : S => φ.val.val)
  let J := ψ.freeVarFinset
  let g (u : J) : I ⊕ J :=
    if h : (u : U) ∈ Set.range a then .inl h.choose else .inr u
  let χ : L.Formula (I ⊕ J) := ψ.restrictFreeVar g
  have hψ : ψ.Realize id := by
    change BoundedFormula.Realize ψ id default
    exact BoundedFormula.realize_iInf.mpr (fun φ => φ.val.property)
  have ha : (χ.iExs J).Realize a := Formula.realize_iExs.mpr
    ⟨Subtype.val, (BoundedFormula.realize_restrictFreeVar id (by
      intro u
      by_cases h : (u : U) ∈ Set.range a
      · simpa only [g, dif_pos h, Sum.elim_inl, id_eq] using h.choose_spec
      · simp only [g, dif_neg h, Sum.elim_inr, id_eq])).mpr hψ⟩
  obtain ⟨w, hw⟩ := Formula.realize_iExs.mp ((ht (χ.iExs J)).mp ha)
  let f (u : U) : V :=
    if h : u ∈ Set.range a then b h.choose
    else if hj : u ∈ J then w ⟨u, hj⟩ else Classical.choice inferInstance
  have hfa : f ∘ a = b := by
    funext i
    have hi : a i ∈ Set.range a := ⟨i, rfl⟩
    have he := (ht ((Term.var hi.choose).equal (Term.var i))).mp
      (Formula.realize_equal.mpr hi.choose_spec)
    simpa [f, hi] using (Formula.realize_equal.mp he)
  have hf : ψ.Realize f :=
    (BoundedFormula.realize_restrictFreeVar f (by
      intro u
      by_cases h : (u : U) ∈ Set.range a
      · simp only [g, f, dif_pos h, Sum.elim_inl]
      · have hu : (u : U) ∈ J := u.property
        simp only [g, f, dif_neg h, dif_pos hu, Sum.elim_inr]
        rfl)).mp hw
  refine ⟨f, hfa, fun φ hφ => ?_⟩
  exact BoundedFormula.realize_iInf.mp hf ⟨φ, hφ⟩

theorem elementary_amalgam :
    ∃ (C : Type) (sC : L.Structure C),
      ∃ (j : @ElementaryEmbedding L U C _ sC)
        (k : @ElementaryEmbedding L V C _ sC), j ∘ a = k ∘ b := by
  classical
  let J := Finset {φ : L.Formula U // φ.Realize id}
  let D := Ultrafilter.of (Filter.atTop : Filter J)
  let C := (D : Filter J).Product (fun _ => V)
  let cls (z : J → V) : C := Quotient.mk ((D : Filter J).productSetoid (fun _ => V)) z
  let _ : L.Structure C := inferInstanceAs
    (L.Structure ((D : Filter J).Product (fun _ => V)))
  choose f hf using finite_diagram a b ht
  have forward {n : ℕ} (φ : L.Formula (Fin n)) (x : Fin n → U)
      (h : φ.Realize x) : ∀ᶠ i in D, φ.Realize (f i ∘ x) := by
    let s : {φ : L.Formula U // φ.Realize id} :=
      ⟨φ.relabel x, Formula.realize_relabel.mpr h⟩
    have he : ∀ᶠ i in (Filter.atTop : Filter J), {s} ≤ i := Filter.eventually_ge_atTop {s}
    filter_upwards [(Ultrafilter.of_le (Filter.atTop : Filter J)) he] with i hi
    exact Formula.realize_relabel.mp ((hf i).2 s (hi (Finset.mem_singleton_self s)))
  let j : U ↪ₑ[L] C :=
    { toFun := fun u => cls (fun i => f i u)
      map_formula' := by
        intro n φ x
        have hLos := Language.Ultraproduct.realize_formula_cast (u := D) φ (fun m i => f i (x m))
        change φ.Realize ((fun u => cls (fun i => f i u)) ∘ x) ↔ _ at hLos
        rw [hLos]
        constructor
        · intro h
          by_contra hn
          have he : ∀ᶠ _ : J in (D : Filter J), False :=
            (h.and (forward φ.not x (Formula.realize_not.mpr hn))).mono
              (fun _ h' => (Formula.realize_not.mp h'.2) h'.1)
          obtain ⟨_, hfalse⟩ := he.exists
          exact hfalse
        · exact forward φ x }
  let k : V ↪ₑ[L] C :=
    { toFun := fun v => cls (fun _ => v)
      map_formula' := by
        intro n φ x
        exact (Language.Ultraproduct.realize_formula_cast φ (fun m _ => x m)).trans
          Filter.eventually_const }
  refine ⟨C, inferInstance, j, k, ?_⟩
  funext i
  change cls (fun t => f t (a i)) = cls (fun _ => b i)
  congr 1
  funext t
  exact congrFun (hf t).1 i

end SpecialTransformations.Section6.NativeAmalgamation
