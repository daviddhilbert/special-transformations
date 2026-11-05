import JohnsonLanguagePrime

/-! Subfields and their valuation-preserving maps as Johnson-language
substructures and embeddings. These constructions use the same underlying
fields and valuation comparison as the RV reduct. -/

open FirstOrder FirstOrder.Language
set_option backward.isDefEq.respectTransparency false

namespace JohnsonValuedExtension

variable {E F Γ Δ : Type} [Field E] [Field F]
  [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]

def subfieldSubstructure (v : Valuation E Γ) (A : Subfield E) :
    @Language.Substructure Language.val E (FirstOrder.valStructure v) := by
  letI := FirstOrder.valStructure v
  exact {
    carrier := A
    fun_mem := by
      intro n f xs hxs
      cases f with
      | add => exact A.add_mem (hxs 0) (hxs 1)
      | mul => exact A.mul_mem (hxs 0) (hxs 1)
      | neg => exact A.neg_mem (hxs 0)
      | zero => exact A.zero_mem
      | one => exact A.one_mem }

def subfieldEmbedding (v : Valuation E Γ) (w : Valuation F Δ)
    (A : Subfield E) (g : A →+* F)
    (hg : ∀ a b : A, w (g a) ≤ w (g b) ↔ v a.1 ≤ v b.1) :
    letI := FirstOrder.valStructure v
    letI := FirstOrder.valStructure w
    (subfieldSubstructure v A) ↪[Language.val] F := by
  letI := FirstOrder.valStructure v
  letI := FirstOrder.valStructure w
  refine {
    toFun := fun a => g ⟨a.1, a.2⟩
    inj' := ?_
    map_fun' := ?_
    map_rel' := ?_ }
  · intro a b hab
    exact Subtype.ext (congrArg Subtype.val (g.injective hab))
  · intro n f xs
    cases f with
    | add => exact g.map_add _ _
    | mul => exact g.map_mul _ _
    | neg => exact g.map_neg _
    | zero => exact g.map_zero
    | one => exact g.map_one
  · intro n r xs
    cases r with
    | le => exact hg ⟨(xs 0).1, (xs 0).2⟩ ⟨(xs 1).1, (xs 1).2⟩

end JohnsonValuedExtension

#print axioms JohnsonValuedExtension.subfieldEmbedding
