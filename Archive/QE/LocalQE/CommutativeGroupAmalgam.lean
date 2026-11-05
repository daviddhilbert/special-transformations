import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Prod

/-! Glue two compatible homomorphisms from subgroups of a commutative group.
The construction descends Mathlib's product homomorphism through the existing
surjective-lift API. Injectivity and preservation of value order are derived. -/

namespace CommutativeGroupAmalgam

variable {G H : Type*} [CommGroup G] [CommGroup H]

def AgreeOnInf (A B : Subgroup G) (fA : A →* H) (fB : B →* H) : Prop :=
  ∀ x : ↥(A ⊓ B), fA ⟨(x : G), x.2.1⟩ = fB ⟨(x : G), x.2.2⟩

def productToSup (A B : Subgroup G) : A × B →* ↥(A ⊔ B) :=
  (Subgroup.inclusion (show A ≤ A ⊔ B from le_sup_left)).coprod
    (Subgroup.inclusion (show B ≤ A ⊔ B from le_sup_right))

@[simp] theorem productToSup_coe (A B : Subgroup G) (a : A) (b : B) :
    (productToSup A B (a, b) : G) = (a : G) * (b : G) := rfl

theorem productToSup_surjective (A B : Subgroup G) :
    Function.Surjective (productToSup A B) := by
  intro x
  obtain ⟨a, b, hab⟩ := Subgroup.mem_sup'.mp x.2
  exact ⟨(a, b), Subtype.ext hab⟩

theorem kernel_le (A B : Subgroup G) (fA : A →* H) (fB : B →* H)
    (hagree : AgreeOnInf A B fA fB) :
    (productToSup A B).ker ≤ (fA.coprod fB).ker := by
  intro x hx
  have hab := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  change (x.1 : G) * (x.2 : G) = 1 at hab
  have hbval : (x.2 : G) = (x.1 : G)⁻¹ := eq_inv_of_mul_eq_one_right hab
  have hbA : (x.2 : G) ∈ A := by rw [hbval]; exact A.inv_mem x.1.2
  have hc := hagree ⟨(x.2 : G), hbA, x.2.2⟩
  have hbinv : (⟨(x.2 : G), hbA⟩ : A) = x.1⁻¹ := Subtype.ext hbval
  apply MonoidHom.mem_ker.mpr
  change fA x.1 * fB x.2 = 1
  rw [← hc, hbinv, map_inv, mul_inv_cancel]

/-- The actual homomorphism on the generated subgroup. -/
noncomputable def glue (A B : Subgroup G) (fA : A →* H) (fB : B →* H)
    (hagree : AgreeOnInf A B fA fB) : ↥(A ⊔ B) →* H :=
  (productToSup A B).liftOfSurjective (productToSup_surjective A B)
    ⟨fA.coprod fB, kernel_le A B fA fB hagree⟩

@[simp] theorem glue_product (A B : Subgroup G) (fA : A →* H) (fB : B →* H)
    (hagree : AgreeOnInf A B fA fB) (a : A) (b : B) :
    glue A B fA fB hagree (productToSup A B (a, b)) = fA a * fB b := by
  exact MonoidHom.liftOfRightInverse_comp_apply (productToSup A B)
    (Function.surjInv (productToSup_surjective A B))
    (Function.rightInverse_surjInv (productToSup_surjective A B))
    ⟨fA.coprod fB, kernel_le A B fA fB hagree⟩ (a, b)

@[simp] theorem glue_left (A B : Subgroup G) (fA : A →* H) (fB : B →* H)
    (hagree : AgreeOnInf A B fA fB) (a : A) :
    glue A B fA fB hagree (Subgroup.inclusion (show A ≤ A ⊔ B from le_sup_left) a) = fA a := by
  simpa only [productToSup, MonoidHom.coprod_apply, map_one, mul_one] using
    glue_product A B fA fB hagree a 1

@[simp] theorem glue_right (A B : Subgroup G) (fA : A →* H) (fB : B →* H)
    (hagree : AgreeOnInf A B fA fB) (b : B) :
    glue A B fA fB hagree (Subgroup.inclusion (show B ≤ A ⊔ B from le_sup_right) b) = fB b := by
  simpa only [productToSup, MonoidHom.coprod_apply, map_one, one_mul] using
    glue_product A B fA fB hagree 1 b

/-- The range-intersection condition rules out any new kernel. In fact it
already makes injectivity of fB follow from that of fA and compatibility. -/
theorem glue_injective (A B : Subgroup G) (fA : A →* H) (fB : B →* H)
    (hagree : AgreeOnInf A B fA fB) (hinj : Function.Injective fA)
    (hinter : ∀ b : B, fB b ∈ fA.range → (b : G) ∈ A) :
    Function.Injective (glue A B fA fB hagree) := by
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  obtain ⟨⟨a, b⟩, rfl⟩ := productToSup_surjective A B x
  rw [glue_product] at hx
  have hbimg : fA (a⁻¹) = fB b := by
    rw [map_inv]
    exact (eq_inv_of_mul_eq_one_right hx).symm
  have hbA : (b : G) ∈ A := hinter b (MonoidHom.mem_range.mpr ⟨a⁻¹, hbimg⟩)
  have hc := hagree ⟨(b : G), hbA, b.2⟩
  have hab : a * (⟨(b : G), hbA⟩ : A) = 1 := by
    apply hinj
    rw [map_mul, hc, map_one]
    exact hx
  apply Subtype.ext
  exact congrArg (fun z : A => (z : G)) hab

/-- Value-one factors contribute nothing to comparison. Thus preserving the
value preorder on B suffices to preserve it on A⊔B after adjoining A. -/
theorem glue_order_iff {Γ Δ : Type*} [Monoid Γ] [Preorder Γ] [Monoid Δ] [Preorder Δ]
    (A B : Subgroup G) (fA : A →* H) (fB : B →* H)
    (hagree : AgreeOnInf A B fA fB) (v : G →* Γ) (w : H →* Δ)
    (hA : ∀ a : A, v (a : G) = 1) (hfA : ∀ a : A, w (fA a) = 1)
    (hB : ∀ b c : B, v (b : G) ≤ v (c : G) ↔ w (fB b) ≤ w (fB c))
    (x y : ↥(A ⊔ B)) :
    v (x : G) ≤ v (y : G) ↔
      w (glue A B fA fB hagree x) ≤ w (glue A B fA fB hagree y) := by
  obtain ⟨⟨a, b⟩, rfl⟩ := productToSup_surjective A B x
  obtain ⟨⟨c, d⟩, rfl⟩ := productToSup_surjective A B y
  simpa only [productToSup_coe, glue_product, map_mul, hA, hfA, one_mul] using hB b d

end CommutativeGroupAmalgam

#print axioms CommutativeGroupAmalgam.glue
#print axioms CommutativeGroupAmalgam.glue_left
#print axioms CommutativeGroupAmalgam.glue_right
#print axioms CommutativeGroupAmalgam.glue_injective
#print axioms CommutativeGroupAmalgam.glue_order_iff
