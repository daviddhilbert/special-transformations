import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Order.Zorn

/-! Directed unions of partial field maps, implemented by their graphs.
This gives the maximal-map construction used to iterate local adjoining steps.
-/

namespace PartialFieldMaps

variable {K L : Type*} [Field K] [Field L]

/-- A subring of the product is a partial field-map graph when it is closed
under coordinatewise inversion and is single valued over its first coordinate. -/
structure IsFieldGraph (S : Subring (K × L)) : Prop where
  inv_mem : ∀ {x : K} {y : L}, (x, y) ∈ S → (x⁻¹, y⁻¹) ∈ S
  functional : ∀ {x : K} {y z : L}, (x, y) ∈ S → (x, z) ∈ S → y = z

def domain (S : Subring (K × L)) (hS : IsFieldGraph S) : Subfield K where
  carrier := {x | ∃ y, (x, y) ∈ S}
  zero_mem' := ⟨0, S.zero_mem⟩
  one_mem' := ⟨1, S.one_mem⟩
  add_mem' := by
    rintro x z ⟨y, hy⟩ ⟨w, hw⟩
    exact ⟨y + w, S.add_mem hy hw⟩
  mul_mem' := by
    rintro x z ⟨y, hy⟩ ⟨w, hw⟩
    exact ⟨y * w, S.mul_mem hy hw⟩
  neg_mem' := by
    rintro x ⟨y, hy⟩
    exact ⟨-y, S.neg_mem hy⟩
  inv_mem' := by
    rintro x ⟨y, hy⟩
    exact ⟨y⁻¹, hS.inv_mem hy⟩

noncomputable def fieldMap (S : Subring (K × L)) (hS : IsFieldGraph S) :
    domain S hS →+* L where
  toFun x := Classical.choose x.2
  map_zero' := hS.functional (Classical.choose_spec (show (0 : K) ∈ domain S hS from
    (domain S hS).zero_mem)) S.zero_mem
  map_one' := hS.functional (Classical.choose_spec (show (1 : K) ∈ domain S hS from
    (domain S hS).one_mem)) S.one_mem
  map_add' x y := hS.functional (Classical.choose_spec (x + y).2)
    (S.add_mem (Classical.choose_spec x.2) (Classical.choose_spec y.2))
  map_mul' x y := hS.functional (Classical.choose_spec (x * y).2)
    (S.mul_mem (Classical.choose_spec x.2) (Classical.choose_spec y.2))

theorem fieldMap_mem (S : Subring (K × L)) (hS : IsFieldGraph S) (x : domain S hS) :
    ((x : K), fieldMap S hS x) ∈ S := Classical.choose_spec x.2

theorem fieldMap_eq (S : Subring (K × L)) (hS : IsFieldGraph S)
    (x : domain S hS) {y : L} (hy : ((x : K), y) ∈ S) : fieldMap S hS x = y :=
  hS.functional (fieldMap_mem S hS x) hy

/-- The graph of an actual homomorphism on a subfield. -/
def graph (F : Subfield K) (σ : F →+* L) : Subring (K × L) :=
  (F.subtype.prod σ).range

theorem mem_graph (F : Subfield K) (σ : F →+* L) {x : K} {y : L} :
    (x, y) ∈ graph F σ ↔ ∃ a : F, (a : K) = x ∧ σ a = y := by
  change (∃ a : F, ((a : K), σ a) = (x, y)) ↔ _
  simp only [Prod.mk.injEq]

theorem isFieldGraph_graph (F : Subfield K) (σ : F →+* L) : IsFieldGraph (graph F σ) where
  inv_mem := by
    intro x y h
    obtain ⟨a, rfl, rfl⟩ := (mem_graph F σ).mp h
    exact (mem_graph F σ).mpr ⟨a⁻¹, rfl, map_inv₀ σ a⟩
  functional := by
    intro x y z hy hz
    obtain ⟨a, ha, rfl⟩ := (mem_graph F σ).mp hy
    obtain ⟨b, hb, rfl⟩ := (mem_graph F σ).mp hz
    exact congrArg σ (Subtype.ext (ha.trans hb.symm))

theorem isFieldGraph_sSup {C : Set (Subring (K × L))}
    (hne : C.Nonempty) (hc : IsChain (· ≤ ·) C)
    (hC : ∀ S ∈ C, IsFieldGraph S) : IsFieldGraph (sSup C) := by
  have hm (z : K × L) : z ∈ sSup C ↔ ∃ S ∈ C, z ∈ S :=
    Subring.mem_sSup_of_directedOn hne hc.directedOn
  constructor
  · intro x y h
    obtain ⟨S, hS, hxy⟩ := (hm _).mp h
    exact (hm _).mpr ⟨S, hS, (hC S hS).inv_mem hxy⟩
  · intro x y z hy hz
    obtain ⟨A, hA, ha⟩ := (hm _).mp hy
    obtain ⟨B, hB, hb⟩ := (hm _).mp hz
    rcases hc.total hA hB with hab | hba
    · exact (hC B hB).functional (hab ha) hb
    · exact (hC A hA).functional ha (hba hb)

/-- A pointwise compatibility condition is preserved by chain unions. -/
def Compatible (P : K → L → Prop) (S : Subring (K × L)) : Prop :=
  IsFieldGraph S ∧ ∀ x y, (x, y) ∈ S → P x y

theorem compatible_sSup (P : K → L → Prop) {C : Set (Subring (K × L))}
    (hne : C.Nonempty) (hc : IsChain (· ≤ ·) C)
    (hC : ∀ S ∈ C, Compatible P S) : Compatible P (sSup C) := by
  refine ⟨isFieldGraph_sSup hne hc (fun S hS => (hC S hS).1), ?_⟩
  intro x y h
  obtain ⟨S, hS, hxy⟩ := (Subring.mem_sSup_of_directedOn hne hc.directedOn).mp h
  exact (hC S hS).2 x y hxy

/-- The chain-union argument produces a maximal partial field map respecting
any fixed elementwise constraint, including a prescribed RV-map graph. -/
theorem exists_maximal_extension (P : K → L → Prop) (S : Subring (K × L))
    (hS : Compatible P S) :
    ∃ T : Subring (K × L), S ≤ T ∧ Maximal (Compatible P) T := by
  apply zorn_le_nonempty₀ {T | Compatible P T} ?_ S hS
  intro C hC hc A hA
  exact ⟨sSup C, compatible_sSup P ⟨A, hA⟩ hc hC, fun B hB => le_sSup hB⟩

end PartialFieldMaps

#print axioms PartialFieldMaps.fieldMap
#print axioms PartialFieldMaps.isFieldGraph_sSup
#print axioms PartialFieldMaps.exists_maximal_extension
