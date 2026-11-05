import ResidueUnitExtension
import PartialFieldMaps
import RVFrame

/-!
Maximal compatible partial field maps contain representatives of every unit
RV class. The enlargement is the actual field embedding constructed by the
residue-algebraic/transcendental calculation. Compatibility assumptions concern
only individual related RV pairs and the ordinary partial-map operation laws.
-/

namespace MaximalResidueExtension

open scoped IntermediateField
open PartialFieldMaps ResidueTranscendentalTransport ResidueAlgebraicTransport

variable {K L Γ Δ : Type*} [Field K] [Field L]
  [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]

theorem graph_domain_fieldMap (S : Subring (K × L)) (hS : IsFieldGraph S) :
    graph (domain S hS) (fieldMap S hS) = S := by
  ext z
  rcases z with ⟨x, y⟩
  constructor
  · intro h
    obtain ⟨a, rfl, rfl⟩ := (mem_graph _ _).mp h
    exact fieldMap_mem S hS a
  · intro h
    let a : domain S hS := ⟨x, y, h⟩
    exact (mem_graph _ _).mpr ⟨a, rfl, fieldMap_eq S hS a h⟩

theorem graph_le_adjoin_graph (F : Subfield K) (σ : F →+* L) (e : K)
    (g : F⟮e⟯ →+* L)
    (hbase : ∀ a : F, g (algebraMap F F⟮e⟯ a) = σ a) :
    graph F σ ≤ graph (F⟮e⟯).toSubfield g := by
  rintro ⟨x, y⟩ h
  obtain ⟨a, rfl, rfl⟩ := (mem_graph F σ).mp h
  exact (mem_graph _ _).mpr ⟨algebraMap F F⟮e⟯ a, rfl, hbase a⟩

theorem compatible_adjoin_graph (P : K → L → Prop) (F : Subfield K) (e : K)
    (g : F⟮e⟯ →+* L) (hP : ∀ x : F⟮e⟯, P (x : K) (g x)) :
    Compatible P (graph (F⟮e⟯).toSubfield g) := by
  refine ⟨isFieldGraph_graph _ _, ?_⟩
  intro x y h
  obtain ⟨a, rfl, rfl⟩ := (mem_graph _ _).mp h
  exact hP a

section Maximal

variable [IsAlgClosed K] [IsAlgClosed L]
variable (v : Valuation K Γ) (w : Valuation L Δ)
  (ρ : Residue v →+* Residue w)
  (R : RVCalc.RV v → RVCalc.RV w → Prop)
  (hzero : R none none)
  (hmul : ∀ a b a' b', R a a' → R b b' →
    R (RVCalc.rvMul v a b) (RVCalc.rvMul w a' b'))
  (hinv : ∀ a a', R a a' → R (rvInv v a) (rvInv w a'))
  (hintegral : ∀ (x : K) (y : L), R (RVCalc.rv v x) (RVCalc.rv w y) →
    v x ≤ 1 → w y ≤ 1)
  (hres : ∀ (x : K) (y : L) (hx : v x ≤ 1) (hy : w y ≤ 1),
    R (RVCalc.rv v x) (RVCalc.rv w y) →
      ρ (M7.vres v x hx) = M7.vres w y hy)
  (hunit : ∀ (x : K) (y : L) (hx : v x = 1) (hy : w y = 1),
    ρ (M7.vres v x hx.le) = M7.vres w y hy.le → R (RVCalc.rv v x) (RVCalc.rv w y))

include hzero hmul hinv hintegral hres hunit

theorem maximal_has_unit_representatives (S : Subring (K × L))
    (hmax : Maximal (Compatible (fun x y => R (RVCalc.rv v x) (RVCalc.rv w y))) S)
    (u : K) (hu : v u = 1) :
    ∃ a : domain S hmax.prop.1,
      v (a : K) = 1 ∧ RVCalc.rv v (a : K) = RVCalc.rv v u := by
  let F := domain S hmax.prop.1
  let σ : F →+* L := fieldMap S hmax.prop.1
  have hb : ∀ a : F, R (RVCalc.rv v (a : K)) (RVCalc.rv w (σ a)) :=
    fun a => hmax.prop.2 _ _ (fieldMap_mem S hmax.prop.1 a)
  have hi : ∀ a : F, v (a : K) ≤ 1 → w (σ a) ≤ 1 :=
    fun a ha => hintegral _ _ (hb a) ha
  have hr : ∀ (a : F) (ha : v (a : K) ≤ 1) (ha' : w (σ a) ≤ 1),
      ρ (M7.vres v (a : K) ha) = M7.vres w (σ a) ha' :=
    fun a ha ha' => hres _ _ ha ha' (hb a)
  obtain ⟨e, he, herv, g, _, hgbase, hgrv⟩ :=
    exists_unit_class_field_extension v w F σ ρ R hzero hmul hinv hi hr hb hunit hu
  let T := graph (F⟮e⟯).toSubfield g
  have hT : Compatible (fun x y => R (RVCalc.rv v x) (RVCalc.rv w y)) T :=
    compatible_adjoin_graph _ F e g hgrv
  have hST : S ≤ T := by
    rw [← graph_domain_fieldMap S hmax.prop.1]
    exact graph_le_adjoin_graph F σ e g hgbase
  have hTS : T ≤ S := hmax.2 hT hST
  have heT : (e, g (IntermediateField.AdjoinSimple.gen F e)) ∈ T :=
    (mem_graph _ _).mpr ⟨IntermediateField.AdjoinSimple.gen F e, rfl, rfl⟩
  exact ⟨⟨e, _, hTS heT⟩, he, herv⟩

/-- The canonical base residue field of a maximal graph is the whole ambient
residue field. This is an output of the local adjoining proofs and maximality. -/
theorem maximal_baseResidueField_eq_top (S : Subring (K × L))
    (hmax : Maximal (Compatible (fun x y => R (RVCalc.rv v x) (RVCalc.rv w y))) S) :
    baseResidueField v (domain S hmax.prop.1) = ⊤ := by
  apply top_unique
  intro z _
  by_cases hz : z = 0
  · rw [hz]
    exact (baseResidueField v _).zero_mem
  obtain ⟨u, hu, huz⟩ := exists_unit_representative v z hz
  obtain ⟨a, ha, harv⟩ :=
    maximal_has_unit_representatives v w ρ R hzero hmul hinv hintegral hres hunit S hmax u hu
  have haz : M7.vres v (a : K) ha.le = z :=
    (residue_eq_of_rv_eq v ha hu harv).trans huz
  rw [← haz]
  exact baseResidueField_contains v _ a ha.le

end Maximal

theorem maximal_has_unit_representatives_of_frame [IsAlgClosed K] [IsAlgClosed L]
    (v : Valuation K Γ) (w : Valuation L Δ)
    (ρ : Residue v →+* Residue w) (R : RVCalc.RV v → RVCalc.RV w → Prop)
    (h : RVFrame v w ρ R) (S : Subring (K × L))
    (hmax : Maximal (Compatible (fun x y => R (RVCalc.rv v x) (RVCalc.rv w y))) S)
    (u : K) (hu : v u = 1) :
    ∃ a : domain S hmax.prop.1,
      v (a : K) = 1 ∧ RVCalc.rv v (a : K) = RVCalc.rv v u :=
  maximal_has_unit_representatives v w ρ R h.zero h.mul h.inv
    (fun _ _ hxy hx => h.integral hxy hx)
    (fun _ _ hx hy hxy => h.residue hxy hx hy)
    (fun x y hx hy hres => (h.unit x y hx hy).mpr hres) S hmax u hu

theorem maximal_baseResidueField_eq_top_of_frame [IsAlgClosed K] [IsAlgClosed L]
    (v : Valuation K Γ) (w : Valuation L Δ)
    (ρ : Residue v →+* Residue w) (R : RVCalc.RV v → RVCalc.RV w → Prop)
    (h : RVFrame v w ρ R) (S : Subring (K × L))
    (hmax : Maximal (Compatible (fun x y => R (RVCalc.rv v x) (RVCalc.rv w y))) S) :
    baseResidueField v (domain S hmax.prop.1) = ⊤ :=
  maximal_baseResidueField_eq_top v w ρ R h.zero h.mul h.inv
    (fun _ _ hxy hx => h.integral hxy hx)
    (fun _ _ hx hy hxy => h.residue hxy hx hy)
    (fun x y hx hy hres => (h.unit x y hx hy).mpr hres) S hmax

theorem exists_maximal_with_full_residue [IsAlgClosed K] [IsAlgClosed L]
    (v : Valuation K Γ) (w : Valuation L Δ)
    (ρ : Residue v →+* Residue w) (R : RVCalc.RV v → RVCalc.RV w → Prop)
    (h : RVFrame v w ρ R) (S : Subring (K × L))
    (hS : Compatible (fun x y => R (RVCalc.rv v x) (RVCalc.rv w y)) S) :
    ∃ T : Subring (K × L), S ≤ T ∧
      ∃ hmax : Maximal (Compatible (fun x y => R (RVCalc.rv v x) (RVCalc.rv w y))) T,
        baseResidueField v (domain T hmax.prop.1) = ⊤ := by
  obtain ⟨T, hST, hmax⟩ := exists_maximal_extension _ S hS
  exact ⟨T, hST, hmax, maximal_baseResidueField_eq_top_of_frame v w ρ R h T hmax⟩

end MaximalResidueExtension

#print axioms MaximalResidueExtension.graph_domain_fieldMap
#print axioms MaximalResidueExtension.graph_le_adjoin_graph
#print axioms MaximalResidueExtension.compatible_adjoin_graph
#print axioms MaximalResidueExtension.maximal_has_unit_representatives
#print axioms MaximalResidueExtension.maximal_baseResidueField_eq_top
#print axioms MaximalResidueExtension.maximal_has_unit_representatives_of_frame
#print axioms MaximalResidueExtension.maximal_baseResidueField_eq_top_of_frame
#print axioms MaximalResidueExtension.exists_maximal_with_full_residue
