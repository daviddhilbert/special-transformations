import ResidueAlgebraicFieldEmbedding
import RVHenselLifting
import RVValueMap

/-!
Root existence for the finite residue-algebraic unit extension.

We transport the residue of a monic integral polynomial evaluation to a chosen
target unit, then use the algebraically closed factorization argument from
RVHenselLifting. This does not require a simple residue root and covers the
inseparable residue case. Combining with the finite-degree calculation gives
an actual field embedding with prescribed partial-RV compatibility.
-/

namespace ResidueAlgebraicTransport

open scoped BigOperators IntermediateField
open Polynomial ResidueTranscendentalTransport

variable {K L Γ Δ : Type*} [Field K] [Field L]
  [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]

theorem residue_eq_of_rv_eq (v : Valuation K Γ) {x y : K}
    (hx : v x = 1) (hy : v y = 1) (hxy : RVCalc.rv v x = RVCalc.rv v y) :
    M7.vres v x hx.le = M7.vres v y hy.le := by
  have hx0 : x ≠ 0 := by intro hz; simpa [hz] using hx
  have hy0 : y ≠ 0 := by intro hz; simpa [hz] using hy
  have hlt := (RVCalc.rv_eq_iff hx0 hy0).mp hxy
  rw [hx] at hlt
  have hz := (M7.vres_eq_zero_iff v (x - y) hlt.le).mpr hlt
  have hsub :
      (⟨x - y, (Valuation.mem_valuationSubring_iff v _).mpr hlt.le⟩ : v.valuationSubring) =
      ⟨x, (Valuation.mem_valuationSubring_iff v _).mpr hx.le⟩ -
        ⟨y, (Valuation.mem_valuationSubring_iff v _).mpr hy.le⟩ := Subtype.ext rfl
  unfold M7.vres at hz ⊢
  rw [hsub, map_sub] at hz
  exact sub_eq_zero.mp hz

/-- Residue transport makes the target evaluation infinitesimal. -/
theorem eval_lt_one (v : Valuation K Γ) (w : Valuation L Δ)
    (F : Subfield K) (σ : F →+* L) (ρ : Residue v →+* Residue w)
    (hintegral : ∀ a : F, v (a : K) ≤ 1 → w (σ a) ≤ 1)
    (hres : ∀ (a : F) (ha : v (a : K) ≤ 1) (hb : w (σ a) ≤ 1),
      ρ (M7.vres v (a : K) ha) = M7.vres w (σ a) hb)
    {e : K} {a₀ : L} (he : v e = 1) (ha₀ : w a₀ = 1)
    (p : Polynomial F) (hc : ∀ i : ℕ, v (p.coeff i : K) ≤ 1)
    (hpe : p.eval₂ F.subtype e = 0)
    (hvar : ρ (M7.vres v e he.le) = M7.vres w a₀ ha₀.le) :
    w (p.eval₂ σ a₀) < 1 := by
  let c : Fin (p.natDegree + 1) → K := fun i => (p.coeff i : K)
  let c' : Fin (p.natDegree + 1) → L := fun i => σ (p.coeff i)
  let m : Fin (p.natDegree + 1) → ℕ := fun i => i
  have hc₁ : ∀ i, v (c i) ≤ 1 := fun i => hc i
  have hc₂ : ∀ i, w (c' i) ≤ 1 := fun i => hintegral _ (hc i)
  have hcoeff : ∀ i, ρ (M7.vres v (c i) (hc₁ i)) = M7.vres w (c' i) (hc₂ i) :=
    fun i => hres _ _ _
  have ht := residue_sum_transport v w ρ (m := m) hc₁ hc₂ he ha₀ hcoeff hvar
  have heval : (∑ i, c i * e ^ m i) = p.eval₂ F.subtype e :=
    (eval₂_eq_fin_sum F.subtype p e).symm
  have heval' : (∑ i, c' i * a₀ ^ m i) = p.eval₂ σ a₀ :=
    (eval₂_eq_fin_sum σ p a₀).symm
  have hz : M7.vres v (∑ i, c i * e ^ m i) (sum_integral v hc₁ he) = 0 := by
    apply (M7.vres_eq_zero_iff v _ _).mpr
    rw [heval, hpe, map_zero]
    exact zero_lt_one
  rw [hz, map_zero] at ht
  have hlt := (M7.vres_eq_zero_iff w _ _).mp ht.symm
  rwa [heval'] at hlt

/-- A root of the source monic integral polynomial gives a genuine target root
with the prescribed residue. No separability assumption is needed. -/
theorem exists_root_with_residue [IsAlgClosed L]
    (v : Valuation K Γ) (w : Valuation L Δ)
    (F : Subfield K) (σ : F →+* L) (ρ : Residue v →+* Residue w)
    (hintegral : ∀ a : F, v (a : K) ≤ 1 → w (σ a) ≤ 1)
    (hres : ∀ (a : F) (ha : v (a : K) ≤ 1) (hb : w (σ a) ≤ 1),
      ρ (M7.vres v (a : K) ha) = M7.vres w (σ a) hb)
    {e : K} {a₀ : L} (he : v e = 1) (ha₀ : w a₀ = 1)
    (p : Polynomial F) (hp : p.Monic) (hc : ∀ i : ℕ, v (p.coeff i : K) ≤ 1)
    (hpe : p.eval₂ F.subtype e = 0)
    (hvar : ρ (M7.vres v e he.le) = M7.vres w a₀ ha₀.le) :
    ∃ d : L, ∃ hd : w d = 1, p.eval₂ σ d = 0 ∧
      ρ (M7.vres v e he.le) = M7.vres w d hd.le ∧
      RVCalc.rv w d = RVCalc.rv w a₀ := by
  have hsmall : w ((p.map σ).eval a₀) < 1 := by
    rw [Polynomial.eval_map]
    exact eval_lt_one v w F σ ρ hintegral hres he ha₀ p hc hpe hvar
  obtain ⟨d, hdroot, hdrv⟩ := RVCalc.exists_root_rv_eq w (hp.map σ) hsmall ha₀
  have hd : w d = 1 := by
    have h := congrArg (RVCalc.vrv w) hdrv
    simpa only [RVCalc.vrv_rv, ha₀] using h
  refine ⟨d, hd, ?_, ?_, hdrv⟩
  · simpa only [Polynomial.IsRoot.def, Polynomial.eval_map] using hdroot
  · exact hvar.trans (residue_eq_of_rv_eq w hd ha₀ hdrv).symm

/-- The full local finite unit extension, including target-root construction. -/
theorem exists_field_embedding_with_root [IsAlgClosed L]
    (v : Valuation K Γ) (w : Valuation L Δ)
    (F : Subfield K) (σ : F →+* L) (ρ : Residue v →+* Residue w)
    (κ : Subfield (Residue v))
    (hκ : ∀ (a : F) (ha : v (a : K) ≤ 1), M7.vres v (a : K) ha ∈ κ)
    (R : RVCalc.RV v → RVCalc.RV w → Prop)
    (hzero : R none none)
    (hmul : ∀ a b a' b', R a a' → R b b' →
      R (RVCalc.rvMul v a b) (RVCalc.rvMul w a' b'))
    (hintegral : ∀ a : F, v (a : K) ≤ 1 → w (σ a) ≤ 1)
    (hres : ∀ (a : F) (ha : v (a : K) ≤ 1) (hb : w (σ a) ≤ 1),
      ρ (M7.vres v (a : K) ha) = M7.vres w (σ a) hb)
    (hbase : ∀ a : F, R (RVCalc.rv v (a : K)) (RVCalc.rv w (σ a)))
    (hunit : ∀ (x : K) (y : L) (hx : v x = 1) (hy : w y = 1),
      ρ (M7.vres v x hx.le) = M7.vres w y hy.le → R (RVCalc.rv v x) (RVCalc.rv w y))
    {e : K} {a₀ : L} (he : v e = 1) (ha₀ : w a₀ = 1)
    (p : Polynomial F) (hp : p.Monic) (hc : ∀ i : ℕ, v (p.coeff i : K) ≤ 1)
    (hpe : p.eval₂ F.subtype e = 0)
    (hdegree : (minpoly κ (M7.vres v e he.le)).natDegree = p.natDegree)
    (hvar : ρ (M7.vres v e he.le) = M7.vres w a₀ ha₀.le) :
    ∃ g : F⟮e⟯ →+* L,
      Function.Injective g ∧
      (∀ a : F, g (algebraMap F F⟮e⟯ a) = σ a) ∧
      RVCalc.rv w (g (IntermediateField.AdjoinSimple.gen F e)) = RVCalc.rv w a₀ ∧
      ∀ x : F⟮e⟯, R (RVCalc.rv v (x : K)) (RVCalc.rv w (g x)) := by
  obtain ⟨d, hd, hpd, hvar', hdrv⟩ :=
    exists_root_with_residue v w F σ ρ hintegral hres he ha₀ p hp hc hpe hvar
  obtain ⟨g, hinj, hbase', hgen, hrv⟩ :=
    exists_field_embedding_of_residue_minpoly v w F σ ρ κ hκ R hzero hmul hintegral hres
      hbase hunit he hd p hp hpe hpd hdegree hvar'
  exact ⟨g, hinj, hbase', by rw [hgen]; exact hdrv, hrv⟩

end ResidueAlgebraicTransport

#print axioms ResidueAlgebraicTransport.residue_eq_of_rv_eq
#print axioms ResidueAlgebraicTransport.eval_lt_one
#print axioms ResidueAlgebraicTransport.exists_root_with_residue
#print axioms ResidueAlgebraicTransport.exists_field_embedding_with_root
