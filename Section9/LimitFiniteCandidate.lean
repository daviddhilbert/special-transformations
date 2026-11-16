module

public import Section9.LimitProjectiveRoots
public import Section9.LimitGeometry
public import Section8.PowerEstimateCore
public import Section8.IsolationRadius
public import VFAlgClosed

@[expose] public section

/-! Transport the finite projective root candidate set into the actual
limit-set definition on the VF and Gamma sorts of the pinned ACVF model. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section8
open scoped BigOperators

namespace SpecialTransformations.Section9

private theorem exists_support_shape {K : Type} [Field K]
    (P : MvPolynomial (Fin 2) K) (hp : P ≠ 0) :
    ∃ D : Finset (ℕ × ℕ), D.Nonempty ∧ ∃ c : ℕ × ℕ → K,
      (∀ d ∈ D, c d ≠ 0) ∧ ∀ x y : K,
        MvPolynomial.eval ![x, y] P = ∑ d ∈ D, c d * x ^ d.1 * y ^ d.2 := by
  classical
  obtain ⟨D, c, ⟨d, hd⟩, hD⟩ := mvPolynomial_has_shape P hp
  let c' (e : ℕ × ℕ) : K := if h : e ∈ D then c ⟨e, h⟩ else 0
  let D' := D.filter (fun e => c' e ≠ 0)
  have hd' : d.val ∈ D' := Finset.mem_filter.mpr ⟨d.property, by simpa [c', d.property] using hd⟩
  refine ⟨D', ⟨d.val, hd'⟩, c', fun e he => (Finset.mem_filter.mp he).2, fun x y => ?_⟩
  rw [hD, shapedPolynomial_eval]
  calc
    _ = ∑ e ∈ D, c' e * x ^ e.1 * y ^ e.2 := by
      rw [← Finset.sum_attach D (fun e => c' e * x ^ e.1 * y ^ e.2)]
      exact Finset.sum_congr rfl fun e _ => by simp [c', e.property]
    _ = _ := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro e he hnot
      have hz : c' e = 0 := by
        by_contra hn
        exact hnot (Finset.mem_filter.mpr ⟨he, hn⟩)
      simp [hz]

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

local notation "VF" => VFType (M := M)
local notation "Γ" => Values.Gamma (M := M)
local notation "w" => Values.presentationValuation (M := M)

theorem memValuedLimitSide_iff_memLimitBall (r : VF) (ε : Γ)
    (hval : Values.vfValueHom r = ε.val) (b : LimitPoint M) (y : VF) :
    memValuedLimitSide w r b y ↔ memLimitBall b ε y := by
  cases b with
  | none =>
    have hinv : Values.vfValueHom r⁻¹ = (ε⁻¹).val := by
      rw [map_inv₀, hval, Values.gamma_val_inv]
    change (w r)⁻¹ < w y ↔ Values.vfValueHom y < (ε⁻¹).val
    rw [← map_inv₀, ← hinv, vfValue_lt_iff_presentation]
  | some b =>
    change w (y - b) < w r ↔ ε.val < Values.vfValueHom (y - b)
    rw [← hval, vfValue_lt_iff_presentation]

/-- A single nonzero polynomial covering a unary scalar relation gives
a finite candidate limit set in the sense of Definition 9.1. -/
theorem exists_finite_limitSet_of_unary_polynomial
    (A : Set (Fin 1 → VF)) (f : (Fin 1 → VF) → Set (Fin 1 → VF))
    (P : MvPolynomial (Fin 2) VF) (hp : P ≠ 0)
    (hcover : ∀ x ∈ A, ∀ y ∈ f x, MvPolynomial.eval ![x 0, y 0] P = 0) :
    ∃ L : Set (Fin 1 → LimitPoint M), L.Finite ∧ IsLimitSet A 0 f L := by
  letI : IsAlgClosed VF := VFAlgClosed.isAlgClosed_vfType
  obtain ⟨D, hD, c, hc, heval⟩ := exists_support_shape P hp
  obtain ⟨B, hB, h⟩ := exists_projective_root_candidates w D hD c hc
  let L := (fun b (_ : Fin 1) => b) '' B
  refine ⟨L, hB.image _, ?_⟩
  rw [isLimitSet_iff]
  intro ε
  obtain ⟨r, hr, hval⟩ := gamma_has_vf_representative ε
  obtain ⟨δ, hδ, hclose⟩ := h r hr
  let γ : Γ := Values.gammaOf (CanonicalRV.encodedRv δ)
    (fun he => hδ ((CanonicalRV.encodedRv_zero_iff δ).mp he))
  refine ⟨γ, fun x hx hnear y hy => ?_⟩
  have hx₀ : x 0 ≠ 0 := by
    intro he
    apply hx.2
    exact funext (fun i => by fin_cases i; exact he)
  have hv : w (x 0) < w δ := by
    apply (vfValue_lt_iff_presentation δ (x 0)).mp
    have hγ : γ.val = Values.vfValueHom δ := rfl
    simpa only [hγ, Pi.zero_apply, sub_zero] using hnear 0
  have hroot : (∑ d ∈ D, c d * x 0 ^ d.1 * y 0 ^ d.2) = 0 := by
    rw [← heval]
    exact hcover x hx.1 y hy
  obtain ⟨b, hb, hyb⟩ := hclose (x 0) (y 0) hx₀ hv hroot
  refine ⟨fun _ => b, ⟨b, hb, rfl⟩, fun i => ?_⟩
  fin_cases i
  exact (memValuedLimitSide_iff_memLimitBall r ε hval b (y 0)).mp hyb

/-- A finite limit cover for every coordinate gives a finite product
cover with one common input radius. -/
theorem exists_finite_limitSet_of_coordinates {n m : ℕ}
    (A : Set (Fin n → VF)) (a : Fin n → VF) (f : (Fin n → VF) → Set (Fin m → VF))
    (h : ∀ i : Fin m, ∃ L : Set (Fin 1 → LimitPoint M), L.Finite ∧
      IsLimitSet A a (fun x => (fun y (_ : Fin 1) => y i) '' f x) L) :
    ∃ L : Set (Fin m → LimitPoint M), L.Finite ∧ IsLimitSet A a f L := by
  classical
  choose Li hfinite hlimit using h
  let Ci (i : Fin m) : Set (LimitPoint M) := (fun b => b 0) '' Li i
  have hCi (i : Fin m) : (Ci i).Finite := (hfinite i).image _
  letI : ∀ i : Fin m, Fintype (Ci i) := fun i => (hCi i).fintype
  let L := Set.range (fun b : ∀ i, Ci i => fun i => (b i).val)
  refine ⟨L, Set.finite_range _, ?_⟩
  rw [isLimitSet_iff]
  intro ε
  have hnear (i : Fin m) := (isLimitSet_iff _ _ _ _).mp (hlimit i) ε
  choose δ hδ using hnear
  let T := insert (1 : Γ) (Finset.univ.image δ)
  have hT : T.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨T.max' hT, fun x hx hclose y hy => ?_⟩
  have hchoice (i : Fin m) : ∃ b ∈ Li i, (fun _ : Fin 1 => y i) ∈ limitBall b ε := by
    have hmem : δ i ∈ T := Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    exact hδ i x hx (vfBall_anti (Finset.le_max' T _ hmem) hclose) _ ⟨y, hy, rfl⟩
  choose b hb hby using hchoice
  let q (i : Fin m) : Ci i := ⟨b i 0, ⟨b i, hb i, rfl⟩⟩
  exact ⟨fun i => (q i).val, Set.mem_range_self q, fun i => hby i 0⟩

end SpecialTransformations.Section9
