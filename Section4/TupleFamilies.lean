import Section4.FamilyCoding

set_option backward.isDefEq.respectTransparency false

/-!
# Uniform RV codes for finite families of VF tuples

The finite coding results of Section 3 are inputs. This module supplies the
Section 4 uniformity argument and proves that the code is unchanged when the
parameter is replaced by another presentation of the same fibre.
-/

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace SpecialTransformations.Section4.TupleFamilies

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {m n : ℕ}

def values (x : Fin n → VFType (M := M)) : Fin n → M := fun i => (x i).val

def RelationDefinable (S : Set M)
    (R : Set ((Fin m → M) × (Fin n → VFType (M := M)))) : Prop :=
  S.Definable LRV {z : Fin m ⊕ Fin n → M |
    ∃ x, (z ∘ Sum.inl, x) ∈ R ∧ values x = z ∘ Sum.inr}

def coordinateRelation (R : Set ((Fin m → M) × (Fin n → VFType (M := M))))
    (i : Fin n) : Set ((Fin m → M) × M) :=
  {p | ∃ x, (p.1, x) ∈ R ∧ (x i).val = p.2}

theorem coordinate_definable (S : Set M)
    (R : Set ((Fin m → M) × (Fin n → VFType (M := M))))
    (hR : RelationDefinable S R) (i : Fin n) :
    RawClosure.Tuple.RelationDefinable S (coordinateRelation R i) := by
  have h := hR.image_comp (Sum.map id (fun _ : Fin 1 => i))
  change S.Definable LRV _
  convert h using 1
  ext z
  constructor
  · rintro ⟨x, hx, he⟩
    refine ⟨Sum.elim (z ∘ Sum.inl) (values x), ⟨x, hx, rfl⟩, ?_⟩
    funext j
    cases j with
    | inl j => rfl
    | inr j => fin_cases j; exact he
  · rintro ⟨w, ⟨x, hx, he⟩, hw⟩
    have ht : w ∘ Sum.inl = z ∘ Sum.inl := by
      funext j
      exact congrFun hw (.inl j)
    refine ⟨x, ht ▸ hx, ?_⟩
    exact (congrFun he i).trans (congrFun hw (.inr 0))

theorem coordinate_finite
    (R : Set ((Fin m → M) × (Fin n → VFType (M := M))))
    (hfinite : ∀ t, {x | (t, x) ∈ R}.Finite) (i : Fin n) (t : Fin m → M) :
    {x | (t, x) ∈ coordinateRelation R i}.Finite := by
  convert (hfinite t).image (fun x : Fin n → VFType (M := M) => (x i).val) using 1
  ext x
  rfl

theorem coordinate_sorted
    (R : Set ((Fin m → M) × (Fin n → VFType (M := M))))
    (i : Fin n) (t : Fin m → M) (x : M) (hx : (t, x) ∈ coordinateRelation R i) :
    iVF x := by
  obtain ⟨a, _, rfl⟩ := hx
  exact (a i).property

noncomputable def code (d : ℕ)
    (R : Set ((Fin m → M) × (Fin n → VFType (M := M))))
    (hfinite : ∀ t, {x | (t, x) ∈ R}.Finite)
    (t : Fin m → M) (x : Fin n → M) (k : Fin (n * d)) : M :=
  let ij := finProdFinEquiv.symm k
  Barycentre.rawCode d
    (vfFamily (coordinateRelation R ij.1) (coordinate_finite R hfinite ij.1))
    t (x ij.1) ij.2

theorem code_fibre_invariant
    (R : Set ((Fin m → M) × (Fin n → VFType (M := M))))
    (hfinite : ∀ t, {x | (t, x) ∈ R}.Finite) (t u : Fin m → M)
    (he : ∀ x, (t, x) ∈ R ↔ (u, x) ∈ R) (d : ℕ)
    (x : Fin n → VFType (M := M)) :
    code d R hfinite t (values x) = code d R hfinite u (values x) := by
  funext k
  let ij := finProdFinEquiv.symm k
  have hc := code_eq_of_fibre_eq (coordinateRelation R ij.1)
    (coordinate_finite R hfinite ij.1) t u (fun y =>
      exists_congr (fun a => and_congr_left (fun _ => he a))) d (x ij.1)
  exact congrFun hc ij.2

theorem uniform_coding (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    (R : Set ((Fin m → M) × (Fin n → VFType (M := M))))
    (hR : RelationDefinable S R) (hfinite : ∀ t, {x | (t, x) ∈ R}.Finite) :
    ∃ d : ℕ,
      (∀ t, Set.InjOn (fun x => code d R hfinite t (values x)) {x | (t, x) ∈ R}) ∧
      (∀ k : Fin (n * d), S.DefinableFun LRV
        (fun z : Fin m ⊕ Fin n → M =>
          code d R hfinite (z ∘ Sum.inl) (z ∘ Sum.inr) k)) ∧
      (∀ t (x : Fin n → VFType (M := M)) k, iRV (code d R hfinite t (values x) k)) := by
  have hb (i : Fin n) : ∃ b : ℕ, ∀ t,
      {x | (t, x) ∈ coordinateRelation R i}.ncard ≤ b :=
    uniform_finite_fibre_bound hs S hsmall (coordinateRelation R i)
      (coordinate_definable S R hR i) (coordinate_finite R hfinite i)
  choose b hb using hb
  let d := ∑ i : Fin n, b i
  have hbound (i : Fin n) (t : Fin m → M) :
      (vfFamily (coordinateRelation R i) (coordinate_finite R hfinite i) t).card ≤ d := by
    rw [vfFamily_card _ _ (coordinate_sorted R i)]
    exact (hb i t).trans (Finset.single_le_sum (fun j _ => Nat.zero_le (b j))
      (Finset.mem_univ i))
  have hfamily (i : Fin n) : RawClosure.Tuple.RelationDefinable S
      (Barycentre.finiteFibreRelation
        (vfFamily (coordinateRelation R i) (coordinate_finite R hfinite i))) := by
    rw [vfFamily_relation _ _ (coordinate_sorted R i)]
    exact coordinate_definable S R hR i
  refine ⟨d, ?_, ?_, ?_⟩
  · intro t x hx y hy he
    funext i
    apply Barycentre.code_injective_of_card_le h00 d
      (vfFamily (coordinateRelation R i) (coordinate_finite R hfinite i) t)
      ((hbound i t).trans (Nat.le_succ d))
    · exact (mem_vfFamily _ _ t (x i)).mpr ⟨x, hx, rfl⟩
    · exact (mem_vfFamily _ _ t (y i)).mpr ⟨y, hy, rfl⟩
    · funext j
      have hj := congrFun he (finProdFinEquiv (i, j))
      simpa only [code, Equiv.symm_apply_apply, values, Barycentre.rawCode_eq_code] using hj
  · intro k
    let ij := finProdFinEquiv.symm k
    have h := Barycentre.rawCode_definable h00 S d
      (vfFamily (coordinateRelation R ij.1) (coordinate_finite R hfinite ij.1))
      (hfamily ij.1) d (hbound ij.1) ij.2
    exact h.comp (show S.DefinableMap LRV
      (fun z : Fin m ⊕ Fin n → M =>
        Sum.elim (z ∘ Sum.inl) (fun _ : Fin 1 => z (.inr ij.1))) from
      fun j => by cases j <;> exact Set.DefinableFun.proj LRV)
  · intro t x k
    dsimp only [code, values]
    rw [Barycentre.rawCode_eq_code]
    exact Barycentre.code_sorted _ _ _ _

end SpecialTransformations.Section4.TupleFamilies
