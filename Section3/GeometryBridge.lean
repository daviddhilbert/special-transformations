import Section3.BooleanCombinations
import Section3.ValuedCMinimal
import VFValued
import RVCalc
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ a b : VFType (M := M), VFValued.predV a b ↔ v a ≤ v b)

def vfImage (s : Set (VFType (M := M))) : Set M := Subtype.val '' s

omit hM in
@[simp] theorem mem_vfImage (a : VFType (M := M)) (s : Set (VFType (M := M))) :
    a.val ∈ vfImage s ↔ a ∈ s := by
  constructor
  · rintro ⟨b, hb, he⟩
    exact (Subtype.ext he : b = a) ▸ hb
  · intro ha
    exact ⟨a, ha, rfl⟩

omit hM in
theorem singleton_isBoolComb (a : VFType (M := M)) :
    IsBoolComb {b : Set M | IsBall b} {a.val} := by
  apply IsBoolComb.basic
  right; right; right
  refine ⟨a.val, a.property, ?_⟩
  ext x
  simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq]
  exact ⟨fun h => ⟨h ▸ a.property, h⟩, fun h => h.2⟩

include hv in
theorem isKBall_vfImage (s : Set (VFType (M := M)))
    (hs : ValOneEC.IsKBall (RingHom.id _) v s) :
    IsBoolComb {b : Set M | IsBall b} (vfImage s) := by
  classical
  cases hs with
  | closed a b =>
    by_cases hb : b = 0
    · subst b
      simp only [RingHom.id_apply, map_zero, ValOneEC.closedBall_zero_radius]
      simpa only [vfImage, Set.image_singleton] using singleton_isBoolComb a
    · apply IsBoolComb.basic
      right; left
      refine ⟨a.val, iRv b.val, a.property, rv_mem hM b.property, ?_, ?_⟩
      · exact fun h => hb ((CanonicalRV.encodedRv_zero_iff b).mp h)
      · ext x
        constructor
        · rintro ⟨c, hc, rfl⟩
          let d : VFType (M := M) := c
          have hd : v (d - a) ≤ v b := hc
          exact ⟨d.property, (hv (d - a) b).mpr hd⟩
        · rintro ⟨hx, hle⟩
          let d : VFType (M := M) := ⟨x, hx⟩
          exact ⟨d, (hv (d - a) b).mp hle, rfl⟩
  | openball a b =>
    by_cases hb : b = 0
    · subst b
      have he : vfImage (ValOneEC.openBall v a (v 0)) = ∅ := by
        ext x
        simp [vfImage, ValOneEC.openBall, not_lt_zero]
      change IsBoolComb {b : Set M | IsBall b} (vfImage (ValOneEC.openBall v a (v (0 : VFType (M := M)))))
      rw [he]
      exact BooleanCombinations.empty
    · apply IsBoolComb.basic
      right; right; left
      refine ⟨a.val, iRv b.val, a.property, rv_mem hM b.property, ?_, ?_⟩
      · exact fun h => hb ((CanonicalRV.encodedRv_zero_iff b).mp h)
      · ext x
        constructor
        · rintro ⟨c, hc, rfl⟩
          let d : VFType (M := M) := c
          have hd : v (d - a) < v b := hc
          refine ⟨d.property, (hv (d - a) b).mpr hd.le, ?_⟩
          exact fun h => (not_le_of_gt hd) ((hv b (d - a)).mp h)
        · rintro ⟨hx, hle, hnle⟩
          let c : VFType (M := M) := ⟨x, hx⟩
          refine ⟨c, ?_, rfl⟩
          exact (lt_iff_le_not_ge).mpr ⟨(hv (c - a) b).mp hle,
            fun h => hnle ((hv b (c - a)).mpr h)⟩
  | univ =>
    apply IsBoolComb.basic
    left
    ext x
    constructor
    · rintro ⟨a, _, rfl⟩; exact a.property
    · intro hx; exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩

include hv in
theorem good_vfImage (s : Set (VFType (M := M)))
    (hs : ValOneEC.Good (RingHom.id _) v s) :
    IsBoolComb {b : Set M | IsBall b} (vfImage s) := by
  classical
  obtain ⟨ι, _, b, t, hb, ht⟩ := hs
  have hbool := BooleanCombinations.boolean (fun i => vfImage (b i))
    (fun i => isKBall_vfImage v hv (b i) (hb i)) t
  have hVF : IsBoolComb {b : Set M | IsBall b} {x | iVF x} :=
    .basic (Or.inl rfl)
  have he : vfImage s = {x | iVF x} ∩ {x | t {i | x ∈ vfImage (b i)} = true} := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a.property, ?_⟩
      change t {i | a.val ∈ vfImage (b i)} = true
      simpa only [mem_vfImage] using (ht a).mp ha
    · rintro ⟨hx, ht'⟩
      let a : VFType (M := M) := ⟨x, hx⟩
      refine ⟨a, (ht a).mpr ?_, rfl⟩
      change t {i | a.val ∈ vfImage (b i)} = true at ht'
      simpa only [mem_vfImage] using ht'
  rw [he]
  exact BooleanCombinations.inter hVF hbool

end SpecialTransformations.Section3
