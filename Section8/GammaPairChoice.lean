import Section8.GammaRadiusBase

/-! Definable witnesses with a unique shift and an upper ray of radii. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem gamma_named_unique_shift_radius (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
    (L : Values.Gamma (M := M) → Values.Gamma (M := M) → Prop)
    (P : Set (Fin 2 → M)) (hP : DefinableOverBase B (fun _ => .rv) P) (hne : P.Nonempty)
    (hProper : ∀ z ∈ P, Proper z)
    (hsem : ∀ z : Fin 2 → M, Proper z → (z ∈ P ↔ L (codeValue (z 0)) (codeValue (z 1))))
    (hunique : ∀ c r d s, L c r → L d s → c = d)
    (hup : ∀ c r, L c r → ∀ s, r ≤ s → L c s)
    (hclosed : ∀ c r, (∀ s, r < s → L c s) → L c r) :
    ∃ c r, GammaDefinableClosureAtBase B c ∧ GammaDefinableClosureAtBase B r ∧ L c r := by
  obtain ⟨w, hw⟩ := hne
  let c := codeValue (w 0)
  let r₀ := codeValue (w 1)
  have hr₀ : L c r₀ := (hsem w (hProper w hw)).mp hw
  have hc : GammaDefinableClosureAtBase B c := by
    have h := hP.image_real (fun _ : Fin 1 => (0 : Fin 2))
    change DefinableOverBase B (fun _ : Fin 1 => .rv) {z | z 0 ∈ Values.gammaPullback {c}}
    convert h using 1 <;> try rfl
    apply Set.ext
    intro z
    constructor
    · intro hz
      let hz₀ : NonzeroRV (z 0) := ⟨hz.choose, hz.choose_spec.choose⟩
      have he : codeValue (z 0) = c := (gammaPullback_mem_codeValue_iff _ (z 0) hz₀).mp hz
      let u : Fin 2 → M := ![z 0, w 1]
      have hu : Proper u := by
        intro i
        fin_cases i
        · exact hz₀
        · exact hProper w hw 1
      refine ⟨u, (hsem u hu).mpr ?_, funext (fun i => by fin_cases i; rfl)⟩
      change L (codeValue (z 0)) r₀
      rwa [he]
    · rintro ⟨u, hu, he⟩
      have hz : z 0 = u 0 := (congrFun he 0).symm
      change z 0 ∈ Values.gammaPullback {c}
      rw [hz]
      apply (gammaPullback_mem_codeValue_iff _ (u 0) (hProper u hu 0)).mpr
      exact hunique _ _ _ _ ((hsem u (hProper u hu)).mp hu) hr₀
  let R : Set (Values.Gamma (M := M)) := {r | L c r}
  have hR : GammaDefinableOverBase B R := by
    have hc' := hc.preimage_real (fun _ : Fin 2 => .rv) (fun _ : Fin 1 => (0 : Fin 2))
    have h := (hP.inter hc').image_real (fun _ : Fin 1 => (1 : Fin 2))
    change DefinableOverBase B (fun _ : Fin 1 => .rv) {z | z 0 ∈ Values.gammaPullback R}
    convert h using 1 <;> try rfl
    apply Set.ext
    intro z
    constructor
    · intro hz
      let hz₀ : NonzeroRV (z 0) := ⟨hz.choose, hz.choose_spec.choose⟩
      let u : Fin 2 → M := ![w 0, z 0]
      have hu : Proper u := by
        intro i
        fin_cases i
        · exact hProper w hw 0
        · exact hz₀
      exact ⟨u, ⟨(hsem u hu).mpr ((gammaPullback_mem_codeValue_iff R (z 0) hz₀).mp hz),
        ⟨(gammaPullback_mem_codeValue_iff _ (w 0) (hProper w hw 0)).mpr rfl, fun i => (hu i).1⟩⟩,
        funext (fun i => by fin_cases i; rfl)⟩
    · rintro ⟨u, ⟨hu, ⟨hcu, _⟩⟩, he⟩
      have hz : z 0 = u 1 := (congrFun he 0).symm
      change z 0 ∈ Values.gammaPullback R
      rw [hz]
      apply (gammaPullback_mem_codeValue_iff R (u 1) (hProper u hu 1)).mpr
      have hc' : codeValue (u 0) = c := (gammaPullback_mem_codeValue_iff _ (u 0) (hProper u hu 0)).mp hcu
      change L c (codeValue (u 1))
      rw [← hc']
      exact (hsem u (hProper u hu)).mp hu
  obtain ⟨r, hr, hrd⟩ := gamma_upper_ray_has_definable_radius_base h00 B hR ⟨r₀, hr₀⟩ (hup c) (hclosed c)
  exact ⟨c, r, hc, hrd, hr⟩

end SpecialTransformations.Section8
