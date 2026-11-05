import Section3.ClosedBallChoice
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.ClosedClassCodes
open ClosedBallCodes
variable {M : Type} [sM : LRV.Structure M]

def classBody (E : Set (Fin 2 → M)) (r : M) : Set M := {x | ![x,r] ∈ E}

def codes (E : Set (Fin 2 → M)) (R : Set M) : Set (Fin 3 → M) :=
  {t | (∀ i, iVF (t i)) ∧ ∃ r ∈ R, rawBall t = classBody E r}

theorem rawBall_definable (S : Set M) :
    S.Definable LRV {z : Fin 3 ⊕ Fin 1 → M | z (.inr 0) ∈ rawBall (z ∘ Sum.inl)} := by
  have h := ClosedBallCodes.relation_definable S
  change S.Definable LRV {z : Fin 3 ⊕ Fin 1 → M |
    (z ∘ Sum.inl, z (.inr 0)) ∈ BallFamilies.relation ball} at h
  convert h using 1
  ext z
  change z (.inr 0) ∈ rawBall (z ∘ Sum.inl) ↔
    ∃ x : VFType (M := M), x.val ∈ rawBall (z ∘ Sum.inl) ∧ x.val = z (.inr 0)
  constructor
  · intro h
    exact ⟨⟨z (.inr 0), h.2.1⟩, h, rfl⟩
  · rintro ⟨x, hx, he⟩
    exact he ▸ hx

theorem eq_class_definable (S : Set M) (E : Set (Fin 2 → M))
    (hE : S.Definable LRV E) :
    S.Definable LRV {z : Fin 3 ⊕ Fin 1 → M | rawBall (z ∘ Sum.inl) = classBody E (z (.inr 0))} := by
  let ι := Fin 3 ⊕ Fin 1
  let p : Fin 3 ⊕ Fin 1 → ι ⊕ Fin 1 :=
    Sum.elim (fun i => .inl (.inl i)) (fun _ => .inr 0)
  let e : Fin 2 → ι ⊕ Fin 1 := ![.inr 0, .inl (.inr 0)]
  have hb := (rawBall_definable S).preimage_comp p
  have he := hE.preimage_comp e
  have h := ((hb.himp he).inter (he.himp hb)).forall_of_finite
  convert h using 1
  ext z
  have he (u : Fin 1 → M) : Sum.elim z u ∘ e = ![u 0,z (.inr 0)] := by
    funext i; fin_cases i <;> rfl
  change rawBall (z ∘ Sum.inl) = classBody E (z (.inr 0)) ↔
    ∀ u : Fin 1 → M,
      ((u 0 ∈ rawBall (z ∘ Sum.inl) → Sum.elim z u ∘ e ∈ E) ∧
       (Sum.elim z u ∘ e ∈ E → u 0 ∈ rawBall (z ∘ Sum.inl)))
  simp only [he]
  constructor
  · intro hh u
    exact ⟨fun hmem => by rw [hh] at hmem; exact hmem,
      fun hmem => by rw [hh]; exact hmem⟩
  · intro hh
    exact Set.ext (fun x => ⟨(hh ![x]).1, (hh ![x]).2⟩)

theorem codes_raw_definable (S : Set M) (E : Set (Fin 2 → M)) (R : Set M)
    (hE : S.Definable LRV E) (hR : S.Definable₁ LRV R) :
    S.Definable LRV (codes E R) := by
  have hr := hR.preimage_comp (Sum.inr : Fin 1 → Fin 3 ⊕ Fin 1)
  have hex := (hr.inter (eq_class_definable S E hE)).exists_of_finite
  have hs : S.Definable LRV {z : Fin 3 → M | ∀ i, iVF (z i)} := by
    rw [Set.ofPred_forall]
    exact Set.definable_iInter_of_finite (fun i =>
      (definableAt_sort S .vf).raw_definable.preimage_comp (fun _ : Fin 1 => i))
  convert hs.inter hex using 1
  ext z
  change ((∀ i, iVF (z i)) ∧ ∃ r ∈ R, rawBall z = classBody E r) ↔
    (∀ i, iVF (z i)) ∧ ∃ u : Fin 1 → M, u 0 ∈ R ∧ rawBall z = classBody E (u 0)
  exact and_congr_right (fun _ => ⟨fun ⟨r,hr,he⟩ => ⟨![r],hr,he⟩, fun ⟨u,hu,he⟩ => ⟨u 0,hu,he⟩⟩)

variable [hM : M ⊨ Axioms.ACVF]

theorem codes_normalize (E : Set (Fin 2 → M)) (R : Set M) :
    @codes M (CanonicalStructure.normalize (M := M)) E R = codes E R := by
  ext t
  simp only [codes, Set.mem_ofPred_eq, rawBall_normalize] <;> rfl

theorem codes_definable (S : Set M) (E : Set (Fin 2 → M)) (R : Set M)
    (hE : DefinableOver S (fun _ => .vf) E) (hR : DefinableAt S .vf R) :
    DefinableOver S (fun _ => .vf) (codes E R) := by
  let N := CanonicalStructure.normalize (M := M)
  letI := sM
  have hEN := (definableOver_normalize_iff S (fun _ => .vf) E).mpr hE
  have hRN := (definableAt_normalize_iff S .vf R).mpr hR
  apply (definableOver_iff_normalized_raw S (fun _ => .vf) _).mpr
  constructor
  · have hc := @codes_raw_definable M N S E R
      (@DefinableOver.raw_definable M N S 2 (fun _ => .vf) E hEN)
      (@DefinableAt.raw_definable M N S .vf R hRN)
    exact codes_normalize E R ▸ hc
  · exact fun t ht => ht.1

theorem codes_finite_values (E : Set (Fin 2 → M)) (R : Set M) (hR : R.Finite) :
    (rawBall '' codes E R).Finite := by
  apply (hR.image (classBody E)).subset
  rintro B ⟨t, ht, rfl⟩
  obtain ⟨r, hr, he⟩ := ht.2
  exact ⟨r, hr, he.symm⟩

theorem codes_cover {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (E : Set (Fin 2 → M)) (R : Set M)
    (hE : ∀ z ∈ E, ∀ i, iVF (z i))
    (hclosed : ∀ r ∈ R, ClosedBallRoots.IsClosedBall v {x : VFType (M := M) | ![x.val,r] ∈ E}) :
    ∀ r ∈ R, ∃ t : codes E R, rawBall t.val = classBody E r := by
  intro r hr
  obtain ⟨t,ht,he⟩ := exists_code_of_closed v hv {x : VFType (M := M) | ![x.val,r] ∈ E} (hclosed r hr)
  have hraw : rawBall t = classBody E r := by
    ext z
    constructor
    · intro hz
      let x : VFType (M := M) := ⟨z,hz.2.1⟩
      have hx : x ∈ ball t := hz
      have hB : x ∈ {x : VFType (M := M) | ![x.val,r] ∈ E} := he.symm ▸ hx
      exact hB
    · intro hz
      let x : VFType (M := M) := ⟨z,hE ![z,r] hz 0⟩
      have hB : x ∈ {x : VFType (M := M) | ![x.val,r] ∈ E} := hz
      have hx : x ∈ ball t := he ▸ hB
      exact hx
  exact ⟨⟨t,ht,r,hr,hraw⟩,hraw⟩

theorem centers (h00 : M ⊨ Axioms.ACVF00) (S : Set M)
    (E : Set (Fin 2 → M)) (R : Set M)
    (hE : DefinableOver S (fun _ => .vf) E) (hR : DefinableAt S .vf R) (hfin : R.Finite) :
    ∃ g : codes E R → M, (∀ t, g t ∈ rawBall t.val) ∧
      DefinableOver S (fun _ => .vf) (centerGraph (codes E R) g) ∧
      ∀ t u : codes E R, rawBall t.val = rawBall u.val → g t = g u :=
  coded_centers h00 S (codes E R) (codes_definable S E R hE hR) (codes_finite_values E R hfin)

end SpecialTransformations.Section3.ClosedClassCodes
