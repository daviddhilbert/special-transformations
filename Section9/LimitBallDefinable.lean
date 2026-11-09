import Section9.LimitGeometry
import Section8.PowerEstimateCore
import Section8.IsolationRadius
import Section3.ClosedClassCodes

/-! Parameter definability of the extended balls in Definition 9.1 and
of the unary hit sets in Lemma 9.4. A centre and a radius may be named in
this proof of a cardinality bound. They are not new fixed parameters for
the set-valued function. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

local notation "VF" => VFType (M := M)

omit [M ⊨ Axioms.ACVF] in
private theorem closed_code_definable (c : Fin 3 → M) :
    (Set.univ : Set M).Definable₁ LRV (ClosedBallCodes.rawBall c) := by
  let F (z : Fin 1 → M) : Fin 3 ⊕ Fin 1 → M := Sum.elim c z
  have hF : (Set.univ : Set M).DefinableMap LRV F := by
    rintro (i | i)
    · exact LRV.definableFun_const _ (Set.mem_univ _)
    · exact Set.DefinableFun.proj LRV
  exact (ClosedClassCodes.rawBall_definable Set.univ).preimage_map hF

theorem exists_definable_limitSide (b : LimitPoint M) (ε : Values.Gamma (M := M)) :
    ∃ C : Set M, DefinableAt Set.univ .vf C ∧
      ∀ y : VF, y.val ∈ C ↔ memLimitBall b ε y := by
  cases b with
  | some a =>
    obtain ⟨r, hr, hv⟩ := Section8.gamma_has_vf_representative ε
    let C := Section8.rawOpenBall a.val r.val
    refine ⟨C, ?_, ?_⟩
    · apply (definableAt_iff_normalized_raw Set.univ .vf C).mpr
      refine ⟨?_, fun _ h => h.2.1⟩
      dsimp only [C, Section8.rawOpenBall]
      rw [← OpenBallCodes.rawBall_normalize]
      letI := CanonicalStructure.normalize (M := M)
      exact Section8.rawOpenBall_definable (Set.mem_univ _) (Set.mem_univ _)
    · intro y
      have h := Section8.mem_rawOpenBall_iff Values.presentationValuation
        Values.presentation_compatible a r y hr
      exact h.trans (by
        change Values.presentationValuation (y - a) < Values.presentationValuation r ↔
          ε.val < Values.vfValueHom (y - a)
        rw [← hv, Section8.vfValue_lt_iff_presentation])
  | none =>
    obtain ⟨r, _, hv⟩ := Section8.gamma_has_vf_representative ε⁻¹
    let c : Fin 3 → M := ![(0 : VF).val, r.val, (1 : VF).val]
    have hc (i : Fin 3) : iVF (c i) := by
      fin_cases i
      · exact (0 : VF).property
      · exact r.property
      · exact (1 : VF).property
    have hflag : c 2 ≠ iVFZero := fun h => (one_ne_zero : (1 : VF) ≠ 0) (Subtype.ext h)
    let C := {x | iVF x} \ ClosedBallCodes.rawBall c
    refine ⟨C, ?_, ?_⟩
    · apply (definableAt_iff_normalized_raw Set.univ .vf C).mpr
      have hVF := ((definableAt_iff_normalized_raw (Set.univ : Set M) .vf {x | iVF x}).mp
        (definableAt_sort Set.univ .vf)).1
      have hclosed : @Set.Definable₁ M (Set.univ : Set M) LRV
          (CanonicalStructure.normalize (M := M)) (ClosedBallCodes.rawBall c) := by
        rw [← ClosedBallCodes.rawBall_normalize c]
        letI := CanonicalStructure.normalize (M := M)
        exact closed_code_definable c
      refine ⟨?_, Set.sdiff_subset⟩
      letI := CanonicalStructure.normalize (M := M)
      exact hVF.inter hclosed.compl
    · intro y
      have hclosed := Set.ext_iff.mp (ClosedBallCodes.ball_eq_closed
        Values.presentationValuation Values.presentation_compatible c hc hflag) y
      change y.val ∈ ClosedBallCodes.rawBall c ↔
        Values.presentationValuation (y - 0) ≤ Values.presentationValuation r at hclosed
      rw [sub_zero] at hclosed
      change (iVF y.val ∧ y.val ∉ ClosedBallCodes.rawBall c) ↔
        Values.vfValueHom y < (ε⁻¹).val
      rw [and_iff_right y.property, hclosed, ← hv, Section8.vfValue_lt_iff_presentation,
        not_le]

def rawLimitBall {m : ℕ} (b : Fin m → LimitPoint M) (ε : Values.Gamma (M := M)) :
    Set (Fin m → M) := vfValues '' limitBall b ε

theorem rawLimitBall_definable {m : ℕ} (b : Fin m → LimitPoint M) (ε : Values.Gamma (M := M)) :
    @Set.Definable M (Set.univ : Set M) LRV (CanonicalStructure.normalize (M := M))
      (Fin m) (rawLimitBall b ε) := by
  classical
  choose C hC hmem using fun i => exists_definable_limitSide (b i) ε
  have hEq : rawLimitBall b ε = {z | ∀ i, z i ∈ C i} := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩ i
      exact (hmem i (y i)).mpr (hy i)
    · intro hz
      let y (i : Fin m) : VF := ⟨z i, (hC i).2 (hz i)⟩
      exact ⟨y, fun i => (hmem i (y i)).mp (hz i), rfl⟩
  rw [hEq, Set.ofPred_forall]
  have hC' (i : Fin m) := ((definableAt_iff_normalized_raw Set.univ .vf (C i)).mp (hC i)).1
  letI := CanonicalStructure.normalize (M := M)
  exact Set.definable_iInter_of_finite (fun i =>
    (hC' i).preimage_comp (fun _ : Fin 1 => i))

def unaryLimitGraph {m : ℕ} (A : Set (Fin 1 → VF))
    (f : (Fin 1 → VF) → Set (Fin m → VF)) : Set ((Fin 1 ⊕ Fin m) → M) :=
  {z | ∃ x ∈ A, ∃ y ∈ f x, Sum.elim (vfValues x) (vfValues y) = z}

def limitHits {m : ℕ} (A : Set (Fin 1 → VF)) (f : (Fin 1 → VF) → Set (Fin m → VF))
    (b : Fin m → LimitPoint M) (ε : Values.Gamma (M := M)) : Set M :=
  {s | ∃ x ∈ A, (x 0).val = s ∧ ∃ y ∈ f x, y ∈ limitBall b ε}

theorem limitHits_definable {m : ℕ} (A : Set (Fin 1 → VF))
    (f : (Fin 1 → VF) → Set (Fin m → VF))
    (hG : @Set.Definable M (Set.univ : Set M) LRV (CanonicalStructure.normalize (M := M))
      (Fin 1 ⊕ Fin m) (unaryLimitGraph A f))
    (b : Fin m → LimitPoint M) (ε : Values.Gamma (M := M)) :
    DefinableAt Set.univ .vf (limitHits A f b ε) := by
  apply (definableAt_iff_normalized_raw Set.univ .vf _).mpr
  refine ⟨?_, ?_⟩
  · have hB := rawLimitBall_definable b ε
    have heq : {z : Fin 1 → M | z 0 ∈ limitHits A f b ε} =
        {z | ∃ w : Fin m → M, Sum.elim z w ∈ unaryLimitGraph A f ∧ w ∈ rawLimitBall b ε} := by
      ext z
      constructor
      · rintro ⟨x, hx, he, y, hy, hyb⟩
        have hxe : vfValues x = z := funext (fun i => by fin_cases i; exact he)
        exact ⟨vfValues y, ⟨x, hx, y, hy, by rw [hxe]⟩, ⟨y, hyb, rfl⟩⟩
      · rintro ⟨w, ⟨x, hx, y, hy, he⟩, y', hy'b, hy'e⟩
        have hxe : (x 0).val = z 0 := congrFun he (.inl 0)
        have hye : vfValues y = w := funext (fun i => congrFun he (.inr i))
        have he := vfValues_injective (hy'e.trans hye.symm)
        exact ⟨x, hx, hxe, y, hy, he ▸ hy'b⟩
    change @Set.Definable M (Set.univ : Set M) LRV (CanonicalStructure.normalize (M := M))
      (Fin 1) {z : Fin 1 → M | z 0 ∈ limitHits A f b ε}
    rw [heq]
    letI := CanonicalStructure.normalize (M := M)
    exact (hG.inter (hB.preimage_comp Sum.inr)).exists_of_finite
  · rintro _ ⟨x, _, rfl, _⟩
    exact (x 0).property

end SpecialTransformations.Section9
