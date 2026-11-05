import Section3.ClosedBallChoice
import Section3.ClosedClassCodes
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.ClassCenterRelation
open ClosedBallCodes
variable {M : Type} [sM : LRV.Structure M]

def relation (C : Set (Fin 3 → M)) (g : C → M) : Set (Fin 2 → M) :=
  {z | ∃ t : C, z 0 ∈ rawBall t.val ∧ g t = z 1}

theorem relation_raw_definable (S : Set M) (C : Set (Fin 3 → M)) (g : C → M)
    (hg : S.Definable LRV (centerGraph C g)) : S.Definable LRV (relation C g) := by
  let idx : Fin 4 → Fin 2 ⊕ Fin 3 := ![.inr 0, .inr 1, .inr 2, .inl 1]
  let jdx : Fin 3 ⊕ Fin 1 → Fin 2 ⊕ Fin 3 := Sum.elim Sum.inr (fun _ => .inl 0)
  have hG := hg.preimage_comp idx
  have hB := (ClosedClassCodes.rawBall_definable S).preimage_comp jdx
  have h := (hG.inter hB).exists_of_finite
  convert h using 1
  ext z
  have he (u : Fin 3 → M) : Fin.init (Sum.elim z u ∘ idx) = u := by
    funext i; fin_cases i <;> rfl
  change (∃ t : C, z 0 ∈ rawBall t.val ∧ g t = z 1) ↔
    ∃ u : Fin 3 → M, (∃ t : C, t.val = Fin.init (Sum.elim z u ∘ idx) ∧ g t = z 1) ∧ z 0 ∈ rawBall u
  simp only [he]
  constructor
  · rintro ⟨t,ht,hg⟩
    exact ⟨t.val,⟨t,rfl,hg⟩,ht⟩
  · rintro ⟨u,⟨t,htu,hg⟩,hu⟩
    exact ⟨t,htu.symm ▸ hu,hg⟩

variable [hM : M ⊨ Axioms.ACVF]

theorem relation_normalize (C : Set (Fin 3 → M)) (g : C → M) :
    @relation M (CanonicalStructure.normalize (M := M)) C g = relation C g := by
  ext z
  simp only [relation, Set.mem_ofPred_eq, rawBall_normalize] <;> rfl

theorem relation_definable (S : Set M) (C : Set (Fin 3 → M)) (g : C → M)
    (hmem : ∀ t : C, g t ∈ rawBall t.val)
    (hg : DefinableOver S (fun _ => .vf) (centerGraph C g)) :
    DefinableOver S (fun _ => .vf) (relation C g) := by
  let N := CanonicalStructure.normalize (M := M)
  letI := sM
  have hGN := (definableOver_normalize_iff S (fun _ => .vf) (centerGraph C g)).mpr hg
  apply (definableOver_iff_normalized_raw S (fun _ => .vf) _).mpr
  constructor
  · have hh := @relation_raw_definable M N S C g
      (@DefinableOver.raw_definable M N S 4 (fun _ => .vf) (centerGraph C g) hGN)
    exact relation_normalize C g ▸ hh
  · rintro z ⟨t,hx,hg⟩ i
    fin_cases i
    · exact hx.2.1
    · exact hg ▸ (hmem t).2.1

/-- Equality of intersecting balls is enough for functionality. The center
function has already been proved invariant under equality of actual balls. -/
theorem functional (C : Set (Fin 3 → M)) (g : C → M)
    (hdisj : ∀ t u : C, (rawBall t.val ∩ rawBall u.val).Nonempty → rawBall t.val = rawBall u.val)
    (hinv : ∀ t u : C, rawBall t.val = rawBall u.val → g t = g u)
    {x c d : M} (hc : ![x,c] ∈ relation C g) (hd : ![x,d] ∈ relation C g) : c = d := by
  obtain ⟨t,ht,hc⟩ := hc
  obtain ⟨u,hu,hd⟩ := hd
  exact hc.symm.trans ((hinv t u (hdisj t u ⟨x,ht,hu⟩)).trans hd)

end SpecialTransformations.Section3.ClassCenterRelation
