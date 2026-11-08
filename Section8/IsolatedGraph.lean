import Section8.NeighbourhoodRelations
import Section3.GammaCodeDefinability

/-! A uniform first-order isolation condition for Lemma 8.2. Radius
parameters are in RV, so fixing them preserves the VF parameter field. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace SpecialTransformations.Section8

variable {M : Type} [LRV.Structure M]

/-- Membership in a ball with radius coded by a nonzero RV element. -/
def rvUniformBall {n : ℕ} (a : Fin n → M) (t : M) : Set (Fin n → M) :=
  {x | GammaParameters.NonzeroRV t ∧
    ∃ r : M, iVF r ∧ iRv r = t ∧ x ∈ uniformBall a r}

theorem rvUniformBallRelation_definable (S : Set M) (n : ℕ) :
    S.Definable LRV {z : ((Fin n ⊕ Fin n) ⊕ Fin 1) → M |
      (fun i => z (.inl (.inr i))) ∈ rvUniformBall (fun i => z (.inl (.inl i))) (z (.inr 0))} := by
  let I := (Fin n ⊕ Fin n) ⊕ Fin 1
  let radius : Fin 1 → I ⊕ Fin 1 := Sum.inr
  let rvCode : Fin 1 → I ⊕ Fin 1 := fun j => .inl (.inr j)
  let box : I → I ⊕ Fin 1 := Sum.elim (fun j => .inl (.inl j)) radius
  have hR := ((definableAt_sort S .vf).raw_definable).preimage_comp radius
  have hT := (GammaParameters.nonzero_rv_definable S).preimage_comp rvCode
  have hB := (uniformBallRelation_definable S n).preimage_comp box
  have hMap : S.DefinableFun LRV (fun z : I ⊕ Fin 1 → M =>
      Structure.funMap (L := LRV) Fn.rvMap (z ∘ radius)) := by
    apply (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol
      (M := M) (L := LRV) Fn.rvMap)).comp
    intro j
    exact Set.DefinableFun.proj LRV
  have hEq := hMap.ofPred_eq (Set.DefinableFun.proj LRV (i := rvCode 0))
  have h := (hT.inter (hR.inter (hEq.inter hB))).exists_of_finite
  convert h using 1
  ext z
  constructor
  · rintro ⟨ht, r, hr, he, hb⟩
    exact ⟨![r], ht, hr, he, hb⟩
  · rintro ⟨u, ht, hr, he, hb⟩
    refine ⟨ht, u 0, hr, ?_, hb⟩
    have hu : (![u 0] : Fin 1 → M) = u := by
      funext j
      fin_cases j
      rfl
    exact (congrArg (Structure.funMap (L := LRV) Fn.rvMap) hu).trans he

/-- Graph points with two RV radius codes such that the corresponding
product of balls contains no graph point with a different input. -/
def graphIsolation {n m : ℕ} (G : Set (Fin n ⊕ Fin m → M)) :
    Set (((Fin n ⊕ Fin m) ⊕ Fin 2) → M) :=
  {z | z ∘ Sum.inl ∈ G ∧
    (∀ j, GammaParameters.NonzeroRV (z (.inr j))) ∧
    ¬ ∃ w ∈ G,
      (w ∘ Sum.inl) ∈ rvUniformBall (fun i => z (.inl (.inl i))) (z (.inr 0)) ∧
      (w ∘ Sum.inr) ∈ rvUniformBall (fun i => z (.inl (.inr i))) (z (.inr 1)) ∧
      ¬ ∀ i, w (.inl i) = z (.inl (.inl i))}

theorem graphIsolation_definable {S : Set M} {n m : ℕ} {G : Set (Fin n ⊕ Fin m → M)}
    (hG : S.Definable LRV G) : S.Definable LRV (graphIsolation G) := by
  let X := Fin n ⊕ Fin m
  let Z := X ⊕ Fin 2
  let codeA : (Fin n ⊕ Fin n) ⊕ Fin 1 → Z ⊕ X := Sum.elim
    (Sum.elim (fun i => .inl (.inl (.inl i))) (fun i => .inr (.inl i))) (fun _ => .inl (.inr 0))
  let codeB : (Fin m ⊕ Fin m) ⊕ Fin 1 → Z ⊕ X := Sum.elim
    (Sum.elim (fun i => .inl (.inl (.inr i))) (fun i => .inr (.inr i))) (fun _ => .inl (.inr 1))
  have hA := (rvUniformBallRelation_definable S n).preimage_comp codeA
  have hB := (rvUniformBallRelation_definable S m).preimage_comp codeB
  have hEq : S.Definable LRV {z : Z ⊕ X → M | ∀ i : Fin n,
      z (.inr (.inl i)) = z (.inl (.inl (.inl i)))} := by
    rw [Set.ofPred_forall]
    exact Set.definable_iInter_of_finite (fun i =>
      (Set.DefinableFun.proj LRV (i := Sum.inr (Sum.inl i))).ofPred_eq
        (Set.DefinableFun.proj LRV (i := Sum.inl (Sum.inl (Sum.inl i)))))
  have hBad := ((hG.preimage_comp (Sum.inr : X → Z ⊕ X)).inter
    (hA.inter (hB.inter hEq.compl))).exists_of_finite
  have hRadii : S.Definable LRV {z : Z → M | ∀ j : Fin 2, GammaParameters.NonzeroRV (z (.inr j))} := by
    rw [Set.ofPred_forall]
    exact Set.definable_iInter_of_finite (fun j => (GammaParameters.nonzero_rv_definable S).preimage_comp
      (fun _ : Fin 1 => (Sum.inr j : Z)))
  convert (hG.preimage_comp (Sum.inl : X → Z)).inter (hRadii.inter hBad.compl) using 1
  ext z
  rfl

/-- Project away the output tuple, retaining both RV radius codes. -/
def inputIsolation {n m : ℕ} (G : Set (Fin n ⊕ Fin m → M)) : Set (Fin n ⊕ Fin 2 → M) :=
  (fun z => z ∘ Sum.elim (fun i => Sum.inl (Sum.inl i)) Sum.inr) '' graphIsolation G

theorem inputIsolation_definable {S : Set M} {n m : ℕ} {G : Set (Fin n ⊕ Fin m → M)}
    (hG : S.Definable LRV G) : S.Definable LRV (inputIsolation G) :=
  (graphIsolation_definable hG).image_comp _

theorem mem_inputIsolation_iff {n m : ℕ} {G : Set (Fin n ⊕ Fin m → M)}
    (x : Fin n → M) (t : Fin 2 → M) :
    Sum.elim x t ∈ inputIsolation G ↔
      ∃ y : Fin m → M, Sum.elim (Sum.elim x y) t ∈ graphIsolation G := by
  constructor
  · rintro ⟨z, hz, he⟩
    have h : Sum.elim (Sum.elim x (fun j => z (.inl (.inr j)))) t = z := by
      funext i
      rcases i with (i | j) | k
      · exact (congrFun he (.inl i)).symm
      · rfl
      · exact (congrFun he (.inr k)).symm
    exact ⟨_, h ▸ hz⟩
  · rintro ⟨y, hy⟩
    refine ⟨Sum.elim (Sum.elim x y) t, hy, ?_⟩
    funext i
    cases i <;> rfl

variable [hM : M ⊨ Axioms.ACVF]

/-- The fibre of the RV-coded relation agrees with the ball at any VF
representative having that RV class. The resulting ball depends only on
its value. -/
theorem rvUniformBall_eq {n : ℕ} (a : Fin n → M) (r : VFType (M := M)) (hr : r ≠ 0) :
    rvUniformBall a (iRv r.val) = uniformBall a r.val := by
  ext x
  constructor
  · rintro ⟨_, s, hs, he, hb⟩ i
    have hi := hb i
    refine ⟨⟨?_, fun hz => hr (Subtype.ext hz)⟩, hi.2.1, ?_⟩
    · intro j
      fin_cases j
      · exact hi.1.1 0
      · exact r.property
    · apply (OpenBallCodes.body_realize ![a i, r.val] (x i)).mpr
      have hc := (OpenBallCodes.body_realize ![a i, s] (x i)).mp hi.2.2
      simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, ← he] using hc
  · intro hx
    exact ⟨⟨rv_mem hM r.property, fun h => hr ((CanonicalRV.encodedRv_zero_iff r).mp h)⟩,
      r.val, r.property, rfl, hx⟩

end SpecialTransformations.Section8
