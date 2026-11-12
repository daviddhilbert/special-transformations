module

public import Section4.GammaRVRowAvoidance
public import Section4.GammaPredicates

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {g : ℕ}

def rvInfiniteIterate
    (hcan : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ) :
    {n : ℕ} → Relation S g n (fun _ => .rv) → (Fin n → Fin g) →
      Relation S g 0 (fun _ => .rv)
  | 0, Q, _ => Q
  | n + 1, Q, v => rvInfiniteIterate hcan h00 hs hsmall
      (rvInfiniteLast hcan h00 hs hsmall Q (v (Fin.last n))) (Fin.init v)

theorem independent_mem_rvInfiniteIterate
    (hcan : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {n : ℕ} (Q : Relation S g n (fun _ => .rv)) (v : Fin n → Fin g)
    (γ : Fin g → Values.Gamma (M := M)) (t : Fin n → CanonicalRV.RVSort M)
    (ht : rvValues t ∈ Q.fibre γ)
    (hval : ∀ i, Values.vrv (t i) = (γ (v i)).val)
    (hind : GammaRVSequenceIndependent ⟨S, Set.range γ⟩ t) :
    Fin.elim0 ∈ (rvInfiniteIterate hcan h00 hs hsmall Q v).fibre γ := by
  induction n with
  | zero =>
    have he : rvValues t = Fin.elim0 := by funext i; exact i.elim0
    exact he ▸ ht
  | succ n ih =>
    exact ih (rvInfiniteLast hcan h00 hs hsmall Q (v (Fin.last n))) (Fin.init v)
      (Fin.init t)
      (independent_mem_rvInfiniteLast hcan h00 hs hsmall Q (v (Fin.last n)) γ t ht
        (hval (Fin.last n)) hind)
      (fun i => hval i.castSucc) hind.1

/-- Every value tuple left by the iteration supports a full independent
RV sequence, even after naming any real representatives of that tuple. -/
theorem rvInfiniteIterate_exists_independent
    (hcan : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ)
    {n : ℕ} (Q : Relation S g n (fun _ => .rv)) (v : Fin n → Fin g)
    (γ : Fin g → Values.Gamma (M := M))
    (hmem : Fin.elim0 ∈ (rvInfiniteIterate hcan h00 hs hsmall Q v).fibre γ) :
    ∃ t : Fin n → CanonicalRV.RVSort M, rvValues t ∈ Q.fibre γ ∧
      RVSequenceIndependent (S ∪ Set.range (rawTuple (representatives γ))) t ∧
      ∀ i, Values.vrv (t i) = (γ (v i)).val := by
  induction n with
  | zero =>
    refine ⟨Fin.elim0, ?_, trivial, fun i => i.elim0⟩
    have he : rvValues (Fin.elim0 : Fin 0 → CanonicalRV.RVSort M) =
        (Fin.elim0 : Fin 0 → M) := by funext i; exact i.elim0
    exact he.symm ▸ hmem
  | succ n ih =>
    let R := rvInfiniteLast hcan h00 hs hsmall Q (v (Fin.last n))
    obtain ⟨b, hb, hbi, hbval⟩ := ih R (Fin.init v) hmem
    obtain ⟨x, hxSame, hxQ, hx0⟩ := rvInfiniteLast_exists_nonalgebraic hcan h00 hκ hs hsmall
      Q (v (Fin.last n)) γ (rvValues b) hb
    have he : rvValues (Fin.snoc b x) = Fin.snoc (rvValues b) x.val := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [rvValues, Fin.snoc_last]
      · simp only [rvValues, Fin.snoc_castSucc]
    refine ⟨Fin.snoc b x, he.symm ▸ hxQ, ?_, ?_⟩
    · simpa only [RVSequenceIndependent, Fin.init_snoc, Fin.snoc_last] using And.intro hbi hx0
    · refine Fin.lastCases ?_ (fun i => ?_)
      · simp only [Fin.snoc_last]
        exact ((Values.vrv_eq_iff x (representatives γ (v (Fin.last n))).val).mpr
          hxSame.2.2).trans (congrArg Subtype.val (representative_value (γ (v (Fin.last n)))))
      · simpa only [Fin.snoc_castSucc, Fin.init_def] using hbval i

theorem gamma_zero_relation_definable (Q : Relation S g 0 (fun _ => .rv)) :
    GammaSyntax.Definable S (fun γ : Fin g → Values.Gamma (M := M) => Fin.elim0 ∈ Q.fibre γ) := by
  let idx : Fin g ⊕ Fin 0 → Fin g := Sum.elim id Fin.elim0
  have h := @Set.Definable.preimage_comp M S LRV (CanonicalStructure.normalize (M := M))
    (Fin g ⊕ Fin 0) (Fin g) idx _ Q.definable
  change @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin g) _
  convert h using 1
  ext a
  have hcodes (ha : Proper a) : values (ofRaw a ha) = GammaSyntax.decode a := by
    funext i
    have hi : NonzeroRV (a i) := ha i
    simp only [values, GammaSyntax.decode, codeValue, dif_pos hi]
    rfl
  have heLeft : (a ∘ idx) ∘ Sum.inl = a := rfl
  have heRight : (a ∘ idx) ∘ Sum.inr = (Fin.elim0 : Fin 0 → M) := by
    funext i
    exact i.elim0
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, heLeft, heRight]
  change (GammaSyntax.Proper a ∧ Fin.elim0 ∈ Q.fibre (GammaSyntax.decode a)) ↔
    (a, Fin.elim0) ∈ Q.carrier
  constructor
  · rintro ⟨ha, hm⟩
    exact (Q.mem_fibre_iff (ofRaw a ha) _ (hcodes ha) Fin.elim0).mp hm
  · intro hm
    have ha := (Q.proper _ hm).1
    exact ⟨ha, (Q.mem_fibre_iff (ofRaw a ha) _ (hcodes ha) Fin.elim0).mpr hm⟩

end SpecialTransformations.Section4

end
