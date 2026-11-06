import Section3.Counting
import Section3.GammaBaseTools
import Section3.GammaCounting
import Section3.GammaParameters
import Section3.GammaProjection
import Section3.GammaSupport
import Section3.NormalizationSaturation

/- Component: TupleFibreCounting -/
open Classical FirstOrder FirstOrder.Language
namespace SpecialTransformations.ModelTheory
variable {L : FirstOrder.Language} {M : Type} [L.Structure M] {ι : Type}

/-- The checked Section3 tuple count, generalized to an arbitrary input
index and language. Input coordinates still range over the actual model M. -/
def HasMore (R : Set ((ι → M) × M)) (d : ℕ) : Set (ι → M) :=
  {a | ∃ x : Fin (d+1) → M, Function.Injective x ∧ ∀ i, (a,x i) ∈ R}

theorem hasMore_definable (S : Set M) (R : Set ((ι → M) × M))
    (hR : S.Definable L {z : ι ⊕ Fin 1 → M | (z ∘ Sum.inl,z (.inr 0)) ∈ R}) (d : ℕ) :
    S.Definable L (HasMore R d) := by
  classical
  let α := ι ⊕ Fin (d+1)
  have hrel (i : Fin (d+1)) : S.Definable L
      {z : α → M | (z ∘ Sum.inl,z (.inr i)) ∈ R} :=
    hR.preimage_comp (Sum.map id (fun _ : Fin 1 => i))
  have hne (p : Fin (d+1) × Fin (d+1)) : S.Definable L
      {z : α → M | p.1 = p.2 ∨ z (.inr p.1) ≠ z (.inr p.2)} := by
    by_cases hp : p.1 = p.2
    · simpa [hp] using (Set.definable_univ S L (α := α))
    · have he : S.Definable L {z : α → M | z (.inr p.1) = z (.inr p.2)} :=
        ⟨(Term.var (.inr p.1)).equal (Term.var (.inr p.2)),rfl⟩
      simpa [hp,Set.compl_ofPred] using he.compl
  have hfull := ((Set.definable_iInter_of_finite hne).inter
    (Set.definable_iInter_of_finite hrel)).exists_of_finite
  convert hfull using 1
  ext x
  simp only [HasMore,Set.mem_ofPred_eq,Set.mem_iInter,Set.mem_inter_iff,
    Sum.elim_inl,Sum.elim_inr,Sum.elim_comp_inl]
  constructor
  · rintro ⟨u,hu,hRu⟩
    exact ⟨u,fun p => or_iff_not_imp_left.mpr (fun hp => hu.ne hp),hRu⟩
  · rintro ⟨u,hu,hRu⟩
    refine ⟨u,?_,hRu⟩
    intro i j hij
    exact (hu (i,j)).resolve_right (by simpa using hij)

end SpecialTransformations.ModelTheory

/- Component: GammaFiniteRows -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def scalarRows {S : Set M} {k n : ℕ} {sn : Fin (n+1) → SortTag}
    (Q : Relation S k (n+1) sn) : Set (((Fin k ⊕ Fin n) → M) × M) :=
  {p | (p.1 ∘ Sum.inl,Fin.snoc (p.1 ∘ Sum.inr) p.2) ∈ Q.carrier}

theorem scalarRows_definable {S : Set M} {k n : ℕ} {sn : Fin (n+1) → SortTag}
    (Q : Relation S k (n+1) sn) :
    @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) ((Fin k ⊕ Fin n) ⊕ Fin 1)
      {z | (z ∘ Sum.inl,z (.inr 0)) ∈ scalarRows Q} := by
  have hQ := Q.definable
  let U := Q.carrier
  let N := CanonicalStructure.normalize (M := M)
  letI := N
  let idx : Fin k ⊕ Fin (n+1) → (Fin k ⊕ Fin n) ⊕ Fin 1 :=
    Sum.elim (fun i => .inl (.inl i)) (Fin.lastCases (.inr 0) (fun i => .inl (.inr i)))
  convert hQ.preimage_comp idx using 1
  ext z
  have hz : (z ∘ idx) ∘ Sum.inr = Fin.snoc (z ∘ Sum.inl ∘ Sum.inr) (z (.inr 0)) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp only [idx,Function.comp_apply,Sum.elim_inr,Fin.lastCases_last,
        Fin.lastCases_castSucc,Fin.snoc_last,Fin.snoc_castSucc]
  change (z ∘ Sum.inl ∘ Sum.inl,Fin.snoc (z ∘ Sum.inl ∘ Sum.inr) (z (.inr 0))) ∈ U ↔
    ((z ∘ idx) ∘ Sum.inl,(z ∘ idx) ∘ Sum.inr) ∈ U
  rw [hz]
  rfl

/-- A first-order bound on scalar rows, with globally invariant Gamma
inputs. No representative is named in the real parameter base. -/
def Relation.cutFiniteRows {S : Set M} {k n : ℕ} {sn : Fin (n+1) → SortTag}
    (Q : Relation S k (n+1) sn) (d : ℕ) : Relation S k (n+1) sn where
  carrier := {p | p ∈ Q.carrier ∧ Sum.elim p.1 (Fin.init p.2) ∉ ModelTheory.HasMore (scalarRows Q) d}
  definable := by
    have hQ := Q.definable
    have hR := scalarRows_definable Q
    let R := scalarRows Q
    let N := CanonicalStructure.normalize (M := M)
    letI := N
    have hc := ModelTheory.hasMore_definable S R hR d
    have hp := hc.compl.preimage_comp
      (Sum.map id Fin.castSucc : Fin k ⊕ Fin n → Fin k ⊕ Fin (n+1))
    convert hQ.inter hp using 1
    ext z
    rfl
  proper := fun p hp => Q.proper p hp.1
  invariant := by
    intro t u htu b
    have hr (x : M) : (Sum.elim (rawTuple t) (Fin.init b),x) ∈ scalarRows Q ↔
        (Sum.elim (rawTuple u) (Fin.init b),x) ∈ scalarRows Q :=
      Q.invariant t u htu (Fin.snoc (Fin.init b) x)
    have hm : Sum.elim (rawTuple t) (Fin.init b) ∈ ModelTheory.HasMore (scalarRows Q) d ↔
        Sum.elim (rawTuple u) (Fin.init b) ∈ ModelTheory.HasMore (scalarRows Q) d := by
      change (∃ x : Fin (d+1) → M, Function.Injective x ∧
        ∀ i, (Sum.elim (rawTuple t) (Fin.init b),x i) ∈ scalarRows Q) ↔
        (∃ x : Fin (d+1) → M, Function.Injective x ∧
        ∀ i, (Sum.elim (rawTuple u) (Fin.init b),x i) ∈ scalarRows Q)
      exact exists_congr (fun x => and_congr Iff.rfl (forall_congr' (fun i => hr (x i))))
    exact and_congr (Q.invariant t u htu b) (not_congr hm)

theorem cutFiniteRows_finite {S : Set M} {k n : ℕ} {sn : Fin (n+1) → SortTag}
    (Q : Relation S k (n+1) sn) (d : ℕ) (c : Fin k → M) (a : Fin n → M) :
    {x | (c,Fin.snoc a x) ∈ (Q.cutFiniteRows d).carrier}.Finite := by
  by_cases hm : Sum.elim c a ∈ ModelTheory.HasMore (scalarRows Q) d
  · have he : {x | (c,Fin.snoc a x) ∈ (Q.cutFiniteRows d).carrier} = ∅ := by
      ext x
      simp only [Relation.cutFiniteRows,Set.mem_ofPred_eq,Fin.init_snoc,hm,not_true_eq_false,
        and_false,Set.mem_empty_iff_false]
    rw [he]
    exact Set.finite_empty
  · have hf := (no_injection_iff_finite_ncard_le (A := {x | (Sum.elim c a,x) ∈ scalarRows Q})
      (d := d)).mp hm
    exact hf.1.subset (fun x hx => hx.1)

theorem cutFiniteRows_row_eq {S : Set M} {k n : ℕ} {sn : Fin (n+1) → SortTag}
    (Q : Relation S k (n+1) sn) (d : ℕ) (c : Fin k → M) (a : Fin n → M)
    (hf : {x | (c,Fin.snoc a x) ∈ Q.carrier}.Finite)
    (hd : {x | (c,Fin.snoc a x) ∈ Q.carrier}.ncard ≤ d) :
    {x | (c,Fin.snoc a x) ∈ (Q.cutFiniteRows d).carrier} =
      {x | (c,Fin.snoc a x) ∈ Q.carrier} := by
  have hm : Sum.elim c a ∉ ModelTheory.HasMore (scalarRows Q) d :=
    (no_injection_iff_finite_ncard_le (A := {x | (Sum.elim c a,x) ∈ scalarRows Q})
      (d := d)).mpr ⟨hf,hd⟩
  ext x
  change ((c,Fin.snoc a x) ∈ Q.carrier ∧
    Sum.elim c (Fin.init (Fin.snoc a x : Fin (n+1) → M)) ∉ ModelTheory.HasMore (scalarRows Q) d) ↔ _
  simp only [Fin.init_snoc,hm,not_false_eq_true,and_true,Set.mem_ofPred_eq]

end SpecialTransformations.Section3.GammaParameters

/- Component: GammaGoodBaseRelations -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

structure GoodBaseRelation (B : Base (M := M)) (n : ℕ) (sn : Fin n → SortTag) (σ : SortTag) where
  carrier : Set ((Fin n → M) × M)
  definable : DefinableOverBase B (Fin.lastCases σ sn)
    {z | (Fin.init z,z (Fin.last n)) ∈ carrier}
  finite : ∀ a, {x | (a,x) ∈ carrier}.Finite

/-- Finite witnesses over an arbitrary Gamma base can be promoted and
cut to globally finite rows over that same base. Gamma support is repaired
after parameter promotion, so temporary names never enter the graph. -/
theorem good_base_relation_of_algebraic (B : Base (M := M)) {n : ℕ}
    (sn : Fin n → SortTag) (a : Fin n → M) (ha : ∀ i, sortEval (sn i) (a i))
    (σ : SortTag) (b : M) (hb : AlgebraicAtBase ⟨B.real ∪ Set.range a,B.gamma⟩ σ b) :
    ∃ R : GoodBaseRelation B n sn σ, (a,b) ∈ R.carrier := by
  obtain ⟨W,⟨k,γ,hγ,Q,hQW⟩,hWf,hbW⟩ := hb
  obtain ⟨H,hHd,hHi,hHa⟩ := promote_gamma_relation B.real a Q
  let sm : Fin (n+1) → SortTag := Fin.lastCases σ sn
  have hSort (i : Fin (n+1)) :=
    ((definableAt_iff_normalized_raw B.real (sm i) {x | sortEval (sm i) x}).mp
      (definableAt_sort B.real (sm i))).1
  have hProper := proper_normalized_definable (M := M) B.real (n := k)
  let R : Relation B.real k (n+1) sm :=
    { carrier := {p | Proper p.1 ∧ (∀ i, sortEval (sm i) (p.2 i)) ∧
        (Fin.init p.2,p.1,fun _ : Fin 1 => p.2 (Fin.last n)) ∈ H}
      definable := by
        let N := CanonicalStructure.normalize (M := M)
        letI := N
        let idx : Fin n ⊕ (Fin k ⊕ Fin 1) → Fin k ⊕ Fin (n+1) :=
          Sum.elim (fun i => .inr i.castSucc)
            (Sum.elim Sum.inl (fun _ => .inr (Fin.last n)))
        have hh := hHd.preimage_comp idx
        have hp := hProper.preimage_comp (Sum.inl : Fin k → Fin k ⊕ Fin (n+1))
        have hs := Set.definable_iInter_of_finite (fun i =>
          (hSort i).preimage_comp (fun _ : Fin 1 => (Sum.inr i : Fin k ⊕ Fin (n+1))))
        convert hp.inter (hs.inter hh) using 1
        ext z
        simp only [Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_iInter,Set.mem_preimage,
          Function.comp_apply]
        rfl
      proper := fun p hp => ⟨hp.1,hp.2.1⟩
      invariant := by
        intro t u htu z
        change (Proper (rawTuple t) ∧ (∀ i, sortEval (sm i) (z i)) ∧
          (Fin.init z,rawTuple t,fun _ : Fin 1 => z (Fin.last n)) ∈ H) ↔
          (Proper (rawTuple u) ∧ (∀ i, sortEval (sm i) (z i)) ∧
          (Fin.init z,rawTuple u,fun _ : Fin 1 => z (Fin.last n)) ∈ H)
        simp only [rawTuple_proper,true_and]
        exact and_congr Iff.rfl (hHi _ _ t u htu) }
  let c := rawTuple (representatives γ)
  have hrow : {x | (c,Fin.snoc a x) ∈ R.carrier} = W := by
    ext x
    have hQx : (c,fun _ : Fin 1 => x) ∈ Q.carrier ↔ x ∈ W :=
      Set.ext_iff.mp hQW (fun _ => x)
    have hh := hHa c (fun _ : Fin 1 => x) (rawTuple_proper (representatives γ))
    constructor
    · intro hx
      exact hQx.mp (hh.mp (by simpa only [Fin.init_snoc,Fin.snoc_last] using hx.2.2))
    · intro hx
      have hqx := hQx.mpr hx
      refine ⟨rawTuple_proper (representatives γ),?_,?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [sm,Fin.lastCases_last,Fin.snoc_last] using (Q.proper _ hqx).2 0
        · simpa only [sm,Fin.lastCases_castSucc,Fin.snoc_castSucc] using ha j
      · simpa only [Fin.init_snoc,Fin.snoc_last] using hh.mpr hqx
  let d := W.ncard
  let U := R.cutFiniteRows d
  have hcut := cutFiniteRows_row_eq R d c a (hrow.symm ▸ hWf)
    (by simpa only [hrow,d] using (le_refl W.ncard))
  let P : Set ((Fin n → M) × M) := {p | (c,Fin.snoc p.1 p.2) ∈ U.carrier}
  have hgraph : DefinableOverBase B sm {z | (Fin.init z,z (Fin.last n)) ∈ P} := by
    refine ⟨k,γ,hγ,U,?_⟩
    ext z
    change (c,z) ∈ U.carrier ↔ (c,Fin.snoc (Fin.init z) (z (Fin.last n))) ∈ U.carrier
    rw [Fin.snoc_init_self]
  refine ⟨⟨P,hgraph,fun v => cutFiniteRows_finite R d c v⟩,?_⟩
  change b ∈ {x | (c,Fin.snoc a x) ∈ U.carrier}
  rw [hcut,hrow]
  exact hbW

end SpecialTransformations.Section3.GammaParameters

/- Component: GammaBaseIntersection -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def baseFamilyIntersection {n : ℕ} (A : Set (Fin n → M)) (σ : SortTag)
    (R : Set ((Fin n → M) × M)) : Set M :=
  {x | sortEval σ x ∧ ∀ a ∈ A, (a,x) ∈ R}

/-- Universal real-tuple intersection over a genuine arbitrary Gamma base.
Boolean operations and projection preserve full code invariance. -/
theorem baseFamilyIntersection_definable (B : Base (M := M)) {n : ℕ}
    (sn : Fin n → SortTag) (A : Set (Fin n → M)) (hA : DefinableOverBase B sn A)
    (σ : SortTag) (R : Set ((Fin n → M) × M))
    (hR : DefinableOverBase B (Fin.lastCases σ sn) {z | (Fin.init z,z (Fin.last n)) ∈ R}) :
    DefinableAtBase B σ (baseFamilyIntersection A σ R) := by
  let sm : Fin (n+1) → SortTag := Fin.lastCases σ sn
  let G : Set (Fin (n+1) → M) := {z | (Fin.init z,z (Fin.last n)) ∈ R}
  let C : Set (Fin (n+1) → M) := {z | Fin.init z ∈ A ∧ z ∈ sortedUniverse sm}
  let Bad := C ∩ (sortedUniverse sm \ G)
  have hC : DefinableOverBase B sm C := hA.preimage_real sm Fin.castSucc
  have hBad : DefinableOverBase B sm Bad := hC.inter hR.compl
  let π : Fin 1 → Fin (n+1) := fun _ => Fin.last n
  have hp := hBad.image_real π
  have hsm : sm ∘ π = (fun _ : Fin 1 => σ) := by
    funext i
    simp only [sm,π,Function.comp_apply,Fin.lastCases_last]
  rw [hsm] at hp
  have hh := hp.compl
  have he : sortedUniverse (fun _ : Fin 1 => σ) \ ((fun w => w ∘ π) '' Bad) =
      {z : Fin 1 → M | z 0 ∈ baseFamilyIntersection A σ R} := by
    ext z
    change ((∀ i : Fin 1, sortEval σ (z i)) ∧
      ¬ ∃ w, w ∈ Bad ∧ w ∘ π = z) ↔
        (sortEval σ (z 0) ∧ ∀ a ∈ A, (a,z 0) ∈ R)
    constructor
    · rintro ⟨hz,hn⟩
      refine ⟨hz 0,?_⟩
      intro a ha
      by_contra hr
      have hs : Fin.snoc a (z 0) ∈ sortedUniverse sm := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [sm,Fin.lastCases_last,Fin.snoc_last] using hz 0
        · simpa only [sm,Fin.lastCases_castSucc,Fin.snoc_castSucc] using hA.proper a ha j
      have hw : Fin.snoc a (z 0) ∈ Bad := by
        refine ⟨⟨?_,hs⟩,hs,?_⟩
        · simpa only [Fin.init_snoc] using ha
        · change (Fin.init (Fin.snoc a (z 0) : Fin (n+1) → M),
            (Fin.snoc a (z 0) : Fin (n+1) → M) (Fin.last n)) ∉ R
          simpa only [Fin.init_snoc,Fin.snoc_last] using hr
      apply hn ⟨Fin.snoc a (z 0),hw,?_⟩
      funext i
      fin_cases i
      change (Fin.snoc a (z 0) : Fin (n+1) → M) (Fin.last n) = z 0
      simp only [Fin.snoc_last]
    · rintro ⟨hz,hall⟩
      refine ⟨?_,?_⟩
      · intro i
        fin_cases i
        exact hz
      · rintro ⟨w,hw,he⟩
        have hlast : w (Fin.last n) = z 0 := congrFun he 0
        have hr := hall (Fin.init w) hw.1.1
        apply hw.2.2
        change (Fin.init w,w (Fin.last n)) ∈ R
        rw [hlast]
        exact hr
  change DefinableOverBase B (fun _ : Fin 1 => σ) _
  rw [← he]
  exact hh

theorem baseFamilyIntersection_finite {n : ℕ} (A : Set (Fin n → M)) (hne : A.Nonempty)
    (σ : SortTag) (R : Set ((Fin n → M) × M))
    (hf : ∀ a, {x | (a,x) ∈ R}.Finite) : (baseFamilyIntersection A σ R).Finite := by
  obtain ⟨a,ha⟩ := hne
  exact (hf a).subset (fun x hx => hx.2 a ha)

end SpecialTransformations.Section3.GammaParameters

/- Component: GammaBaseDescent -/
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem GoodBaseRelation.slice_common_names (B : Base (M := M)) {n : ℕ}
    (sn : Fin n → SortTag) (σ : SortTag) (R : GoodBaseRelation B n sn σ) (b : M) :
    @Set.Definable M (insert b (commonRealNames B)) LRV
      (CanonicalStructure.normalize (M := M)) (Fin n) {a | (a,b) ∈ R.carrier} := by
  let C := commonRealNames B
  let U := R.carrier
  have hD := (definableOver_iff_normalized_raw C (Fin.lastCases σ sn) _).mp
    R.definable.common_names
  let N := CanonicalStructure.normalize (M := M)
  letI := N
  have hG := hD.1.mono (Set.subset_insert b C)
  let F (z : Fin n → M) : Fin (n+1) → M := Fin.snoc z b
  have hF : (insert b C).DefinableMap LRV F := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [F,Fin.snoc_last] using
        (LRV.definableFun_const (Fin n) (Set.mem_insert b C))
    · simpa only [F,Fin.snoc_castSucc,Function.comp_apply] using
        (Set.DefinableFun.proj (L := LRV) (A := insert b C) (i := j))
  convert hG.preimage_map hF using 1
  ext z
  simp only [Set.mem_preimage,Set.mem_ofPred_eq,F,Fin.init_snoc,Fin.snoc_last]

/-- Compactness over proof-only common names gives a finite union of
relations over the original imaginary base. Every resulting real row is
finite; no representative appears in the conclusion's real base. -/
theorem uniform_good_base_relation_cover {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    {n : ℕ} (sn : Fin n → SortTag) (A : Set (Fin n → M))
    (hA : DefinableOverBase B sn A) (σ : SortTag) (b : M)
    (hb : ∀ a ∈ A, AlgebraicAtBase ⟨B.real ∪ Set.range a,B.gamma⟩ σ b) :
    ∃ R : GoodBaseRelation B n sn σ, ∀ a ∈ A, (a,b) ∈ R.carrier := by
  let Names := commonRealNames B
  let slice (R : GoodBaseRelation B n sn σ) : Set (Fin n → M) := {a | (a,b) ∈ R.carrier}
  let C := Set.range slice
  have hcover : ∀ a ∈ A, ∃ c ∈ C, a ∈ c := by
    intro a ha
    obtain ⟨R,hR⟩ := good_base_relation_of_algebraic B sn a (hA.proper a ha) σ b (hb a ha)
    exact ⟨slice R,Set.mem_range_self _,hR⟩
  have hAN := (definableOver_iff_normalized_raw Names sn A).mp hA.common_names
  have hsmall := small_insert hκ Names (commonRealNames_small hκ B hr hγ) b
  have hsN := hs.normalize
  let N := CanonicalStructure.normalize (M := M)
  have hDom : @Set.Definable M (insert b Names) LRV N (Fin n) A := by
    letI := N
    exact hAN.1.mono (Set.subset_insert b Names)
  letI := sM
  obtain ⟨C₀,hC₀,hsub,hcov⟩ := @Saturated.definable_finite_subcover_tuple M N κ hsN
    (insert b Names) hsmall n A
    hDom C
    (by rintro _ ⟨R,rfl⟩; exact GoodBaseRelation.slice_common_names B sn σ R b) hcover
  letI := hC₀.fintype
  have hchoice (c : C₀) : ∃ R : GoodBaseRelation B n sn σ, slice R = c.val := hsub c.property
  choose rel hrel using hchoice
  let U : Set ((Fin n → M) × M) := {p | ∃ c : C₀, p ∈ (rel c).carrier}
  have hUd : DefinableOverBase B (Fin.lastCases σ sn)
      {z | (Fin.init z,z (Fin.last n)) ∈ U} := by
    convert DefinableOverBase.finite_iUnion (Finset.univ : Finset C₀)
      (fun c => {z | (Fin.init z,z (Fin.last n)) ∈ (rel c).carrier})
      (fun c _ => (rel c).definable) using 1
    ext z
    simp only [U,Set.mem_ofPred_eq,Set.mem_iUnion,Finset.mem_univ,exists_prop,true_and]
  have hUf (a : Fin n → M) : {x | (a,x) ∈ U}.Finite := by
    have hh := Set.finite_iUnion (fun c : C₀ => (rel c).finite a)
    simpa only [U,Set.mem_ofPred_eq,Set.iUnion_ofPred] using hh
  refine ⟨⟨U,hUd,hUf⟩,?_⟩
  intro a ha
  obtain ⟨c,hc,hac⟩ := hcov a ha
  refine ⟨⟨c,hc⟩,?_⟩
  change a ∈ slice (rel ⟨c,hc⟩)
  rw [hrel]
  exact hac

/-- Lemma3.1 for real outputs over a genuinely arbitrary small base in
VF, RV and Gamma. The defining graph retains its original imaginary base. -/
theorem lemma_3_1_full_gamma_base {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    {n : ℕ} (sn : Fin n → SortTag) (A : Set (Fin n → M))
    (hA : DefinableOverBase B sn A) (hne : A.Nonempty) (σ : SortTag) (b : M)
    (hb : ∀ a ∈ A, AlgebraicAtBase ⟨B.real ∪ Set.range a,B.gamma⟩ σ b) :
    AlgebraicAtBase B σ b := by
  obtain ⟨R,hcov⟩ := uniform_good_base_relation_cover hκ hs B hr hγ sn A hA σ b hb
  obtain ⟨a₀,ha₀⟩ := hne
  obtain ⟨W,hW,hWf,hbW⟩ := hb a₀ ha₀
  refine ⟨baseFamilyIntersection A σ R.carrier,
    baseFamilyIntersection_definable B sn A hA σ R.carrier R.definable,
    baseFamilyIntersection_finite A ⟨a₀,ha₀⟩ σ R.carrier R.finite,?_,?_⟩
  · exact hW.proper b hbW
  · exact hcov

end SpecialTransformations.Section3.GammaParameters
