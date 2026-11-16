module

public import Section3.FibreDescent
public import Section3.GammaBaseDescent
public import Section3.GammaFiniteOrder
public import Section3.GeneralCosetChoice

@[expose] public section

/- Full ambient-Gamma descent. Parameter promotion adapts the checked
GammaBaseDescent construction; finite-cover and intersection arguments retain
full code invariance. Ordered Gamma acl=dcl makes a partial least-output
selection sufficient; no general minimum-existence theorem is assumed. -/

/- Component: GammaScalarPromotion -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Promote a finite real tuple out of a scalar definable set while
retaining the original Gamma support and full representative invariance.
This relation has no assumed global row finiteness. -/
theorem promote_scalar_definable_base (B : Base (M := M)) {n : ℕ}
    (sn : Fin n → SortTag) (a : Fin n → M) (ha : ∀ i, sortEval (sn i) (a i))
    (σ : SortTag) (W : Set M)
    (hW : DefinableAtBase ⟨B.real ∪ Set.range a,B.gamma⟩ σ W) :
    ∃ P : Set ((Fin n → M) × M),
      DefinableOverBase B (Fin.lastCases σ sn) {z | (Fin.init z,z (Fin.last n)) ∈ P} ∧
      {x | (a,x) ∈ P} = W := by
  obtain ⟨k,γ,hγ,Q,hQW⟩ := hW
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
  let P : Set ((Fin n → M) × M) := {p | (c,Fin.snoc p.1 p.2) ∈ R.carrier}
  have hgraph : DefinableOverBase B sm {z | (Fin.init z,z (Fin.last n)) ∈ P} := by
    refine ⟨k,γ,hγ,R,?_⟩
    ext z
    change (c,z) ∈ R.carrier ↔ (c,Fin.snoc (Fin.init z) (z (Fin.last n))) ∈ R.carrier
    rw [Fin.snoc_init_self]
  exact ⟨P,hgraph,hrow⟩

end SpecialTransformations.Section3.GammaParameters

/- Component: GammaOutputHull -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

theorem nonzero_rv_sorted_definable (S : Set M) :
    SpecialTransformations.Section3.DefinableAt S .rv {x | NonzeroRV x} := by
  apply (definableAt_iff_normalized_raw S .rv _).mpr
  exact ⟨nonzero_codes_normalized_definable S,fun x hx => hx.1⟩

theorem same_scalar_sorted_definable (S : Set M) :
    SpecialTransformations.Section3.DefinableOver S (fun _ : Fin 2 => .rv)
      {z | SameScalar (z 0) (z 1)} := by
  apply (definableOver_iff_normalized_raw S (fun _ => .rv) _).mpr
  constructor
  · have h := @same_scalar_definable M (CanonicalStructure.normalize (M := M)) S
    simpa only [same_scalar_normalize] using h
  · intro z hz i
    fin_cases i
    · exact hz.1.1
    · exact hz.2.1.1

def baseOutputHull (sn : Fin n → SortTag) (R : Set ((Fin n → M) × M)) :
    Set ((Fin n → M) × M) :=
  {p | (∀ i, sortEval (sn i) (p.1 i)) ∧ p ∈ invariantHull R}

/-- Universal closure in the output value class preserves definability
over the original imaginary base and restores full output invariance. -/
theorem baseOutputHull_definable (B : Base (M := M)) (sn : Fin n → SortTag)
    (R : Set ((Fin n → M) × M))
    (hR : DefinableOverBase B (Fin.lastCases .rv sn) {z | (Fin.init z,z (Fin.last n)) ∈ R}) :
    DefinableOverBase B (Fin.lastCases .rv sn)
      {z | (Fin.init z,z (Fin.last n)) ∈ baseOutputHull sn R} := by
  let sm : Fin (n+1) → SortTag := Fin.lastCases .rv sn
  let st : Fin (n+2) → SortTag := Fin.lastCases .rv sm
  let ix : Fin (n+1) → Fin (n+2) :=
    Fin.snoc (fun i : Fin n => i.castSucc.castSucc) (Fin.last (n+1))
  let ip : Fin 2 → Fin (n+2) := ![Fin.last (n+1),(Fin.last n).castSucc]
  have hL := hR.preimage_real st ix
  have hE := (real_definableOverBase B _ _ (same_scalar_sorted_definable B.real)).preimage_real st ip
  let F : Set (Fin (n+2) → M) := (sortedUniverse st \
    {w | SameScalar ((w ∘ ip) 0) ((w ∘ ip) 1) ∧ w ∈ sortedUniverse st}) ∪
    {w | ((Fin.init (w ∘ ix)),(w ∘ ix) (Fin.last n)) ∈ R ∧ w ∈ sortedUniverse st}
  have hF : DefinableOverBase B st F := hE.compl.union hL
  have hall := hF.forall_last
  have hst : st ∘ Fin.castSucc = sm := by
    funext i
    simp only [st,Function.comp_apply,Fin.lastCases_castSucc]
  rw [hst] at hall
  have hNZ := (real_definableAtBase B .rv _ (nonzero_rv_sorted_definable B.real)).preimage_real
    sm (fun _ : Fin 1 => Fin.last n)
  have hfull := hall.inter hNZ
  have hPoint (z : Fin (n+1) → M) (hz : z ∈ sortedUniverse sm) (u : M) (hu : iRV u) :
      Fin.snoc z u ∈ F ↔ (SameScalar u (z (Fin.last n)) → (Fin.init z,u) ∈ R) := by
    let w : Fin (n+2) → M := Fin.snoc z u
    have hw : w ∈ sortedUniverse st := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [st,Fin.lastCases_last,w,Fin.snoc_last,sortEval,iRV] using hu
      · simpa only [st,Fin.lastCases_castSucc,w,Fin.snoc_castSucc] using hz j
    have hix : w ∘ ix = Fin.snoc (Fin.init z) u := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Function.comp_apply,ix,w,Fin.snoc_last]
      · simp only [Function.comp_apply,ix,w,Fin.snoc_castSucc,Fin.init]
    change ((w ∈ sortedUniverse st ∧ ¬ (SameScalar ((w ∘ ip) 0) ((w ∘ ip) 1) ∧
      w ∈ sortedUniverse st)) ∨
      (((Fin.init (w ∘ ix)),(w ∘ ix) (Fin.last n)) ∈ R ∧ w ∈ sortedUniverse st)) ↔ _
    have he0 : (w ∘ ip) 0 = u := by change w (Fin.last (n+1)) = u; simp only [w,Fin.snoc_last]
    have he1 : (w ∘ ip) 1 = z (Fin.last n) := by
      change w (Fin.last n).castSucc = z (Fin.last n)
      simp only [w,Fin.snoc_castSucc]
    rw [he0,he1,hix]
    simp only [hw,true_and,and_true,Fin.init_snoc,Fin.snoc_last]
    tauto
  convert hfull using 1
  all_goals try rfl
  ext z
  change ((∀ i, sortEval (sn i) (Fin.init z i)) ∧ NonzeroRV (z (Fin.last n)) ∧
    ∀ u, SameScalar u (z (Fin.last n)) → (Fin.init z,u) ∈ R) ↔
    (z ∈ sortedUniverse sm ∧ ∀ u, sortEval (st (Fin.last (n+1))) u → Fin.snoc z u ∈ F) ∧
    ((z ∘ fun _ : Fin 1 => Fin.last n) 0 ∈ {x | NonzeroRV x} ∧ z ∈ sortedUniverse sm)
  constructor
  · rintro ⟨hs,ht,hall⟩
    have hz : z ∈ sortedUniverse sm := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [sm,Fin.lastCases_last,sortEval,iRV] using ht.1
      · simpa only [sm,Fin.lastCases_castSucc,Fin.init] using hs j
    refine ⟨⟨hz,?_⟩,ht,hz⟩
    intro u hu
    apply (hPoint z hz u (by simpa only [st,Fin.lastCases_last,sortEval,iRV] using hu)).mpr
    exact hall u
  · rintro ⟨⟨hz,hall⟩,ht,_⟩
    refine ⟨?_,ht,?_⟩
    · intro i
      simpa only [sm,Fin.lastCases_castSucc,Fin.init] using hz i.castSucc
    · intro u hu
      have huS : sortEval (st (Fin.last (n+1))) u := by
        simpa only [st,Fin.lastCases_last,sortEval,iRV] using hu.1.1
      exact (hPoint z hz u hu.1.1).mp (hall u huS) hu

theorem SameScalar.codeValue_eq {x y : M} (h : SameScalar x y) : codeValue x = codeValue y :=
  le_antisymm ((original_le_codeValue_iff x y h.1 h.2.1).mp h.2.2.1)
    ((original_le_codeValue_iff y x h.2.1 h.1).mp h.2.2.2)

theorem invariantHull_gamma_row_eq (R : Set ((Fin n → M) × M)) (a : Fin n → M)
    (W : Set (Values.Gamma (M := M)))
    (hrow : {x | (a,x) ∈ R} = Values.gammaPullback W) :
    {x | (a,x) ∈ invariantHull R} = Values.gammaPullback W := by
  ext t
  constructor
  · rintro ⟨ht,hall⟩
    have he : SameScalar t t := ⟨ht,ht,RVCalc.le_refl_rv hM ht.1,RVCalc.le_refl_rv hM ht.1⟩
    have hx : t ∈ {x | (a,x) ∈ R} := hall t he
    rwa [hrow] at hx
  · intro ht
    have htNZ : NonzeroRV t := ⟨ht.1,ht.2.1⟩
    refine ⟨htNZ,?_⟩
    intro u hu
    have htW := (gammaPullback_mem_codeValue_iff W t htNZ).mp ht
    have huW : u ∈ Values.gammaPullback W :=
      (gammaPullback_mem_codeValue_iff W u hu.1).mpr (hu.codeValue_eq.symm ▸ htW)
    change u ∈ {x | (a,x) ∈ R}
    rwa [hrow]

theorem baseOutputHull_row_eq (sn : Fin n → SortTag) (R : Set ((Fin n → M) × M))
    (a : Fin n → M) (ha : ∀ i, sortEval (sn i) (a i))
    (W : Set (Values.Gamma (M := M)))
    (hrow : {x | (a,x) ∈ R} = Values.gammaPullback W) :
    {x | (a,x) ∈ baseOutputHull sn R} = Values.gammaPullback W := by
  have hh := invariantHull_gamma_row_eq R a W hrow
  ext t
  change ((∀ i, sortEval (sn i) (a i)) ∧ (a,t) ∈ invariantHull R) ↔ _
  rw [and_iff_right ha]
  exact Set.ext_iff.mp hh t

theorem baseOutputHull_invariant (sn : Fin n → SortTag) (R : Set ((Fin n → M) × M))
    (a : Fin n → M) (t u : Code (M := M)) (he : value t = value u) :
    (a,raw t) ∈ baseOutputHull sn R ↔ (a,raw u) ∈ baseOutputHull sn R :=
  and_congr Iff.rfl (invariantHull_invariant R a t u he)

end SpecialTransformations.Section3.GammaParameters

/- Component: GammaLeastOutput -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

def baseLeastOutput (R : Set ((Fin n → M) × M)) : Set ((Fin n → M) × M) :=
  {p | p ∈ R ∧ ∀ u, (p.1,u) ∈ R → iLe p.2 u}

/-- Keeping a least output is a definable partial operation. No minimum
is asserted for arbitrary rows; rows without a least value simply vanish. -/
theorem baseLeastOutput_definable (B : Base (M := M)) (sn : Fin n → SortTag)
    (R : Set ((Fin n → M) × M))
    (hR : DefinableOverBase B (Fin.lastCases .rv sn) {z | (Fin.init z,z (Fin.last n)) ∈ R}) :
    DefinableOverBase B (Fin.lastCases .rv sn)
      {z | (Fin.init z,z (Fin.last n)) ∈ baseLeastOutput R} := by
  let sm : Fin (n+1) → SortTag := Fin.lastCases .rv sn
  let st : Fin (n+2) → SortTag := Fin.lastCases .rv sm
  let ix : Fin (n+1) → Fin (n+2) :=
    Fin.snoc (fun i : Fin n => i.castSucc.castSucc) (Fin.last (n+1))
  let ip : Fin 2 → Fin (n+2) := ![(Fin.last n).castSucc,Fin.last (n+1)]
  have hQ := hR.preimage_real st ix
  have hN := (real_definableOverBase B _ _ (not_le_pair_definable B.real)).preimage_real st ip
  have hBad := (hQ.inter hN).image_real Fin.castSucc
  have hst : st ∘ Fin.castSucc = sm := by
    funext i
    simp only [st,Function.comp_apply,Fin.lastCases_castSucc]
  rw [hst] at hBad
  have hfull := hR.inter hBad.compl
  convert hfull using 1
  all_goals try rfl
  ext z
  have hBadPoint (hz : (Fin.init z,z (Fin.last n)) ∈ R) :
      z ∈ (fun w : Fin (n+2) → M => w ∘ Fin.castSucc) ''
        ({w | (Fin.init (w ∘ ix),(w ∘ ix) (Fin.last n)) ∈ R ∧ w ∈ sortedUniverse st} ∩
         {w | ((∀ i, iRV ((w ∘ ip) i)) ∧ ¬ iLe ((w ∘ ip) 0) ((w ∘ ip) 1)) ∧ w ∈ sortedUniverse st}) ↔
      ∃ u, (Fin.init z,u) ∈ R ∧ ¬ iLe (z (Fin.last n)) u := by
    constructor
    · rintro ⟨w,⟨⟨hq,_⟩,⟨⟨_,hn⟩,_⟩⟩,he⟩
      have hwi : Fin.init w = z := he
      have hix : w ∘ ix = Fin.snoc (Fin.init z) (w (Fin.last (n+1))) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [Function.comp_apply,ix,Fin.snoc_last]
        · simp only [Function.comp_apply,ix,Fin.snoc_castSucc,Fin.init]
          exact congrFun he j.castSucc
      have hx : w (Fin.last n).castSucc = z (Fin.last n) := congrFun he (Fin.last n)
      refine ⟨w (Fin.last (n+1)),?_,?_⟩
      · simpa only [hix,Fin.init_snoc,Fin.snoc_last] using hq
      · change ¬ iLe (w (Fin.last n).castSucc) (w (Fin.last (n+1))) at hn
        rwa [hx] at hn
    · rintro ⟨u,hu,hn⟩
      let w : Fin (n+2) → M := Fin.snoc z u
      have hix : w ∘ ix = Fin.snoc (Fin.init z) u := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [Function.comp_apply,ix,w,Fin.snoc_last]
        · simp only [Function.comp_apply,ix,w,Fin.snoc_castSucc,Fin.init]
      have huRV : iRV u := by
        let y : Fin (n+1) → M := Fin.snoc (Fin.init z) u
        have hy : (Fin.init y,y (Fin.last n)) ∈ R := by
          simpa only [y,Fin.init_snoc,Fin.snoc_last] using hu
        simpa only [y,sm,Fin.snoc_last,Fin.lastCases_last,sortEval,iRV] using hR.proper y hy (Fin.last n)
      have hw : w ∈ sortedUniverse st := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [st,Fin.lastCases_last,w,Fin.snoc_last,sortEval,iRV] using huRV
        · simpa only [st,Fin.lastCases_castSucc,w,Fin.snoc_castSucc] using hR.proper z hz j
      refine ⟨w,⟨⟨?_,hw⟩,⟨⟨?_,?_⟩,hw⟩⟩,?_⟩
      · simpa only [hix,Fin.init_snoc,Fin.snoc_last] using hu
      · intro i
        fin_cases i
        · change iRV (w (Fin.last n).castSucc)
          simpa only [w,Fin.snoc_castSucc,sm,Fin.lastCases_last,sortEval,iRV] using hR.proper z hz (Fin.last n)
        · change iRV (w (Fin.last (n+1)))
          simpa only [w,Fin.snoc_last] using huRV
      · change ¬ iLe (w (Fin.last n).castSucc) (w (Fin.last (n+1)))
        simpa only [w,Fin.snoc_castSucc,Fin.snoc_last] using hn
      · funext i
        simp only [w,Function.comp_apply,Fin.snoc_castSucc]
  change ((Fin.init z,z (Fin.last n)) ∈ R ∧ ∀ u, (Fin.init z,u) ∈ R → iLe (z (Fin.last n)) u) ↔ _
  constructor
  · rintro ⟨hz,hle⟩
    refine ⟨hz,hR.proper z hz,?_⟩
    intro hb
    obtain ⟨u,hu,hn⟩ := (hBadPoint hz).mp hb
    exact hn (hle u hu)
  · rintro ⟨hz,_,hn⟩
    refine ⟨hz,?_⟩
    intro u hu
    by_contra hnot
    exact hn ((hBadPoint hz).mpr ⟨u,hu,hnot⟩)

/-- Least-output rows contain at most one actual Gamma value, whether or
not any arbitrary original row has a minimum. -/
theorem baseLeastOutput_gamma_finite (R : Set ((Fin n → M) × M)) (a : Fin n → M) :
    (gammaRow (baseLeastOutput R) a).Finite := by
  apply Set.Subsingleton.finite
  intro γ hγ δ hδ
  have hγδ : iLe (raw (representative γ)) (raw (representative δ)) := hγ.2 _ hδ.1
  have hδγ : iLe (raw (representative δ)) (raw (representative γ)) := hδ.2 _ hγ.1
  exact (representative_value γ).symm.trans
    (((value_eq_iff _ _).mpr ⟨hγδ,hδγ⟩).trans (representative_value δ))

theorem baseLeastOutput_invariant (R : Set ((Fin n → M) × M))
    (hNZ : ∀ a t, (a,t) ∈ R → NonzeroRV t)
    (hInv : ∀ a (t u : Code (M := M)), value t = value u → ((a,raw t) ∈ R ↔ (a,raw u) ∈ R))
    (a : Fin n → M) (t u : Code (M := M)) (he : value t = value u) :
    (a,raw t) ∈ baseLeastOutput R ↔ (a,raw u) ∈ baseLeastOutput R := by
  have hh (t u : Code (M := M)) (he : value t = value u)
      (ht : (a,raw t) ∈ baseLeastOutput R) : (a,raw u) ∈ baseLeastOutput R := by
    refine ⟨(hInv a t u he).mp ht.1,?_⟩
    intro y hy
    have htNZ : NonzeroRV (raw t) := ⟨raw_rv t,raw_ne_zero t⟩
    have huNZ : NonzeroRV (raw u) := ⟨raw_rv u,raw_ne_zero u⟩
    apply (original_le_codeValue_iff _ _ huNZ (hNZ a y hy)).mpr
    have hl := (original_le_codeValue_iff _ _ htNZ (hNZ a y hy)).mp (ht.2 y hy)
    simpa only [codeValue_raw,he] using hl
  exact ⟨hh t u he,hh u t he.symm⟩

theorem baseLeastOutput_singleton_row (R : Set ((Fin n → M) × M)) (a : Fin n → M)
    (δ : Values.Gamma (M := M))
    (hrow : {t | (a,t) ∈ R} = Values.gammaPullback {δ}) :
    {t | (a,t) ∈ baseLeastOutput R} = Values.gammaPullback {δ} := by
  ext t
  constructor
  · rintro ⟨ht,_⟩
    change t ∈ {t | (a,t) ∈ R} at ht
    rwa [hrow] at ht
  · intro ht
    have htNZ : NonzeroRV t := ⟨ht.1,ht.2.1⟩
    have htm : (a,t) ∈ R := by
      change t ∈ {t | (a,t) ∈ R}
      rwa [hrow]
    refine ⟨htm,?_⟩
    intro u hu
    have hum : u ∈ Values.gammaPullback {δ} := by
      change u ∈ {t | (a,t) ∈ R} at hu
      rwa [hrow] at hu
    have huNZ : NonzeroRV u := ⟨hum.1,hum.2.1⟩
    have htδ : codeValue t = δ := (gammaPullback_mem_codeValue_iff {δ} t htNZ).mp ht
    have huδ : codeValue u = δ := (gammaPullback_mem_codeValue_iff {δ} u huNZ).mp hum
    exact (original_le_codeValue_iff t u htNZ huNZ).mpr (by rw [htδ,huδ])

end SpecialTransformations.Section3.GammaParameters

/- Component: GammaBaseGammaRelations -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Finite actual-Gamma rows, represented by their complete invariant
nonzero RV preimages over one original real/Gamma base. -/
structure GoodBaseGammaRelation (B : Base (M := M)) (n : ℕ) (sn : Fin n → SortTag) where
  carrier : Set ((Fin n → M) × M)
  definable : DefinableOverBase B (Fin.lastCases .rv sn) {z | (Fin.init z,z (Fin.last n)) ∈ carrier}
  proper : ∀ a t, (a,t) ∈ carrier → NonzeroRV t
  invariant : ∀ a (t u : Code (M := M)), value t = value u →
    ((a,raw t) ∈ carrier ↔ (a,raw u) ∈ carrier)
  finite : ∀ a, (gammaRow carrier a).Finite

/-- The ordered Gamma sort makes an algebraic witness definable. Real
parameter promotion, universal output closure and a partial least-value
selection give globally finite Gamma rows without naming representatives. -/
theorem good_base_gamma_relation_of_algebraic (B : Base (M := M)) {n : ℕ}
    (sn : Fin n → SortTag) (a : Fin n → M) (ha : ∀ i, sortEval (sn i) (a i))
    (δ : Values.Gamma (M := M))
    (hδ : GammaAlgebraicAtBase ⟨B.real ∪ Set.range a,B.gamma⟩ δ) :
    ∃ R : GoodBaseGammaRelation B n sn, (a,raw (representative δ)) ∈ R.carrier := by
  have hδDef := (gamma_algebraic_iff_definable_base _ δ).mp hδ
  obtain ⟨P,hPd,hPa⟩ := promote_scalar_definable_base B sn a ha .rv (Values.gammaPullback {δ}) hδDef
  let H := baseOutputHull sn P
  have hHd := baseOutputHull_definable B sn P hPd
  have hNZ (b : Fin n → M) (t : M) (ht : (b,t) ∈ H) : NonzeroRV t := ht.2.1
  have hHi := baseOutputHull_invariant sn P
  have hHa := baseOutputHull_row_eq sn P a ha {δ} hPa
  let T := baseLeastOutput H
  have hTd := baseLeastOutput_definable B sn H hHd
  have hTa := baseLeastOutput_singleton_row H a δ hHa
  refine ⟨⟨T,hTd,fun b t ht => hNZ b t ht.1,
    baseLeastOutput_invariant H hNZ hHi,baseLeastOutput_gamma_finite H⟩,?_⟩
  change raw (representative δ) ∈ {t | (a,t) ∈ T}
  rw [hTa]
  exact (mem_gammaPullback_code {δ} (representative δ)).mpr (representative_value δ)

end SpecialTransformations.Section3.GammaParameters

/- Component: GammaBaseGammaCover -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem GoodBaseGammaRelation.slice_common_names (B : Base (M := M)) {n : ℕ}
    (sn : Fin n → SortTag) (R : GoodBaseGammaRelation B n sn) (b : M) :
    @Set.Definable M (insert b (commonRealNames B)) LRV
      (CanonicalStructure.normalize (M := M)) (Fin n) {a | (a,b) ∈ R.carrier} := by
  let C := commonRealNames B
  let U := R.carrier
  have hD := (definableOver_iff_normalized_raw C (Fin.lastCases .rv sn) _).mp
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


theorem uniform_good_base_gamma_relation_cover {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    {n : ℕ} (sn : Fin n → SortTag) (A : Set (Fin n → M))
    (hA : DefinableOverBase B sn A) (δ : Values.Gamma (M := M))
    (hb : ∀ a ∈ A, GammaAlgebraicAtBase ⟨B.real ∪ Set.range a,B.gamma⟩ δ) :
    ∃ R : GoodBaseGammaRelation B n sn, ∀ a ∈ A, (a,raw (representative δ)) ∈ R.carrier := by
  let b := raw (representative δ)
  let Names := commonRealNames B
  let slice (R : GoodBaseGammaRelation B n sn) : Set (Fin n → M) := {a | (a,b) ∈ R.carrier}
  let C := Set.range slice
  have hcover : ∀ a ∈ A, ∃ c ∈ C, a ∈ c := by
    intro a ha
    obtain ⟨R,hR⟩ := good_base_gamma_relation_of_algebraic B sn a (hA.proper a ha) δ (hb a ha)
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
    (by rintro _ ⟨R,rfl⟩; exact GoodBaseGammaRelation.slice_common_names B sn R b) hcover
  letI := hC₀.fintype
  have hchoice (c : C₀) : ∃ R : GoodBaseGammaRelation B n sn, slice R = c.val := hsub c.property
  choose rel hrel using hchoice
  let U : Set ((Fin n → M) × M) := {p | ∃ c : C₀, p ∈ (rel c).carrier}
  have hUd : DefinableOverBase B (Fin.lastCases .rv sn)
      {z | (Fin.init z,z (Fin.last n)) ∈ U} := by
    convert DefinableOverBase.finite_iUnion (Finset.univ : Finset C₀)
      (fun c => {z | (Fin.init z,z (Fin.last n)) ∈ (rel c).carrier})
      (fun c _ => (rel c).definable) using 1
    ext z
    simp only [U,Set.mem_ofPred_eq,Set.mem_iUnion,Finset.mem_univ,exists_prop,true_and]
  have hUf (a : Fin n → M) : (gammaRow U a).Finite := by
    have hh := Set.finite_iUnion (fun c : C₀ => (rel c).finite a)
    simpa only [gammaRow,U,Set.mem_ofPred_eq,Set.iUnion_ofPred] using hh
  refine ⟨⟨U,hUd,?_,?_,hUf⟩,?_⟩
  · rintro a t ⟨c,hc⟩
    exact (rel c).proper a t hc
  · intro a t u he
    change (∃ c : C₀, (a,raw t) ∈ (rel c).carrier) ↔ ∃ c : C₀, (a,raw u) ∈ (rel c).carrier
    exact exists_congr (fun c => (rel c).invariant a t u he)
  · intro a ha
    obtain ⟨c,hc,hac⟩ := hcov a ha
    refine ⟨⟨c,hc⟩,?_⟩
    change a ∈ slice (rel ⟨c,hc⟩)
    rw [hrel]
    exact hac
  

end SpecialTransformations.Section3.GammaParameters

/- Component: GammaBaseGammaDescent -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem GoodBaseGammaRelation.mem_raw_iff (B : Base (M := M)) {n : ℕ}
    (sn : Fin n → SortTag) (R : GoodBaseGammaRelation B n sn)
    (a : Fin n → M) (t : Code (M := M)) :
    (a,raw t) ∈ R.carrier ↔ value t ∈ gammaRow R.carrier a :=
  R.invariant a t (representative (value t)) (representative_value (value t)).symm

/-- The universal intersection over a nonempty real family is a finite
set of actual Gamma values. Its full code preimage stays over exactly B. -/
theorem gamma_base_family_intersection (B : Base (M := M)) {n : ℕ}
    (sn : Fin n → SortTag) (A : Set (Fin n → M)) (hA : DefinableOverBase B sn A)
    (hne : A.Nonempty) (R : GoodBaseGammaRelation B n sn) :
    let W : Set (Values.Gamma (M := M)) := {γ | ∀ a ∈ A, γ ∈ gammaRow R.carrier a}
    GammaDefinableOverBase B W ∧ W.Finite := by
  intro W
  obtain ⟨a₀,ha₀⟩ := hne
  have he : Values.gammaPullback W = baseFamilyIntersection A .rv R.carrier := by
    ext t
    constructor
    · intro ht
      have htNZ : NonzeroRV t := ⟨ht.1,ht.2.1⟩
      let c : Code (M := M) := ⟨⟨t,htNZ.1⟩,htNZ.2⟩
      have hW : value c ∈ W := (mem_gammaPullback_code W c).mp ht
      refine ⟨htNZ.1,?_⟩
      intro a ha
      exact (R.mem_raw_iff B sn a c).mpr (hW a ha)
    · rintro ⟨htRV,hall⟩
      have htNZ := R.proper a₀ t (hall a₀ ha₀)
      let c : Code (M := M) := ⟨⟨t,htNZ.1⟩,htNZ.2⟩
      apply (mem_gammaPullback_code W c).mpr
      intro a ha
      exact (R.mem_raw_iff B sn a c).mp (hall a ha)
  refine ⟨?_,(R.finite a₀).subset (fun γ hγ => hγ a₀ ha₀)⟩
  change DefinableAtBase B .rv (Values.gammaPullback W)
  rw [he]
  exact baseFamilyIntersection_definable B sn A hA .rv R.carrier R.definable

/-- Lemma3.1 for Gamma outputs over an arbitrary small real/Gamma base.
The family may have any finite mixed real arity. Genuine saturation and
both ambient-base cardinal bounds are visible; no section is named. -/
theorem lemma_3_1_gamma_output_full_base {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    {n : ℕ} (sn : Fin n → SortTag) (A : Set (Fin n → M))
    (hA : DefinableOverBase B sn A) (hne : A.Nonempty) (δ : Values.Gamma (M := M))
    (hδ : ∀ a ∈ A, GammaAlgebraicAtBase ⟨B.real ∪ Set.range a,B.gamma⟩ δ) :
    GammaAlgebraicAtBase B δ := by
  obtain ⟨R,hcov⟩ := uniform_good_base_gamma_relation_cover hκ hs B hr hγ sn A hA δ hδ
  let W : Set (Values.Gamma (M := M)) := {γ | ∀ a ∈ A, γ ∈ gammaRow R.carrier a}
  obtain ⟨hWd,hWf⟩ := gamma_base_family_intersection B sn A hA hne R
  exact ⟨W,hWd,hWf,hcov⟩

end SpecialTransformations.Section3.GammaParameters

/- Component: GammaBaseFibreDescent -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters

/-- Pure cardinality bound; no first-order structure is placed on Gamma. -/
theorem small_insert_carrier {α : Type} {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (S : Set α) (hS : Cardinal.mk S < κ) (b : α) : Cardinal.mk ↥(insert b S) < κ :=
  Cardinal.mk_insert_le.trans_lt
    (Cardinal.add_lt_of_lt hκ hS (Cardinal.one_lt_aleph0.trans_le hκ))

theorem small_union_range_carrier {α : Type} {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (S : Set α) (hS : Cardinal.mk S < κ) {n : ℕ} (a : Fin n → α) :
    Cardinal.mk ↥(S ∪ Set.range a) < κ := by
  classical
  have hh : ∀ T : Finset α, Cardinal.mk ↥(S ∪ (T : Set α)) < κ := by
    intro T
    induction T using Finset.induction_on with
    | empty => simpa only [Finset.coe_empty,Set.union_empty] using hS
    | @insert b T hb ih =>
      have he : S ∪ ((insert b T : Finset α) : Set α) = insert b (S ∪ (T : Set α)) := by
        ext x
        simp only [Finset.coe_insert,Set.mem_union,Set.mem_insert_iff]
        tauto
      rw [he]
      exact small_insert_carrier hκ _ ih b
  simpa only [(Set.finite_range a).coe_toFinset] using hh (Set.finite_range a).toFinset

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem corollary_3_2_vf_full_base {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (B : Base (M := M))
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    {n : ℕ} (t : Fin n → M) (A : Set (Fin n → M)) (b : M) (σ : SortTag)
    (hA : DefinableOverBase ⟨B.real ∪ Set.range t,B.gamma⟩ (fun _ => .vf) A)
    (hne : A.Nonempty) (_hfibre : A ⊆ tupleRVFibre t)
    (hb : ∀ a ∈ A, AlgebraicAtBase ⟨B.real ∪ Set.range a,B.gamma⟩ σ b) :
    AlgebraicAtBase ⟨B.real ∪ Set.range t,B.gamma⟩ σ b := by
  apply lemma_3_1_full_gamma_base hκ hs ⟨B.real ∪ Set.range t,B.gamma⟩
    (small_union_range hκ B.real hr t) hγ (fun _ => .vf) A hA hne σ b
  intro a ha
  exact (hb a ha).mono (Set.union_subset_union_left _ Set.subset_union_left) (Set.Subset.refl _)

theorem corollary_3_2_vf_gamma_output_full_base {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (B : Base (M := M))
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    {n : ℕ} (t : Fin n → M) (A : Set (Fin n → M)) (δ : Values.Gamma (M := M))
    (hA : DefinableOverBase ⟨B.real ∪ Set.range t,B.gamma⟩ (fun _ => .vf) A)
    (hne : A.Nonempty) (_hfibre : A ⊆ tupleRVFibre t)
    (hδ : ∀ a ∈ A, GammaAlgebraicAtBase ⟨B.real ∪ Set.range a,B.gamma⟩ δ) :
    GammaAlgebraicAtBase ⟨B.real ∪ Set.range t,B.gamma⟩ δ := by
  apply lemma_3_1_gamma_output_full_base hκ hs ⟨B.real ∪ Set.range t,B.gamma⟩
    (small_union_range hκ B.real hr t) hγ (fun _ => .vf) A hA hne δ
  intro a ha
  exact (hδ a ha).mono (Set.union_subset_union_left _ Set.subset_union_left) (Set.Subset.refl _)

theorem corollary_3_2_rv_full_base {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (B : Base (M := M))
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    {n : ℕ} (γ : Fin n → Values.Gamma (M := M)) (A : Set (Fin n → M)) (b : M) (σ : SortTag)
    (hA : DefinableOverBase ⟨B.real,B.gamma ∪ Set.range γ⟩ (fun _ => .rv) A)
    (hne : A.Nonempty)
    (_hfibre : ∀ a ∈ A, ∃ t : Fin n → Code (M := M), rawTuple t = a ∧ values t = γ)
    (hb : ∀ a ∈ A, AlgebraicAtBase ⟨B.real ∪ Set.range a,B.gamma⟩ σ b) :
    AlgebraicAtBase ⟨B.real,B.gamma ∪ Set.range γ⟩ σ b := by
  apply lemma_3_1_full_gamma_base hκ hs ⟨B.real,B.gamma ∪ Set.range γ⟩
    hr (small_union_range_carrier hκ B.gamma hγ γ) (fun _ => .rv) A hA hne σ b
  intro a ha
  exact (hb a ha).mono (Set.Subset.refl _) Set.subset_union_left

theorem corollary_3_2_rv_gamma_output_full_base {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (B : Base (M := M))
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    {n : ℕ} (γ : Fin n → Values.Gamma (M := M)) (A : Set (Fin n → M)) (δ : Values.Gamma (M := M))
    (hA : DefinableOverBase ⟨B.real,B.gamma ∪ Set.range γ⟩ (fun _ => .rv) A)
    (hne : A.Nonempty)
    (_hfibre : ∀ a ∈ A, ∃ t : Fin n → Code (M := M), rawTuple t = a ∧ values t = γ)
    (hδ : ∀ a ∈ A, GammaAlgebraicAtBase ⟨B.real ∪ Set.range a,B.gamma⟩ δ) :
    GammaAlgebraicAtBase ⟨B.real,B.gamma ∪ Set.range γ⟩ δ := by
  apply lemma_3_1_gamma_output_full_base hκ hs ⟨B.real,B.gamma ∪ Set.range γ⟩
    hr (small_union_range_carrier hκ B.gamma hγ γ) (fun _ => .rv) A hA hne δ
  intro a ha
  exact (hδ a ha).mono (Set.Subset.refl _) Set.subset_union_left

end SpecialTransformations.Section3.GammaParameters

/- Component: GammaCodedParameters -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem gamma_value_of_named_code (B : Base (M := M)) (t : Code (M := M))
    (ht : raw t ∈ B.real) : GammaDefinableClosureAtBase B (value t) := by
  let S : Set M := B.real
  let E : M → M → Prop := SameScalar
  let r : M := raw t
  have hSame := (definableOver_iff_normalized_raw S (fun _ : Fin 2 => .rv)
    {z | SameScalar (z 0) (z 1)}).mp (same_scalar_sorted_definable S)
  have hD : SpecialTransformations.Section3.DefinableAt S .rv {x | E r x} := by
    apply (definableAt_iff_normalized_raw S .rv _).mpr
    refine ⟨?_,fun x hx => hx.2.1.1⟩
    let N := CanonicalStructure.normalize (M := M)
    letI := sM
    have hRaw : @Set.Definable₁ M S LRV N {x | E r x} := by
      letI := N
      have hF : S.DefinableMap LRV (fun z : Fin 1 → M => ![r,z 0]) := by
        intro i
        fin_cases i
        · exact LRV.definableFun_const (Fin 1) ht
        · exact Set.DefinableFun.proj LRV
      exact hSame.1.preimage_map hF
    exact hRaw
  have he : {x | E r x} = Values.gammaPullback {value t} := by
    ext x
    constructor
    · intro hx
      let u : Code (M := M) := ⟨⟨x,hx.2.1.1⟩,hx.2.1.2⟩
      exact ⟨hx.2.1.1,hx.2.1.2,((value_eq_iff t u).mpr hx.2.2).symm⟩
    · rintro ⟨hx,h0,hv⟩
      let u : Code (M := M) := ⟨⟨x,hx⟩,h0⟩
      exact ⟨⟨raw_rv t,raw_ne_zero t⟩,⟨hx,h0⟩,(value_eq_iff t u).mp hv.symm⟩
  change DefinableAtBase B .rv (Values.gammaPullback {value t})
  rw [← he]
  exact real_definableAtBase B .rv _ hD

theorem AlgebraicAtBase.eliminate_definable_params {B C : Base (M := M)}
    {σ : SortTag} {b : M} (hb : AlgebraicAtBase C σ b)
    (hr : ∀ c ∈ C.real, ∃ τ, DefinableClosureAtBase B τ c)
    (hγ : ∀ γ ∈ C.gamma, GammaDefinableClosureAtBase B γ) : AlgebraicAtBase B σ b := by
  obtain ⟨W,hW,hWf,hbW⟩ := hb
  exact ⟨W,DefinableOverBase.eliminate_definable_params hW hr hγ,hWf,hbW⟩

theorem GammaAlgebraicAtBase.eliminate_definable_params {B C : Base (M := M)}
    {δ : Values.Gamma (M := M)} (hδ : GammaAlgebraicAtBase C δ)
    (hr : ∀ c ∈ C.real, ∃ τ, DefinableClosureAtBase B τ c)
    (hγ : ∀ γ ∈ C.gamma, GammaDefinableClosureAtBase B γ) : GammaAlgebraicAtBase B δ := by
  obtain ⟨W,hW,hWf,hδW⟩ := hδ
  exact ⟨W,DefinableOverBase.eliminate_definable_params hW hr hγ,hWf,hδW⟩

end SpecialTransformations.Section3.GammaParameters

/- Component: GammaInputDescent -/
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3.GammaParameters
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def gammaIndex {k n : ℕ} (i : Fin k) : Fin (k+n) := finSumFinEquiv (.inl i)
def realIndex {k n : ℕ} (i : Fin n) : Fin (k+n) := finSumFinEquiv (.inr i)
def mixedCodeSort {k n : ℕ} (sn : Fin n → SortTag) : Fin (k+n) → SortTag :=
  Sum.elim (fun _ : Fin k => .rv) sn ∘ finSumFinEquiv.symm

def mixedCodeFamily {k n : ℕ}
    (A : Set ((Fin n → M) × (Fin k → Values.Gamma (M := M)))) : Set (Fin (k+n) → M) :=
  {z | Proper (z ∘ gammaIndex) ∧ (z ∘ realIndex,fun i => codeValue (z (gammaIndex i))) ∈ A}

theorem mixedCodeFamily_nonempty {k n : ℕ}
    (A : Set ((Fin n → M) × (Fin k → Values.Gamma (M := M)))) (hne : A.Nonempty) :
    (mixedCodeFamily A).Nonempty := by
  obtain ⟨⟨a,γ⟩,ha⟩ := hne
  let z : Fin (k+n) → M := Sum.elim (rawTuple (representatives γ)) a ∘ finSumFinEquiv.symm
  have hγ : z ∘ gammaIndex = rawTuple (representatives γ) := by
    funext i
    simp only [Function.comp_apply,z,gammaIndex,Equiv.symm_apply_apply,Sum.elim_inl]
  have hr : z ∘ realIndex = a := by
    funext i
    simp only [Function.comp_apply,z,realIndex,Equiv.symm_apply_apply,Sum.elim_inr]
  have hv : (fun i : Fin k => codeValue (z (gammaIndex i))) = γ := by
    funext i
    have hi := congrFun hγ i
    change z (gammaIndex i) = raw (representative (γ i)) at hi
    rw [hi,codeValue_raw,representative_value]
  refine ⟨z,?_,?_⟩
  · rw [hγ]
    exact rawTuple_proper _
  · rw [hr,hv]
    exact ha

/-- Each decoded Gamma input name is definable from every proper code
for that input. All real names are retained in the same finite code tuple. -/
theorem decoded_parameters_definable (B : Base (M := M)) {l k n : ℕ}
    (z : Fin l → M) (ir : Fin n → Fin l) (ig : Fin k → Fin l)
    (hz : ∀ i, NonzeroRV (z (ig i))) :
    let C : Base (M := M) := ⟨B.real ∪ Set.range (z ∘ ir),
      B.gamma ∪ Set.range (fun i => codeValue (z (ig i)))⟩
    let D : Base (M := M) := ⟨B.real ∪ Set.range z,B.gamma⟩
    (∀ c ∈ C.real, ∃ σ, DefinableClosureAtBase D σ c) ∧
      ∀ γ ∈ C.gamma, GammaDefinableClosureAtBase D γ := by
  intro C D
  constructor
  · intro c hc
    apply (subset_closureBase D).1
    rcases hc with hc | ⟨i,rfl⟩
    · exact Or.inl hc
    · exact Or.inr ⟨ir i,rfl⟩
  · intro γ hγ
    rcases hγ with hγ | ⟨i,rfl⟩
    · exact gamma_name_definable D γ hγ
    · let t : Code (M := M) := ⟨⟨z (ig i),(hz i).1⟩,(hz i).2⟩
      have ht := gamma_value_of_named_code D t (Or.inr ⟨ig i,rfl⟩)
      have he : codeValue (z (ig i)) = value t := by
        simp only [codeValue,dif_pos (hz i)]
        rfl
      change GammaDefinableClosureAtBase D (codeValue (z (ig i)))
      exact he.symm ▸ ht

/-- Lemma3.1 with arbitrary finite mixed VF/RV/Gamma indexing tuples.
Definability of the indexing family is its full proper real-code preimage;
all temporary input representatives are eliminated from the conclusion. -/
theorem lemma_3_1_mixed_gamma_input {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (B : Base (M := M))
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    {k n : ℕ} (sn : Fin n → SortTag)
    (A : Set ((Fin n → M) × (Fin k → Values.Gamma (M := M))))
    (hA : DefinableOverBase B (mixedCodeSort (k := k) sn) (mixedCodeFamily A)) (hne : A.Nonempty)
    (σ : SortTag) (b : M)
    (hb : ∀ p ∈ A, AlgebraicAtBase ⟨B.real ∪ Set.range p.1,B.gamma ∪ Set.range p.2⟩ σ b) :
    AlgebraicAtBase B σ b := by
  apply lemma_3_1_full_gamma_base hκ hs B hr hγ (mixedCodeSort sn) (mixedCodeFamily A)
    hA (mixedCodeFamily_nonempty A hne) σ b
  intro z hz
  obtain ⟨hnz,hzA⟩ := hz
  obtain ⟨hreal,hgamma⟩ := decoded_parameters_definable B z realIndex gammaIndex hnz
  exact (hb _ hzA).eliminate_definable_params hreal hgamma

theorem lemma_3_1_mixed_gamma_input_gamma_output {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (B : Base (M := M))
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    {k n : ℕ} (sn : Fin n → SortTag)
    (A : Set ((Fin n → M) × (Fin k → Values.Gamma (M := M))))
    (hA : DefinableOverBase B (mixedCodeSort (k := k) sn) (mixedCodeFamily A)) (hne : A.Nonempty)
    (δ : Values.Gamma (M := M))
    (hδ : ∀ p ∈ A, GammaAlgebraicAtBase ⟨B.real ∪ Set.range p.1,B.gamma ∪ Set.range p.2⟩ δ) :
    GammaAlgebraicAtBase B δ := by
  apply lemma_3_1_gamma_output_full_base hκ hs B hr hγ (mixedCodeSort sn) (mixedCodeFamily A)
    hA (mixedCodeFamily_nonempty A hne) δ
  intro z hz
  obtain ⟨hnz,hzA⟩ := hz
  obtain ⟨hreal,hgamma⟩ := decoded_parameters_definable B z realIndex gammaIndex hnz
  exact (hδ _ hzA).eliminate_definable_params hreal hgamma

end SpecialTransformations.Section3.GammaParameters
