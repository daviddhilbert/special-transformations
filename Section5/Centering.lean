module

public import Section5.Assembly
public import Section5.UnaryUniform

@[expose] public section

/-!
# Preparing a vertical root locus by a lower-dimensional transformation

The lower transformation is supplied by the dimensional induction. The
result here derives the prepared-locus condition for the actual lifted
root family, without treating that condition as part of finiteness.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations.Section5

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m l t : ℕ}
variable {A : DefSet (M := M) S (n + 1) m} {B : DefSet (M := M) S (n + 1) l}

namespace Chain

theorem HeadCompatible.append {c : ℕ} {C : DefSet (M := M) S (n + 1) c}
    (T : Chain S (n + 1) A B) (U : Chain S (n + 1) B C)
    (hT : T.HeadCompatible) (hU : U.HeadCompatible) : (T.append U).HeadCompatible := by
  induction T with
  | nil _ => exact hU
  | cons p tail ih => exact ⟨hT.1, ih U hT.2 hU⟩

theorem TailProgram.append {c : ℕ} {C : DefSet (M := M) S (n + 1) c}
    (T : Chain S (n + 1) A B) (U : Chain S (n + 1) B C)
    (hT : T.TailProgram) (hU : U.TailProgram) : (T.append U).TailProgram := by
  induction T with
  | nil _ => exact hU
  | cons p tail ih => exact ⟨hT.1, hT.2.1, ih U hT.2.2 hU⟩

theorem lastKind_append {N a b c : ℕ} {X : DefSet (M := M) S N a}
    {Y : DefSet (M := M) S N b} {Z : DefSet (M := M) S N c}
    (T : Chain S N X Y) (U : Chain S N Y Z) (previous : Option Bool) :
    (T.append U).lastKind previous = U.lastKind (T.lastKind previous) := by
  induction T generalizing previous with
  | nil _ => rfl
  | cons p tail ih => cases p <;> exact ih U _

end Chain

theorem dropHead_canonical_old (σ : Fin t → Fin l) (p : Point (M := M) (n + 1) l) :
    dropHead (fun i => Fin.natAdd (n + 1) (σ i)) (canonical p) = dropHead σ p := by
  refine Prod.ext rfl ?_
  funext i
  exact canonical_old p (σ i)

/-- Finish a lifted program at a canonical boundary, retaining its comparison
map. A canonical step is appended precisely when the boundary needs it. -/
theorem finish_tail_lift (hA : AllTagged A)
    {C : DefSet (M := M) S n t} (f : Map A C)
    (W : SpecialBijection A B) (hW : W.chain.TailProgram)
    (hAlt : W.chain.Alternating (some false)) (σ : Fin t → Fin l)
    (hcomm : ∀ a : A, dropHead σ (W.toMap a).val = (f a).val) :
    ∃ r : ℕ, ∃ D : DefSet (M := M) S (n + 1) r, ∃ ρ : Fin t → Fin r,
      ∃ V : SpecialBijection A D, V.chain.Alternating (some false) ∧
        V.chain.TailProgram ∧ V.chain.lastKind (some false) = some false ∧
        AllTagged D ∧ ∀ a : A, dropHead ρ (V.toMap a).val = (f a).val := by
  by_cases hlast : W.chain.lastKind (some false) = some false
  · exact ⟨l, B, σ, W, hAlt, hW, hlast,
      W.chain.lastKind_allTagged (some false) (fun _ => hA) hlast, hcomm⟩
  · let U := SpecialBijection.canonical B
    have hUa : U.chain.Alternating (W.chain.lastKind (some false)) := ⟨hlast, trivial⟩
    have hVa := W.chain.append_alternating U.chain (some false) hAlt hUa
    let V := W.comp U ((W.chain.append U.chain).alternating_none (some false) hVa)
    refine ⟨(n + 1) + l, canonicalImage B,
      (fun i => Fin.natAdd (n + 1) (σ i)), V, hVa,
      Chain.TailProgram.append W.chain U.chain hW ⟨trivial, (fun _ => rfl), trivial⟩,
      ?_, canonicalImage_allTagged B, ?_⟩
    · exact W.chain.lastKind_append U.chain (some false)
    · intro a
      have he := SpecialBijection.comp_toMap W U V.alternating
      change dropHead (fun i => Fin.natAdd (n + 1) (σ i)) (V.toMap a).val = _
      rw [he]
      exact (dropHead_canonical_old σ (W.toMap a).val).trans (hcomm a)

theorem prepared_verticalHull (R : VerticalRootFamily A) (hA : IsRVPullback (carrier A))
    (k : Fin m) (hTag : Tagged (carrier A) 0 k)
    {C : DefSet (M := M) S n t} (T : SpecialBijection (baseImage A) C)
    (hprep : ∀ a b : C, SameRV a.val b.val →
      ((T.inverseMap a).val ∈ carrier (baseImage R.set) ↔
        (T.inverseMap b).val ∈ carrier (baseImage R.set)))
    (W : SpecialBijection A B) (hW : W.chain.TailProgram) (σ : Fin t → Fin l)
    (hcomm : ∀ a : A, dropHead σ (W.toMap a).val = (T.toMap (baseProjection A a)).val) :
    IsRVPullback (R.pushTail W hW (W.chain.labelIndex k)
      (Chain.TailProgram.tagged W.chain hW k hTag)).verticalHull := by
  let Q := R.pushTail W hW (W.chain.labelIndex k) (Chain.TailProgram.tagged W.chain hW k hTag)
  have hB := W.preserves_pullback hA
  apply (isRVPullback_iff Q.verticalHull).mpr
  intro p hp q hpq
  have hpB : p ∈ carrier B := hB ▸ Q.verticalHull_subset_hull hp
  have hqB := (isRVPullback_iff _).mp hB p hpB q hpq
  let pB : B := ⟨p, hpB⟩
  let qB : B := ⟨q, hqB⟩
  let a := W.inverseMap pB
  let b := W.inverseMap qB
  obtain ⟨x₀, hx₀, hxRV⟩ := hp
  obtain ⟨r, hr, hWr⟩ := (R.mem_imageSet W.toMap _).mp ((Q.mem_fibre _ _).mp hx₀)
  have htail : TailEq (W.toMap r).val p := by
    intro i
    have hh := congrArg (fun z : Point (M := M) (n + 1) l => vfAt z i.succ) hWr
    simpa only [insertHead, dropHead, vfAt, Fin.cons_succ] using hh
  have hrlabels : (W.toMap r).val.2 = p.2 := by
    have hh := congrArg Prod.snd hWr
    exact hh
  have hrRV : SameRV (W.toMap r).val p := by
    apply (sameRV_iff _ _).mpr
    refine ⟨?_, hrlabels⟩
    intro i
    cases i using Fin.cases with
    | zero =>
      have hx := congrArg (fun z : Point (M := M) (n + 1) l => vfAt z 0) hWr
      exact (congrArg rv hx).trans hxRV
    | succ i => exact congrArg rv (htail i)
  have hback := W.compatible_inverse_pair (Chain.TailProgram.headCompatible W.chain hW)
    (W.toMap r) pB hrRV htail
  rw [W.inverse_apply] at hback
  have hsame := W.inverse_contractible (W.toMap r) pB hrRV
  rw [W.inverse_apply] at hsame
  have hbase : dropHead id r.val = dropHead id a.val :=
    Prod.ext (funext hback.1) (((sameRV_iff _ _).mp hsame).2)
  have haRoot : (baseProjection A a).val ∈ carrier (baseImage R.set) := by
    apply (mem_baseImage R.set _).mpr
    refine ⟨vfAt r.val 0, ?_⟩
    change insertHead (vfAt r.val 0) (dropHead id a.val) ∈ carrier R.set
    rw [← hbase, insertHead_dropHead]
    exact hr
  have hWp : (W.toMap a).val = p := congrArg Subtype.val (W.apply_inverse pB)
  have hWq : (W.toMap b).val = q := congrArg Subtype.val (W.apply_inverse qB)
  have hTa : (T.toMap (baseProjection A a)).val = dropHead σ p :=
    (hcomm a).symm.trans (congrArg (dropHead σ) hWp)
  have hTb : (T.toMap (baseProjection A b)).val = dropHead σ q :=
    (hcomm b).symm.trans (congrArg (dropHead σ) hWq)
  have hlow : SameRV (T.toMap (baseProjection A a)).val (T.toMap (baseProjection A b)).val := by
    rw [hTa, hTb]
    exact sameRV_dropHead σ hpq
  have htransfer := hprep (T.toMap (baseProjection A a)) (T.toMap (baseProjection A b)) hlow
  rw [T.inverse_apply, T.inverse_apply] at htransfer
  have hbRoot := htransfer.mp haRoot
  obtain ⟨x, hx⟩ := (mem_baseImage R.set _).mp hbRoot
  have hxA := R.subset hx
  have hxRV : rv x = rv (vfAt b.val 0) := (hTag _ hxA).symm.trans (hTag _ b.property)
  have hxR : replace 0 b.val x ∈ carrier R.set := (replace_zero_insertHead b.val x).symm ▸ hx
  let s : A := ⟨replace 0 b.val x, R.subset hxR⟩
  have hWs := Chain.TailProgram.replace_head W.chain hW b x hxRV (R.subset hxR)
  change (W.toMap s).val = replace 0 (W.toMap b).val x at hWs
  have hWs' : (W.toMap s).val = replace 0 q x :=
    hWs.trans (congrArg (fun z : Point (M := M) (n + 1) l => replace 0 z x) hWq)
  have hxQ : replace 0 q x ∈ carrier Q.set :=
    (R.mem_imageSet W.toMap _).mpr ⟨s, hxR, hWs'⟩
  have hf := Chain.TailProgram.headFixed W.chain hW b
  change vfAt (W.toMap b).val 0 = vfAt b.val 0 at hf
  refine ⟨x, (Q.mem_fibre _ _).mpr ((replace_zero_insertHead q x) ▸ hxQ), ?_⟩
  exact hxRV.trans ((congrArg rv hf).symm.trans
    (congrArg (fun z : Point (M := M) (n + 1) l => rv (vfAt z 0)) hWq))

/-- The induction predicate for RV-valued definable maps. This definition is
only a statement; the dimensional existence theorem must prove it. -/
def RVPreparation (S : Set M) (N : ℕ) : Prop :=
  ∀ {a k : ℕ} (D : DefSet (M := M) S N a) (previous : Option Bool),
    (previous = some false → AllTagged D) →
    ∀ f : Map D (PresentedSet.univ (pointSpace (M := M) 0 k) S),
    ∃ b : ℕ, ∃ E : DefSet (M := M) S N b, ∃ T : SpecialBijection D E,
      T.chain.Alternating previous ∧ IsRVPullback (carrier E) ∧
        Contractible (Map.comp f T.inverseMap)

/-- The lower-dimensional induction prepares the actual projected root
indicator. Its lift therefore prepares the vertical root locus. -/
theorem prepare_vertical_locus (ih : RVPreparation (M := M) S n)
    (R : VerticalRootFamily A) (hA : IsRVPullback (carrier A)) (hAll : AllTagged A)
    (k : Fin m) (hTag : Tagged (carrier A) 0 k) :
    ∃ r : ℕ, ∃ D : DefSet (M := M) S (n + 1) r, ∃ V : SpecialBijection A D,
      ∃ hV : V.chain.TailProgram, V.chain.Alternating (some false) ∧
        V.chain.lastKind (some false) = some false ∧ AllTagged D ∧
        IsRVPullback (R.pushTail V hV (V.chain.labelIndex k)
          (Chain.TailProgram.tagged V.chain hV k hTag)).verticalHull := by
  let f := membershipMap (baseImage A) (baseImage R.set)
  obtain ⟨t, C, T, hTa, hC, hc⟩ := ih (baseImage A) (some false)
    (fun _ => baseImage_allTagged A hAll) f
  have hprep : ∀ a b : C, SameRV a.val b.val →
      ((T.inverseMap a).val ∈ carrier (baseImage R.set) ↔
        (T.inverseMap b).val ∈ carrier (baseImage R.set)) := by
    intro a b he
    have hh := congrFun (((sameRV_iff _ _).mp (hc a b he)).2) 0
    exact (membershipMap_eq_iff (baseImage A) (baseImage R.set)
      (T.inverseMap a) (T.inverseMap b)).mp hh
  obtain ⟨b, B, σ, W, hWa, hW, hcomm, _⟩ := T.chain.lift_dropHead_compatible A id
    (fun p hp => (baseProjection A ⟨p, hp⟩).property) (some false) hTa
  let W' : SpecialBijection A B := ⟨W, W.alternating_none (some false) hWa⟩
  let g := Map.comp T.toMap (baseProjection A)
  obtain ⟨r, D, ρ, V, hVa, hV, hlast, htags, hproj⟩ :=
    finish_tail_lift hAll g W' hW hWa σ hcomm
  refine ⟨r, D, V, hV, hVa, hlast, htags, ?_⟩
  exact prepared_verticalHull R hA k hTag T hprep V hV ρ hproj

/-- Finite vertical root reduction. The induction on the root bound is
separate from the induction on VF dimension, which supplies only the
lower-dimensional preparation of projected indicators. -/
theorem vertical_centralize (h00 : M ⊨ Axioms.ACVF00)
    (ih : RVPreparation (M := M) S n) (d : ℕ) :
    ∀ {a : ℕ} (D : DefSet (M := M) S (n + 1) a) (R : VerticalRootFamily D),
      IsRVPullback (carrier D) → AllTagged D → R.Bound d →
    ∃ b : ℕ, ∃ E : DefSet (M := M) S (n + 1) b, ∃ T : SpecialBijection D E,
      T.chain.Alternating (some false) ∧ T.chain.HeadCompatible ∧
        T.chain.lastKind (some false) = some false ∧ AllTagged E ∧
        IsRVPullback (carrier E) ∧
        ∀ a : D, a.val ∈ carrier R.set → vfAt (T.toMap a).val 0 = 0 := by
  induction d with
  | zero =>
    intro a D R hD hAll hd
    exact ⟨a, D, SpecialBijection.refl D, trivial, trivial, rfl, hAll, hD,
      fun a ha => R.bound_zero hd a.val ha⟩
  | succ d recurse =>
    intro a D R hD hAll hd
    obtain ⟨k, hk⟩ := hAll 0
    obtain ⟨b, E, W, hW, hWa, hlast, htags, hHull⟩ :=
      prepare_vertical_locus ih R hD hAll k hk
    let k' := W.chain.labelIndex k
    have hk' := Chain.TailProgram.tagged W.chain hW k hk
    let Q := R.pushTail W hW k' hk'
    have hQ : Q.Bound (d + 1) := R.pushTail_bound W hW k' hk' (d + 1) hd
    let V := Q.step h00 (d + 1) hQ k' hk' hHull
    let P := Q.stepFamily h00 (d + 1) hQ k' hk' hHull
    have hV : V.chain.Alternating (some false) := ⟨by decide, by decide, trivial⟩
    have hVc : V.chain.HeadCompatible := ⟨FocusGeometry.headBlind_zero _, trivial, trivial⟩
    have hEt : AllTagged (Q.stepTarget h00 (d + 1) hQ k' hk' hHull) :=
      canonicalImage_allTagged _
    have hEr := V.preserves_pullback (W.preserves_pullback hD)
    obtain ⟨c, F, U, hUa, hUc, hUl, hUt, hUr, hz⟩ := recurse _ P hEr hEt
      (Q.step_bound h00 d hQ k' hk' hHull)
    have hKa := W.chain.append_alternating V.chain (some false) hWa (by simpa only [hlast] using hV)
    let K := W.comp V ((W.chain.append V.chain).alternating_none (some false) hKa)
    have hKl : K.chain.lastKind (some false) = some false :=
      W.chain.lastKind_append V.chain (some false)
    have hTa := K.chain.append_alternating U.chain (some false) hKa (by simpa only [hKl] using hUa)
    let T := K.comp U ((K.chain.append U.chain).alternating_none (some false) hTa)
    refine ⟨c, F, T, hTa, ?_, ?_, hUt, hUr, ?_⟩
    · exact Chain.HeadCompatible.append K.chain U.chain
        (Chain.HeadCompatible.append W.chain V.chain
          (Chain.TailProgram.headCompatible W.chain hW) hVc) hUc
    · exact (K.chain.lastKind_append U.chain (some false)).trans (by simpa only [hKl] using hUl)
    · intro a ha
      have hWaRoot : (W.toMap a).val ∈ carrier Q.set :=
        (R.mem_imageSet W.toMap _).mpr ⟨a, ha, rfl⟩
      have hVaRoot : (V.toMap (W.toMap a)).val ∈ carrier P.set :=
        (Q.mem_imageSet V.toMap _).mpr ⟨W.toMap a, hWaRoot, rfl⟩
      have hh := hz (V.toMap (W.toMap a)) hVaRoot
      have hKmap := SpecialBijection.comp_toMap W V K.alternating
      have hTmap := SpecialBijection.comp_toMap K U T.alternating
      change vfAt (T.toMap a).val 0 = 0
      rw [hTmap, hKmap]
      exact hh

end SpecialTransformations.Section5
