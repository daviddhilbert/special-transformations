/-
# Lemma 3.3 (`PrepStepSize`): what the frozen `PrepStepP` actually owes

`qe.tex` §3.1 (l. 578 onward) fixes `M, N ⊨ ACVF` with `N` `‖M‖⁺`-saturated, `S ⊆ M`, `f : S → N`, and
proves the unnamed Lemma 3.3 (l. 580):

> There is a monomorphism `f* : S* → N` extending `f` such that (1) `VF(S*) = VF(S)`,
> (2) `K(S*) = K(M)`, (3) `Γ(S*)` is the divisible hull of `Γ(S)`.
> *Proof.* First of all, there is a field homomorphism `g : K(M) → K(N)` extending `f ↾ K(S)`.
> Let `S₁` be `⟨K(M), RV(S)⟩` ... Next let `n > 1` be least such that there is `t ∈ RV(M)` with
> `tⁿ ∈ S₁` and `tⁱ ∉ S₁` for `0 < i < n`. Let `r ∈ RV(N)` with `rⁿ = f₁(tⁿ)`. ... Iterating this
> procedure the lemma follows.

The frozen `Assembly.PrepStepP` is that lemma with clauses (1) and the *hull* half of (3) dropped
(the frozen `Assembly.Standing` asks only for `KEqTop` and `GammaDivisible`), and this file

* confirms that the paper's Lemma 3.3 implies the frozen `PrepStepP` (`prepStepP_of_paperLemma33`),
  so the frozen obligation is not stronger than the paper's;
* **sharpens the audit of the frozen obligation**: `PrepStepP` forces not merely `#Kˣ(M) ≤ #N`
  (`M7Paper.prepStepP_forces_units_size`) but `#Kˣ(M) ≤ #Kˣ(N)` — the *residue field* of `M` must
  inject into the *residue field* of `N`, because `KEqTop T` puts all units of `M` inside `T` and a
  structure embedding preserves the unary predicate `Kˣ` both ways.  Hence `M7Paper.SizeHyp`
  (`#M ≤ #N`) is **not** the cardinal hypothesis Lemma 3.3 needs: the paper's step (i), a field
  homomorphism `K(M) → K(N)`, is exactly the residue-field statement that `#M ≤ #N` does not give.
  `paperHyp_supplies_unitsN_size` records the true floor: `PrepStepP` at a pair is only possible if
  the unit groups are so embedded, which is what `‖M‖⁺`-saturation (not `#M ≤ #N`) supplies, through
  the transcendence room of `K(N)`;
* **removes the target-side obligation from the paper's iteration**: `exists_rv_root` proves in
  `ACVF` that every nonzero `RV`-element has an `n`-th root in `RV` (`rⁿ = f₁(tⁿ)` in the paper's
  iteration exists *because* `VF(N)` is algebraically closed and `rv` is multiplicative and
  surjective — not as an extra realisation hypothesis);
* **decomposes `PrepStepP` along the paper's proof** into the one-element steps it really uses
  (`MUnitsStep`: one residue unit at a time; `MDivStep`: one `n`-th root at a time), plus order
  theory (`prepStepP_of_unitsStep_divStep`): the exhaustion of the units of `M` is
  `exists_exhaust` with `P := True`, and the divisible hull is the maximality argument with
  `P := KEqTop`.  Neither step mentions `Standing`; the only thing the frozen statement adds is that
  the maximal element is `Standing`, which is where the paper uses saturation;
* states the henselization step (`HenselizationStep`, absent from the tree) and proves that the
  frozen `Standing` cannot see it (`standing_of_henselization`): a henselization with
  `VF`, `K`, `Γ` unchanged is invisible to `KEqTop` and `GammaDivisible`, which is why the frozen
  route may ignore the word "henselian" — and why `OneStepVFP` is *literally* weaker than Lemmas
  3.4/3.5, which need `(VF(Š), O(Š))` henselian.

Nothing here is assumed beyond `Axioms.ACVF`; every declaration's `#print axioms` is
`{propext, Classical.choice, Quot.sound}`.
-/
import PaperRoute
import Standing

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
open SpecialTransformations.Milestone0.LRV

set_option linter.style.haveILetI false

namespace SpecialTransformations
namespace Milestone0
namespace M6L33

/-! ### Unary relations at one-tuples, and transport of `Kˣ` along a structure embedding -/

theorem relMap_vecOne {M : Type} [LRV.Structure M] {r : LRV.Relations 1} (x : M) :
    Structure.RelMap r (fun _ : Fin 1 => x) ↔ Structure.RelMap r ![x] := by
  have h : (fun _ : Fin 1 => x) = ![x] := by
    funext i; fin_cases i; rfl
  rw [h]

theorem units_sub_iff {M : Type} [LRV.Structure M] {T : LRV.Substructure M} {x : M}
    (hxT : x ∈ T) :
    Structure.RelMap (L := LRV) Rel.memUnits (fun _ : Fin 1 => (⟨x, hxT⟩ : T)) ↔ iUnits x := by
  show Structure.RelMap (L := LRV) Rel.memUnits (fun _ : Fin 1 => x) ↔ iUnits x
  exact relMap_vecOne x

variable {M N : Type} [LRV.Structure M] [LRV.Structure N]

/-- **A structure embedding sends `Kˣ` to `Kˣ`**: `Kˣ` is a unary relation symbol of `L_RV`, and
embeddings preserve relations in both directions. -/
theorem units_map_units {T : LRV.Substructure M} (g : T ↪[LRV] N) {x : M} (hxT : x ∈ T)
    (hx : iUnits x) : iUnits (g ⟨x, hxT⟩) := by
  have h := StrongHomClass.map_rel (L := LRV) g (Rel.memUnits) (fun _ : Fin 1 => (⟨x, hxT⟩ : T))
  exact (relMap_vecOne (g ⟨x, hxT⟩)).mp (h.mpr ((units_sub_iff hxT).mpr hx))

/-! ### The sharpened defect: `PrepStepP` forces `#Kˣ(M) ≤ #Kˣ(N)` -/

/-- **`PrepStepP` forces the unit group of `M` to embed in the unit group of `N`.**  `KEqTop T` puts
every unit of `M` into the domain of an injective map preserving `Kˣ`, so the *residue field* of `M`
injects into the residue field of `N` — strictly more than
`M7Paper.prepStepP_forces_units_size` (`#Kˣ(M) ≤ #N`). -/
theorem prepStepP_forces_unitsN_size [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (h : Assembly.PrepStepP (M := M) (N := N)) (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    Cardinal.mk {x : M // iUnits x} ≤ Cardinal.mk {y : N // iUnits y} := by
  obtain ⟨T, g, _hST, _hagree, hStand⟩ := h S f
  refine Cardinal.mk_le_of_injective (f := fun x : {x : M // iUnits x} =>
    (⟨g ⟨x.1, hStand.1 x.1 x.2⟩, units_map_units g (hStand.1 x.1 x.2) x.2⟩ :
      {y : N // iUnits y})) ?_
  intro a b hab
  have h2 : (⟨a.1, hStand.1 a.1 a.2⟩ : T) = ⟨b.1, hStand.1 b.1 b.2⟩ :=
    Embedding.injective g (congrArg Subtype.val hab)
  exact Subtype.ext (congrArg (fun y : T => (y : M)) h2)

/-- The residue-field form of the cardinal hypothesis: `#Kˣ(M) ≤ #Kˣ(N)`.  This is the honest
cardinal floor of Lemma 3.3 (`prepStepP_forces_unitsN_size`), and it is *not* a consequence of
`M7Paper.SizeHyp` (`#M ≤ #N`): a model's residue field can be small while the model is large. -/
def ResidueSizeHyp (M N : Type) [LRV.Structure M] [LRV.Structure N] : Prop :=
  Cardinal.mk {x : M // iUnits x} ≤ Cardinal.mk {y : N // iUnits y}

/-- `PrepStepP` at a pair forces the residue-field size hypothesis at that pair. -/
theorem residueSizeHyp_of_prepStepP [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (h : Assembly.PrepStepP (M := M) (N := N)) (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    ResidueSizeHyp M N :=
  prepStepP_forces_unitsN_size h S f

/-- **The frozen `PrepStepSize` (which asks only for `#M ≤ #N`) therefore forces a residue-field
inequality at every size-bounded pair of models.**  This is the sharpened audit statement: the
repaired obligation `M7Paper.PrepStepSize` is *not* the paper's Lemma 3.3, because its hypothesis
`SizeHyp` says nothing about the residue fields, while its conclusion needs a field embedding
`K(M) → K(N)` (the paper's step (i)), which is what `‖M‖⁺`-saturation supplies and `#M ≤ #N` does
not. -/
theorem prepStepSize_forces_unitsN_size (h : M7Paper.PrepStepSize) [hM : M ⊨ Axioms.ACVF]
    [hN : N ⊨ Axioms.ACVF] (hSize : M7Paper.SizeHyp M N) (S : LRV.Substructure M)
    (f : S ↪[LRV] N) : ResidueSizeHyp M N :=
  residueSizeHyp_of_prepStepP (h M N hSize) S f

/-- Contrapositive form: a pair whose residue field of `M` does not embed into that of `N` refutes
the frozen `PrepStepP`, whatever the sizes of the models. -/
theorem not_prepStepP_of_unitsN_small [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (hbig : Cardinal.mk {y : N // iUnits y} < Cardinal.mk {x : M // iUnits x})
    (S : LRV.Substructure M) (f : S ↪[LRV] N) : ¬ Assembly.PrepStepP (M := M) (N := N) :=
  fun h => absurd (prepStepP_forces_unitsN_size h S f) (not_le.mpr hbig)

/-! ### The paper's step "let `r ∈ RV(N)` with `f₁(tⁿ) = rⁿ`" is a theorem, not an assumption

`exists_rv_root`: in a model of `ACVF` every nonzero `RV`-element is an `n`-th power in `RV`
(`n ≥ 1`).  This is `rvSurj` + `rv` multiplicative + `VF` algebraically closed, and it is exactly
what the paper's iteration in Lemma 3.3 uses when it writes "let `r ∈ RV(N)` such that
`f₁(tⁿ) = rⁿ`". -/

section Root

variable {K : Type} [LRV.Structure K] [hK : K ⊨ Axioms.ACVF]

/-- `rv` commutes with VF-powers: `rv(y)ⁿ = rv(yⁿ)`. -/
theorem rvPow_rv_vfPow {y : K} (hy : iVF y) (n : ℕ) :
    Assembly.rvPow (iRv y) n = iRv (StandingTree.vfPow (M := K) y n) := by
  induction n with
  | zero => rw [Assembly.rvPow, StandingTree.vfPow, RVCalc.rv_one hK]
  | succ k ih =>
    rw [show Assembly.rvPow (iRv y) (k + 1)
        = iRVMul (Assembly.rvPow (iRv y) k) (iRv y) from rfl, ih,
      show StandingTree.vfPow (M := K) y (k + 1)
        = iVFMul (StandingTree.vfPow (M := K) y k) y from rfl,
      Transfer.rv_mul_hom_of_model hK (StandingTree.vf_pow_mem (M := K) hy k) hy]

/-- **Every nonzero `RV`-element has an `n`-th root in `RV`** (`n ≥ 1`). -/
theorem exists_rv_root {s : K} (hsrv : iRV s) (hs0 : s ≠ iRVZero) {n : ℕ} (hn : 1 ≤ n) :
    ∃ r : K, iRV r ∧ r ≠ iRVZero ∧ Assembly.rvPow r n = s := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨x, hxVF, hxr⟩ : ∃ x : K, iVF x ∧ iRv x = s := by
    rcases Assembly.RVeqRvVF_of_model (M := K) s hsrv with ⟨x, hx, hxr⟩ | hz
    · exact ⟨x, hx, hxr⟩
    · exact absurd hz hs0
  have hx0 : x ≠ Transfer.iVFZero := by
    intro h
    exact hs0 (by rw [← hxr, h, RVCalc.rv_zero_eq hK])
  obtain ⟨y, hy, hypow⟩ := StandingTree.vf_root (M := K) (hM := hK) hxVF (n := k + 1) (by omega)
  have hy0 : y ≠ Transfer.iVFZero := by
    intro h
    have h1 : StandingTree.vfPow (M := K) y (k + 1) = Transfer.iVFZero := by
      rw [h]; exact StandingTree.vfPow_zero_succ k
    rw [hypow] at h1
    exact hx0 h1
  refine ⟨iRv y, Transfer.rv_mem hK hy, VFValued.rv_ne_zero_of_ne_zero hy hy0, ?_⟩
  rw [rvPow_rv_vfPow hy (k + 1), hypow, hxr]

end Root

/-! ### The two one-element steps of the paper's iteration

The proof of Lemma 3.3 in `qe.tex` (l. 580) is an iteration with exactly two kinds of step:

* the residue-field step: `f₁` is `f` extended from `RV(S)` to `⟨K(M), RV(S)⟩` by a field
  homomorphism `g : K(M) → K(N)`; one element of `K(M)` at a time, this is `UnitsStep`;
* the divisible-hull step: "let `n > 1` be least such that there is `t ∈ RV(M)` with `tⁿ ∈ S₁` but
  `tⁱ ∉ S₁` for `0 < i < n`; let `r ∈ RV(N)` such that `f₁(tⁿ) = rⁿ`", and extend by `t ↦ r`.  One
  step at a time, this is `MDivStep`.

Neither step mentions `Standing`, `KEqTop`-preservation being the only invariant the first needs, and
the second needing the first to have been done (`MDivStep` takes `KEqTop` as a hypothesis).  That the
two steps *suffice* is pure order theory, proved as `prepStepP_of_unitsStep_divStep`: exhaust the
units of `M` (`exists_exhaust` with `P := True`), then take a maximal partial isomorphism whose domain
still contains all units (`zorn_le₀` with `P := KEqTop`), which cannot fail to be `Γ`-divisible
because `MDivStep` would extend it strictly.  Nothing in the two steps is size-theoretic: the size
hypothesis of `M7Paper.PrepStepSize` is *only* needed to prove `UnitsStep` (the paper's field
homomorphism `K(M) → K(N)`, which `‖M‖⁺`-saturation supplies through the transcendence room of
`K(N)`) — see `residueSizeHyp_of_unitsStep`. -/

section Steps

/-- **The residue-field step, one element at a time.**  Every partial isomorphism `M ≃ₚ N` extends to
one whose domain contains a prescribed element of `Kˣ(M)`.

This is the paper's step (i) (`g : K(M) → K(N)`) and nothing else: it is the statement that the
residue field of `M` has room in `N`.  It is *not* size-free — `residueSizeHyp_of_unitsStep` shows it
forces `#Kˣ(M) ≤ #Kˣ(N)`. -/
def UnitsStep : Prop :=
  ∀ (G : M ≃ₚ[LRV] N) (m : M), iUnits m → ∃ G' : M ≃ₚ[LRV] N, G ≤ G' ∧ m ∈ G'.dom

/-- **The divisible-hull step, one element at a time.**  A partial isomorphism whose domain already
contains all of `Kˣ(M)` and whose value group is not divisible extends strictly, and the extension
still contains all of `Kˣ(M)`.

This is the paper's iteration with `t ∈ RV(M)`, `tⁿ ∈ S₁`, `r ∈ RV(N)` with `f₁(tⁿ) = rⁿ`: the
existence of `r` is *not* part of the hypothesis (`exists_rv_root` proves it in `ACVF`), only the
extension of the partial isomorphism by `t ↦ r` is. -/
def MDivStep : Prop :=
  ∀ (G : M ≃ₚ[LRV] N), Assembly.KEqTop G.dom → ¬ Assembly.GammaDivisible G.dom →
    ∃ G' : M ≃ₚ[LRV] N, G ≤ G' ∧ Assembly.KEqTop G'.dom ∧ ∃ m : M, m ∈ G'.dom ∧ m ∉ G.dom

/-- The residues of the two one-element steps at a pair imply the frozen `PrepStepP` at that pair.
No size hypothesis: it is used only to *prove* `UnitsStep`. -/
theorem prepStepP_of_unitsStep_divStep [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (hU : UnitsStep (M := M) (N := N)) (hD : MDivStep (M := M) (N := N)) :
    Assembly.PrepStepP (M := M) (N := N) := by
  intro S f
  -- Step 1: exhaust the residue units of `M`.
  obtain ⟨G₁, hG₀G₁, -, hunits⟩ :=
    exists_exhaust (L := LRV) (M := M) (N := N) (fun _ => True) (fun m => iUnits m)
      (fun _ _ _ _ => trivial)
      (fun G _ m hm => by
        obtain ⟨G', hle, hm'⟩ := hU G m hm
        exact ⟨G', hle, trivial, hm'⟩)
      (embPE f) trivial
  have hK₁ : Assembly.KEqTop G₁.dom := fun m hm => hunits m hm
  -- Step 2: a maximal partial isomorphism above `G₁` preserving `KEqTop` is `Γ`-divisible.
  have hzorn : ∀ c ⊆ {G : M ≃ₚ[LRV] N | G₁ ≤ G ∧ Assembly.KEqTop G.dom},
      IsChain (· ≤ ·) c → ∃ ub ∈ {G : M ≃ₚ[LRV] N | G₁ ≤ ub ∧ Assembly.KEqTop ub.dom},
        ∀ z ∈ c, z ≤ ub := by
    intro c hcs hch
    rcases c.eq_empty_or_nonempty with rfl | hne
    · exact ⟨G₁, ⟨le_rfl, hK₁⟩, by simp⟩
    · have hKc : ∀ z ∈ c, Assembly.KEqTop z.dom := fun z hz => (hcs hz).2
      have hle : G₁ ≤ chainSup c hne hch :=
        (hcs hne.choose_spec).1.trans (le_chainSup hne hch hne.choose_spec)
      exact ⟨chainSup c hne hch,
        ⟨hle, Assembly.KEqTop_chainSup hne hch hKc⟩, fun z hz => le_chainSup hne hch hz⟩
  obtain ⟨G₂, hG₂⟩ := zorn_le₀ {G : M ≃ₚ[LRV] N | G₁ ≤ G ∧ Assembly.KEqTop G.dom} hzorn
  have hG₁G₂ : G₁ ≤ G₂ := hG₂.1.1
  have hK₂ : Assembly.KEqTop G₂.dom := hG₂.1.2
  have hdiv : Assembly.GammaDivisible G₂.dom := by
    by_contra hnot
    obtain ⟨G', hle, hK', m, hm', hm⟩ := hD G₂ hK₂ hnot
    exact hm (PartialEquiv.dom_le_dom (hG₂.2 ⟨hG₁G₂.trans hle, hK'⟩ hle) hm')
  have hST : S ≤ G₂.dom := fun x hx => PartialEquiv.dom_le_dom (hG₀G₁.trans hG₁G₂) hx
  refine ⟨G₂.dom, PartialEquiv.toEmbedding G₂, hST, ?_, hK₂, hdiv⟩
  intro x
  have h1 : (PartialEquiv.toEmbedding G₂ ⟨(x : M), hST x.2⟩ : N)
      = ((G₂.toEquiv ⟨(x : M), hST x.2⟩ : G₂.cod) : N) := rfl
  rw [h1]
  exact agree_of_le f (hG₀G₁.trans hG₁G₂) x (hST x.2)

/-- **The residue-field step forces the residue-field size condition.**  Exhausting the units of `M`
with `UnitsStep` and applying the injective map of the partial isomorphism on units gives
`#Kˣ(M) ≤ #Kˣ(N)`.  Hence the necessarily true cardinal hypothesis of Lemma 3.3 is
`ResidueSizeHyp`, not `M7Paper.SizeHyp` (`#M ≤ #N`). -/
theorem residueSizeHyp_of_unitsStep [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (hU : UnitsStep (M := M) (N := N)) (G₀ : M ≃ₚ[LRV] N) : ResidueSizeHyp M N := by
  obtain ⟨G, -, -, hunits⟩ :=
    exists_exhaust (L := LRV) (M := M) (N := N) (fun _ => True) (fun m => iUnits m)
      (fun _ _ _ _ => trivial)
      (fun G _ m hm => by
        obtain ⟨G', hle, hm'⟩ := hU G m hm
        exact ⟨G', hle, trivial, hm'⟩)
      G₀ trivial
  refine Cardinal.mk_le_of_injective (f := fun x : {x : M // iUnits x} =>
    (⟨PartialEquiv.toEmbedding G ⟨x.1, hunits x.1 x.2⟩,
      units_map_units (PartialEquiv.toEmbedding G) (hunits x.1 x.2) x.2⟩ :
        {y : N // iUnits y})) ?_
  intro a b hab
  have hv : (PartialEquiv.toEmbedding G ⟨a.1, hunits a.1 a.2⟩ : N)
      = PartialEquiv.toEmbedding G ⟨b.1, hunits b.1 b.2⟩ :=
    congrArg (fun z : {y : N // iUnits y} => (z : N)) hab
  have h2 : (⟨a.1, hunits a.1 a.2⟩ : G.dom) = ⟨b.1, hunits b.1 b.2⟩ :=
    (PartialEquiv.toEmbedding G).injective hv
  exact Subtype.ext (congrArg (fun y : G.dom => (y : M)) h2)


/-- The paper's Lemma 3.3 obligations at every pair, assembled: `UnitsStep` (`K(M)` has room in
`K(N)`, the paper's step (i)) and `MDivStep` (the divisible hull of `Γ(S)`, the paper's iteration)
imply the frozen `M7Paper.PrepStepSize`, hence discharge the frozen route's first ingredient. -/
theorem PrepStepSize_of_steps
    (hU : ∀ (P Q : Type) [LRV.Structure P] [LRV.Structure Q] [P ⊨ Axioms.ACVF]
      [Q ⊨ Axioms.ACVF], UnitsStep (M := P) (N := Q))
    (hD : ∀ (P Q : Type) [LRV.Structure P] [LRV.Structure Q] [P ⊨ Axioms.ACVF]
      [Q ⊨ Axioms.ACVF], MDivStep (M := P) (N := Q)) : M7Paper.PrepStepSize :=
  fun P Q _ _ _ _ _ => prepStepP_of_unitsStep_divStep (hU P Q) (hD P Q)

/-! ### The paper's Lemma 3.3 with its three clauses

`qe.tex` l. 580 gives more than the frozen `Assembly.PrepStepP` asks for: `VF(S*) = VF(S)`,
`K(S*) = K(M)` and `Γ(S*)` *the divisible hull* of `Γ(S)`.  The frozen statement keeps only
`KEqTop` and `GammaDivisible`, so the frozen obligation is the weaker one; the paper's version is
recorded here (with the hull clause as "every value in `Γ(T)` has a positive power in `Γ(S)`", which
together with `GammaDivisible T` and the minimality of the divisible hull says that `Γ(T)` *is* the
divisible hull of `Γ(S)`), and `prepStepP_of_paperLemma33` checks that it does imply the frozen
statement. -/

/-- The three clauses of Lemma 3.3 for a pair `S ≤ T` of substructures of a model of `ACVF`:
(1) `VF(T) = VF(S)`; (2) `K(T) = K(M)` (the frozen `KEqTop`); (3) `Γ(T)` is divisible and every
element of `Γ(T)` has a positive power in `Γ(S)` (i.e. `Γ(T)` is contained in the divisible hull of
`Γ(S)`; with `S ≤ T` and `GammaDivisible T` this is `Γ(T) = ` the divisible hull of `Γ(S)`). -/
def Lemma33Clauses (S T : LRV.Substructure M) : Prop :=
  S ≤ T ∧
  (∀ x : M, iVF x → (x ∈ T ↔ x ∈ S)) ∧
  Assembly.KEqTop T ∧
  Assembly.GammaDivisible T ∧
  (∀ t : M, t ∈ T → iRV t → t ≠ iRVZero → ∃ n : ℕ, 1 ≤ n ∧
    ∃ u : M, u ∈ S ∧ iRV u ∧ u ≠ iRVZero ∧
      ∃ c : M, c ∈ S ∧ iUnits c ∧ Assembly.rvPow t n = iRVMul u c)

/-- **Lemma 3.3** (`qe.tex` l. 580) at a fixed pair of models, verbatim in the frozen encoding:
there is a monomorphism `f* : S* → N` extending `f` with the three clauses above. -/
def PaperLemma33 : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N),
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ Lemma33Clauses S T

/-- The paper's Lemma 3.3 implies the frozen `PrepStepP`: the frozen statement drops clause (1) and
the hull half of clause (3), and keeps `KEqTop`, `GammaDivisible`. -/
theorem prepStepP_of_paperLemma33 [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (h : PaperLemma33 (M := M) (N := N)) : Assembly.PrepStepP (M := M) (N := N) := by
  intro S f
  obtain ⟨T, g, hST, hagree, -, -, hK, hdiv, -⟩ := h S f
  exact ⟨T, g, hST, hagree, hK, hdiv⟩

/-- Hence the paper's Lemma 3.3 discharges the frozen route's first ingredient. -/
theorem PrepStepSize_of_paperLemma33
    (h : ∀ (P Q : Type) [LRV.Structure P] [LRV.Structure Q] [P ⊨ Axioms.ACVF]
      [Q ⊨ Axioms.ACVF], PaperLemma33 (M := P) (N := Q)) : M7Paper.PrepStepSize :=
  fun P Q _ _ _ _ _ => prepStepP_of_paperLemma33 (h P Q)

/-! ### The henselization step, and why the frozen statements never mention it

The paper's proof of Proposition 3.9 begins:

> since the henselization `Š^h` of `Š` in `M` is an immediate extension, we have
> `RV(⟨Š^h, Š⟩) = RV(Š)`.  So we may assume that `(VF(Š), O(Š))` is henselian.

`Immediate` below is that "immediate extension" at the level of the frozen encoding (`RV` does not
grow), and `standing_of_immediate` proves what the paper uses it for: the frozen `Standing` cannot
see an immediate extension, so the henselization is invisible to `PrepStep`/`OneStepVFP` **provided
the one-step is available at henselian domains**.  `oneStepVFP_of_hensel` makes that proviso
explicit: for any property `P` of substructures playing the role of "`(VF, O)` henselian", a
one-element step at `P`-domains plus an `Immediate`, `P`-gaining extension step gives the frozen
`OneStepVFP`.  The tree has no henselization existence proof, so `OneStepVFP` is *literally* weaker
than Lemmas 3.4/3.5, which are stated at henselian `Š`. -/

/-- `T` is an **immediate** extension of `S`: it adds no `RV`-sort elements (so `RV(T) = RV(S)`,
hence `K(T) = K(S)` and `Γ(T) = Γ(S)`).  The henselization of `VF(Š)` inside `M` is immediate in
this sense — that is exactly the paper's sentence. -/
def Immediate (S T : LRV.Substructure M) : Prop :=
  S ≤ T ∧ ∀ x : M, x ∈ T → iRV x → x ∈ S

/-- **The frozen `Standing` is invariant under immediate extensions.** -/
theorem standing_of_immediate {S T : LRV.Substructure M} (h : Immediate S T)
    (hS : Assembly.Standing S) : Assembly.Standing T := by
  refine ⟨fun x hx => h.1 (hS.1 x hx), ?_⟩
  intro t ht hrv h0 n hn
  obtain ⟨u, c, hu, hru, hu0, hc, hcu, heq⟩ := hS.2 t (h.2 t ht hrv) hrv h0 n hn
  exact ⟨u, c, h.1 hu, hru, hu0, h.1 hc, hcu, heq⟩

/-- **The henselization step of Proposition 3.9's proof**, as a named obligation: every monomorphism
of a substructure extends along an immediate (hence `Standing`-preserving) extension whose `VF` part
is henselian.  The henselianity clause is the parameter `P` of `oneStepVFP_of_hensel`; existence of
such a `T` with `VF(T) = VF(S)`, `K(T) = K(S)`, `Γ(T) = Γ(S)` and `(VF(T), O(T))` henselian is the
missing classical input (a henselization inside `M`, then unique lifting of `f` by Lemma 3.4). -/
def HenselizationStep (P : LRV.Substructure M → Prop) : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N),
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ Immediate S T ∧ P T

/-- **The frozen one-step needs no henselianity hypothesis** once the one-element step is granted at
henselian (`P`-)domains: henselize immediately (`HenselizationStep P`), apply the step there, and
compose.  This is exactly the paper's "we may assume that `(VF(Š), O(Š))` is henselian". -/
theorem oneStepVFP_of_hensel [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    {P : LRV.Substructure M → Prop}
    (hOne : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Assembly.Standing S → P S →
      ∀ m : M, iVF m → ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
        (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Assembly.Standing T)
    (hHens : HenselizationStep (M := M) (N := N) P) :
    Assembly.OneStepVFP (M := M) (N := N) := by
  intro S f hStand m hm
  obtain ⟨T, g, hST, hagree, himm, hPT⟩ := hHens S f
  obtain ⟨T₂, g₂, hTT₂, hagree₂, hmT₂, hStandT₂⟩ :=
    hOne T g (standing_of_immediate himm hStand) hPT m hm
  refine ⟨T₂, g₂, hST.trans hTT₂, ?_, hmT₂, hStandT₂⟩
  intro x
  have h1 : (⟨(x : M), (hST.trans hTT₂) x.2⟩ : T₂)
      = ⟨(x : M), hTT₂ (hST x.2)⟩ := rfl
  rw [h1, hagree₂ ⟨(x : M), hST x.2⟩, hagree x]

/-! ### Wiring into the tree's headline theorem -/

/-- **Theorem 2.3** with Lemma 3.3 discharged by its two one-element steps: the frozen first
ingredient `M7Paper.PrepStepSize` is supplied by `UnitsStep` (the paper's field homomorphism
`K(M) → K(N)`, one element at a time) and `MDivStep` (the divisible hull of `Γ(S)`, one `n`-th root
at a time).  The remaining hypotheses are exactly `M7Paper`'s other two. -/
theorem paper_theorem_2_3_sat_of_steps
    (hShoen : M7Paper.ShoenfieldTestSat)
    (hU : ∀ (P Q : Type) [LRV.Structure P] [LRV.Structure Q] [P ⊨ Axioms.ACVF]
      [Q ⊨ Axioms.ACVF], UnitsStep (M := P) (N := Q))
    (hD : ∀ (P Q : Type) [LRV.Structure P] [LRV.Structure Q] [P ⊨ Axioms.ACVF]
      [Q ⊨ Axioms.ACVF], MDivStep (M := P) (N := Q))
    (hOne : M7Paper.OneStepSizeFree) : HasQE Axioms.ACVF :=
  M7Paper.paper_theorem_2_3_sat hShoen (PrepStepSize_of_steps hU hD) hOne

/-- The same with the paper's own Lemma 3.3 in place of the two steps. -/
theorem paper_theorem_2_3_sat_of_paperLemma33
    (hShoen : M7Paper.ShoenfieldTestSat)
    (h33 : ∀ (P Q : Type) [LRV.Structure P] [LRV.Structure Q] [P ⊨ Axioms.ACVF]
      [Q ⊨ Axioms.ACVF], PaperLemma33 (M := P) (N := Q))
    (hOne : M7Paper.OneStepSizeFree) : HasQE Axioms.ACVF :=
  M7Paper.paper_theorem_2_3_sat hShoen (PrepStepSize_of_paperLemma33 h33) hOne

/-! ### Where the frozen `PrepStepP` sits: it is equivalent to the extension property given the one-step

`Assembly.standing_top` (`QE/Standing.lean`: every model of `ACVF` is `Standing` at `⊤`) means that
the frozen `PrepStepP` can be obtained from the *extension property* at the pair by taking `T = ⊤`.
Conversely `Assembly.prop39P_noVFGen` obtains the extension property from `PrepStepP` and the frozen
one-step `OneStepVFP`.  So, given `OneStepVFP`, the frozen Lemma 3.3 ingredient is *equivalent* to
Proposition 3.9's conclusion at the pair: it is not a weaker stepping stone in the frozen encoding,
and the paper's Lemma 3.3 is a genuine intermediate only in that it is provable from saturation
(`UnitsStep` + `MDivStep`, `prepStepP_of_unitsStep_divStep`) rather than by exhausting `VF`. -/

/-- The extension property at the pair implies the frozen `PrepStepP` (`T := ⊤`, `Standing ⊤`). -/
theorem prepStepP_of_total_extension [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (h : ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), ∃ g : M ↪[LRV] N,
      ∀ x : S, g (x : M) = f x) : Assembly.PrepStepP (M := M) (N := N) := by
  intro S f
  obtain ⟨g, hg⟩ := h S f
  refine ⟨⊤, g.comp (Substructure.topEquiv (L := LRV) (M := M)).toEmbedding,
    fun _ => by simp, ?_, StandingTree.standing_top⟩
  intro x
  show g ((Substructure.topEquiv (L := LRV) (M := M)).toEmbedding ⟨(x : M), trivial⟩) = f x
  exact hg x

/-- **Given the frozen one-step, the frozen Lemma 3.3 ingredient is equivalent to Proposition 3.9's
conclusion at the pair.** -/
theorem prepStepP_iff_total_extension [hM : M ⊨ Axioms.ACVF] [hN : N ⊨ Axioms.ACVF]
    (hOne : Assembly.OneStepVFP (M := M) (N := N)) :
    Assembly.PrepStepP (M := M) (N := N) ↔
      ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), ∃ g : M ↪[LRV] N,
        ∀ x : S, g (x : M) = f x :=
  ⟨fun hPrep S f => Assembly.prop39P_noVFGen hPrep hOne S f,
    fun h => prepStepP_of_total_extension h⟩

/-- The same at the level of the route's named obligations. -/
theorem PrepStepSize_of_Prop39Size (h : M7Paper.Prop39Size) : M7Paper.PrepStepSize :=
  fun P Q _ _ _ _ hSize => prepStepP_of_total_extension (fun S f => h P Q hSize S f)

/-- **`M7Paper.PrepStepSize` and `M7Paper.Prop39Size` are equivalent given the frozen one-step**
`M7Paper.OneStepSizeFree`: the route's first ingredient is not weaker than its target. -/
theorem PrepStepSize_iff_Prop39Size (hOne : M7Paper.OneStepSizeFree) :
    M7Paper.PrepStepSize ↔ M7Paper.Prop39Size :=
  ⟨fun hPrep => M7Paper.prop39Size_of_two hPrep hOne,
    fun h39 => PrepStepSize_of_Prop39Size h39⟩


end Steps

end M6L33
end Milestone0
end SpecialTransformations

#print axioms SpecialTransformations.Milestone0.M6L33.units_map_units
#print axioms SpecialTransformations.Milestone0.M6L33.prepStepP_forces_unitsN_size
#print axioms SpecialTransformations.Milestone0.M6L33.prepStepSize_forces_unitsN_size
#print axioms SpecialTransformations.Milestone0.M6L33.not_prepStepP_of_unitsN_small
#print axioms SpecialTransformations.Milestone0.M6L33.exists_rv_root
#print axioms SpecialTransformations.Milestone0.M6L33.prepStepP_of_unitsStep_divStep
#print axioms SpecialTransformations.Milestone0.M6L33.residueSizeHyp_of_unitsStep
#print axioms SpecialTransformations.Milestone0.M6L33.PrepStepSize_of_steps
#print axioms SpecialTransformations.Milestone0.M6L33.prepStepP_of_paperLemma33
#print axioms SpecialTransformations.Milestone0.M6L33.PrepStepSize_of_paperLemma33
#print axioms SpecialTransformations.Milestone0.M6L33.standing_of_immediate
#print axioms SpecialTransformations.Milestone0.M6L33.oneStepVFP_of_hensel
#print axioms SpecialTransformations.Milestone0.M6L33.paper_theorem_2_3_sat_of_steps
#print axioms SpecialTransformations.Milestone0.M6L33.paper_theorem_2_3_sat_of_paperLemma33
#print axioms SpecialTransformations.Milestone0.M6L33.prepStepP_of_total_extension
#print axioms SpecialTransformations.Milestone0.M6L33.prepStepP_iff_total_extension
#print axioms SpecialTransformations.Milestone0.M6L33.PrepStepSize_of_Prop39Size
#print axioms SpecialTransformations.Milestone0.M6L33.PrepStepSize_iff_Prop39Size
