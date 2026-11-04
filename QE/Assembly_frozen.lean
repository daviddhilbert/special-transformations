/-
**The frozen-vocabulary assembly of Theorem 2.3**: the paper's Section 3 reduction, stated over
`Milestone0/Encoding.lean`'s own `LRV`, `Axioms.ACVF` and `HasQE`, with the encoding **imported**,
not copied.

     theorem theorem_2_3_quantifier_elimination_of_ingredients
         (hShoen : Assembly.ShoenfieldTest) (hPrep) (hOne) (hVFGen) : HasQE Axioms.ACVF

`hShoen` is Shoenfield's test, `hPrep`/`hOne`/`hVFGen` are the paper's Lemmas 3.3-3.8 and Remark
3.1.  Nothing is `sorry`, no `axiom`, and every declaration's `#print axioms` is
`{propext, Classical.choice, Quot.sound}`.

## Why this file exists

`QE/Reduction_assembly.lean` is a verbatim copy of `Milestone0/Encoding.lean` at commit `d608de6`
(sha256 `78607b94...`), i.e. **before** the guard repair `f18b6f5`.  Its `Axioms.ACVFpaper` is
`vfField ∪ vfAlgClosed ∪ rvGroup ∪ kField ∪ kAlgClosed ∪ preorderRV ∪ rvAxioms` — the frozen one
adds `∪ repairRV ∪ repairRV`, nine axioms — and its `HasQE` is the old unrestricted
`∀ alpha phi, exists psi, IsQF psi and T ⊨ phi ↔ psi`, whereas the frozen one is well-sorted-guarded.
So `theorem_2_3_of_three` in that file is a theorem about a pre-repair snapshot, not about the frozen
target.  `Assembly_val.lean` has the same shape of problem (it embeds its own copy).

The first repair of this was `.ultramath/smw1kqpdp/m8/M8Asm.lean` (member m8), which spliced
`Encoding.lean:1,1880` verbatim in front of `Reduction_assembly.lean`'s Parts B and C and byte-audited
the splice.  That is correct but leaves a third copy of the encoding in the tree, which is the
condition that produced the drift in the first place.  This file is the same assembly with the copy
replaced by `import Enc`, so drift is impossible: the definitions are `Milestone0/Encoding.lean`'s
own.  The only edit to m8's text is that the final declaration cannot keep the frozen name — it is
already taken by the `sorry`-ed target — so it is `..._of_ingredients`.

## What this does NOT do

`Assembly.Saturated` (`QE/Reduction_assembly.lean:1245`, spliced below) is **too strong**: it says
every element's complete type over the image of a substructure is realized, which is Proposition
3.9's own conclusion.  Consequently `Assembly.extensionProperty_of_saturated` derives the extension
property from it with no use of `hPrep`, `hOne` or `hVFGen`, and
`Assembly.shoenfieldTest_iff_hasQE` shows `ShoenfieldTest` is equivalent to the conclusion.  So the
four hypotheses above are **not** a reduction of Theorem 2.3 yet: the file proves the implication, and
the implication is vacuous at this interface.  The repair is sketched in the same place:
`Assembly.SaturatedFS` (finitely satisfiable formula sets), `Assembly.saturatedFS_of_saturated`,
`Assembly.Prop39FS`, `Assembly.ShoenfieldTestFS`, `Assembly.theorem_2_3_of_fs`.  Under `SaturatedFS`
the content of `hPrep`/`hOne`/`hVFGen` is exactly finite satisfiability, which is what Lemmas 3.3-3.8
and Remark 3.1 are for.

Build (the olean for `Enc` is in `.scratch2/sec3/`):

    cp QE/Assembly_frozen.lean .scratch2/sec3/AF.lean && cd .scratch2/sec3 \
      && LEAN_PATH=$PWD:$LEAN_PATH lean AF.lean
-/

import Enc

open FirstOrder FirstOrder.Language
open scoped FirstOrder
open SpecialTransformations.Milestone0.LRV

namespace SpecialTransformations
namespace Milestone0


-- ===== appended verbatim from QE/Reduction_assembly.lean, Parts B and C =====
/-! ## Back-and-forth (general, copied from `BackAndForth.lean`) -/

universe u w w'

variable {L : Language.{u}} {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

/-! ## Unions of chains of partial isomorphisms -/

/-- The index type of a chain is directed. -/
theorem chain_isDirected (c : Set (M ≃ₚ[L] N)) (hch : IsChain (· ≤ ·) c) :
    IsDirectedOrder ↥c :=
  ⟨fun a b => by
    rcases eq_or_ne a b with rfl | hne
    · exact ⟨a, le_rfl, le_rfl⟩
    · rcases hch a.2 b.2 (fun hh => hne (Subtype.ext hh)) with h' | h'
      · exact ⟨b, h', le_rfl⟩
      · exact ⟨a, le_rfl, h'⟩⟩

/-- The union of a nonempty chain of partial isomorphisms `M ≃ₚ[L] N`: a chain in the order of
`PartialEquiv` is a directed system of substructures and the union of the maps is again a partial
isomorphism (`DirectLimit.partialEquivLimit`). -/
noncomputable def chainSup (c : Set (M ≃ₚ[L] N)) (hne : c.Nonempty)
    (hch : IsChain (· ≤ ·) c) : M ≃ₚ[L] N :=
  letI : Nonempty ↥c := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  letI : IsDirectedOrder ↥c := chain_isDirected c hch
  DirectLimit.partialEquivLimit (⟨Subtype.val, fun _ _ hh => hh⟩ : ↥c →o M ≃ₚ[L] N)

/-- Every member of a chain is below its union. -/
theorem le_chainSup {c : Set (M ≃ₚ[L] N)} (hne : c.Nonempty) (hch : IsChain (· ≤ ·) c)
    {z : M ≃ₚ[L] N} (hz : z ∈ c) : z ≤ chainSup c hne hch := by
  letI : Nonempty ↥c := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  letI : IsDirectedOrder ↥c := chain_isDirected c hch
  exact DirectLimit.le_partialEquivLimit (⟨Subtype.val, fun _ _ hh => hh⟩ : ↥c →o M ≃ₚ[L] N)
    ⟨z, hz⟩

/-! ## Exhausting a set of elements -/

/-- **The paper's transfinite bookkeeping**, abstractly.  Let `P` be a property of partial
isomorphisms `M ≃ₚ[L] N` (e.g. "the domain satisfies the standing assumptions of Lemmas 3.4-3.8")
that is preserved by unions of chains, and suppose every `P`-partial isomorphism can be enlarged,
preserving `P`, so that its domain contains any one prescribed element of a set `Q ⊆ M` (the
one-element steps of Lemmas 3.4-3.8).  Then every `P`-partial isomorphism extends to a
`P`-partial isomorphism whose domain contains all of `Q` ("iterating these procedures we may
exhaust all elements"). -/
theorem exists_exhaust (P : (M ≃ₚ[L] N) → Prop) (Q : M → Prop)
    (hsup : ∀ (c : Set (M ≃ₚ[L] N)) (hne : c.Nonempty) (hch : IsChain (· ≤ ·) c),
      (∀ z ∈ c, P z) → P (chainSup c hne hch))
    (hstep : ∀ (G : M ≃ₚ[L] N), P G → ∀ m : M, Q m →
      ∃ G' : M ≃ₚ[L] N, G ≤ G' ∧ P G' ∧ m ∈ G'.dom)
    (G₀ : M ≃ₚ[L] N) (hP₀ : P G₀) :
    ∃ G : M ≃ₚ[L] N, G₀ ≤ G ∧ P G ∧ ∀ m : M, Q m → m ∈ G.dom := by
  let s : Set (M ≃ₚ[L] N) := {G | P G ∧ G₀ ≤ G}
  have hs : G₀ ∈ s := ⟨hP₀, le_rfl⟩
  have hzorn : ∀ c ⊆ s, IsChain (· ≤ ·) c → ∃ ub ∈ s, ∀ z ∈ c, z ≤ ub := by
    intro c hcs hch
    rcases c.eq_empty_or_nonempty with rfl | hne
    · exact ⟨G₀, hs, by simp⟩
    · have hPc : ∀ z ∈ c, P z := fun z hz => (hcs hz).1
      refine ⟨chainSup c hne hch, ⟨hsup c hne hch hPc, ?_⟩, fun z hz => le_chainSup hne hch hz⟩
      exact (hcs hne.choose_spec).2.trans (le_chainSup hne hch hne.choose_spec)
  obtain ⟨G, hG⟩ := zorn_le₀ s hzorn
  · refine ⟨G, hG.1.2, hG.1.1, fun m hm => ?_⟩
    by_contra hmem
    obtain ⟨G', hGG', hPG', hmG'⟩ := hstep G hG.1.1 m hm
    have hG's : G' ∈ s := ⟨hPG', hG.1.2.trans hGG'⟩
    have hle : G' ≤ G := hG.2 hG's hGG'
    exact hmem (PartialEquiv.dom_le_dom hle hmG')

/-! ## The one-element extension property, and full extension -/

/-- The one-element extension property in partial-isomorphism form. -/
def OneStep : Prop := ∀ (f : M ≃ₚ[L] N) (m : M), ∃ g : M ≃ₚ[L] N, f ≤ g ∧ m ∈ g.dom

/-- Every partial isomorphism extends to one whose domain is all of `M`. -/
theorem exists_dom_top (h : OneStep (L := L) (M := M) (N := N)) (f : M ≃ₚ[L] N) :
    ∃ g : M ≃ₚ[L] N, f ≤ g ∧ g.dom = ⊤ := by
  obtain ⟨G, hfG, -, hall⟩ :=
    exists_exhaust (L := L) (M := M) (N := N) (fun _ => True) (fun _ => True)
      (fun _ _ _ _ => trivial) (fun G _ m _ => by obtain ⟨g, h1, h2⟩ := h G m; exact ⟨g, h1, trivial, h2⟩) f trivial
  refine ⟨G, hfG, ?_⟩
  ext x
  exact ⟨fun _ => Substructure.mem_top x, fun _ => hall x trivial⟩

/-- The paper's one-element extension property, in the form used in Lemmas 3.4-3.8: an embedding
of a substructure of `M` into `N` extends to a larger substructure containing a prescribed
element. -/
def OneStepEmb : Prop :=
  ∀ (S : L.Substructure M) (f : S ↪[L] N) (m : M),
    ∃ (T : L.Substructure M) (g : T ↪[L] N) (hST : S ≤ T),
      m ∈ T ∧ ∀ x : S, g ⟨(x : M), hST x.2⟩ = f x

/-- The partial isomorphism associated with an embedding of a substructure. -/
noncomputable def embPE {S : L.Substructure M} (f : S ↪[L] N) : M ≃ₚ[L] N :=
  ⟨S, f.toHom.range, f.equivRange⟩

/-- An embedding of a larger substructure which agrees with `f` on `S` gives a larger partial
isomorphism. -/
theorem embPE_le_of_extends {S T : L.Substructure M} (f : S ↪[L] N) (g : T ↪[L] N)
    (hST : S ≤ T) (hagree : ∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) :
    embPE f ≤ embPE g := by
  rw [PartialEquiv.le_iff]
  refine ⟨hST, ?_, ?_⟩
  · rintro y ⟨x, rfl⟩
    exact ⟨⟨(x : M), hST x.2⟩, hagree x⟩
  · intro x
    apply Subtype.ext
    show (f.equivRange x : N) = (g ⟨(x : M), hST x.2⟩ : N)
    rw [hagree x]
    exact Embedding.equivRange_apply f x

/-- If a partial isomorphism sits above the partial isomorphism of `f`, then it agrees with `f`
on the domain of `f`. -/
theorem agree_of_le {S : L.Substructure M} (f : S ↪[L] N) {G : M ≃ₚ[L] N}
    (hle : embPE f ≤ G) (x : S) (hx : (x : M) ∈ G.dom) :
    ((G.toEquiv ⟨(x : M), hx⟩ : G.cod) : N) = f x := by
  have key := congrArg (fun y : G.cod => (y : N))
    (PartialEquiv.toEquiv_inclusion_apply hle x)
  have harg : (⟨(x : M), hx⟩ : G.dom)
      = Substructure.inclusion (PartialEquiv.dom_le_dom hle) x := Subtype.ext rfl
  rw [harg, key]
  exact Embedding.equivRange_apply f x

/-- The embedding form implies the partial-isomorphism form. -/
theorem oneStep_of_oneStepEmb (h : OneStepEmb (L := L) (M := M) (N := N)) :
    OneStep (L := L) (M := M) (N := N) := by
  intro f m
  obtain ⟨T, g, hST, hmT, hagree⟩ := h f.dom (PartialEquiv.toEmbedding f) m
  refine ⟨⟨T, g.toHom.range, g.equivRange⟩, ?_, ?_⟩
  swap
  · exact hmT
  rw [PartialEquiv.le_iff]
  refine ⟨hST, ?_, ?_⟩
  · rintro y hy
    refine ⟨⟨((f.toEquiv.symm ⟨y, hy⟩ : f.dom) : M), hST (f.toEquiv.symm ⟨y, hy⟩).2⟩, ?_⟩
    show g ⟨((f.toEquiv.symm ⟨y, hy⟩ : f.dom) : M), hST (f.toEquiv.symm ⟨y, hy⟩).2⟩ = y
    rw [hagree]
    simp
  · intro x
    apply Subtype.ext
    show ((f.toEquiv x : f.cod) : N) = (g ⟨(x : M), hST x.2⟩ : N)
    rw [hagree]
    rfl

/-- **Shoenfield's total-extension step**: if every embedding of a substructure of `M` into `N`
can be extended one element at a time, then every embedding of a substructure of `M` into `N`
extends to an embedding defined on all of `M`.  (Proposition 3.9's last step; the one-element
property is what Lemmas 3.2-3.8 and Remark 3.1 supply.) -/
theorem exists_total_embedding (h : OneStepEmb (L := L) (M := M) (N := N))
    (S : L.Substructure M) (f : S ↪[L] N) :
    ∃ g : M ↪[L] N, ∀ x : S, g (x : M) = f x := by
  obtain ⟨G, hle, htop⟩ := exists_dom_top (oneStep_of_oneStepEmb h) (embPE f)
  refine ⟨PartialEquiv.toEmbeddingOfEqTop htop, ?_⟩
  intro x
  rw [PartialEquiv.toEmbeddingOfEqTop_apply]
  exact agree_of_le f hle x (htop.symm ▸ Substructure.mem_top (x : M))

/-! ## Realising an atomic type extends a monomorphism by one element -/

namespace Realize

open FirstOrder FirstOrder.Language

variable {L : Language.{u}} {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]
variable {S : L.Substructure M} {f : S ↪[L] N} {m : M} {b : N}

/-- the parameters of the type, evaluated in `M` -/
def mv (S : L.Substructure M) (m : M) : S ⊕ Unit → M :=
  Sum.elim (fun s => (s : M)) (fun _ => m)

/-- the parameters of the type, evaluated in `N` -/
def wv (f : S ↪[L] N) (b : N) : S ⊕ Unit → N :=
  Sum.elim (fun s => f s) (fun _ => b)

/-- **`b` realises the atomic type of `m` over `S`** (pushed forward by `f`): equalities of
terms with parameters in `S` and the point `m` transfer, and so do relation atoms. -/
def RealizesAtomic (S : L.Substructure M) (f : S ↪[L] N) (m : M) (b : N) : Prop :=
  (∀ (u v : L.Term (S ⊕ Unit)),
      u.realize (mv S m) = v.realize (mv S m) ↔ u.realize (wv f b) = v.realize (wv f b)) ∧
    (∀ (n : ℕ) (r : L.Relations n) (ts : Fin n → L.Term (S ⊕ Unit)),
      Structure.RelMap r (fun i => (ts i).realize (mv S m)) ↔
        Structure.RelMap r (fun i => (ts i).realize (wv f b)))

/-- the generators `↑S ∪ {m}` mapped into `S ⊕ Unit` -/
noncomputable def kappa (S : L.Substructure M) (m : M) (hm : m ∉ S) :
    ↥((S : Set M) ∪ {m}) → S ⊕ Unit := by
  classical
  exact fun y => if h : (y : M) ∈ S then Sum.inl ⟨y.1, h⟩ else Sum.inr ()

theorem mv_kappa (hm : m ∉ S) (y : ↥((S : Set M) ∪ {m})) :
    mv S m (kappa S m hm y) = (y : M) := by
  classical
  unfold kappa mv
  split_ifs with h
  · rfl
  · have hy : (y : M) = m := by
      rcases (show (y : M) = m ∨ (y : M) ∈ S from by simpa using y.2) with h3 | h3
      · simpa using h3
      · exact absurd h3 h
    simp [hy]

/-- the value in `N` of the generators `↑S ∪ {m}` -/
noncomputable def toN (S : L.Substructure M) (f : S ↪[L] N) (b : N) (m : M) (hm : m ∉ S) :
    ↥((S : Set M) ∪ {m}) → N :=
  fun y => wv f b (kappa S m hm y)

theorem realize_mv (hm : m ∉ S) (u : L.Term ↥((S : Set M) ∪ {m})) :
    (u.relabel (kappa S m hm)).realize (mv S m) = u.realize (Subtype.val) := by
  rw [Term.realize_relabel]
  congr 1
  funext y
  exact mv_kappa hm y

theorem realize_wv (hm : m ∉ S) (u : L.Term ↥((S : Set M) ∪ {m})) :
    (u.relabel (kappa S m hm)).realize (wv f b) = u.realize (toN S f b m hm) := by
  rw [Term.realize_relabel]
  rfl

/-- Terms with the same value in `M` have the same value in `N`. -/
theorem realize_eq (hb : RealizesAtomic S f m b) (hm : m ∉ S)
    (t₁ t₂ : L.Term ↥((S : Set M) ∪ {m}))
    (h : t₁.realize (Subtype.val : ↥((S : Set M) ∪ {m}) → M) = t₂.realize Subtype.val) :
    t₁.realize (toN S f b m hm) = t₂.realize (toN S f b m hm) := by
  have h' : (t₁.relabel (kappa S m hm)).realize (mv S m) = (t₂.relabel (kappa S m hm)).realize (mv S m) := by
    rw [realize_mv hm, realize_mv hm]; exact h
  rw [← realize_wv hm, ← realize_wv hm]
  exact (hb.1 _ _).mp h'

/-- Terms with the same value in `N` have the same value in `M`. -/
theorem realize_eq' (hb : RealizesAtomic S f m b) (hm : m ∉ S)
    (t₁ t₂ : L.Term ↥((S : Set M) ∪ {m}))
    (h : t₁.realize (toN S f b m hm) = t₂.realize (toN S f b m hm)) :
    t₁.realize (Subtype.val : ↥((S : Set M) ∪ {m}) → M) = t₂.realize Subtype.val := by
  rw [← realize_wv hm, ← realize_wv hm] at h
  rw [← realize_mv hm, ← realize_mv hm]
  exact (hb.1 _ _).mpr h

/-- the value in `N` of a point of `closure L (↑S ∪ {m})` -/
noncomputable def gfun (f : S ↪[L] N) (b : N) (hm : m ∉ S) (x : M)
    (hx : x ∈ Substructure.closure L ((S : Set M) ∪ {m})) : N :=
  (Classical.choose (Substructure.mem_closure_iff_exists_term.mp hx)).realize (toN S f b m hm)

theorem gfun_spec (hb : RealizesAtomic S f m b) (hm : m ∉ S)
    (t : L.Term ↥((S : Set M) ∪ {m})) :
    gfun f b hm (t.realize (Subtype.val : ↥((S : Set M) ∪ {m}) → M))
        (Term.realize_mem t Subtype.val (fun a => Substructure.subset_closure a.2))
      = t.realize (toN S f b m hm) :=
  realize_eq hb hm _ t
    (Classical.choose_spec (Substructure.mem_closure_iff_exists_term.mp
      (Term.realize_mem t Subtype.val (fun a => Substructure.subset_closure a.2))))



/-- every element of the generated substructure is the value of a term -/
theorem exists_term_eq {x : M} (hx : x ∈ Substructure.closure L ((S : Set M) ∪ {m})) :
    ∃ t : L.Term ↥((S : Set M) ∪ {m}), t.realize (Subtype.val : ↥((S : Set M) ∪ {m}) → M) = x :=
  Substructure.mem_closure_iff_exists_term.mp hx

theorem gfun_eq (hb : RealizesAtomic S f m b) (hm : m ∉ S)
    (t : L.Term ↥((S : Set M) ∪ {m})) (x : M)
    (hx : x ∈ Substructure.closure L ((S : Set M) ∪ {m}))
    (ht : t.realize (Subtype.val : ↥((S : Set M) ∪ {m}) → M) = x) :
    gfun f b hm x hx = t.realize (toN S f b m hm) := by
  unfold gfun
  exact realize_eq hb hm _ t (by rw [Classical.choose_spec (exists_term_eq (S := S) (m := m) hx)]; exact ht.symm)

section OneStep

variable (hb : RealizesAtomic S f m b) (hm : m ∉ S)

/-- The embedding of `closure L (↑S ∪ {m})` in `N` determined by `f` and by the realisation
`b` of the atomic type of `m`. -/
noncomputable def gEmb : ↥(Substructure.closure L ((S : Set M) ∪ {m})) ↪[L] N where
  toFun x := gfun f b hm x.1 x.2
  inj' x y hxy := by
    apply Subtype.ext
    have hx := Classical.choose_spec (exists_term_eq (S := S) (m := m) x.2)
    have hy := Classical.choose_spec (exists_term_eq (S := S) (m := m) y.2)
    have h := realize_eq' hb hm _ _ hxy
    rw [← hx, ← hy]
    exact h
  map_fun' {n} F x := by
    let t : Fin n → L.Term ↥((S : Set M) ∪ {m}) := fun i =>
      Classical.choose (exists_term_eq (S := S) (m := m) (x i).2)
    have hx : ∀ i, (t i).realize (Subtype.val : ↥((S : Set M) ∪ {m}) → M) = (x i).1 :=
      fun i => Classical.choose_spec (exists_term_eq (S := S) (m := m) (x i).2)
    have ht : (Term.func F t).realize (Subtype.val : ↥((S : Set M) ∪ {m}) → M)
        = Structure.funMap F (fun i => (x i).1) := by
      simp only [Term.realize_func]
      congr 1
      funext i
      exact hx i
    show gfun f b hm (Structure.funMap F (fun i => (x i).1)) _ = Structure.funMap F (fun i => gfun f b hm (x i).1 (x i).2)
    rw [gfun_eq hb hm (Term.func F t) (Structure.funMap F (fun i => (x i).1)) _ ht]
    rw [Term.realize_func]
    exact congrArg (Structure.funMap F) (funext fun i => (gfun_eq hb hm (t i) (x i).1 _ (hx i)).symm)
  map_rel' {n} r x := by
    let t : Fin n → L.Term ↥((S : Set M) ∪ {m}) := fun i =>
      Classical.choose (exists_term_eq (S := S) (m := m) (x i).2)
    have hx : ∀ i, (t i).realize (Subtype.val : ↥((S : Set M) ∪ {m}) → M) = (x i).1 :=
      fun i => Classical.choose_spec (exists_term_eq (S := S) (m := m) (x i).2)
    have h := hb.2 n r (fun i => (t i).relabel (kappa S m hm))
    simp only [realize_mv hm, realize_wv hm] at h
    rw [show (fun i => (t i).realize (Subtype.val : ↥((S : Set M) ∪ {m}) → M))
        = (fun i => (x i).1) from funext hx] at h
    rw [show (fun i => (t i).realize (toN S f b m hm))
        = (fun i => gfun f b hm (x i).1 (x i).2) from
      funext fun i => (gfun_eq hb hm (t i) (x i).1 _ (hx i)).symm] at h
    show Structure.RelMap r ((fun y : ↥(Substructure.closure L ((S : Set M) ∪ {m})) =>
      gfun f b hm y.1 y.2) ∘ x) ↔ Structure.RelMap r x
    exact h.symm

/-- **A realisation of the atomic type of one element extends the embedding by that element.** -/
theorem exists_oneStep (hb : RealizesAtomic S f m b) (hm : m ∉ S) :
    ∃ (T : L.Substructure M) (g : T ↪[L] N) (hST : S ≤ T),
      m ∈ T ∧ ∀ x : S, g ⟨(x : M), hST x.2⟩ = f x := by
  refine ⟨Substructure.closure L ((S : Set M) ∪ {m}), gEmb hb hm, ?_, ?_, ?_⟩
  · intro x hx
    exact Substructure.subset_closure (Set.mem_union_left _ hx)
  · exact Substructure.subset_closure (Set.mem_union_right _ (Set.mem_singleton m))
  · intro x
    have hxT : (x : M) ∈ Substructure.closure L ((S : Set M) ∪ {m}) :=
      Substructure.subset_closure (Set.mem_union_left {m} x.2)
    have hk : kappa S m hm (⟨(x : M), Set.mem_union_left {m} x.2⟩ : ↥((S : Set M) ∪ {m}))
        = Sum.inl (⟨(x : M), x.2⟩ : S) := by
      simp only [kappa]
      exact (dif_pos x.2).trans (congrArg Sum.inl (Subtype.ext rfl))
    show gfun f b hm (x : M) hxT = f x
    rw [gfun_eq hb hm (Term.var (⟨(x : M), Set.mem_union_left {m} x.2⟩ : ↥((S : Set M) ∪ {m})))
      (x : M) hxT rfl]
    show toN S f b m hm ⟨(x : M), Set.mem_union_left {m} x.2⟩ = f x
    show wv f b (kappa S m hm ⟨(x : M), Set.mem_union_left {m} x.2⟩) = f x
    rw [hk]
    rfl

end OneStep


/-- Type realisation gives the one-element extension property. -/
theorem oneStepEmb_of_realizesAtomic
    (h : ∀ (S : L.Substructure M) (f : S ↪[L] N) (m : M), m ∉ S → ∃ b : N, RealizesAtomic S f m b) :
    OneStepEmb (L := L) (M := M) (N := N) := by
  intro S f m
  by_cases hm : m ∈ S
  · exact ⟨S, f, le_rfl, hm, fun x => rfl⟩
  · obtain ⟨b, hb⟩ := h S f m hm
    exact exists_oneStep hb hm

/-- **Shoenfield's extension step from type realisability**: if the atomic type of every element
of `M` over every substructure is realisable in `N`, then every monomorphism of a substructure of
`M` into `N` extends to a monomorphism defined on all of `M`. -/
theorem exists_total_embedding_of_realizesAtomic
    (h : ∀ (S : L.Substructure M) (f : S ↪[L] N) (m : M), m ∉ S → ∃ b : N, RealizesAtomic S f m b)
    (S : L.Substructure M) (f : S ↪[L] N) :
    ∃ g : M ↪[L] N, ∀ x : S, g (x : M) = f x :=
  exists_total_embedding (oneStepEmb_of_realizesAtomic h) S f

end Realize
/-! ## Part C. The paper's Section 3.1, assembled

The paper fixes `M, N ⊨ ACVF` with `N` `‖M‖⁺`-saturated, a substructure `S ⊆ M` and a
monomorphism `f : S → N`, and proves Proposition 3.9 (`lrv:mono:lift`): `f` extends to a
monomorphism `M → N`.  The ingredients are Lemma 3.3 (enlarge to a substructure with `K(S) = K(M)`
and `Γ(S)` divisible), Lemmas 3.4-3.8 (add one element of `VF(M)` at a time, preserving those
two properties), and Remark 3.1 together with Weispfenning's QE theorem for `L_v` (extend a
monomorphism whose domain is `VF`-generated, the target being saturated).

Each ingredient is stated below as a named `Prop` with its hypotheses spelled out; everything
that follows is proved from them. -/

namespace Assembly

open Axioms

/-! ### The two standing assumptions of the paper -/

variable {M : Type*} [LRV.Structure M] [M ⊨ ACVF]

/-- the `n`-th power in the `RV` sort -/
def rvPow (x : M) : ℕ → M
  | 0 => iRVOne
  | (n + 1) => iRVMul (rvPow x n) x

/-- `K(S) = K(M)`: every unit of `M` already lies in the substructure `S`.  (`K = Kˣ ∪ {0}` is
the residue field inside the `RV` sort; `0` is in `S` because it is a constant.) -/
def KEqTop (S : LRV.Substructure M) : Prop := ∀ x : M, iUnits x → x ∈ S

/-- `Γ(S)` is divisible.  `Γ = RV / Kˣ`, so an element of `Γ(S)` is `[t]` with `t ∈ RV(S)`,
`t ≠ 0`, and divisibility says: for every `n ≥ 1` there are `u ∈ RV(S)`, `u ≠ 0`, and
`c ∈ Kˣ(S)` with `uⁿ = t · c`. -/
def GammaDivisible (S : LRV.Substructure M) : Prop :=
  ∀ t : M, t ∈ S → iRV t → t ≠ iRVZero → ∀ n : ℕ, 1 ≤ n →
    ∃ u c : M, u ∈ S ∧ iRV u ∧ u ≠ iRVZero ∧ c ∈ S ∧ iUnits c ∧ rvPow u n = iRVMul t c

/-- the paper's standing assumptions after Lemma 3.3 -/
def Standing (S : LRV.Substructure M) : Prop := KEqTop S ∧ GammaDivisible S

/-- `S` is `VF`-generated (the paper's `rv(VF(S)) = RV(S)`): every element of the `RV` sort in
`S` is `rv` of an element of the `VF` sort in `S`, except possibly the absorbing element
`0 = rv(0)`, which is handled by the second disjunct.  (In a model of `ACVF` even that element
has a witness, namely `0` of the `VF` sort — see `RVeqRvVF_of_model`.) -/
def IsVFGen (S : LRV.Substructure M) : Prop :=
  ∀ x : M, x ∈ S → iRV x → (∃ y : M, y ∈ S ∧ iVF y ∧ iRv y = x) ∨ x = iRVZero

/-- In a model of `ACVF` every element of the `RV` sort is `rv` of an element of the `VF` sort,
up to the residue zero: `RV = rv(VF^×) ∪ {0}`, where `0 = ∞ = rv(0)`.  This is the content of the
axiom `Axioms.rvSurj` (the paper's surjectivity of `rv : VF^× → RV^×`, which since the
identification of `0` with `∞` reads "every `RV`-element other than `rv(0)` is `rv(x)`"), so it
is a theorem about models of `ACVF`; `RVeqRvVF_of_model` below proves it.  It is kept as a
named `Prop` because the Section 3.1 argument (Proposition 3.9) uses it as an explicit
hypothesis: the paper derives it from the model-theoretic description of `RV`, the encoding
derives it from the axiom. -/
def RVeqRvVF (M : Type*) [LRV.Structure M] : Prop :=
  ∀ x : M, iRV x → (∃ y : M, iVF y ∧ iRv y = x) ∨ x = iRVZero

/-! ### Reading an encoded axiom off a model

`allSorted ss φ` abbreviates `∀ x̄ ∈ s̄, φ`.  To extract the content of an axiom from a model one
has to unfold `BoundedFormula.alls`, `sortedHyps` and the term constructors; the lemmas below do
that.  They are used once, for `Axioms.rvSurj`. -/

section Realize

open FirstOrder FirstOrder.Language

/-- the assignment that sends the variables `Fin k` to the values `xs` -/
abbrev rho {k : ℕ} (xs : Fin k → M) : Empty ⊕ Fin k → M := Sum.elim default xs

theorem ev_tv {k : ℕ} (xs : Fin k → M) (i : Fin k) :
    Term.realize (rho xs) (LRV.tv i.val i.isLt) = xs i := by
  simp [LRV.tv, rho]

/-- evaluation of an arity-`0` function symbol -/
theorem ev_fun0 {k : ℕ} (xs : Fin k → M) (f : Fn 0) :
    Term.realize (rho xs) (Term.func f (fun i => i.elim0) : LRV.Tm k)
      = Structure.funMap (L := LRV) f (fun i : Fin 0 => i.elim0) := by
  have key : Term.realize (rho xs) (Term.func f (fun i => i.elim0) : LRV.Tm k)
      = Structure.funMap (L := LRV) f
        (fun i : Fin 0 => Term.realize (rho xs) (Fin.elim0 i)) := rfl
  rw [key]
  congr 1
  funext i
  exact i.elim0

@[simp] theorem ev_rvZero {k : ℕ} (xs : Fin k → M) :
    Term.realize (rho xs) (LRV.tRVZero (n := k)) = iRVZero := by
  rw [LRV.tRVZero, ev_fun0]
  rfl

/-- the value of a unary term constructor -/
theorem ev_un {k : ℕ} (xs : Fin k → M) (f : Fn 1) (t : LRV.Tm k) :
    Term.realize (rho xs) (Term.func f ![t] : LRV.Tm k)
      = Structure.funMap (L := LRV) f ![Term.realize (rho xs) t] := by
  have key : Term.realize (rho xs) (Term.func f ![t] : LRV.Tm k)
      = Structure.funMap (L := LRV) f
        (fun i : Fin 1 => Term.realize (rho xs) (![t] i)) := rfl
  rw [key]
  have h1 : (fun i : Fin 1 => Term.realize (rho xs) (![t] i))
      = ![Term.realize (rho xs) t] := by
    funext i
    fin_cases i
    rfl
  rw [h1]

@[simp] theorem ev_rvMap {k : ℕ} (xs : Fin k → M) (t : LRV.Tm k) :
    Term.realize (rho xs) (LRV.tRv t) = iRv (Term.realize (rho xs) t) :=
  ev_un xs Fn.rvMap t

@[simp] theorem real_memRV {k : ℕ} (xs : Fin k → M) (t : LRV.Tm k) :
    (LRV.pRVsort t).Realize (default : Empty → M) xs ↔ iRV (Term.realize (rho xs) t) := by
  have key : (LRV.pRVsort t).Realize (default : Empty → M) xs
      = iRV (Term.realize (rho xs) t) := by
    show Structure.RelMap (L := LRV) Rel.memRV (fun i : Fin 1 => Term.realize (rho xs) (![t] i))
      = Structure.RelMap (L := LRV) Rel.memRV ![Term.realize (rho xs) t]
    have h1 : (fun i : Fin 1 => Term.realize (rho xs) (![t] i))
        = ![Term.realize (rho xs) t] := by
      funext i
      fin_cases i
      rfl
    rw [h1]
  rw [key]

@[simp] theorem real_memVF {k : ℕ} (xs : Fin k → M) (t : LRV.Tm k) :
    (LRV.pVF t).Realize (default : Empty → M) xs ↔ iVF (Term.realize (rho xs) t) := by
  have key : (LRV.pVF t).Realize (default : Empty → M) xs
      = iVF (Term.realize (rho xs) t) := by
    show Structure.RelMap (L := LRV) Rel.memVF (fun i : Fin 1 => Term.realize (rho xs) (![t] i))
      = Structure.RelMap (L := LRV) Rel.memVF ![Term.realize (rho xs) t]
    have h1 : (fun i : Fin 1 => Term.realize (rho xs) (![t] i))
        = ![Term.realize (rho xs) t] := by
      funext i
      fin_cases i
      rfl
    rw [h1]
  rw [key]

@[simp] theorem real_eq {k : ℕ} (xs : Fin k → M) (t u : LRV.Tm k) :
    (LRV.pEq t u).Realize (default : Empty → M) xs ↔
      Term.realize (rho xs) t = Term.realize (rho xs) u := by
  rw [LRV.pEq, FirstOrder.Language.BoundedFormula.realize_bdEqual]

theorem real_sortPred_rv {k : ℕ} (xs : Fin k → M) (t : LRV.Tm k) :
    (LRV.sortPred .rv t).Realize (default : Empty → M) xs ↔ iRV (Term.realize (rho xs) t) :=
  real_memRV xs t

theorem real_sortPred_vf {k : ℕ} (xs : Fin k → M) (t : LRV.Tm k) :
    (LRV.sortPred .vf t).Realize (default : Empty → M) xs ↔ iVF (Term.realize (rho xs) t) :=
  real_memVF xs t

theorem realize_sortedHyps_aux {k : ℕ} (ss : Fin k → SortTag) (l : List (Fin k))
    (xs : Fin k → M) :
    (l.foldr (fun i acc => LRV.sortPred (ss i) (LRV.tv i.val i.isLt) ⊓ acc) ⊤).Realize
        (default : Empty → M) xs ↔
      ∀ i ∈ l, (LRV.sortPred (ss i) (LRV.tv i.val i.isLt)).Realize (default : Empty → M) xs := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

theorem realize_sortedHyps {k : ℕ} (ss : Fin k → SortTag) (xs : Fin k → M) :
    (LRV.sortedHyps ss).Realize (default : Empty → M) xs ↔
      ∀ i : Fin k, (LRV.sortPred (ss i) (LRV.tv i.val i.isLt)).Realize (default : Empty → M) xs := by
  rw [LRV.sortedHyps, realize_sortedHyps_aux]
  exact ⟨fun h i => h i (List.mem_finRange i), fun h i _ => h i⟩

/-- **`M ⊨ allSorted ss φ` unfolded**: for every tuple from the sorts `ss`, `φ` holds. -/
theorem model_allSorted_iff {k : ℕ} (ss : Fin k → SortTag) (φ : LRV.Bf k) :
    M ⊨ LRV.allSorted ss φ ↔
      ∀ xs : Fin k → M,
        (∀ i : Fin k, (LRV.sortPred (ss i) (LRV.tv i.val i.isLt)).Realize
          (default : Empty → M) xs) →
        φ.Realize (default : Empty → M) xs := by
  have h1 : M ⊨ LRV.allSorted ss φ ↔
      ∀ xs : Fin k → M, (LRV.sortedHyps ss ⟹ φ).Realize (default : Empty → M) xs :=
    FirstOrder.Language.BoundedFormula.realize_alls
  refine h1.trans (forall_congr' fun xs => ?_)
  exact (FirstOrder.Language.BoundedFormula.realize_imp).trans
    (imp_congr (realize_sortedHyps ss xs) Iff.rfl)

@[simp] theorem real_exSorted_vf {k : ℕ} (xs : Fin k → M) (φ : LRV.Bf (k + 1)) :
    (LRV.exSorted .vf φ).Realize (default : Empty → M) xs ↔
      ∃ a : M, iVF a ∧ φ.Realize (default : Empty → M) (Fin.snoc xs a) := by
  have h := FirstOrder.Language.BoundedFormula.realize_ex
    (θ := LRV.sortPred .vf (LRV.tv k (Nat.lt_succ_self k)) ⊓ φ)
    (v := (default : Empty → M)) (xs := xs)
  refine h.trans (exists_congr fun a => ?_)
  have h2 : (LRV.sortPred .vf (LRV.tv k (Nat.lt_succ_self k))).Realize
      (default : Empty → M) (Fin.snoc xs a) ↔ iVF a := by
    rw [real_sortPred_vf]
    have htv : Term.realize (rho (Fin.snoc xs a)) (LRV.tv k (Nat.lt_succ_self k)) = a := by
      simp only [LRV.tv, rho, Term.realize_var, Sum.elim_inr]
      exact Fin.snoc_last (α := fun _ => M) a xs
    rw [htv]
  have h3 : ((LRV.sortPred .vf (LRV.tv k (Nat.lt_succ_self k)) ⊓ φ).Realize
      (default : Empty → M) (Fin.snoc xs a)) ↔
      (iVF a ∧ φ.Realize (default : Empty → M) (Fin.snoc xs a)) := by
    rw [FirstOrder.Language.BoundedFormula.realize_inf, h2]
  exact h3

/-- **`RV = rv(VF^×) ∪ {0}` in every model of `ACVF`**: read off the axiom `Axioms.rvSurj`, which
says that every `RV`-element other than `rv(0)` is `rv(x)`. -/
theorem RVeqRvVF_of_model : RVeqRvVF M := by
  intro x hxRV
  by_cases hx0 : x = iRVZero
  · exact Or.inr hx0
  · left
    have hmem : Axioms.rvSurj ∈ Axioms.ACVF := by
      simp [Axioms.ACVF, Axioms.ACVFpaper, Axioms.rvAxioms, Axioms.ofList]
    have hreal : M ⊨ Axioms.rvSurj := Theory.realize_sentence_of_mem (T := Axioms.ACVF) hmem
    have hbody := (model_allSorted_iff ![SortTag.rv] _).mp hreal ![x]
      (fun i => by
        have hi : ![SortTag.rv] i = SortTag.rv := by fin_cases i; rfl
        rw [hi, real_sortPred_rv, ev_tv]
        fin_cases i
        exact hxRV)
    rw [FirstOrder.Language.BoundedFormula.realize_imp,
      FirstOrder.Language.BoundedFormula.realize_not, real_eq, ev_rvZero] at hbody
    have hx0' : Term.realize (rho ![x]) ((&0 : LRV.Tm 1)) ≠ iRVZero := by
      have hx : Term.realize (rho ![x]) ((&0 : LRV.Tm 1)) = x := by simp [rho]
      rwa [hx]
    have hex := hbody hx0'
    rw [real_exSorted_vf] at hex
    obtain ⟨a, haVF, ha⟩ := hex
    refine ⟨a, haVF, ?_⟩
    rw [real_eq, ev_rvMap] at ha
    have h1 : Term.realize (rho (Fin.snoc ![x] a)) ((&1 : LRV.Tm 2)) = a := by
      simp only [rho, Term.realize_var, Sum.elim_inr]
      exact Fin.snoc_last (α := fun _ => M) a ![x]
    have h0 : Term.realize (rho (Fin.snoc ![x] a)) ((&0 : LRV.Tm 2)) = x := by
      simp [rho]
    rw [h1, h0] at ha
    exact ha

end Realize

end Assembly

/-- **Saturation**, recorded in the only form the argument uses: for every model `M` of `ACVF`,
every substructure `S ⊆ M`, every monomorphism `f : S → N` and every `m ∈ M`, the complete type
of `m` over `S` is realised in `N`.  This is a consequence of `N` being `‖M‖⁺`-saturated
(compactness: the type has `|S| + ℵ₀ ≤ ‖M‖` parameters).  Mathlib has no notion of saturation,
so it is left as an explicit hypothesis of the theorems that need it. -/
def Assembly.Saturated (N : Type w) [LRV.Structure N] : Prop :=
  ∀ (M : Type w) [LRV.Structure M] [M ⊨ Axioms.ACVF] (S : LRV.Substructure M)
    (f : S ↪[LRV] N) (m : M),
    ∃ b : N, ∀ (φ : LRV.Formula (S ⊕ Unit)),
      φ.Realize (Sum.elim (fun s => (s : M)) (fun _ => m)) →
      φ.Realize (Sum.elim (fun s => f s) (fun _ => b))

namespace Assembly

open Axioms

section

variable {M : Type*} [LRV.Structure M] [LRV.Structure N] [M ⊨ ACVF] [N ⊨ ACVF]

/-! ### The paper's ingredients, as explicit hypotheses -/

/-- **Lemma 3.3** (unnamed in the paper), together with the henselization step at the start of
the proof of Proposition 3.9: from any monomorphism of a substructure of `M` into `N` one can
pass (using saturation) to one whose domain satisfies `K(S) = K(M)` and `Γ(S)` divisible. -/
def PrepStep (hSat : Saturated N) : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N),
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ Standing T

/-- **Lemmas 3.4-3.8** (`lift:all:root`, `lift:divisible:hull`, `lift:transcendental`,
`e:transc`, `lift:value:full`), in the form in which the proof of Proposition 3.9 uses them: one
element of the `VF` sort can be added to the domain, keeping `K(S) = K(M)` and `Γ(S)` divisible
(Lemma 3.5 keeps the first too, by the proof of `lift:divisible:hull`).  The paper proves this
under the extra case hypotheses of the lemmas and then exhausts `K(M)`; here the case analysis
and the exhaustion are separated, `exists_vf_all` below supplying the exhaustion. -/
def OneStepVF (hSat : Saturated N) : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), Standing S → ∀ m : M, iVF m →
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ m ∈ T ∧ Standing T

/-- **Remark 3.1** (`L:v:and:L:RV`) together with Weispfenning's QE theorem for `L_v`
(Theorem `weis:qe`, an explicit hypothesis of this development, never an axiom): a monomorphism
whose domain is `VF`-generated extends to all of `M` when the target is saturated.

**The `Saturated N` parameter is not optional.**  Without it the statement is false: `⊥` is
`VF`-generated (it contains the constants, and `rv 1` is `rv` of the constant `1`), so the
saturation-free form asserts `∃ g : M ↪[LRV] N` for *every* pair of models of `ACVF`, in particular
an injection from an uncountable model into a countable one.  The paper's step is exactly the
saturated one — `qe.tex:552`: *"If `L` is sufficiently saturated then, by Theorem 2.7, `f'` may be
extended to an `L_v`-monomorphism `f : K → L`"* — and `prop39` already has `hSat` in scope when it
uses this, so demanding it costs nothing. -/
def VFGenCase (hSat : Saturated N) : Prop :=
  ∀ (S : LRV.Substructure M) (f : S ↪[LRV] N), IsVFGen S →
    ∃ g : M ↪[LRV] N, ∀ x : S, g (x : M) = f x

/-! ### `K(S) = K(M)` and divisibility of `Γ(S)` are preserved by unions of chains -/

theorem KEqTop_chainSup {c : Set (M ≃ₚ[LRV] N)} (hne : c.Nonempty)
    (hch : IsChain (· ≤ ·) c) (h : ∀ z ∈ c, KEqTop z.dom) :
    KEqTop (chainSup c hne hch).dom :=
  fun x hx => PartialEquiv.dom_le_dom (le_chainSup hne hch hne.choose_spec)
    (h _ hne.choose_spec x hx)

theorem GammaDivisible_chainSup {c : Set (M ≃ₚ[LRV] N)} (hne : c.Nonempty)
    (hch : IsChain (· ≤ ·) c) (h : ∀ z ∈ c, GammaDivisible z.dom) :
    GammaDivisible (chainSup c hne hch).dom := by
  letI : Nonempty ↥c := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  letI : IsDirectedOrder ↥c := chain_isDirected c hch
  intro t ht hrv h0 n hn
  have hsup : (chainSup c hne hch).dom
      = ⨆ z : ↥c, (z.1 : M ≃ₚ[LRV] N).dom :=
    DirectLimit.dom_partialEquivLimit _
  have hdir : Directed (· ≤ ·) (fun z : ↥c => (z.1 : M ≃ₚ[LRV] N).dom) :=
    Monotone.directed_le (fun _ _ hab => PartialEquiv.dom_le_dom hab)
  have ht' : t ∈ ⨆ z : ↥c, (z.1 : M ≃ₚ[LRV] N).dom := by rw [← hsup]; exact ht
  rw [Substructure.mem_iSup_of_directed hdir] at ht'
  obtain ⟨z, hz⟩ := ht'
  obtain ⟨u, cc, hu, hru, hu0, hc, hcu, heq⟩ := h z.1 z.2 t hz hrv h0 n hn
  have hzle : (z.1 : M ≃ₚ[LRV] N) ≤ chainSup c hne hch := le_chainSup hne hch z.2
  exact ⟨u, cc, PartialEquiv.dom_le_dom hzle hu, hru, hu0,
    PartialEquiv.dom_le_dom hzle hc, hcu, heq⟩

theorem Standing_chainSup {c : Set (M ≃ₚ[LRV] N)} (hne : c.Nonempty)
    (hch : IsChain (· ≤ ·) c) (h : ∀ z ∈ c, Standing z.dom) :
    Standing (chainSup c hne hch).dom :=
  ⟨KEqTop_chainSup hne hch fun z hz => (h z hz).1,
   GammaDivisible_chainSup hne hch fun z hz => (h z hz).2⟩

/-! ### The exhaustion step -/

/-- Lemmas 3.4-3.8 in partial-isomorphism form: they are about monomorphisms of substructures,
which is the same data as a partial isomorphism (its codomain is the range). -/
theorem oneStepVF_pe (hSat : Saturated N) (h : OneStepVF (M := M) (N := N) hSat) :
    ∀ (G : M ≃ₚ[LRV] N), Standing G.dom → ∀ m : M, iVF m →
      ∃ G' : M ≃ₚ[LRV] N, G ≤ G' ∧ Standing G'.dom ∧ m ∈ G'.dom := by
  intro G hStandG m hm
  obtain ⟨T, g, hGT, hagree, hmT, hStandT⟩ := h G.dom (PartialEquiv.toEmbedding G) hStandG m hm
  refine ⟨embPE g, ?_, hStandT, hmT⟩
  rw [PartialEquiv.le_iff]
  refine ⟨hGT, ?_, ?_⟩
  · rintro y hy
    refine ⟨⟨((G.toEquiv.symm ⟨y, hy⟩ : G.dom) : M), hGT (G.toEquiv.symm ⟨y, hy⟩).2⟩, ?_⟩
    show g ⟨((G.toEquiv.symm ⟨y, hy⟩ : G.dom) : M), hGT (G.toEquiv.symm ⟨y, hy⟩).2⟩ = y
    rw [hagree]
    simp
  · intro x
    apply Subtype.ext
    show ((G.toEquiv x : G.cod) : N) = (g ⟨(x : M), hGT x.2⟩ : N)
    rw [hagree]
    rfl

/-- **The paper's exhaustion** ("iterating these procedures we may exhaust all elements in
`K(M)`"): from Lemma 3.3 and Lemmas 3.4-3.8, every monomorphism of a substructure of `M` into
`N` extends to one whose domain contains every element of the `VF` sort of `M`. -/
theorem exists_vf_all (hSat : Saturated N) (hPrep : PrepStep (M := M) (N := N) hSat)
    (hOne : OneStepVF (M := M) (N := N) hSat) (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    ∃ (T : LRV.Substructure M) (g : T ↪[LRV] N) (hST : S ≤ T),
      (∀ x : S, g ⟨(x : M), hST x.2⟩ = f x) ∧ (∀ y : M, iVF y → y ∈ T) := by
  obtain ⟨T₀, f₀, hST₀, hagree₀, hStand₀⟩ := hPrep S f
  obtain ⟨G, hG₀G, hStand, hall⟩ :=
    exists_exhaust (L := LRV) (M := M) (N := N) (fun G => Standing G.dom) (fun m => iVF m)
      (fun c hne hch hP => Standing_chainSup hne hch hP)
      (oneStepVF_pe hSat hOne) (embPE f₀) hStand₀
  refine ⟨G.dom, PartialEquiv.toEmbedding G, hST₀.trans (PartialEquiv.dom_le_dom hG₀G), ?_, hall⟩
  intro x
  have h1 : (PartialEquiv.toEmbedding G
        ⟨(x : M), PartialEquiv.dom_le_dom hG₀G (hST₀ x.2)⟩ : N)
      = ((G.toEquiv ⟨(x : M), PartialEquiv.dom_le_dom hG₀G (hST₀ x.2)⟩ : G.cod) : N) := rfl
  rw [h1, agree_of_le f₀ hG₀G ⟨(x : M), hST₀ x.2⟩ (PartialEquiv.dom_le_dom hG₀G (hST₀ x.2))]
  exact hagree₀ x

/-- A substructure containing all `VF` elements of `M` is `VF`-generated, in a model of `ACVF`. -/
theorem isVFGen_of_vf_all (hRv : RVeqRvVF M) {T : LRV.Substructure M}
    (hT : ∀ y : M, iVF y → y ∈ T) : IsVFGen T := by
  intro x hxS hxRV
  rcases hRv x hxRV with ⟨y, hyVF, hyx⟩ | hzero
  · exact Or.inl ⟨y, hT y hyVF, hyVF, hyx⟩
  · exact Or.inr hzero

/-- **Proposition 3.9** (`lrv:mono:lift`), proved from the paper's Lemmas 3.3-3.8 and
Remark 3.1. -/
theorem prop39 (hSat : Saturated N) (hRv : RVeqRvVF M)
    (hPrep : PrepStep (M := M) (N := N) hSat) (hOne : OneStepVF (M := M) (N := N) hSat)
    (hVFGen : VFGenCase (M := M) (N := N) hSat) (S : LRV.Substructure M) (f : S ↪[LRV] N) :
    ∃ g : M ↪[LRV] N, ∀ x : S, g (x : M) = f x := by
  obtain ⟨T, g, hST, hagree, hall⟩ := exists_vf_all hSat hPrep hOne S f
  obtain ⟨g', hg'⟩ := hVFGen T g (isVFGen_of_vf_all hRv hall)
  exact ⟨g', fun x => by rw [hg' ⟨(x : M), hST x.2⟩, hagree x]⟩

end

/-! ### Theorem 3.10 -/

/-- **Shoenfield's test** in the frozen encoding, in the form used for Theorem 3.10: the
extension property of Proposition 3.9 implies quantifier elimination.  This is the hard
direction of Shoenfield's criterion; the easy direction (QE implies the extension property, the
step used in Remark 3.1) is the general back-and-forth machinery of Part B. -/
def ShoenfieldTest : Prop :=
  (∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ ACVF] [N ⊨ ACVF]
      (hSat : Saturated N) (S : LRV.Substructure M) (f : S ↪[LRV] N),
      ∃ g : M ↪[LRV] N, ∀ x : S, g (x : M) = f x) →
    HasQE ACVF

/-- **The paper's Section 3.1 in one structure**: the four algebraic ingredients, uniformly in
the models.  (Weispfenning's QE theorem for `L_v` enters through `vfgen`, via Remark 3.1;
saturation enters each of them.) -/
structure AlgIngredients : Prop where
  /-- `RV = rv(VF^×) ∪ {0}`: this is the content of the axiom `Axioms.rvSurj` (the paper's
  surjectivity of `rv`), so it is a *theorem* (`RVeqRvVF_of_model`).  It is kept as a field so
  that `theorem_2_3_of_hypotheses` keeps the shape it had; `theorem_2_3_of_three` discharges
  it. -/
  rv : ∀ (M : Type) [LRV.Structure M], M ⊨ ACVF → RVeqRvVF M
  /-- Lemma 3.3 + henselization -/
  prep : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ ACVF] [N ⊨ ACVF]
    (hSat : Saturated N), PrepStep (M := M) (N := N) hSat
  /-- Lemmas 3.4-3.8 -/
  one : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ ACVF] [N ⊨ ACVF]
    (hSat : Saturated N), OneStepVF (M := M) (N := N) hSat
  /-- Remark 3.1 + Weispfenning's QE theorem for `L_v` -/
  vfgen : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ ACVF] [N ⊨ ACVF]
    (hSat : Saturated N), VFGenCase (M := M) (N := N) hSat

/-- **Theorem 3.10 of arXiv:1006.1393 = Theorem 2.3 of arXiv:1006.2467**, modulo the four
hypotheses listed in `AlgIngredients` and the hard direction of Shoenfield's test. -/
theorem theorem_2_3_of_hypotheses (hShoen : ShoenfieldTest) (hAlg : AlgIngredients) :
    HasQE ACVF := by
  apply hShoen
  intro M N _ _ hM hN hSat S f
  exact prop39 hSat (hAlg.rv M hM) (hAlg.prep M N hSat) (hAlg.one M N hSat) (hAlg.vfgen M N hSat) S f

/-- **Theorem 3.10 with the `RV = rv(VF^×) ∪ {0}` hypothesis discharged.**  Since the axiom
`Axioms.rvSurj` is the paper's surjectivity of `rv` (every `RV`-element other than `rv(0)` is
`rv(x)`), the first ingredient of `AlgIngredients` is a theorem (`RVeqRvVF_of_model`), and only
the three remaining ingredients are needed.  (Before the identification of `0` with `∞` the axiom
was guarded by `Kˣ` and this hypothesis could not be discharged.) -/
theorem theorem_2_3_of_three (hShoen : ShoenfieldTest)
    (hPrep : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ ACVF] [N ⊨ ACVF]
      (hSat : Saturated N), PrepStep (M := M) (N := N) hSat)
    (hOne : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ ACVF] [N ⊨ ACVF]
      (hSat : Saturated N), OneStepVF (M := M) (N := N) hSat)
    (hVFGen : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ ACVF] [N ⊨ ACVF]
      (hSat : Saturated N), VFGenCase (M := M) (N := N) hSat) :
    HasQE ACVF :=
  theorem_2_3_of_hypotheses hShoen
    { rv := fun M _ _ => RVeqRvVF_of_model (M := M)
      prep := hPrep
      one := hOne
      vfgen := hVFGen }

end Assembly

/-! ## Wiring to the frozen target

Everything above this point is `Milestone0/Encoding.lean` lines 1–1880 verbatim (checked by
`audit.sh`), so `HasQE`, `WellSorted`, `sortEval` and `Axioms.ACVF` below are *the frozen ones* —
including `repairRV` in `ACVF` and the well-sorted, `sortEval`-relativised `HasQE` — and the
reduction of `QE/Reduction_assembly.lean` (Parts B and C, appended verbatim) is here re-elaborated
against them.

`QE/Reduction_assembly.lean` carries the **pre-repair** copy of the encoding
(`git show d608de6:Milestone0/Encoding.lean`, sha256 `78607b94…`).  Against that copy its
`theorem_2_3_of_three` proves the *unrestricted* `HasQE`, which is refuted in the tree
(`QE-PLAN.md`), and its `Axioms.ACVF` lacks `repairRV`.  So the tree's statement is not the frozen
one; the statements below are. -/

namespace Assembly

open Axioms

/-! ### What `Assembly.Saturated` already gives

`Assembly.Saturated N` asserts, for *every* monomorphism `f : S ↪[LRV] N` and every `m : M`, the
realization of the **complete** type of `m` over `S` pushed by `f` — with no consistency
requirement on that type.  Genuine saturation only realizes *consistent* types, so `Saturated` is
strictly stronger than saturation, and strong enough to give the extension property outright: -/

/-- Realization of the complete type implies realization of the atomic type, hence
`Realize.RealizesAtomic`, hence (by the back-and-forth machinery of Part B) the one-element and
then the total extension. -/
theorem realizesAtomic_of_saturated {M N : Type} [LRV.Structure M] [LRV.Structure N]
    [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF] (hSat : Saturated N)
    (S : LRV.Substructure M) (f : S ↪[LRV] N) (m : M) :
    ∃ b : N, Realize.RealizesAtomic S f m b := by
  classical
  obtain ⟨b, hb⟩ := hSat M S f m
  have hb' : ∀ φ : LRV.Formula (S ⊕ Unit),
      φ.Realize (Realize.mv S m) → φ.Realize (Realize.wv f b) := hb
  have key : ∀ (u v : LRV.Term (S ⊕ Unit)),
      (u.realize (Realize.mv S m) = v.realize (Realize.mv S m) ↔
        u.realize (Realize.wv f b) = v.realize (Realize.wv f b)) := by
    intro u v
    constructor
    · intro h
      have h2 : (Term.equal u v).Realize (Realize.wv f b) := hb' (Term.equal u v) (by
        simpa only [Formula.realize_equal] using h)
      simpa only [Formula.realize_equal] using h2
    · intro h
      by_contra hc
      have h1 : (Term.equal u v).not.Realize (Realize.mv S m) := by
        simpa only [Formula.realize_not, Formula.realize_equal] using hc
      have h2 : ¬ (Term.equal u v).Realize (Realize.wv f b) := hb' (Term.equal u v).not h1
      exact h2 (by simpa only [Formula.realize_equal] using h)
  have keyR : ∀ (n : ℕ) (r : LRV.Relations n) (ts : Fin n → LRV.Term (S ⊕ Unit)),
      (Structure.RelMap r (fun i => (ts i).realize (Realize.mv S m)) ↔
        Structure.RelMap r (fun i => (ts i).realize (Realize.wv f b))) := by
    intro n r ts
    constructor
    · intro h
      have h2 : (r.formula ts).Realize (Realize.wv f b) := hb' (r.formula ts) (by
        simpa only [Formula.realize_rel] using h)
      simpa only [Formula.realize_rel] using h2
    · intro h
      by_contra hc
      have h1 : (r.formula ts).not.Realize (Realize.mv S m) := by
        simpa only [Formula.realize_not, Formula.realize_rel] using hc
      have h2 : ¬ (r.formula ts).Realize (Realize.wv f b) := hb' (r.formula ts).not h1
      exact h2 (by simpa only [Formula.realize_rel] using h)
  exact ⟨b, fun u v => key u v, fun n r ts => keyR n r ts⟩

/-- **The extension property of Proposition 3.9 follows from `Saturated` alone** — with no use of
Lemmas 3.3–3.8 and none of Remark 3.1. -/
theorem extensionProperty_of_saturated :
    ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF]
      (hSat : Saturated N) (S : LRV.Substructure M) (f : S ↪[LRV] N),
      ∃ g : M ↪[LRV] N, ∀ x : S, g (x : M) = f x := by
  intro M N _ _ _ _ hSat S f
  exact Realize.exists_total_embedding_of_realizesAtomic
    (fun S f m _ => realizesAtomic_of_saturated hSat S f m) S f

/-- **`ShoenfieldTest` is therefore equivalent to its own conclusion.**  Its antecedent is a
theorem, so the tree's criterion `(extension property) → HasQE` says nothing more than `HasQE`. -/
theorem shoenfieldTest_iff_hasQE : ShoenfieldTest ↔ HasQE Axioms.ACVF :=
  ⟨fun h => h extensionProperty_of_saturated, fun h _ => h⟩

/-- In particular the three Section 3.1 ingredients are *not needed* to reach the frozen target
from `ShoenfieldTest`. -/
theorem hasQE_of_shoenfieldTest_only (h : ShoenfieldTest) : HasQE Axioms.ACVF :=
  h extensionProperty_of_saturated

/-! ### The repair: `Saturated` with the consistency requirement restored

`SaturatedFS` requires realization only for types that are *finitely satisfiable* over the pushed
parameters — which is what `‖M‖⁺`-saturation of `N` gives, by compactness.  The difference is
exactly the mathematical content of Shoenfield's test: for a theory without QE the pushed type need
not be finitely satisfiable, so `SaturatedFS` does not imply the extension property. -/

/-- **Finitely satisfiable type realization.**  Given that every formula of the type of `m` over `S`
is realized in `N` over the pushed parameters (finite satisfiability — a conjunction of such
formulas is itself such a formula), the whole type is realized. -/
def SaturatedFS (N : Type) [LRV.Structure N] : Prop :=
  ∀ (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF] (S : LRV.Substructure M)
    (f : S ↪[LRV] N) (m : M),
    (∀ (φ : LRV.Formula (S ⊕ Unit)),
        φ.Realize (Realize.mv S m) → ∃ b : N, φ.Realize (Realize.wv f b)) →
      ∃ b : N, ∀ (φ : LRV.Formula (S ⊕ Unit)),
        φ.Realize (Realize.mv S m) → φ.Realize (Realize.wv f b)

/-- The tree's `Saturated` is the special case with no satisfiability hypothesis. -/
theorem saturatedFS_of_saturated {N : Type} [LRV.Structure N] (h : Saturated N) :
    SaturatedFS N :=
  fun M _ _ S f m _ => h M S f m

/-- **Proposition 3.9 at `SaturatedFS`** — the paper's extension property with the saturation
notion that does not already assert it.  This is what the three Section 3.1 lemma-props must be
shown to give (they must be restated at `SaturatedFS`: proving finite satisfiability of the pushed
type is then part of their content, which is exactly the paper's work). -/
def Prop39FS : Prop :=
  ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF]
    (hSat : SaturatedFS N) (S : LRV.Substructure M) (f : S ↪[LRV] N),
    ∃ g : M ↪[LRV] N, ∀ x : S, g (x : M) = f x

/-- **Shoenfield's test with the consistency requirement restored**: the criterion to prove next.
Its antecedent is *not* a theorem (unlike the one of `ShoenfieldTest`), so this statement is not
equivalent to `HasQE` by the argument above; it is Shoenfield's hard direction in the form the
paper uses it. -/
def ShoenfieldTestFS : Prop := Prop39FS → HasQE Axioms.ACVF

/-- The composite step, for the next session: a proof of `ShoenfieldTestFS` and of `Prop39FS` at
`SaturatedFS` gives the frozen Theorem 2.3 outright — with no other hypothesis. -/
theorem theorem_2_3_of_fs (hShoen : ShoenfieldTestFS) (h39 : Prop39FS) : HasQE Axioms.ACVF :=
  hShoen h39

/-! ### The paper's Section 3.1, from the three lemma-props -/

/-- The paper's Section 3.1 in one structure, from the three lemma-props, with the `RV`-field
`rv` **discharged** (`RVeqRvVF_of_model`, proved from the frozen axiom `rvSurj`). -/
theorem algIngredients_of_three
    (hPrep : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF] (hSat : Saturated N), PrepStep (M := M) (N := N) hSat)
    (hOne : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF] (hSat : Saturated N), OneStepVF (M := M) (N := N) hSat)
    (hVFGen : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF] (hSat : Saturated N), VFGenCase (M := M) (N := N) hSat) :
    AlgIngredients where
  rv := fun M _ _ => RVeqRvVF_of_model (M := M)
  prep := hPrep
  one := hOne
  vfgen := hVFGen

end Assembly

/-- **Theorem 2.3** (Yin, *Special transformations in algebraically closed valued fields*, APAL
2010; quoted there from arXiv:1006.1393, Theorem 3.10): the theory `ACVF` admits quantifier
elimination — the frozen statement of `Milestone0/Encoding.lean` (same name, same conclusion
`HasQE Axioms.ACVF`, definitions byte-identical), **modulo the four hypotheses named here**:
`hShoen` (Shoenfield's test), `hPrep` (Lemma 3.3 + henselization), `hOne` (Lemmas 3.4–3.8) and
`hVFGen` (Remark 3.1 + Weispfenning) — the last three in the form `Assembly.PrepStep`,
`Assembly.OneStepVF`, `Assembly.VFGenCase`.

**Read the audit**: `Assembly.shoenfieldTest_iff_hasQE` proves that `hShoen` is *equivalent to the
conclusion* under the tree's `Assembly.Saturated`, and
`Assembly.extensionProperty_of_saturated` proves that Proposition 3.9's conclusion needs none of
`hPrep`, `hOne`, `hVFGen`.  So this theorem is true but its hypotheses are not a reduction of
Theorem 2.3: the content has to come from `Assembly.ShoenfieldTestFS` together with the three
lemma-props restated at `Assembly.SaturatedFS`. -/
theorem theorem_2_3_quantifier_elimination_of_ingredients (hShoen : Assembly.ShoenfieldTest)
    (hPrep : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF] (hSat : Assembly.Saturated N),
      Assembly.PrepStep (M := M) (N := N) hSat)
    (hOne : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF] (hSat : Assembly.Saturated N),
      Assembly.OneStepVF (M := M) (N := N) hSat)
    (hVFGen : ∀ (M N : Type) [LRV.Structure M] [LRV.Structure N] [M ⊨ Axioms.ACVF]
      [N ⊨ Axioms.ACVF] (hSat : Assembly.Saturated N), Assembly.VFGenCase (M := M) (N := N) hSat) :
    HasQE Axioms.ACVF :=
  Assembly.theorem_2_3_of_three hShoen hPrep hOne hVFGen

end Milestone0
end SpecialTransformations

#print axioms SpecialTransformations.Milestone0.Assembly.RVeqRvVF_of_model
#print axioms SpecialTransformations.Milestone0.Assembly.prop39
#print axioms SpecialTransformations.Milestone0.Assembly.realizesAtomic_of_saturated
#print axioms SpecialTransformations.Milestone0.Assembly.extensionProperty_of_saturated
#print axioms SpecialTransformations.Milestone0.Assembly.shoenfieldTest_iff_hasQE
#print axioms SpecialTransformations.Milestone0.Assembly.hasQE_of_shoenfieldTest_only
#print axioms SpecialTransformations.Milestone0.Assembly.saturatedFS_of_saturated
#print axioms SpecialTransformations.Milestone0.Assembly.theorem_2_3_of_fs
#print axioms SpecialTransformations.Milestone0.Assembly.algIngredients_of_three
#print axioms SpecialTransformations.Milestone0.Assembly.theorem_2_3_of_hypotheses
#print axioms SpecialTransformations.Milestone0.theorem_2_3_quantifier_elimination_of_ingredients
