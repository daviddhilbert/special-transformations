import Mathlib.ModelTheory.PartialEquiv
import Mathlib.Order.Zorn
import Mathlib.Tactic.SplitIfs

/-! Generic chain unions, Zorn exhaustion, and atomic-type packaging extracted
from QE/BackAndForth.lean. Proofs are unchanged; the namespace is isolated.
Used for genuine saturation-to-extension arguments. -/

set_option linter.style.haveILetI false

open FirstOrder FirstOrder.Language

namespace QESaturatedBackAndForth

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

end QESaturatedBackAndForth

#print axioms QESaturatedBackAndForth.embPE_le_of_extends
#print axioms QESaturatedBackAndForth.agree_of_le
#print axioms QESaturatedBackAndForth.exists_exhaust
#print axioms QESaturatedBackAndForth.exists_dom_top
#print axioms QESaturatedBackAndForth.exists_total_embedding
#print axioms QESaturatedBackAndForth.Realize.exists_oneStep
#print axioms QESaturatedBackAndForth.Realize.exists_total_embedding_of_realizesAtomic
