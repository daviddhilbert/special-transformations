import Section4.TupleFamilies
import CanonicalRV

set_option backward.isDefEq.respectTransparency false

/-!
# Separating the fibres of a finite definable equivalence relation

The parameter tuples may be multiple representatives of an imaginary value.
Coherence says that two intersecting fibres coincide. No section of an
imaginary quotient is required to be definable.
-/

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace SpecialTransformations.Section4.FiniteRefinement

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {m n r : ℕ}

abbrev MixedTuple (n r : ℕ) := (Fin n → VFType (M := M)) × (Fin r → CanonicalRV.RVSort M)

def values (x : MixedTuple (M := M) n r) : Fin n ⊕ Fin r → M :=
  Sum.elim (TupleFamilies.values x.1) (fun j => (x.2 j).val)

theorem values_injective : Function.Injective (values (M := M) (n := n) (r := r)) := by
  intro x y he
  apply Prod.ext
  · funext i
    exact Subtype.ext (congrFun he (.inl i))
  · funext j
    exact Subtype.ext (congrFun he (.inr j))

def RelationDefinable (S : Set M)
    (G : Set ((Fin m → M) × MixedTuple (M := M) n r)) : Prop :=
  S.Definable LRV {z : Fin m ⊕ (Fin n ⊕ Fin r) → M |
    ∃ x, (z ∘ Sum.inl, x) ∈ G ∧ values x = z ∘ Sum.inr}

def vfProjection (G : Set ((Fin m → M) × MixedTuple (M := M) n r)) :
    Set ((Fin m → M) × (Fin n → VFType (M := M))) :=
  {p | ∃ s, (p.1, (p.2, s)) ∈ G}

theorem vfProjection_definable (S : Set M)
    (G : Set ((Fin m → M) × MixedTuple (M := M) n r))
    (hG : RelationDefinable S G) : TupleFamilies.RelationDefinable S (vfProjection G) := by
  have h := hG.image_comp (Sum.map id (Sum.inl : Fin n → Fin n ⊕ Fin r))
  change S.Definable LRV _
  convert h using 1
  ext z
  constructor
  · rintro ⟨x, ⟨s, hx⟩, he⟩
    refine ⟨Sum.elim (z ∘ Sum.inl) (values (x, s)), ⟨(x, s), hx, rfl⟩, ?_⟩
    funext j
    cases j with
    | inl j => rfl
    | inr j => exact congrFun he j
  · rintro ⟨w, ⟨x, hx, he⟩, hw⟩
    have ht : w ∘ Sum.inl = z ∘ Sum.inl := by
      funext j
      exact congrFun hw (.inl j)
    refine ⟨x.1, ⟨x.2, ht ▸ hx⟩, ?_⟩
    funext j
    exact (congrFun he (.inl j)).trans (congrFun hw (.inr j))

theorem vfProjection_finite
    (G : Set ((Fin m → M) × MixedTuple (M := M) n r))
    (hfinite : ∀ t, {x | (t, x) ∈ G}.Finite) (t : Fin m → M) :
    {x | (t, x) ∈ vfProjection G}.Finite := by
  convert (hfinite t).image Prod.fst using 1
  ext x
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨(x, s), hs, rfl⟩
  · rintro ⟨⟨a, s⟩, hs, rfl⟩
    exact ⟨s, hs⟩

def support (G : Set ((Fin m → M) × MixedTuple (M := M) n r)) :
    Set (MixedTuple (M := M) n r) := {x | ∃ t, (t, x) ∈ G}

/-- The nondefinable representative is used only to define a function whose
complete graph is then proved definable by existential quantification. -/
noncomputable def representative
    (G : Set ((Fin m → M) × MixedTuple (M := M) n r)) (x : support G) : Fin m → M :=
  Classical.choose x.property

theorem representative_mem
    (G : Set ((Fin m → M) × MixedTuple (M := M) n r)) (x : support G) :
    (representative G x, x.val) ∈ G := Classical.choose_spec x.property

noncomputable def separator (d : ℕ)
    (G : Set ((Fin m → M) × MixedTuple (M := M) n r))
    (hfinite : ∀ t, {x | (t, x) ∈ G}.Finite)
    (x : support G) : Fin r ⊕ Fin (n * d) → M :=
  Sum.elim (fun j => (x.val.2 j).val)
    (TupleFamilies.code d (vfProjection G) (vfProjection_finite G hfinite)
      (representative G x) (TupleFamilies.values x.val.1))

def Coherent (G : Set ((Fin m → M) × MixedTuple (M := M) n r)) : Prop :=
  ∀ t u x, (t, x) ∈ G → (u, x) ∈ G → ∀ y, (t, y) ∈ G ↔ (u, y) ∈ G

theorem projection_fibres_eq
    (G : Set ((Fin m → M) × MixedTuple (M := M) n r)) (hcoh : Coherent G)
    (t u : Fin m → M) (x : MixedTuple (M := M) n r)
    (ht : (t, x) ∈ G) (hu : (u, x) ∈ G) (a : Fin n → VFType (M := M)) :
    (t, a) ∈ vfProjection G ↔ (u, a) ∈ vfProjection G :=
  exists_congr (fun s => hcoh t u x ht hu (a, s))

theorem separator_eq (d : ℕ)
    (G : Set ((Fin m → M) × MixedTuple (M := M) n r))
    (hfinite : ∀ t, {x | (t, x) ∈ G}.Finite) (hcoh : Coherent G)
    (t : Fin m → M) (x : support G) (ht : (t, x.val) ∈ G) :
    separator d G hfinite x = Sum.elim (fun j => (x.val.2 j).val)
      (TupleFamilies.code d (vfProjection G) (vfProjection_finite G hfinite)
        t (TupleFamilies.values x.val.1)) := by
  unfold separator
  rw [TupleFamilies.code_fibre_invariant _ _ (representative G x) t
    (projection_fibres_eq G hcoh _ _ x.val (representative_mem G x) ht)]

theorem separator_sorted (d : ℕ)
    (G : Set ((Fin m → M) × MixedTuple (M := M) n r))
    (hfinite : ∀ t, {x | (t, x) ∈ G}.Finite)
    (hsorted : ∀ t (x : Fin n → VFType (M := M)) k,
      iRV (TupleFamilies.code d (vfProjection G) (vfProjection_finite G hfinite)
        t (TupleFamilies.values x) k)) (x : support G) (j : Fin r ⊕ Fin (n * d)) :
    iRV (separator d G hfinite x j) := by
  cases j with
  | inl j => exact (x.val.2 j).property
  | inr j => exact hsorted _ _ _

theorem separator_injective_on_fibres (d : ℕ)
    (G : Set ((Fin m → M) × MixedTuple (M := M) n r))
    (hfinite : ∀ t, {x | (t, x) ∈ G}.Finite) (hcoh : Coherent G)
    (hinj : ∀ t, Set.InjOn (fun x =>
      TupleFamilies.code d (vfProjection G) (vfProjection_finite G hfinite)
        t (TupleFamilies.values x)) {x | (t, x) ∈ vfProjection G})
    (t : Fin m → M) (x y : support G)
    (hx : (t, x.val) ∈ G) (hy : (t, y.val) ∈ G)
    (he : separator d G hfinite x = separator d G hfinite y) : x = y := by
  rw [separator_eq d G hfinite hcoh t x hx, separator_eq d G hfinite hcoh t y hy] at he
  apply Subtype.ext
  apply Prod.ext
  · apply hinj t ⟨x.val.2, hx⟩ ⟨y.val.2, hy⟩
    funext j
    exact congrFun he (.inr j)
  · funext j
    exact Subtype.ext (congrFun he (.inl j))

theorem separator_graph_definable (d : ℕ) (S : Set M)
    (G : Set ((Fin m → M) × MixedTuple (M := M) n r))
    (hG : RelationDefinable S G)
    (hfinite : ∀ t, {x | (t, x) ∈ G}.Finite) (hcoh : Coherent G)
    (hcode : ∀ k : Fin (n * d), S.DefinableFun LRV
      (fun z : Fin m ⊕ Fin n → M =>
        TupleFamilies.code d (vfProjection G) (vfProjection_finite G hfinite)
          (z ∘ Sum.inl) (z ∘ Sum.inr) k)) :
    S.Definable LRV
      {w : (Fin n ⊕ Fin r) ⊕ (Fin r ⊕ Fin (n * d)) → M |
        ∃ x : support G, values x.val = w ∘ Sum.inl ∧
          separator d G hfinite x = w ∘ Sum.inr} := by
  let I := (Fin n ⊕ Fin r) ⊕ (Fin r ⊕ Fin (n * d))
  let input (z : I ⊕ Fin m → M) := z ∘ Sum.inl ∘ Sum.inl
  let output (z : I ⊕ Fin m → M) := z ∘ Sum.inl ∘ Sum.inr
  have hg := hG.preimage_comp
    (Sum.elim Sum.inr (fun i => Sum.inl (Sum.inl i)) :
      Fin m ⊕ (Fin n ⊕ Fin r) → I ⊕ Fin m)
  have hrv (j : Fin r) : S.Definable LRV
      {z : I ⊕ Fin m → M | input z (.inr j) = output z (.inl j)} :=
    RawClosure.definable_equal_coordinates S _ _
  have hnew (k : Fin (n * d)) : S.Definable LRV
      {z : I ⊕ Fin m → M | TupleFamilies.code d (vfProjection G)
        (vfProjection_finite G hfinite) (z ∘ Sum.inr) (input z ∘ Sum.inl) k =
          output z (.inr k)} := by
    apply Set.DefinableFun.ofPred_eq _ (Set.DefinableFun.proj LRV)
    exact (hcode k).comp (show S.DefinableMap LRV
      (fun z : I ⊕ Fin m → M => Sum.elim (z ∘ Sum.inr) (input z ∘ Sum.inl)) from
      fun j => by cases j <;> exact Set.DefinableFun.proj LRV)
  have h := ((hg.inter (Set.definable_iInter_of_finite hrv)).inter
    (Set.definable_iInter_of_finite hnew)).exists_of_finite
  convert h using 1
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · rintro ⟨x, hx, he⟩
    let t := representative G x
    refine ⟨t, ⟨⟨x.val, representative_mem G x, hx⟩, ?_⟩, ?_⟩
    · intro j
      exact (congrFun hx (.inr j)).symm.trans (congrFun he (.inl j))
    · intro k
      have hv := congrFun hx
      change TupleFamilies.code d (vfProjection G) (vfProjection_finite G hfinite)
        t (w ∘ Sum.inl ∘ Sum.inl) k = w (.inr (.inr k))
      have hxvf : TupleFamilies.values x.val.1 = w ∘ Sum.inl ∘ Sum.inl := by
        funext i
        exact hv (.inl i)
      rw [← hxvf]
      exact congrFun he (.inr k)
  · rintro ⟨t, ⟨⟨x, hx, hv⟩, hrv⟩, hnew⟩
    let a : support G := ⟨x, t, hx⟩
    refine ⟨a, hv, ?_⟩
    rw [separator_eq d G hfinite hcoh t a hx]
    funext j
    cases j with
    | inl j => exact (congrFun hv (.inr j)).trans (hrv j)
    | inr k =>
      have hxvf : TupleFamilies.values x.1 = w ∘ Sum.inl ∘ Sum.inl := by
        funext i
        exact congrFun hv (.inl i)
      change TupleFamilies.code d (vfProjection G) (vfProjection_finite G hfinite)
        t (TupleFamilies.values x.1) k = w (.inr (.inr k))
      rw [hxvf]
      exact hnew k

theorem uniform_separator (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    (G : Set ((Fin m → M) × MixedTuple (M := M) n r))
    (hG : RelationDefinable S G)
    (hfinite : ∀ t, {x | (t, x) ∈ G}.Finite) (hcoh : Coherent G) :
    ∃ d : ℕ,
      (∀ t (x y : support G), (t, x.val) ∈ G → (t, y.val) ∈ G →
        separator d G hfinite x = separator d G hfinite y → x = y) ∧
      (∀ x j, iRV (separator d G hfinite x j)) ∧
      S.Definable LRV
        {w : (Fin n ⊕ Fin r) ⊕ (Fin r ⊕ Fin (n * d)) → M |
          ∃ x : support G, values x.val = w ∘ Sum.inl ∧
            separator d G hfinite x = w ∘ Sum.inr} := by
  obtain ⟨d, hinj, hcode, hsort⟩ := TupleFamilies.uniform_coding h00 hs S hsmall
    (vfProjection G) (vfProjection_definable S G hG) (vfProjection_finite G hfinite)
  exact ⟨d, separator_injective_on_fibres d G hfinite hcoh hinj,
    separator_sorted d G hfinite hsort, separator_graph_definable d S G hG hfinite hcoh hcode⟩

/-- The substantive finite-to-one refinement in Lemma 4.2. `E` is the full
real-code relation for an arbitrary target, including imaginary targets.
The original map is preserved, and a uniformly finite RV tuple makes it
injective. Neither code representatives nor fibre points are added to S. -/
theorem finite_map_refinement (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    {Y : Type} (A : Set (MixedTuple (M := M) n r)) (g : A → Y)
    (E : (Fin m → M) → Y → Prop)
    (hcover : ∀ y, ∃ t, E t y)
    (hsingle : ∀ t y y', E t y → E t y' → y = y')
    (hgraph : RelationDefinable S {p | ∃ a : A, a.val = p.2 ∧ E p.1 (g a)})
    (hfinite : ∀ y, {a : A | g a = y}.Finite) :
    ∃ j : ℕ, ∃ h : A → Fin j → M,
      Function.Injective (fun a => (g a, h a)) ∧ (∀ a k, iRV (h a k)) ∧
      S.Definable LRV {w : (Fin n ⊕ Fin r) ⊕ Fin j → M |
        ∃ a : A, values a.val = w ∘ Sum.inl ∧ h a = w ∘ Sum.inr} := by
  let G : Set ((Fin m → M) × MixedTuple (M := M) n r) :=
    {p | ∃ a : A, a.val = p.2 ∧ E p.1 (g a)}
  have hGfin (t : Fin m → M) : {x | (t, x) ∈ G}.Finite := by
    by_cases ht : ∃ a : A, E t (g a)
    · obtain ⟨a, ha⟩ := ht
      apply ((hfinite (g a)).image Subtype.val).subset
      rintro x ⟨b, rfl, hb⟩
      exact ⟨b, hsingle t (g b) (g a) hb ha, rfl⟩
    · have he : {x | (t, x) ∈ G} = ∅ := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨a, _, ha⟩
        exact ht ⟨a, ha⟩
      rw [he]
      exact Set.finite_empty
  have hcoh : Coherent G := by
    rintro t u x ⟨a, rfl, ha⟩ ⟨b, hb, hu⟩ y
    have hba : b = a := Subtype.ext hb
    subst b
    constructor
    · rintro ⟨c, hc, htc⟩
      refine ⟨c, hc, ?_⟩
      rwa [hsingle t (g c) (g a) htc ha]
    · rintro ⟨c, hc, huc⟩
      refine ⟨c, hc, ?_⟩
      rwa [hsingle u (g c) (g a) huc hu]
  have hsupport : support G = A := by
    ext x
    constructor
    · rintro ⟨t, a, rfl, _⟩
      exact a.property
    · intro hx
      obtain ⟨t, ht⟩ := hcover (g ⟨x, hx⟩)
      exact ⟨t, ⟨x, hx⟩, rfl, ht⟩
  let toSupport (a : A) : support G := ⟨a.val, hsupport.symm ▸ a.property⟩
  have htoSupport : Function.Surjective toSupport := by
    intro x
    exact ⟨⟨x.val, hsupport ▸ x.property⟩, Subtype.ext rfl⟩
  obtain ⟨d, hinj, hsort, hdef⟩ := uniform_separator h00 hs S hsmall G hgraph hGfin hcoh
  let e : Fin r ⊕ Fin (n * d) ≃ Fin (r + n * d) := finSumFinEquiv
  let h (a : A) (j : Fin (r + n * d)) := separator d G hGfin (toSupport a) (e.symm j)
  refine ⟨r + n * d, h, ?_, (fun a j => hsort _ _), ?_⟩
  · intro a b hab
    have hg : g a = g b := congrArg Prod.fst hab
    obtain ⟨t, ht⟩ := hcover (g a)
    have he : separator d G hGfin (toSupport a) = separator d G hGfin (toSupport b) := by
      funext j
      have hj := congrFun (congrArg Prod.snd hab) (e j)
      simpa only [h, Equiv.symm_apply_apply] using hj
    have hx := hinj t (toSupport a) (toSupport b) ⟨a, rfl, ht⟩
      ⟨b, rfl, hg ▸ ht⟩ he
    exact Subtype.ext (congrArg (fun z : support G => z.val) hx)
  · have hd := hdef.preimage_comp (Sum.map id e)
    convert hd using 1
    ext w
    constructor
    · rintro ⟨a, ha, he⟩
      refine ⟨toSupport a, ha, ?_⟩
      funext j
      have hj := congrFun he (e j)
      simpa only [h, Equiv.symm_apply_apply, Function.comp_apply, Sum.map_inr] using hj
    · rintro ⟨x, hx, he⟩
      obtain ⟨a, rfl⟩ := htoSupport x
      refine ⟨a, hx, ?_⟩
      funext j
      exact (congrFun he (e.symm j)).trans (congrArg (fun k => w (.inr k))
        (e.apply_symm_apply j))

end SpecialTransformations.Section4.FiniteRefinement
