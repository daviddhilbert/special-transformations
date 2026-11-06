import Section3.AngularPattern
import Section3.FiniteValueFibres
import Section3.GammaBaseTools
import Section3.GammaCounting
import Section3.InfiniteValueFibres
import Section3.TupleCompactness
import Section3.TupleRelations

/- Component: AngularMinimality -/
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
namespace SpecialTransformations.Section3

/-- Finite angular exceptions force finite/cofinite traces in a value fibre. -/
theorem finite_or_cofinite_of_finite_exceptions {α β : Type}
    (f : α → β) (A T : Set α) (hT : T.Finite)
    (hpattern : ∀ x y, f x = f y → x ∉ T → y ∉ T → (x ∈ A ↔ y ∈ A)) (b : β) :
    {x | f x = b ∧ x ∈ A}.Finite ∨ {x | f x = b ∧ x ∉ A}.Finite := by
  by_cases hf : {x | f x = b ∧ x ∈ A}.Finite
  · exact Or.inl hf
  right
  have hnot : ¬ {x | f x = b ∧ x ∈ A} ⊆ T := fun h => hf (hT.subset h)
  obtain ⟨t,ht,htT⟩ := Set.not_subset.mp hnot
  apply hT.subset
  rintro u ⟨hu,hua⟩
  by_contra huT
  exact hua ((hpattern t u (ht.1.trans hu.symm) htT huT).mp ht.2)

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The induced definable subsets of each actual nonzero RV value fibre
are finite or cofinite, with arbitrary real parameters. Under ACVF(0,0)
the fibre itself is infinite by the separately checked infinitude theorem. -/
theorem rv_value_fibre_finite_or_cofinite (S A : Set M) (hA : DefinableAt S .rv A)
    (γ : Values.Gamma (M := M)) :
    (Values.fibre A γ).Finite ∨
      {t : CanonicalRV.RVSort M | Values.vrv t = γ.val ∧ t.val ∉ A}.Finite := by
  obtain ⟨T,hT,hTRV,hpattern⟩ := rv_set_finite_angular_exceptions S A hA
  let T' : Set (CanonicalRV.RVSort M) := {t | t.val ∈ T}
  have hT' : T'.Finite := hT.preimage Subtype.val_injective.injOn
  exact finite_or_cofinite_of_finite_exceptions Values.vrv {t | t.val ∈ A} T' hT'
    (fun t u htu ht hu => hpattern t u htu ht hu) γ.val

theorem rv_value_fibre_finite_or_cofinite_gamma_base
    (B : GammaParameters.Base (M := M)) (A : Set M)
    (hA : GammaParameters.DefinableAtBase B .rv A) (γ : Values.Gamma (M := M)) :
    (Values.fibre A γ).Finite ∨
      {t : CanonicalRV.RVSort M | Values.vrv t = γ.val ∧ t.val ∉ A}.Finite :=
  rv_value_fibre_finite_or_cofinite (GammaParameters.commonRealNames B) A hA.common_names γ

end SpecialTransformations.Section3

/- Component: UniformFiniteSides -/
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0
namespace SpecialTransformations.Section3.RawClosure.Tuple
variable {M : Type} [LRV.Structure M] {n : ℕ}

/-- Genuine saturation turns a definable finite-side dichotomy into a
uniform finite-side cardinal bound. The index domain may be definable over
any small parameter set; no cardinality assumption is bundled in saturation. -/
theorem uniform_finite_side {κ : Cardinal} (hs : Saturated M κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ)
    (D : Set (Fin n → M)) (hD : S.Definable LRV D)
    (R Q : Set ((Fin n → M) × M))
    (hR : RelationDefinable S R) (hQ : RelationDefinable S Q)
    (hside : ∀ a ∈ D, {x | (a,x) ∈ R}.Finite ∨ {x | (a,x) ∈ Q}.Finite) :
    ∃ N : ℕ, ∀ a ∈ D,
      ({x | (a,x) ∈ R}.Finite ∧ {x | (a,x) ∈ R}.ncard ≤ N) ∨
      ({x | (a,x) ∈ Q}.Finite ∧ {x | (a,x) ∈ Q}.ncard ≤ N) := by
  let C (k : ℕ) : Set (Fin n → M) := (HasMore R k)ᶜ ∪ (HasMore Q k)ᶜ
  have hCd (k : ℕ) : S.Definable LRV (C k) :=
    (hasMore_definable S R hR k).compl.union (hasMore_definable S Q hQ k).compl
  have hcover : ∀ a ∈ D, ∃ c ∈ Set.range C, a ∈ c := by
    intro a ha
    rcases hside a ha with h | h
    · refine ⟨C {x | (a,x) ∈ R}.ncard,Set.mem_range_self _,Or.inl ?_⟩
      exact no_inj_iff_finite_ncard_le.mpr ⟨h,le_rfl⟩
    · refine ⟨C {x | (a,x) ∈ Q}.ncard,Set.mem_range_self _,Or.inr ?_⟩
      exact no_inj_iff_finite_ncard_le.mpr ⟨h,le_rfl⟩
  obtain ⟨C₀,hC₀,hsub,hcov⟩ := hs.definable_finite_subcover_tuple
    S hsmall D hD (Set.range C) (by rintro c ⟨k,rfl⟩; exact hCd k) hcover
  letI := hC₀.fintype
  choose k hk using fun c : C₀ => hsub c.property
  let N := Finset.univ.sup k
  refine ⟨N,?_⟩
  intro a ha
  obtain ⟨c,hc,hac⟩ := hcov a ha
  let c' : C₀ := ⟨c,hc⟩
  have hkN : k c' ≤ N := Finset.le_sup (Finset.mem_univ c')
  have hac' : a ∈ C (k c') := (hk c').symm ▸ hac
  rcases hac' with h | h
  · have hh := (no_inj_iff_finite_ncard_le (s := {x | (a,x) ∈ R}) (k := k c')).mp h
    exact Or.inl ⟨hh.1,hh.2.trans hkN⟩
  · have hh := (no_inj_iff_finite_ncard_le (s := {x | (a,x) ∈ Q}) (k := k c')).mp h
    exact Or.inr ⟨hh.1,hh.2.trans hkN⟩

/-- If the two sides cover an infinite fibre, the uniform dichotomy also
bounds every finite fibre on either side. This is the compactness ingredient
for elimination of the 'there are infinitely many' quantifier in a
strongly minimal fibre, without assuming elimination as an extra axiom. -/
theorem uniform_finite_fibres_from_dichotomy {κ : Cardinal} (hs : Saturated M κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ)
    (D : Set (Fin n → M)) (hD : S.Definable LRV D)
    (R Q : Set ((Fin n → M) × M))
    (hR : RelationDefinable S R) (hQ : RelationDefinable S Q)
    (hside : ∀ a ∈ D, {x | (a,x) ∈ R}.Finite ∨ {x | (a,x) ∈ Q}.Finite)
    (hinf : ∀ a ∈ D, ({x | (a,x) ∈ R} ∪ {x | (a,x) ∈ Q}).Infinite) :
    ∃ N : ℕ, ∀ a ∈ D,
      ({x | (a,x) ∈ R}.Finite → {x | (a,x) ∈ R}.ncard ≤ N) ∧
      ({x | (a,x) ∈ Q}.Finite → {x | (a,x) ∈ Q}.ncard ≤ N) := by
  obtain ⟨N,hN⟩ := uniform_finite_side hs S hsmall D hD R Q hR hQ hside
  refine ⟨N,fun a ha => ?_⟩
  constructor
  · intro hf
    rcases hN a ha with h | h
    · exact h.2
    · exact ((hinf a ha) (hf.union h.1)).elim
  · intro hf
    rcases hN a ha with h | h
    · exact ((hinf a ha) (h.1.union hf)).elim
    · exact h.2

end SpecialTransformations.Section3.RawClosure.Tuple

/- Component: NoOrderedImage -/
open Classical
namespace SpecialTransformations.Section3

/-- A uniform bound on one side of every order cut prevents an infinite
image. The bound is on actual source points and permits arbitrary fibres.
This is the order-combinatorial part of the RV-fibre no-order argument. -/
theorem finite_image_of_uniform_small_cut {α β : Type} [LinearOrder β]
    (A : Set α) (f : α → β) (N : ℕ)
    (hcut : ∀ b : β,
      ({x | x ∈ A ∧ f x < b}.Finite ∧ {x | x ∈ A ∧ f x < b}.ncard ≤ N) ∨
      ({x | x ∈ A ∧ ¬ f x < b}.Finite ∧ {x | x ∈ A ∧ ¬ f x < b}.ncard ≤ N)) :
    (f '' A).Finite := by
  by_contra hf
  have hf' : (f '' A).Infinite := hf
  haveI : Infinite (f '' A) := hf'.to_subtype
  obtain ⟨e⟩ := nonempty_orderEmbedding_of_finite_infinite (Fin (2*N+3)) (f '' A)
  have hex (i : Fin (2*N+3)) : ∃ x ∈ A, f x = (e i).val := (e i).property
  choose x hxA hfx using hex
  have hxi : Function.Injective x := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    rw [← hfx i,← hfx j,hij]
  let mid : Fin (2*N+3) := ⟨N+1,by omega⟩
  let left (i : Fin (N+1)) : Fin (2*N+3) := ⟨i.val,by omega⟩
  let right (i : Fin (N+1)) : Fin (2*N+3) := ⟨i.val+N+2,by omega⟩
  have hlefti : Function.Injective left := by
    intro i j h; apply Fin.ext
    exact congrArg (fun z : Fin (2*N+3) => z.val) h
  have hrighti : Function.Injective right := by
    intro i j h; apply Fin.ext
    have hh := congrArg Fin.val h
    dsimp only [right] at hh
    omega
  have hleft : ∀ i, x (left i) ∈ {x | x ∈ A ∧ f x < (e mid).val} := by
    intro i
    refine ⟨hxA _,?_⟩
    rw [hfx]
    exact e.strictMono (show left i < mid from by change i.val < N+1; exact i.isLt)
  have hright : ∀ i, x (right i) ∈ {x | x ∈ A ∧ ¬ f x < (e mid).val} := by
    intro i
    refine ⟨hxA _,?_⟩
    rw [hfx]
    exact not_lt_of_ge ((e.strictMono (show mid < right i from by
      change N+1 < i.val+N+2; omega)).le)
  rcases hcut (e mid).val with h | h
  · exact GammaParameters.no_injection_iff_finite_ncard_le.mpr h ⟨x ∘ left,hxi.comp hlefti,hleft⟩
  · exact GammaParameters.no_injection_iff_finite_ncard_le.mpr h ⟨x ∘ right,hxi.comp hrighti,hright⟩

end SpecialTransformations.Section3

/- Component: FiniteThresholds -/
open Classical
namespace SpecialTransformations.Section3.FiniteThresholds
variable {α : Type} [LinearOrder α]

def SameCuts (E : Finset α) (x y : α) : Prop :=
  ∀ c ∈ E, (x < c ↔ y < c) ∧ (c < x ↔ c < y)

def Determines (E : Finset α) (A : Set α) : Prop :=
  ∀ x y, SameCuts E x y → (x ∈ A ↔ y ∈ A)

def IsInfimum (A : Set α) (c : α) : Prop :=
  (∀ x ∈ A, c ≤ x) ∧ ∀ b, (∀ x ∈ A, b ≤ x) → b ≤ c

theorem sameCuts_below (E : Finset α) (x y : α)
    (hx : ∀ c ∈ E, x < c) (hy : ∀ c ∈ E, y < c) : SameCuts E x y := by
  intro c hc
  exact ⟨iff_of_true (hx c hc) (hy c hc),
    iff_of_false (not_lt_of_ge (hx c hc).le) (not_lt_of_ge (hy c hc).le)⟩

theorem sameCuts_in_gap (E : Finset α) (c e x y : α)
    (hE : ∀ t ∈ E, t ≤ c ∨ e ≤ t)
    (hcx : c < x) (hxe : x < e) (hcy : c < y) (hye : y < e) : SameCuts E x y := by
  intro t ht
  rcases hE t ht with h | h
  · have htx := lt_of_le_of_lt h hcx
    have hty := lt_of_le_of_lt h hcy
    exact ⟨iff_of_false (not_lt_of_ge htx.le) (not_lt_of_ge hty.le),iff_of_true htx hty⟩
  · have hxt := lt_of_lt_of_le hxe h
    have hyt := lt_of_lt_of_le hye h
    exact ⟨iff_of_true hxt hyt,iff_of_false (not_lt_of_ge hxt.le) (not_lt_of_ge hyt.le)⟩

theorem Determines.compl (E : Finset α) (A : Set α) (h : Determines E A) :
    Determines E Aᶜ := fun x y hxy => not_congr (h x y hxy)

theorem left_tail [Nonempty α] (E : Finset α) (A : Set α) (h : Determines E A) :
    ∃ b : α, ∀ x y, x < b → y < b → (x ∈ A ↔ y ∈ A) := by
  by_cases he : E.Nonempty
  · refine ⟨E.min' he,fun x y hx hy => h x y ?_⟩
    exact sameCuts_below E x y (fun c hc => lt_of_lt_of_le hx (E.min'_le c hc))
      (fun c hc => lt_of_lt_of_le hy (E.min'_le c hc))
  · have he' : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    refine ⟨Classical.arbitrary α,fun x y _ _ => h x y ?_⟩
    intro c hc
    exact (Finset.notMem_empty c (he' ▸ hc)).elim

theorem one_side_bounded_below [Nonempty α] (E : Finset α) (A : Set α)
    (h : Determines E A) :
    (∃ b, ∀ x ∈ A, b ≤ x) ∨ (∃ b, ∀ x ∈ Aᶜ, b ≤ x) := by
  obtain ⟨b,hb⟩ := left_tail E A h
  by_cases ha : ∃ a, a < b ∧ a ∈ A
  · obtain ⟨a,hab,ha⟩ := ha
    right
    refine ⟨b,fun x hx => le_of_not_gt (fun hxb => ?_)⟩
    exact hx ((hb a x hab hxb).mp ha)
  · left
    exact ⟨b,fun x hx => le_of_not_gt (fun hxb => ha ⟨x,hxb,hx⟩)⟩

/-- A nonempty bounded-below set determined by finitely many actual
thresholds has an actual infimum. It contains that point or a right
adjacent interval. This does not assume completeness of the order. -/
theorem exists_infimum [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α]
    (E : Finset α) (A : Set α) (h : Determines E A) (hne : A.Nonempty)
    (hbounded : ∃ b, ∀ x ∈ A, b ≤ x) :
    ∃ c, IsInfimum A c ∧ (c ∈ A ∨ ∃ e, c < e ∧ Set.Ioo c e ⊆ A) := by
  obtain ⟨b,hb⟩ := hbounded
  have hE : E.Nonempty := by
    by_contra he
    have he' : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    obtain ⟨a,ha⟩ := hne
    obtain ⟨z,hzb⟩ := exists_lt b
    have hza := (h a z (by intro c hc; exact (Finset.notMem_empty c (he' ▸ hc)).elim)).mp ha
    exact not_le_of_gt hzb (hb z hza)
  have hmin : ∀ x ∈ A, E.min' hE ≤ x := by
    intro x hx
    by_contra hnx
    have hxm : x < E.min' hE := lt_of_not_ge hnx
    obtain ⟨z,hz⟩ := exists_lt (min b (E.min' hE))
    have hzb : z < b := lt_of_lt_of_le hz (min_le_left _ _)
    have hzm : z < E.min' hE := lt_of_lt_of_le hz (min_le_right _ _)
    have hp := sameCuts_below E x z
      (fun t ht => lt_of_lt_of_le hxm (E.min'_le t ht))
      (fun t ht => lt_of_lt_of_le hzm (E.min'_le t ht))
    exact not_le_of_gt hzb (hb z ((h x z hp).mp hx))
  let G := E.filter (fun c => ∀ x ∈ A, c ≤ x)
  have hG : G.Nonempty := ⟨E.min' hE,Finset.mem_filter.mpr ⟨E.min'_mem hE,hmin⟩⟩
  let c := G.max' hG
  have hcG : c ∈ G := G.max'_mem hG
  have hcE : c ∈ E := (Finset.mem_filter.mp hcG).1
  have hcA : ∀ x ∈ A, c ≤ x := (Finset.mem_filter.mp hcG).2
  by_cases hc : c ∈ A
  · exact ⟨c,⟨hcA,fun z hz => hz c hc⟩,Or.inl hc⟩
  have hgap : ∃ e, c < e ∧ (∀ t ∈ E, t ≤ c ∨ e ≤ t) ∧
      ∃ a, c < a ∧ a < e ∧ a ∈ A := by
    let H := E.filter (c < ·)
    by_cases hH : H.Nonempty
    · let e := H.min' hH
      have heH : e ∈ H := H.min'_mem hH
      have heE : e ∈ E := (Finset.mem_filter.mp heH).1
      have hce : c < e := (Finset.mem_filter.mp heH).2
      have heLB : ¬ ∀ x ∈ A, e ≤ x := by
        intro he
        have heG : e ∈ G := Finset.mem_filter.mpr ⟨heE,he⟩
        exact not_le_of_gt hce (G.le_max' e heG)
      push_neg at heLB
      obtain ⟨a,ha,hae⟩ := heLB
      refine ⟨e,hce,?_,a,lt_of_le_of_ne (hcA a ha) (fun he => hc (he.symm ▸ ha)),hae,ha⟩
      intro t ht
      by_cases hct : c < t
      · exact Or.inr (H.min'_le t (Finset.mem_filter.mpr ⟨ht,hct⟩))
      · exact Or.inl (le_of_not_gt hct)
    · obtain ⟨a,ha⟩ := hne
      have hca : c < a := lt_of_le_of_ne (hcA a ha) (fun he => hc (he.symm ▸ ha))
      obtain ⟨e,hae⟩ := exists_gt a
      refine ⟨e,hca.trans hae,?_,a,hca,hae,ha⟩
      intro t ht
      left
      exact le_of_not_gt (fun hct => hH ⟨t,Finset.mem_filter.mpr ⟨ht,hct⟩⟩)
  obtain ⟨e,hce,hcell,a,hca,hae,ha⟩ := hgap
  have hinterval : Set.Ioo c e ⊆ A := by
    intro x hx
    exact (h a x (sameCuts_in_gap E c e a x hcell hca hae hx.1 hx.2)).mp ha
  refine ⟨c,⟨hcA,?_⟩,Or.inr ⟨e,hce,hinterval⟩⟩
  intro z hz
  apply le_of_not_gt
  intro hcz
  obtain ⟨x,hcx,hxm⟩ := exists_between (lt_min_iff.mpr ⟨hcz,hce⟩)
  have hxA := hinterval ⟨hcx,lt_of_lt_of_le hxm (min_le_right z e)⟩
  exact not_le_of_gt (lt_of_lt_of_le hxm (min_le_left z e)) (hz x hxA)

def BoundedBelow (A : Set α) : Prop := ∃ b, ∀ x ∈ A, b ≤ x

/-- Intrinsic endpoint selection, with priority given to the set's infimum
when it is bounded below. Otherwise use the complement's infimum. -/
def CanonicalEndpoint (A : Set α) (c : α) : Prop :=
  (BoundedBelow A ∧ IsInfimum A c) ∨ (¬ BoundedBelow A ∧ IsInfimum Aᶜ c)

theorem infimum_unique {A : Set α} {c d : α}
    (hc : IsInfimum A c) (hd : IsInfimum A d) : c = d :=
  le_antisymm (hd.2 c hc.1) (hc.2 d hd.1)

theorem canonicalEndpoint_unique {A : Set α} {c d : α}
    (hc : CanonicalEndpoint A c) (hd : CanonicalEndpoint A d) : c = d := by
  rcases hc with ⟨hb,hc⟩ | ⟨hb,hc⟩
  · rcases hd with ⟨_,hd⟩ | ⟨hn,_⟩
    · exact infimum_unique hc hd
    · exact (hn hb).elim
  · rcases hd with ⟨hn,_⟩ | ⟨_,hd⟩
    · exact (hb hn).elim
    · exact infimum_unique hc hd

theorem canonicalEndpoint_exists [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α]
    (E : Finset α) (A : Set α) (h : Determines E A)
    (hne : A.Nonempty) (hcomp : Aᶜ.Nonempty) : ∃ c, CanonicalEndpoint A c := by
  letI : Nonempty α := ⟨hne.choose⟩
  by_cases hb : BoundedBelow A
  · obtain ⟨c,hc,_⟩ := exists_infimum E A h hne hb
    exact ⟨c,Or.inl ⟨hb,hc⟩⟩
  · have hbc : BoundedBelow Aᶜ := (one_side_bounded_below E A h).resolve_left hb
    obtain ⟨c,hc,_⟩ := exists_infimum E Aᶜ (Determines.compl E A h) hcomp hbc
    exact ⟨c,Or.inr ⟨hb,hc⟩⟩

/-- Every selected endpoint is touched by the set: either at the endpoint
or throughout a one-sided adjacent interval. -/
theorem canonicalEndpoint_touches [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α]
    (E : Finset α) (A : Set α) (h : Determines E A) (hne : A.Nonempty)
    (c : α) (hc : CanonicalEndpoint A c) :
    c ∈ A ∨ (∃ e, c < e ∧ Set.Ioo c e ⊆ A) ∨ (∃ e, e < c ∧ Set.Ioo e c ⊆ A) := by
  rcases hc with ⟨hb,hc⟩ | ⟨_,hc⟩
  · obtain ⟨d,hd,hlocal⟩ := exists_infimum E A h hne hb
    have he : d = c := infimum_unique hd hc
    subst d
    exact hlocal.elim Or.inl (fun hi => Or.inr (Or.inl hi))
  · obtain ⟨e,he⟩ := exists_lt c
    right; right
    refine ⟨e,he,fun x hx => ?_⟩
    by_contra hxa
    exact not_le_of_gt hx.2 (hc.1 x hxa)

def RightContact {τ : Type} (R : α → τ → Prop) (b : α) : Set τ :=
  {t | ∃ e, b < e ∧ ∀ x, b < x → x < e → R x t}

def LeftContact {τ : Type} (R : α → τ → Prop) (b : α) : Set τ :=
  {t | ∃ e, e < b ∧ ∀ x, x < b → e < x → R x t}

/-- Uniformly finite rows leave only finitely many parameters whose rows
contain a right-hand interval touching the fixed endpoint. -/
theorem finite_right_contacts [DenselyOrdered α] {τ : Type}
    (R : α → τ → Prop) (b : α) (d : ℕ)
    (hrows : ∀ x, {t | R x t}.Finite ∧ {t | R x t}.ncard ≤ d) :
    (RightContact R b).Finite := by
  apply (GammaParameters.no_injection_iff_finite_ncard_le (A := RightContact R b) (d := d)).mp ?_ |>.1
  rintro ⟨u,hu,hm⟩
  choose e he hr using fun i => hm i
  let F := Finset.univ.image e
  have hF : F.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
  let c := F.min' hF
  have hbc : b < c := by
    obtain ⟨i,hi,hei⟩ := Finset.mem_image.mp (F.min'_mem hF)
    change b < F.min' hF
    rw [← hei]
    exact he i
  obtain ⟨x,hbx,hxc⟩ := exists_between hbc
  apply GammaParameters.no_injection_iff_finite_ncard_le.mpr (hrows x)
  refine ⟨u,hu,fun i => hr i x hbx ?_⟩
  exact lt_of_lt_of_le hxc (F.min'_le (e i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))

theorem finite_left_contacts [DenselyOrdered α] {τ : Type}
    (R : α → τ → Prop) (b : α) (d : ℕ)
    (hrows : ∀ x, {t | R x t}.Finite ∧ {t | R x t}.ncard ≤ d) :
    (LeftContact R b).Finite := by
  exact finite_right_contacts (α := OrderDual α) R b d hrows

/-- The local endpoint alternatives give finite fibres of the intrinsic
selector. No definable choice, saturation, or completeness is assumed here. -/
theorem finite_touched_parameters [DenselyOrdered α] {τ : Type}
    (R : α → τ → Prop) (b : α) (d : ℕ)
    (hrows : ∀ x, {t | R x t}.Finite ∧ {t | R x t}.ncard ≤ d)
    (T : Set τ) (htouch : ∀ t ∈ T,
      R b t ∨ t ∈ RightContact R b ∨ t ∈ LeftContact R b) : T.Finite := by
  have hf := ((hrows b).1.union (finite_right_contacts R b d hrows)).union
    (finite_left_contacts R b d hrows)
  apply hf.subset
  intro t ht
  rcases htouch t ht with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

end SpecialTransformations.Section3.FiniteThresholds
