import Section9.LimitGeometry

/-! The finite limit-set geometry in Lemma 9.4. The separation argument
includes the paper's formal infinity coordinate. Minimality then forces
every candidate limit point to be visited arbitrarily close to the input. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

private def gammaAtNonzero (x : VFType (M := M)) (hx : x ≠ 0) : Values.Gamma (M := M) :=
  Values.gammaOf (CanonicalRV.encodedRv x) (fun h => hx ((CanonicalRV.encodedRv_zero_iff x).mp h))

private theorem finite_infinite_separated (b : VFType (M := M)) :
    ∃ ε : Values.Gamma (M := M), ∀ y : VFType (M := M),
      memLimitBall (some b) ε y → ¬ memLimitBall none ε y := by
  by_cases hb : b = 0
  · subst b
    refine ⟨1, fun y hfin hinf => ?_⟩
    simp only [memLimitBall, sub_zero, inv_one, Values.gamma_val_one] at hfin hinf
    exact (not_lt_of_ge hfin.le) hinf
  · let γ := gammaAtNonzero b hb
    let ε := max (1 : Values.Gamma (M := M)) γ⁻¹
    have hε₁ : ε⁻¹ ≤ 1 := by
      simpa only [inv_one] using inv_le_inv' (le_max_left (1 : Values.Gamma (M := M)) γ⁻¹)
    have hε₂ : ε⁻¹ ≤ γ := by
      simpa only [inv_inv] using inv_le_inv' (le_max_right (1 : Values.Gamma (M := M)) γ⁻¹)
    refine ⟨ε, fun y hfin hinf => ?_⟩
    change ε.val < Values.vfValueHom (y - b) at hfin
    change Values.vfValueHom y < (ε⁻¹).val at hinf
    have he : (ε⁻¹).val ≤ ε.val :=
      show ε⁻¹ ≤ ε from hε₁.trans (le_max_left _ _)
    have hmin := vfValue_min_le_sub (y - b) (-b)
    rw [show y - b - (-b) = y by abel, vfValue_neg] at hmin
    exact (not_lt_of_ge ((le_min (he.trans hfin.le)
      (show (ε⁻¹).val ≤ Values.vfValueHom b from hε₂)).trans hmin)) hinf

private theorem limit_coordinates_separated {b c : LimitPoint M} (h : b ≠ c) :
    ∃ ε : Values.Gamma (M := M), ∀ y : VFType (M := M),
      memLimitBall b ε y → ¬ memLimitBall c ε y := by
  cases b with
  | none =>
    cases c with
    | none => exact (h rfl).elim
    | some c =>
      obtain ⟨ε, hε⟩ := finite_infinite_separated c
      exact ⟨ε, fun y hinf hfin => hε y hfin hinf⟩
  | some b =>
    cases c with
    | none => exact finite_infinite_separated b
    | some c =>
      have hbc : b ≠ c := fun he => h (congrArg some he)
      let ε := gammaAtNonzero (b - c) (sub_ne_zero.mpr hbc)
      refine ⟨ε, fun y hyb hyc => ?_⟩
      change ε.val < Values.vfValueHom (y - b) at hyb
      change ε.val < Values.vfValueHom (y - c) at hyc
      have hh := vfValue_min_le_sub (y - c) (y - b)
      rw [show y - c - (y - b) = b - c by abel] at hh
      have hbound : min (Values.vfValueHom (y - c)) (Values.vfValueHom (y - b)) ≤ ε.val := hh
      exact (not_lt_of_ge hbound) (lt_min hyc hyb)

theorem exists_disjoint_limitBall {m : ℕ} {b c : Fin m → LimitPoint M} (h : b ≠ c) :
    ∃ ε : Values.Gamma (M := M), Disjoint (limitBall b ε) (limitBall c ε) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, b i ≠ c i := by
    by_contra hn
    push_neg at hn
    exact h (funext hn)
  obtain ⟨ε, hε⟩ := limit_coordinates_separated hi
  exact ⟨ε, Set.disjoint_left.mpr (fun _ hyb hyc => hε _ (hyb i) (hyc i))⟩

/-- The finitely many candidate limit points can be separated by one
radius, even when some coordinates are infinity. -/
theorem exists_pairwise_disjoint_limitBall {m : ℕ} {L : Set (Fin m → LimitPoint M)}
    (hL : L.Finite) : ∃ ε : Values.Gamma (M := M),
      L.Pairwise (fun b c => Disjoint (limitBall b ε) (limitBall c ε)) := by
  classical
  letI := hL.fintype
  have h (p : L × L) : ∃ ε : Values.Gamma (M := M),
      p.1.val ≠ p.2.val → Disjoint (limitBall p.1.val ε) (limitBall p.2.val ε) := by
    by_cases he : p.1.val = p.2.val
    · exact ⟨1, fun hn => (hn he).elim⟩
    · obtain ⟨ε, hε⟩ := exists_disjoint_limitBall he
      exact ⟨ε, fun _ => hε⟩
  choose r hr using h
  let S := insert (1 : Values.Gamma (M := M)) (Finset.univ.image r)
  have hS : S.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨S.max' hS, ?_⟩
  intro b hb c hc hbc
  let p : L × L := (⟨b, hb⟩, ⟨c, hc⟩)
  have hmem : r p ∈ S := Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩)
  have hle : r p ≤ S.max' hS := Finset.le_max' S _ hmem
  exact (hr p hbc).mono (limitBall_anti hle) (limitBall_anti hle)

/-- Every neighbourhood of a point of a minimal limit set is hit by
some output in every punctured input neighbourhood. -/
theorem IsMinimalLimitSet.frequently_hits {n m : ℕ}
    {A : Set (Fin n → VFType (M := M))} {a : Fin n → VFType (M := M)}
    {f : (Fin n → VFType (M := M)) → Set (Fin m → VFType (M := M))}
    {L : Set (Fin m → LimitPoint M)} (hL : IsMinimalLimitSet A a f L)
    {b : Fin m → LimitPoint M} (hb : b ∈ L) (ε δ : Values.Gamma (M := M)) :
    ∃ x ∈ A \ {a}, x ∈ vfBall a δ ∧ ∃ y ∈ f x, y ∈ limitBall b ε := by
  classical
  by_contra hn
  have hsub : L \ {b} ⊂ L := by
    refine Set.ssubset_iff_subset_ne.mpr ⟨Set.sdiff_subset, ?_⟩
    intro he
    have h : b ∈ L \ {b} := he.symm ▸ hb
    exact h.2 rfl
  apply hL.2 _ hsub
  rw [isLimitSet_iff]
  intro ε'
  obtain ⟨δ', hδ'⟩ := (isLimitSet_iff A a f L).mp hL.1 (max ε ε')
  refine ⟨max δ δ', ?_⟩
  intro x hx hnear y hy
  obtain ⟨c, hc, hyc⟩ := hδ' x hx (vfBall_anti (le_max_right _ _) hnear) y hy
  refine ⟨c, ⟨hc, ?_⟩, limitBall_anti (le_max_right _ _) hyc⟩
  intro he
  have hcb : c = b := he
  subst c
  exact hn ⟨x, hx, vfBall_anti (le_max_left _ _) hnear,
    y, hy, limitBall_anti (le_max_left _ _) hyc⟩

/-- A finite limit set contains every point whose neighbourhoods are
hit arbitrarily close to the input centre. -/
theorem IsLimitSet.mem_of_frequently_hits {n m : ℕ}
    {A : Set (Fin n → VFType (M := M))} {a : Fin n → VFType (M := M)}
    {f : (Fin n → VFType (M := M)) → Set (Fin m → VFType (M := M))}
    {L : Set (Fin m → LimitPoint M)} (hL : IsLimitSet A a f L) (hf : L.Finite)
    {b : Fin m → LimitPoint M} (hhit : ∀ ε δ : Values.Gamma (M := M),
      ∃ x ∈ A \ {a}, x ∈ vfBall a δ ∧ ∃ y ∈ f x, y ∈ limitBall b ε) : b ∈ L := by
  by_contra hb
  obtain ⟨ε, hε⟩ := exists_pairwise_disjoint_limitBall (hf.insert b)
  obtain ⟨δ, hδ⟩ := (isLimitSet_iff A a f L).mp hL ε
  obtain ⟨x, hx, hxδ, y, hy, hyb⟩ := hhit ε δ
  obtain ⟨c, hc, hyc⟩ := hδ x hx hxδ y hy
  have hbc : b ≠ c := fun he => hb (he.symm ▸ hc)
  exact Set.disjoint_left.mp (hε (Set.mem_insert b L) (Set.mem_insert_of_mem b hc) hbc) hyb hyc

/-- A finite minimal limit set is determined by frequent neighbourhood
hits. This characterization allows its definability to be proved without
naming the candidate points obtained from polynomial roots. -/
theorem IsMinimalLimitSet.mem_iff_frequently_hits {n m : ℕ}
    {A : Set (Fin n → VFType (M := M))} {a : Fin n → VFType (M := M)}
    {f : (Fin n → VFType (M := M)) → Set (Fin m → VFType (M := M))}
    {L : Set (Fin m → LimitPoint M)} (hL : IsMinimalLimitSet A a f L) (hf : L.Finite)
    (b : Fin m → LimitPoint M) : b ∈ L ↔ ∀ ε δ : Values.Gamma (M := M),
      ∃ x ∈ A \ {a}, x ∈ vfBall a δ ∧ ∃ y ∈ f x, y ∈ limitBall b ε :=
  ⟨fun hb => hL.frequently_hits hb, hL.1.mem_of_frequently_hits hf⟩

/-- If a finite minimal limit exists, it is the unique minimal limit,
including for tuples containing the formal point at infinity. -/
theorem IsMinimalLimitSet.eq_of_finite {n m : ℕ}
    {A : Set (Fin n → VFType (M := M))} {a : Fin n → VFType (M := M)}
    {f : (Fin n → VFType (M := M)) → Set (Fin m → VFType (M := M))}
    {L₁ L₂ : Set (Fin m → LimitPoint M)} (h₁ : IsMinimalLimitSet A a f L₁)
    (h₂ : IsMinimalLimitSet A a f L₂) (hf₁ : L₁.Finite) : L₁ = L₂ := by
  have hsub : L₂ ⊆ L₁ := fun _ hb => h₁.1.mem_of_frequently_hits hf₁ (h₂.frequently_hits hb)
  exact Set.Subset.antisymm
    (fun _ hb => h₂.1.mem_of_frequently_hits (hf₁.subset hsub) (h₁.frequently_hits hb)) hsub

/-- The finite case of Lemma 9.3, allowing the formal infinity in the
output coordinates. -/
theorem IsMinimalLimitSet.union_of_finite {n m : ℕ}
    {A : Set (Fin n → VFType (M := M))} {a : Fin n → VFType (M := M)}
    {f₁ f₂ : (Fin n → VFType (M := M)) → Set (Fin m → VFType (M := M))}
    {L₁ L₂ : Set (Fin m → LimitPoint M)} (h₁ : IsMinimalLimitSet A a f₁ L₁)
    (h₂ : IsMinimalLimitSet A a f₂ L₂) (hf₁ : L₁.Finite) (hf₂ : L₂.Finite) :
    IsMinimalLimitSet A a (fun x => f₁ x ∪ f₂ x) (L₁ ∪ L₂) := by
  constructor
  · rw [isLimitSet_iff]
    intro ε
    obtain ⟨δ₁, hδ₁⟩ := (isLimitSet_iff A a f₁ L₁).mp h₁.1 ε
    obtain ⟨δ₂, hδ₂⟩ := (isLimitSet_iff A a f₂ L₂).mp h₂.1 ε
    refine ⟨max δ₁ δ₂, fun x hx hnear y hy => ?_⟩
    rcases hy with hy | hy
    · obtain ⟨b, hb, hyb⟩ := hδ₁ x hx (vfBall_anti (le_max_left _ _) hnear) y hy
      exact ⟨b, Or.inl hb, hyb⟩
    · obtain ⟨b, hb, hyb⟩ := hδ₂ x hx (vfBall_anti (le_max_right _ _) hnear) y hy
      exact ⟨b, Or.inr hb, hyb⟩
  · intro L hL hlim
    obtain ⟨hsub, hne⟩ := Set.ssubset_iff_subset_ne.mp hL
    have hf := (hf₁.union hf₂).subset hsub
    apply hne (Set.Subset.antisymm hsub ?_)
    intro b hb
    apply hlim.mem_of_frequently_hits hf
    intro ε δ
    rcases hb with hb | hb
    · obtain ⟨x, hx, hnear, y, hy, hyb⟩ := h₁.frequently_hits hb ε δ
      exact ⟨x, hx, hnear, y, Or.inl hy, hyb⟩
    · obtain ⟨x, hx, hnear, y, hy, hyb⟩ := h₂.frequently_hits hb ε δ
      exact ⟨x, hx, hnear, y, Or.inr hy, hyb⟩

/-- A finite set of candidate limits contains a minimal limit set. -/
theorem IsLimitSet.exists_minimal_subset {n m : ℕ}
    {A : Set (Fin n → VFType (M := M))} {a : Fin n → VFType (M := M)}
    {f : (Fin n → VFType (M := M)) → Set (Fin m → VFType (M := M))}
    {L : Set (Fin m → LimitPoint M)} (hL : IsLimitSet A a f L) (hf : L.Finite) :
    ∃ K ⊆ L, IsMinimalLimitSet A a f K ∧ K.Finite := by
  classical
  let P (k : ℕ) := ∃ K ⊆ L, IsLimitSet A a f K ∧ K.ncard = k
  have hP : ∃ k, P k := ⟨L.ncard, L, Set.Subset.rfl, hL, rfl⟩
  obtain ⟨K, hKL, hK, hcard⟩ := Nat.find_spec hP
  have hKf := hf.subset hKL
  refine ⟨K, hKL, ⟨hK, ?_⟩, hKf⟩
  intro K' hsub hlimit
  have hmin := Nat.find_min' hP (show P K'.ncard from
    ⟨K', hsub.subset.trans hKL, hlimit, rfl⟩)
  exact (not_lt_of_ge hmin) (hcard ▸ Set.ncard_lt_ncard hsub hKf)

end SpecialTransformations.Section9
