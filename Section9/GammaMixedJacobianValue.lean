import Section9.MixedJacobianFibreTransfer
import Section5.GammaInvariantLogic
import Section8.GammaRadiusBase

/-! Gamma-definability of the total mixed Jacobian.

A mixed map whose graph is Gamma-definable over a base `B` has a total
mixed Jacobian (the determinant of the mixed derivative where it exists,
zero elsewhere) whose graph is Gamma-definable over `B`.

Strategy: the Gamma graph of `f` is the fibre, at representatives of finitely
many Gamma points, of a code-invariant relation `R` over `B.real`. Carrying
the codes as extra RV labels turns `R` into one mixed map `F` over `B.real`;
the existing definability of total Jacobians applies to `F`. Since mixed
derivatives only see fixed-label fibres (`FibreMatch`), the Jacobian of `F`
at code labels `t` is the Jacobian of the map with graph `R_t`; this family
is code-invariant and its fibre at the representatives is the Jacobian of
`f`. No input beyond the existing definability API is used. -/

set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.Section4.rawVFSpace SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.rawMixedSpace

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point gammaPointCode gammaPointSort GammaGraphDefinable vfAt)

namespace SpecialTransformations.Section9

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n r s k : ℕ}

/-- The base point of a point whose last `k` RV labels carry codes. -/
def codeBase (w : (Fin n → VFType (M := M)) × (Fin (r+k) → CanonicalRV.RVSort M)) :
    (Fin n → VFType (M := M)) × (Fin r → CanonicalRV.RVSort M) :=
  (w.1, fun i => w.2 (Fin.castAdd k i))

/-- The raw codes carried by the last `k` RV labels. -/
def codeLabels (w : (Fin n → VFType (M := M)) × (Fin (r+k) → CanonicalRV.RVSort M)) : Fin k → M :=
  fun i => (w.2 (Fin.natAdd r i)).val

/-- The fibre relation of a code family, read with codes carried as labels. -/
def codeFamilyRel (R : Set ((Fin k → M) × (Fin ((n+r)+(n+s)) → M)))
    (w : (Fin n → VFType (M := M)) × (Fin (r+k) → CanonicalRV.RVSort M))
    (y : (Fin n → VFType (M := M)) × (Fin s → CanonicalRV.RVSort M)) : Prop :=
  (codeLabels w, Fin.append (gammaPointCode (codeBase w)) (gammaPointCode y)) ∈ R

/-- Index map reading a code family relation from label-carrying codes. -/
def codeFamilyIndex : Fin k ⊕ Fin ((n+r)+(n+s)) → (Fin n ⊕ Fin (r+k)) ⊕ (Fin n ⊕ Fin s) :=
  Sum.elim (fun i => .inl (.inr (Fin.natAdd r i)))
    (Fin.append (Fin.append (fun i => .inl (.inl i)) (fun i => .inl (.inr (Fin.castAdd k i))))
      (Fin.append (fun i => .inr (.inl i)) (fun i => .inr (.inr i))))

theorem codeFamily_codes (w : (Fin n → VFType (M := M)) × (Fin (r+k) → CanonicalRV.RVSort M))
    (y : (Fin n → VFType (M := M)) × (Fin s → CanonicalRV.RVSort M)) :
    Sum.elim (mixedValues w) (mixedValues y) ∘ (codeFamilyIndex (n := n) (r := r) (s := s) (k := k)) ∘ Sum.inl =
      codeLabels w ∧
    Sum.elim (mixedValues w) (mixedValues y) ∘ (codeFamilyIndex (n := n) (r := r) (s := s) (k := k)) ∘ Sum.inr =
      Fin.append (gammaPointCode (codeBase w)) (gammaPointCode y) := by
  constructor
  · rfl
  · funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [Function.comp_apply, codeFamilyIndex, Sum.elim_inr, Fin.append_left]
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp [Fin.append_left, gammaPointCode, codeBase, vfAt, mixedValues, vfValues]
      · simp [Fin.append_right, gammaPointCode, codeBase, mixedValues, rvValues]
    · simp only [Function.comp_apply, codeFamilyIndex, Sum.elim_inr, Fin.append_right]
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp [Fin.append_left, gammaPointCode, vfAt, mixedValues, vfValues]
      · simp [Fin.append_right, gammaPointCode, mixedValues, rvValues]

theorem codeFamilyRel_definable (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M}
    (R : Set ((Fin k → M) × (Fin ((n+r)+(n+s)) → M)))
    (hR : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin k ⊕ Fin ((n+r)+(n+s)))
      {z | (z ∘ Sum.inl, z ∘ Sum.inr) ∈ R}) :
    (rawMixedSpace (M := M) n (r+k)).RelationDefinable (rawMixedSpace n s) S (codeFamilyRel R) := by
  rw [Section8.normalize_eq_of_isCanonical hc] at hR
  have h := ((hR.preimage_comp (codeFamilyIndex (n := n) (r := r) (s := s) (k := k))).inter
    (((rawMixedSpace (M := M) n (r+k)).definable_domain S).preimage_comp Sum.inl)).inter
    (((rawMixedSpace (M := M) n s).definable_domain S).preimage_comp Sum.inr)
  change S.Definable LRV _
  convert h using 1
  ext z
  constructor
  · rintro ⟨hx, hy, hR'⟩
    refine ⟨⟨?_, hx⟩, hy⟩
    have he : z = Sum.elim (mixedValues ((rawMixedSpace (M := M) n (r+k)).decode ⟨_, hx⟩))
        (mixedValues ((rawMixedSpace (M := M) n s).decode ⟨_, hy⟩)) := by
      rw [mixedValues_decode, mixedValues_decode]
      exact (Sum.elim_comp_inl_inr z).symm
    obtain ⟨h1, h2⟩ := codeFamily_codes ((rawMixedSpace (M := M) n (r+k)).decode ⟨_, hx⟩)
      ((rawMixedSpace (M := M) n s).decode ⟨_, hy⟩)
    change (z ∘ codeFamilyIndex ∘ Sum.inl, z ∘ codeFamilyIndex ∘ Sum.inr) ∈ R
    rw [he, h1, h2]
    exact hR'
  · rintro ⟨⟨hR', hx⟩, hy⟩
    refine ⟨hx, hy, ?_⟩
    have he : z = Sum.elim (mixedValues ((rawMixedSpace (M := M) n (r+k)).decode ⟨_, hx⟩))
        (mixedValues ((rawMixedSpace (M := M) n s).decode ⟨_, hy⟩)) := by
      rw [mixedValues_decode, mixedValues_decode]
      exact (Sum.elim_comp_inl_inr z).symm
    obtain ⟨h1, h2⟩ := codeFamily_codes ((rawMixedSpace (M := M) n (r+k)).decode ⟨_, hx⟩)
      ((rawMixedSpace (M := M) n s).decode ⟨_, hy⟩)
    change (z ∘ codeFamilyIndex ∘ Sum.inl, z ∘ codeFamilyIndex ∘ Sum.inr) ∈ R at hR'
    rw [he, h1, h2] at hR'
    exact hR'


/-! ### The family map on its uniqueness domain -/

/-- `y` is the unique output of the code family at `w`. -/
def codeFamilyGood (R : Set ((Fin k → M) × (Fin ((n+r)+(n+s)) → M)))
    (w : (Fin n → VFType (M := M)) × (Fin (r+k) → CanonicalRV.RVSort M))
    (y : (Fin n → VFType (M := M)) × (Fin s → CanonicalRV.RVSort M)) : Prop :=
  codeFamilyRel R w y ∧ ∀ y', codeFamilyRel R w y' → y' = y

theorem codeFamilyGood_definable (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M}
    (R : Set ((Fin k → M) × (Fin ((n+r)+(n+s)) → M)))
    (hR : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin k ⊕ Fin ((n+r)+(n+s)))
      {z | (z ∘ Sum.inl, z ∘ Sum.inr) ∈ R}) :
    (rawMixedSpace (M := M) n (r+k)).RelationDefinable (rawMixedSpace n s) S (codeFamilyGood R) := by
  let P := rawMixedSpace (M := M) n (r+k)
  let Q := rawMixedSpace (M := M) n s
  have hrel := codeFamilyRel_definable hc R hR
  have hneq : Q.RelationDefinable Q S (fun y y' => y ≠ y') := by
    have he := (Q.definable_prod_iff Q S (fun y y' => y = y')).mpr (Q.relation_eq_definable S)
    exact (Q.definable_prod_iff Q S _).mp (he.compl (Q.prod Q))
  have hbad : P.RelationDefinable Q S (fun w y => ∃ y', codeFamilyRel R w y' ∧ y' ≠ y) :=
    hrel.comp P Q Q hneq
  have hgood := ((P.definable_prod_iff Q S _).mpr hrel).inter (P.prod Q)
    (((P.definable_prod_iff Q S _).mpr hbad).compl (P.prod Q))
  have hgood' : (P.prod Q).Definable S {p | codeFamilyRel R p.1 p.2 ∧
      ¬ ∃ y', codeFamilyRel R p.1 y' ∧ y' ≠ p.2} := hgood
  apply ((P.definable_prod_iff Q S (fun w y => codeFamilyRel R w y ∧
      ¬ ∃ y', codeFamilyRel R w y' ∧ y' ≠ y)).mp hgood').congr P Q
  intro w y
  constructor
  · rintro ⟨h, hu⟩
    exact ⟨h, fun y' hy' => by_contra (fun hne => hu ⟨y', hy', hne⟩)⟩
  · rintro ⟨h, hu⟩
    exact ⟨h, fun ⟨y', hy', hne⟩ => hne (hu y' hy')⟩

/-- The domain of the code family map: points where the family has exactly one output. -/
def codeFamilyDomain (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M}
    (R : Set ((Fin k → M) × (Fin ((n+r)+(n+s)) → M)))
    (hR : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin k ⊕ Fin ((n+r)+(n+s)))
      {z | (z ∘ Sum.inl, z ∘ Sum.inr) ∈ R}) :
    DefSet (rawMixedSpace (M := M) n (r+k)) S :=
  ⟨{w | ∃ y, codeFamilyGood R w y}, (codeFamilyGood_definable hc R hR).exists_right _ _⟩

/-- The code family as one actual mixed map over the real parameters. -/
noncomputable def codeFamilyMap (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M}
    (R : Set ((Fin k → M) × (Fin ((n+r)+(n+s)) → M)))
    (hR : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin k ⊕ Fin ((n+r)+(n+s)))
      {z | (z ∘ Sum.inl, z ∘ Sum.inr) ∈ R}) :
    Map (codeFamilyDomain hc R hR) (DefSet.univ (rawMixedSpace (M := M) n s) S) :=
  Map.ofFunctionalRelation (R := codeFamilyGood R) (codeFamilyGood_definable hc R hR)
    (fun _ _ h => ⟨⟨_, h⟩, Set.mem_univ _⟩) (fun w => w.property)
    (fun _ y z hy hz => (hz.2 y hy.1))

theorem codeFamilyMap_good (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M}
    (R : Set ((Fin k → M) × (Fin ((n+r)+(n+s)) → M)))
    (hR : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin k ⊕ Fin ((n+r)+(n+s)))
      {z | (z ∘ Sum.inl, z ∘ Sum.inr) ∈ R}) (w : codeFamilyDomain hc R hR) :
    codeFamilyGood R w.val (codeFamilyMap hc R hR w).val :=
  Map.ofFunctionalRelation_graph _ _ _ _ w

/-! ### Transfer of total Jacobians along matching fibres -/

theorem FibreMatch.totalJacobian_iff {S S' : Set M} {r' s' : ℕ}
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {A' : DefSet (rawMixedSpace (M := M) n r') S'} {B' : DefSet (rawMixedSpace (M := M) n s') S'}
    (f : Map A B) (f' : Map A' B') (p : A) (p' : A') (h : FibreMatch f f' p p') (J : VFType (M := M)) :
    Sum.elim (mixedValues p.val) (fun _ : Fin 1 => J.val) ∈ totalMixedJacobianCodes f ↔
      Sum.elim (mixedValues p'.val) (fun _ : Fin 1 => J.val) ∈ totalMixedJacobianCodes f' := by
  rw [mem_totalMixedJacobianCodes_iff, mem_totalMixedJacobianCodes_iff]
  simp only [h.derivative_iff]


/-! ### Code-label joins and invariance -/

/-- Attach codes as the last `k` RV labels of a point. -/
def codeJoin (p : (Fin n → VFType (M := M)) × (Fin r → CanonicalRV.RVSort M)) (t : Fin k → Code (M := M)) :
    (Fin n → VFType (M := M)) × (Fin (r+k) → CanonicalRV.RVSort M) :=
  (p.1, Fin.append p.2 (fun i => (t i).val))

@[simp] theorem codeBase_codeJoin (p : (Fin n → VFType (M := M)) × (Fin r → CanonicalRV.RVSort M))
    (t : Fin k → Code (M := M)) : codeBase (codeJoin p t) = p := by
  refine Prod.ext rfl ?_
  funext i
  change Fin.append p.2 (fun i => (t i).val) (Fin.castAdd k i) = p.2 i
  exact Fin.append_left _ _ i

@[simp] theorem codeLabels_codeJoin (p : (Fin n → VFType (M := M)) × (Fin r → CanonicalRV.RVSort M))
    (t : Fin k → Code (M := M)) : codeLabels (codeJoin p t) = rawTuple t := by
  funext i
  change ((Fin.append p.2 (fun i => (t i).val)) (Fin.natAdd r i)).val = raw (t i)
  rw [Fin.append_right]
  rfl

theorem codeJoin_codeBase (w : (Fin n → VFType (M := M)) × (Fin (r+k) → CanonicalRV.RVSort M))
    (hw : Proper (codeLabels w)) : codeJoin (codeBase w) (ofRaw (codeLabels w) hw) = w := by
  refine Prod.ext rfl ?_
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · change Fin.append (codeBase w).2 (fun i => (ofRaw (codeLabels w) hw i).val) (Fin.castAdd k i) = _
    exact Fin.append_left _ _ i
  · change Fin.append (codeBase w).2 (fun i => (ofRaw (codeLabels w) hw i).val) (Fin.natAdd r i) = _
    rw [Fin.append_right]
    rfl

theorem codeFamilyRel_join_iff {sn : Fin ((n+r)+(n+s)) → SortTag} {S : Set M}
    (R : Relation S k ((n+r)+(n+s)) sn)
    (p : (Fin n → VFType (M := M)) × (Fin r → CanonicalRV.RVSort M))
    (y : (Fin n → VFType (M := M)) × (Fin s → CanonicalRV.RVSort M))
    (t u : Fin k → Code (M := M)) (h : values t = values u) :
    codeFamilyRel R.carrier (codeJoin p t) y ↔ codeFamilyRel R.carrier (codeJoin p u) y := by
  unfold codeFamilyRel
  rw [codeBase_codeJoin, codeBase_codeJoin, codeLabels_codeJoin, codeLabels_codeJoin]
  exact R.invariant t u h _

theorem codeFamilyGood_join_iff {sn : Fin ((n+r)+(n+s)) → SortTag} {S : Set M}
    (R : Relation S k ((n+r)+(n+s)) sn)
    (p : (Fin n → VFType (M := M)) × (Fin r → CanonicalRV.RVSort M))
    (y : (Fin n → VFType (M := M)) × (Fin s → CanonicalRV.RVSort M))
    (t u : Fin k → Code (M := M)) (h : values t = values u) :
    codeFamilyGood R.carrier (codeJoin p t) y ↔ codeFamilyGood R.carrier (codeJoin p u) y := by
  unfold codeFamilyGood
  simp only [codeFamilyRel_join_iff R p _ t u h]

theorem codeFamily_proper {sn : Fin ((n+r)+(n+s)) → SortTag} {S : Set M}
    (R : Relation S k ((n+r)+(n+s)) sn)
    {w : (Fin n → VFType (M := M)) × (Fin (r+k) → CanonicalRV.RVSort M)}
    {y : (Fin n → VFType (M := M)) × (Fin s → CanonicalRV.RVSort M)}
    (h : codeFamilyRel R.carrier w y) : Proper (codeLabels w) := (R.proper _ h).1


section FamilyMatches
variable (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M} {sn : Fin ((n+r)+(n+s)) → SortTag}
variable (R : Relation S k ((n+r)+(n+s)) sn)

theorem codeFamily_good_unique {w : (Fin n → VFType (M := M)) × (Fin (r+k) → CanonicalRV.RVSort M)}
    {y y' : (Fin n → VFType (M := M)) × (Fin s → CanonicalRV.RVSort M)}
    (hy : codeFamilyGood R.carrier w y) (hy' : codeFamilyGood R.carrier w y') : y = y' :=
  hy'.2 y hy.1

theorem codeFamilyDomain_join_iff
    (p : (Fin n → VFType (M := M)) × (Fin r → CanonicalRV.RVSort M))
    (t u : Fin k → Code (M := M)) (h : values t = values u) :
    codeJoin p t ∈ (codeFamilyDomain hc R.carrier R.definable).carrier ↔
      codeJoin p u ∈ (codeFamilyDomain hc R.carrier R.definable).carrier := by
  change (∃ y, codeFamilyGood R.carrier (codeJoin p t) y) ↔ ∃ y, codeFamilyGood R.carrier (codeJoin p u) y
  simp only [codeFamilyGood_join_iff R p _ t u h]

/-- Changing codes with equal values matches the fibres of the family map. -/
theorem codeFamily_fibreMatch_codes
    (p : (Fin n → VFType (M := M)) × (Fin r → CanonicalRV.RVSort M))
    (t u : Fin k → Code (M := M)) (h : values t = values u)
    (hw : codeJoin p t ∈ (codeFamilyDomain hc R.carrier R.definable).carrier)
    (hw' : codeJoin p u ∈ (codeFamilyDomain hc R.carrier R.definable).carrier) :
    FibreMatch (codeFamilyMap hc R.carrier R.definable) (codeFamilyMap hc R.carrier R.definable)
      ⟨_, hw⟩ ⟨_, hw'⟩ := by
  have hval : ∀ (x : Fin n → VFType (M := M))
      (h₁ : codeJoin (x, p.2) t ∈ (codeFamilyDomain hc R.carrier R.definable).carrier)
      (h₂ : codeJoin (x, p.2) u ∈ (codeFamilyDomain hc R.carrier R.definable).carrier),
      (codeFamilyMap hc R.carrier R.definable ⟨_, h₁⟩).val =
        (codeFamilyMap hc R.carrier R.definable ⟨_, h₂⟩).val := by
    intro x h₁ h₂
    have g₁ := codeFamilyMap_good hc R.carrier R.definable ⟨_, h₁⟩
    have g₂ := codeFamilyMap_good hc R.carrier R.definable ⟨_, h₂⟩
    exact codeFamily_good_unique R ((codeFamilyGood_join_iff R _ _ t u h).mp g₁) g₂
  refine ⟨rfl, fun x => codeFamilyDomain_join_iff hc R (x, p.2) t u h, ?_, ?_⟩
  · intro x h₁ h₂
    exact congrArg Prod.fst (hval x h₁ h₂)
  · intro x h₁ h₂
    change (codeFamilyMap hc R.carrier R.definable ⟨codeJoin (x, p.2) t, h₁⟩).val.2 =
        (codeFamilyMap hc R.carrier R.definable ⟨codeJoin p t, hw⟩).val.2 ↔
      (codeFamilyMap hc R.carrier R.definable ⟨codeJoin (x, p.2) u, h₂⟩).val.2 =
        (codeFamilyMap hc R.carrier R.definable ⟨codeJoin p u, hw'⟩).val.2
    rw [hval x h₁ h₂, hval p.1 hw hw']

/-- At codes whose family fibre is the graph of `f`, the family map matches `f`. -/
theorem codeFamily_fibreMatch_graph {S' : Set M} {A : DefSet (rawMixedSpace (M := M) n r) S'}
    {D : DefSet (rawMixedSpace (M := M) n s) S'} (f : Map A D) (t : Fin k → Code (M := M))
    (hgraph : ∀ q y, codeFamilyRel R.carrier (codeJoin q t) y ↔ ∃ a : A, a.val = q ∧ (f a).val = y)
    (a : A) :
    ∃ hw : codeJoin a.val t ∈ (codeFamilyDomain hc R.carrier R.definable).carrier,
      FibreMatch f (codeFamilyMap hc R.carrier R.definable) a ⟨_, hw⟩ := by
  have hmem : ∀ q, q ∈ A.carrier ↔ codeJoin q t ∈ (codeFamilyDomain hc R.carrier R.definable).carrier := by
    intro q
    constructor
    · intro hq
      refine ⟨(f ⟨q, hq⟩).val, (hgraph q _).mpr ⟨⟨q, hq⟩, rfl, rfl⟩, fun y' hy' => ?_⟩
      obtain ⟨a', ha', rfl⟩ := (hgraph q y').mp hy'
      have he : a' = ⟨q, hq⟩ := Subtype.ext ha'
      rw [he]
    · rintro ⟨y, hy, _⟩
      obtain ⟨a', ha', _⟩ := (hgraph q y).mp hy
      exact ha' ▸ a'.property
  have hval : ∀ q (h₁ : q ∈ A.carrier)
      (h₂ : codeJoin q t ∈ (codeFamilyDomain hc R.carrier R.definable).carrier),
      (f ⟨q, h₁⟩).val = (codeFamilyMap hc R.carrier R.definable ⟨_, h₂⟩).val := by
    intro q h₁ h₂
    have g := codeFamilyMap_good hc R.carrier R.definable ⟨_, h₂⟩
    obtain ⟨a', ha', hfa⟩ := (hgraph q _).mp g.1
    have he : a' = ⟨q, h₁⟩ := Subtype.ext ha'
    rw [← he, hfa]
  have hw := (hmem a.val).mp a.property
  refine ⟨hw, rfl, fun x => hmem (x, a.val.2), ?_, ?_⟩
  · intro x h₁ h₂
    exact congrArg Prod.fst (hval (x, a.val.2) h₁ h₂)
  · intro x h₁ h₂
    have ha : (f a).val = (codeFamilyMap hc R.carrier R.definable ⟨_, hw⟩).val := by
      have := hval a.val a.property hw
      exact this
    change (f ⟨(x, a.val.2), h₁⟩).val.2 = (f a).val.2 ↔
      (codeFamilyMap hc R.carrier R.definable ⟨codeJoin (x, a.val.2) t, h₂⟩).val.2 =
        (codeFamilyMap hc R.carrier R.definable ⟨codeJoin a.val t, hw⟩).val.2
    rw [hval (x, a.val.2) h₁ h₂, ha]

end FamilyMatches


/-! ### The Gamma Jacobian relation -/

theorem gammaPointCode_append_injective {a b u w : ℕ} {p p' : Point (M := M) a b} {q q' : Point (M := M) u w}
    (h : Fin.append (gammaPointCode p) (gammaPointCode q) = Fin.append (gammaPointCode p') (gammaPointCode q')) :
    p = p' ∧ q = q' := by
  have hp : gammaPointCode p = gammaPointCode p' := by
    funext i
    simpa only [Fin.append_left] using congrFun h (Fin.castAdd (u+w) i)
  have hq : gammaPointCode q = gammaPointCode q' := by
    funext i
    simpa only [Fin.append_right] using congrFun h (Fin.natAdd (a+b) i)
  have inj : ∀ {c d : ℕ} {x y : Point (M := M) c d}, gammaPointCode x = gammaPointCode y → x = y := by
    intro c d x y hxy
    apply Prod.ext
    · funext i
      apply Subtype.ext
      simpa only [gammaPointCode, vfAt, Fin.append_left] using congrFun hxy (Fin.castAdd d i)
    · funext i
      apply Subtype.ext
      simpa only [gammaPointCode, Fin.append_right] using congrFun hxy (Fin.natAdd c i)
  exact ⟨inj hp, inj hq⟩

theorem gammaPointCode_append_sorted {a b u w : ℕ} (p : Point (M := M) a b) (q : Point (M := M) u w) :
    ∀ i, sortEval (Fin.append (gammaPointSort a b) (gammaPointSort u w) i)
      (Fin.append (gammaPointCode p) (gammaPointCode q) i) := by
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [Fin.append_left]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [gammaPointSort, gammaPointCode, Fin.append_left, sortEval, vfAt]
      exact (p.1 j).property
    · simp only [gammaPointSort, gammaPointCode, Fin.append_right, sortEval]
      exact (p.2 j).property
  · simp only [Fin.append_right]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [gammaPointSort, gammaPointCode, Fin.append_left, sortEval, vfAt]
      exact (q.1 j).property
    · simp only [gammaPointSort, gammaPointCode, Fin.append_right, sortEval]
      exact (q.2 j).property

/-- The one-coordinate VF point. -/
def vfPoint1 (v : VFType (M := M)) : Point (M := M) 1 0 := (fun _ => v, Fin.elim0)

/-- Index map reading the Jacobian relation from label-carrying codes. -/
def codeJacobianIndex : (Fin n ⊕ Fin (r+k)) ⊕ Fin 1 → Fin k ⊕ Fin ((n+r)+(1+0)) :=
  Sum.elim (Sum.elim (fun i => .inr (Fin.castAdd (1+0) (Fin.castAdd r i)))
    (Fin.append (fun j => .inr (Fin.castAdd (1+0) (Fin.natAdd n j))) (fun c => .inl c)))
    (fun _ => .inr (Fin.natAdd (n+r) (Fin.castAdd 0 0)))

theorem codeJacobianIndex_iff (zz : Fin k ⊕ Fin ((n+r)+(1+0)) → M)
    (w : (Fin n → VFType (M := M)) × (Fin (r+k) → CanonicalRV.RVSort M)) (v : VFType (M := M)) :
    zz ∘ codeJacobianIndex (n := n) (r := r) (k := k) = Sum.elim (mixedValues w) (fun _ : Fin 1 => v.val) ↔
      zz ∘ Sum.inl = codeLabels w ∧
        zz ∘ Sum.inr = Fin.append (gammaPointCode (codeBase w)) (gammaPointCode (vfPoint1 v)) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · funext c
      have := congrFun h (.inl (.inr (Fin.natAdd r c)))
      simpa [codeJacobianIndex, Fin.append_right, mixedValues, rvValues, codeLabels] using this
    · funext j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · have := congrFun h (.inl (.inl i))
          simpa [codeJacobianIndex, Fin.append_left, gammaPointCode, codeBase, vfAt, mixedValues,
            vfValues] using this
        · have := congrFun h (.inl (.inr (Fin.castAdd k i)))
          simpa [codeJacobianIndex, Fin.append_left, Fin.append_right, gammaPointCode, codeBase,
            mixedValues, rvValues] using this
      · refine Fin.addCases (fun i => ?_) (fun i => Fin.elim0 i) j
        have hi : i = 0 := Subsingleton.elim i 0
        subst hi
        have := congrFun h (.inr 0)
        have happ : Fin.append (fun _ : Fin 1 => v.val) (fun i : Fin 0 => ((Fin.elim0 i :
            CanonicalRV.RVSort M)).val) 0 = v.val := Fin.append_left _ _ 0
        simpa [codeJacobianIndex, Fin.append_left, Fin.append_right, gammaPointCode, vfPoint1,
          vfAt, happ] using this
  · rintro ⟨hl, hb⟩
    funext idx
    rcases idx with (i | j) | i
    · have := congrFun hb (Fin.castAdd (1+0) (Fin.castAdd r i))
      simpa [codeJacobianIndex, Fin.append_left, gammaPointCode, codeBase, vfAt, mixedValues,
        vfValues] using this
    · refine Fin.addCases (fun j => ?_) (fun c => ?_) j
      · have := congrFun hb (Fin.castAdd (1+0) (Fin.natAdd n j))
        simpa [codeJacobianIndex, Fin.append_left, Fin.append_right, gammaPointCode, codeBase,
          mixedValues, rvValues] using this
      · have := congrFun hl c
        simpa [codeJacobianIndex, Fin.append_right, mixedValues, rvValues, codeLabels] using this
    · have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      have := congrFun hb (Fin.natAdd (n+r) (Fin.castAdd 0 0))
      have happ : Fin.append (fun _ : Fin 1 => v.val) (fun i : Fin 0 => ((Fin.elim0 i :
          CanonicalRV.RVSort M)).val) 0 = v.val := Fin.append_left _ _ 0
      simpa [codeJacobianIndex, Fin.append_left, Fin.append_right, gammaPointCode, vfPoint1,
        vfAt, happ] using this

/-- **Gamma total Jacobian.** The total mixed Jacobian of a mixed map with a Gamma graph
over `B` has a Gamma graph over `B`. -/
theorem gamma_total_mixed_jacobian_graph (hc : CanonicalStructure.IsCanonical (M := M))
    {B : Base (M := M)} {S : Set M} (hn : 0 < n)
    {A : DefSet (rawMixedSpace (M := M) n r) S} {D : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A D)
    (hf : GammaGraphDefinable B (fun (p : Point (M := M) n r) (q : Point (M := M) n s) =>
      ∃ a : A, a.val = p ∧ (f a).val = q)) :
    GammaGraphDefinable B (fun (p : Point (M := M) n r) (z : Point (M := M) 1 0) =>
      ∃ _ : p ∈ A.carrier, Sum.elim (mixedValues p) (fun _ : Fin 1 => (vfAt z 0).val) ∈
        totalMixedJacobianCodes f) := by
  obtain ⟨k, γ, hγ, R, hfib⟩ := hf
  let D' := codeFamilyDomain hc R.carrier R.definable
  let F := codeFamilyMap hc R.carrier R.definable
  let t₀ := representatives γ
  have hgraph : ∀ q y, codeFamilyRel R.carrier (codeJoin q t₀) y ↔
      ∃ a : A, a.val = q ∧ (f a).val = y := by
    intro q y
    unfold codeFamilyRel
    rw [codeBase_codeJoin, codeLabels_codeJoin]
    change Fin.append (gammaPointCode q) (gammaPointCode y) ∈ R.fibre γ ↔ _
    rw [hfib]
    constructor
    · rintro ⟨p', q', hpq, he⟩
      obtain ⟨rfl, rfl⟩ := gammaPointCode_append_injective he
      exact hpq
    · intro h
      exact ⟨q, y, h, rfl⟩
  let carrierSet : Set ((Fin k → M) × (Fin ((n+r)+(1+0)) → M)) :=
    {pr | ∃ w : D'.carrier, ∃ v : VFType (M := M), pr.1 = codeLabels w.val ∧
      pr.2 = Fin.append (gammaPointCode (codeBase w.val)) (gammaPointCode (vfPoint1 v)) ∧
      Sum.elim (mixedValues w.val) (fun _ : Fin 1 => v.val) ∈ totalMixedJacobianCodes F}
  -- invariance under change of codes
  have hinv : ∀ t u : Fin k → Code (M := M), values t = values u →
      ∀ b, (rawTuple t, b) ∈ carrierSet → (rawTuple u, b) ∈ carrierSet := by
    rintro t u htu b ⟨w, v, hl, hb, hJ⟩
    obtain ⟨y, hy⟩ := w.property
    have hp : Proper (codeLabels w.val) := codeFamily_proper R hy.1
    have ht : ofRaw (codeLabels w.val) hp = t := rawTuple_injective (by rw [rawTuple_ofRaw]; exact hl.symm)
    have hw : codeJoin (codeBase w.val) t = w.val := by rw [← ht]; exact codeJoin_codeBase w.val hp
    have hwt : codeJoin (codeBase w.val) t ∈ D'.carrier := by rw [hw]; exact w.property
    have hwu := (codeFamilyDomain_join_iff hc R (codeBase w.val) t u htu).mp hwt
    have hm := codeFamily_fibreMatch_codes hc R (codeBase w.val) t u htu hwt hwu
    refine ⟨⟨_, hwu⟩, v, (codeLabels_codeJoin _ u).symm, ?_, ?_⟩
    · change b = Fin.append (gammaPointCode (codeBase (codeJoin (codeBase w.val) u))) _
      rw [codeBase_codeJoin]
      exact hb
    · have hJ' : Sum.elim (mixedValues (⟨_, hwt⟩ : D'.carrier).val) (fun _ : Fin 1 => v.val) ∈
          totalMixedJacobianCodes F := by
        have he : (⟨_, hwt⟩ : D'.carrier) = w := Subtype.ext hw
        rw [he]
        exact hJ
      exact (FibreMatch.totalJacobian_iff F F _ _ hm v).mp hJ'
  -- the fibre at the representatives is the Jacobian graph of `f`
  have hfibre : {b | (rawTuple t₀, b) ∈ carrierSet} = {z | ∃ p q, (∃ _ : p ∈ A.carrier,
      Sum.elim (mixedValues p) (fun _ : Fin 1 => (vfAt q 0).val) ∈ totalMixedJacobianCodes f) ∧
      Fin.append (gammaPointCode p) (gammaPointCode q) = z} := by
    ext b
    constructor
    · rintro ⟨w, v, hl, hb, hJ⟩
      obtain ⟨y, hy⟩ := w.property
      have hp : Proper (codeLabels w.val) := codeFamily_proper R hy.1
      have ht : ofRaw (codeLabels w.val) hp = t₀ :=
        rawTuple_injective (by rw [rawTuple_ofRaw]; exact hl.symm)
      have hw : codeJoin (codeBase w.val) t₀ = w.val := by rw [← ht]; exact codeJoin_codeBase w.val hp
      have hy' : codeFamilyRel R.carrier (codeJoin (codeBase w.val) t₀) y := by rw [hw]; exact hy.1
      obtain ⟨a, ha, _⟩ := (hgraph _ y).mp hy'
      obtain ⟨hw₀, hm⟩ := codeFamily_fibreMatch_graph hc R f t₀ hgraph a
      have hJ' : Sum.elim (mixedValues (⟨_, hw₀⟩ : D'.carrier).val) (fun _ : Fin 1 => v.val) ∈
          totalMixedJacobianCodes F := by
        have he : (⟨_, hw₀⟩ : D'.carrier) = w := Subtype.ext (by
          change codeJoin a.val t₀ = w.val
          rw [ha]
          exact hw)
        rw [he]
        exact hJ
      have hJf := (FibreMatch.totalJacobian_iff f F a _ hm v).mpr hJ'
      refine ⟨a.val, vfPoint1 v, ⟨a.property, hJf⟩, ?_⟩
      have hb' : b = Fin.append (gammaPointCode (codeBase w.val)) (gammaPointCode (vfPoint1 v)) := hb
      rw [hb', ← ha]
    · rintro ⟨p, q, ⟨hpA, hJ⟩, rfl⟩
      obtain ⟨hw₀, hm⟩ := codeFamily_fibreMatch_graph hc R f t₀ hgraph ⟨p, hpA⟩
      have hJF := (FibreMatch.totalJacobian_iff f F ⟨p, hpA⟩ _ hm (vfAt q 0)).mp hJ
      refine ⟨⟨_, hw₀⟩, vfAt q 0, (codeLabels_codeJoin _ _).symm, ?_, hJF⟩
      change Fin.append (gammaPointCode p) (gammaPointCode q) =
        Fin.append (gammaPointCode (codeBase (codeJoin p t₀))) (gammaPointCode (vfPoint1 (vfAt q 0)))
      rw [codeBase_codeJoin]
      have hq : q = vfPoint1 (vfAt q 0) := by
        refine Prod.ext ?_ (funext (fun i => Fin.elim0 i))
        funext i
        have hi : i = 0 := Subsingleton.elim i 0
        rw [hi]
        rfl
      rw [← hq]
  -- definability over the real base
  let P' := rawMixedSpace (M := M) n (r+k)
  let ι := codeJacobianIndex (n := n) (r := r) (k := k)
  let T' : Set ((Fin n ⊕ Fin (r+k)) ⊕ Fin 1 → M) :=
    (fun g => g ∘ Sum.inl) ⁻¹' P'.preimage D'.carrier ∩
      (fun g => g ∘ fun _ : Fin 1 => (Sum.inr 0 : (Fin n ⊕ Fin (r+k)) ⊕ Fin 1)) ⁻¹'
        (rawVFSpace (M := M) 1).domain ∩ totalMixedJacobianCodes F
  have hT' : (B.real).Definable LRV T' :=
    ((D'.definable.preimage_comp Sum.inl).inter
      (((rawVFSpace (M := M) 1).definable_domain B.real).preimage_comp (fun _ : Fin 1 => Sum.inr 0))).inter
      (totalMixedJacobianCodes_definable hn F)
  have hcodes : {zz : Fin k ⊕ Fin ((n+r)+(1+0)) → M | (zz ∘ Sum.inl, zz ∘ Sum.inr) ∈ carrierSet} =
      (fun zz : Fin k ⊕ Fin ((n+r)+(1+0)) → M => zz ∘ ι) ⁻¹' T' := by
    ext zz
    constructor
    · rintro ⟨w, v, hl, hb, hJ⟩
      have hE := (codeJacobianIndex_iff zz w.val v).mpr ⟨hl, hb⟩
      change zz ∘ ι ∈ T'
      rw [hE]
      refine ⟨⟨?_, ?_⟩, hJ⟩
      · refine ⟨mixedValues_mem_domain (M := M) w.val, ?_⟩
        change (rawMixedSpace (M := M) n (r+k)).decode ⟨mixedValues w.val, _⟩ ∈ D'.carrier
        have hd : (rawMixedSpace (M := M) n (r+k)).decode ⟨mixedValues w.val, mixedValues_mem_domain w.val⟩ =
            w.val := mixedValues_injective (mixedValues_decode _)
        rw [hd]
        exact w.property
      · exact ⟨fun _ => v, rfl⟩
    · rintro ⟨⟨⟨hx, hD⟩, hvf⟩, hJ⟩
      let w : D'.carrier := ⟨_, hD⟩
      let v := (rawVFSpace (M := M) 1).decode ⟨_, hvf⟩ 0
      have hv : v.val = zz (ι (.inr 0)) := congrFun (vfValues_decode ⟨_, hvf⟩) 0
      have hE : zz ∘ ι = Sum.elim (mixedValues w.val) (fun _ : Fin 1 => v.val) := by
        have hm : mixedValues w.val = zz ∘ ι ∘ Sum.inl := mixedValues_decode _
        funext idx
        rcases idx with i | i
        · exact (congrFun hm i).symm
        · have hi : i = 0 := Subsingleton.elim i 0
          subst hi
          exact hv.symm
      obtain ⟨hl, hb⟩ := (codeJacobianIndex_iff zz w.val v).mp hE
      refine ⟨w, v, hl, hb, ?_⟩
      rw [← hE]
      exact hJ
  have hdef : @Set.Definable M B.real LRV (CanonicalStructure.normalize (M := M))
      (Fin k ⊕ Fin ((n+r)+(1+0))) {zz | (zz ∘ Sum.inl, zz ∘ Sum.inr) ∈ carrierSet} := by
    rw [Section8.normalize_eq_of_isCanonical hc, hcodes]
    exact hT'.preimage_comp ι
  let R' : Relation B.real k ((n+r)+(1+0)) (Fin.append (gammaPointSort n r) (gammaPointSort 1 0)) :=
    { carrier := carrierSet
      definable := hdef
      proper := by
        rintro ⟨c, b⟩ ⟨w, v, hl, hb, _⟩
        obtain ⟨y, hy⟩ := w.property
        refine ⟨hl ▸ codeFamily_proper R hy.1, ?_⟩
        rw [hb]
        exact gammaPointCode_append_sorted _ _
      invariant := fun t u htu b => ⟨hinv t u htu b, hinv u t htu.symm b⟩ }
  refine ⟨k, γ, hγ, R', ?_⟩
  change {b | (rawTuple (representatives γ), b) ∈ carrierSet} = _
  exact hfibre


/-- **Gamma total Jacobian map.** A mixed map with a Gamma graph over `B` (positive VF
dimension) has a total Jacobian map with a Gamma graph over `B`, equal to the Jacobian
determinant wherever the mixed derivative exists. Gamma counterpart of
`exists_totalMixedJacobianMap_of_pos`. -/
theorem gamma_exists_totalMixedJacobianMap (hc : CanonicalStructure.IsCanonical (M := M))
    {B : Base (M := M)} {S : Set M} (hn : 0 < n)
    {A : DefSet (rawMixedSpace (M := M) n r) S} {D : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A D)
    (hf : GammaGraphDefinable B (fun (p : Point (M := M) n r) (q : Point (M := M) n s) =>
      ∃ a : A, a.val = p ∧ (f a).val = q)) :
    ∃ j : Map A (DefSet.univ (rawVFSpace (M := M) 1) S),
      GammaGraphDefinable B (fun (p : Point (M := M) n r) (z : Point (M := M) 1 0) =>
        ∃ a : A, a.val = p ∧ (j a).val = z.1) ∧
      ∀ p L, HasMixedVFDerivativeAt f p L → (j p).val 0 = (LinearMap.toMatrix' L).det := by
  let P := rawMixedSpace (M := M) n r
  let Q := rawVFSpace (M := M) 1
  let R (x : P.Carrier) (y : Q.Carrier) :=
    x ∈ A.carrier ∧ Sum.elim (mixedValues x) (fun i => (y i).val) ∈ totalMixedJacobianCodes f
  have hR : P.RelationDefinable Q S R := by
    have h := (A.definable.preimage_comp (Sum.inl : P.Index → P.Index ⊕ Q.Index)).inter
      (((Q.domain_definable.mono (Set.empty_subset S)).preimage_comp Sum.inr).inter
        (totalMixedJacobianCodes_definable hn f))
    change S.Definable LRV (P.relation Q R)
    convert h using 1
    ext z
    constructor
    · rintro ⟨hx, hy, hA, hz⟩
      refine ⟨⟨hx, hA⟩, hy, ?_⟩
      change Sum.elim (mixedValues (P.decode ⟨_, hx⟩)) (vfValues (Q.decode ⟨_, hy⟩)) ∈ _ at hz
      rw [mixedValues_decode, vfValues_decode] at hz
      exact (Sum.elim_comp_inl_inr z) ▸ hz
    · rintro ⟨⟨hx,hA⟩, hy, hz⟩
      refine ⟨hx, hy, hA, ?_⟩
      change Sum.elim (mixedValues (P.decode ⟨_, hx⟩)) (vfValues (Q.decode ⟨_, hy⟩)) ∈ _
      rw [mixedValues_decode, vfValues_decode]
      exact (Sum.elim_comp_inl_inr z).symm ▸ hz
  have hdom (x y) (h : R x y) : x ∈ A.carrier ∧ y ∈ (DefSet.univ Q S).carrier :=
    ⟨h.1, Set.mem_univ _⟩
  have hcode (y : Q.Carrier) : (fun i => (y i).val) = fun _ => (y 0).val := by
    funext i
    fin_cases i
    rfl
  have htotal (p : A) : ∃ y, R p.val y := by
    obtain ⟨J, hJ, _⟩ := existsUnique_totalMixedJacobianValue f p
    exact ⟨fun _ => J, p.property, hJ⟩
  have huniq (x y z) (hy : R x y) (hz : R x z) : y = z := by
    obtain ⟨J, _, hJ⟩ := existsUnique_totalMixedJacobianValue f ⟨x, hy.1⟩
    have hy' := hy.2
    have hz' := hz.2
    rw [hcode y] at hy'
    rw [hcode z] at hz'
    funext i
    fin_cases i
    exact (hJ _ hy').trans (hJ _ hz').symm
  let J : Map A (DefSet.univ Q S) := Map.ofFunctionalRelation hR hdom htotal huniq
  have hJgraph (a : A) : R a.val (J a).val := Map.ofFunctionalRelation_graph hR hdom htotal huniq a
  refine ⟨J, ?_, fun p L hL => ?_⟩
  · apply Section5.GammaGraphDefinable.congr (gamma_total_mixed_jacobian_graph hc hn f hf)
    intro p z
    constructor
    · rintro ⟨hp, hz⟩
      refine ⟨⟨p, hp⟩, rfl, ?_⟩
      have h1 := (hJgraph ⟨p, hp⟩).2
      rw [hcode] at h1
      obtain ⟨Jv, _, hJv⟩ := existsUnique_totalMixedJacobianValue f ⟨p, hp⟩
      have he : (J ⟨p, hp⟩).val 0 = vfAt z 0 := (hJv _ h1).trans (hJv _ hz).symm
      funext i
      fin_cases i
      exact he
    · rintro ⟨a, rfl, hz⟩
      refine ⟨a.property, ?_⟩
      have h1 := (hJgraph a).2
      rw [hcode] at h1
      have he : (J a).val 0 = vfAt z 0 := congrFun hz 0
      rw [← he]
      exact h1
  · have he := huniq p.val (J p).val (fun _ => (LinearMap.toMatrix' L).det)
      (hJgraph p) ⟨p.property, (mem_totalMixedJacobianCodes_iff f p _).mpr (Or.inl ⟨L, hL, rfl⟩)⟩
    exact congrFun he 0

end SpecialTransformations.Section9
