import Section6.RVSubstructure
import Section6.ContractionGraph

/-! The genuine RV reduct and QF graph definitions over RV(S). The
input RVQFDefinitions is the earlier ACVF QE/RV-literal normal-form
consequence, authorized as given. It concerns only the ACVF ambient
model. Transfer to an arbitrary substructure is proved by an actual
embedding and QF preservation; no RV quantifier elementarity is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace SpecialTransformations.Section6.RVGraphLanguage
open RVAbstraction

def RVBase : Language := ⟨RVFunction, RVRelation⟩

variable {C : Type} [LRV.Structure C] [hC : C ⊨ Axioms.ACVF]

@[instance_reducible] def ambientStructure : RVBase.Structure (RV (M := C)) where
  funMap f z := ⟨Structure.funMap (L := LRV) f.val (fun i => (z i).val), by
    have hh := CanonicalStructure.function_sort hC f.val (fun i => (z i).val) (by
      intro i
      rw [f.property.2 i]
      exact (z i).property)
    simpa only [f.property.1, sortEval, iRV] using hh⟩
  RelMap r z := Structure.RelMap (L := LRV) r.val (fun i => (z i).val)

@[instance_reducible] def substructureStructure (X : LRV.Substructure C) :
    RVBase.Structure (SubRV (X : Set C)) where
  funMap f z :=
    letI := ambientStructure (C := C)
    ⟨Structure.funMap (L := RVBase) f (fun i => (z i).val),
      X.fun_mem f.val _ (fun i => (z i).property)⟩
  RelMap r z :=
    letI := ambientStructure (C := C)
    Structure.RelMap (L := RVBase) r (fun i => (z i).val)

@[instance_reducible] def ambientWithParameters (S : LRV.Substructure C) :
    RVBase[[SubRV (S : Set C)]].Structure (RV (M := C)) := by
  letI := ambientStructure (C := C)
  letI : (constantsOn (SubRV (S : Set C))).Structure (RV (M := C)) :=
    constantsOn.structure (fun s => s.val)
  exact inferInstance

@[instance_reducible] def sourceWithParameters (S X : LRV.Substructure C) (hSX : S ≤ X) :
    RVBase[[SubRV (S : Set C)]].Structure (SubRV (X : Set C)) := by
  letI := substructureStructure X
  letI : (constantsOn (SubRV (S : Set C))).Structure (SubRV (X : Set C)) :=
    constantsOn.structure (fun s => ⟨s.val, hSX s.property⟩)
  exact inferInstance

def parameterEmbedding (S X : LRV.Substructure C) (hSX : S ≤ X) :
    @Embedding RVBase[[SubRV (S : Set C)]] (SubRV (X : Set C)) (RV (M := C))
      (sourceWithParameters S X hSX) (ambientWithParameters S) := by
  letI := sourceWithParameters S X hSX
  letI := ambientWithParameters S
  refine {
    toFun := fun q => q.val
    inj' := fun _ _ h => Subtype.ext h
    map_fun' := ?_
    map_rel' := ?_ }
  ·
    intro n f z
    cases f with
    | inl f => rfl
    | inr f =>
      cases n with
      | zero => rfl
      | succ n => exact isEmptyElim f
  ·
    intro n r z
    cases r with
    | inl r => rfl
    | inr r => exact isEmptyElim r

def RawRVSet {q : ℕ} (U : Set (Fin q → RV (M := C))) : Set (Fin q → C) :=
  {z | ∃ u ∈ U, (fun i => (u i).val) = z}

/-- The precise earlier-section input: pure RV definable sets in ACVF
have QF definitions in the RV reduct with RV parameters from the original
substructure. This input makes no statement about henselian fields or
elimination in an RV expansion. -/
def RVQFDefinitions (S : LRV.Substructure C) : Prop :=
  ∀ (q : ℕ) (U : Set (Fin q → RV (M := C))),
    Section4.RawDefinable (S : Set C) (RawRVSet U) →
    ∃ φ : RVBase[[SubRV (S : Set C)]].Formula (Fin q), φ.IsQF ∧
      ∀ u, u ∈ U ↔ @Formula.Realize _ _ (ambientWithParameters S) _ φ u

/-- A single ambient QF definition works on every substructure containing
the same base. The formula is chosen before X. -/
theorem qf_definition_on_substructures (S : LRV.Substructure C)
    (hdefs : RVQFDefinitions S) {q : ℕ} (U : Set (Fin q → RV (M := C)))
    (hU : Section4.RawDefinable (S : Set C) (RawRVSet U)) :
    ∃ φ : RVBase[[SubRV (S : Set C)]].Formula (Fin q), φ.IsQF ∧
      ∀ (X : LRV.Substructure C) (hSX : S ≤ X) (u : Fin q → SubRV (X : Set C)),
        (fun i => (u i).val) ∈ U ↔
          @Formula.Realize _ _ (sourceWithParameters S X hSX) _ φ u := by
  obtain ⟨φ, hq, he⟩ := hdefs q U hU
  refine ⟨φ, hq, ?_⟩
  intro X hSX u
  letI := sourceWithParameters S X hSX
  letI := ambientWithParameters S
  let j := parameterEmbedding S X hSX
  have hp := hq.realize_embedding j (v := u) (xs := (default : Fin 0 → SubRV (X : Set C)))
  have hb : j ∘ (default : Fin 0 → SubRV (X : Set C)) =
      (default : Fin 0 → RV (M := C)) := Subsingleton.elim _ _
  rw [hb] at hp
  exact (he (fun i => (u i).val)).trans hp

def contractionRVSet {S : Set C} {n l k : ℕ}
    {A : PresentedSet (keySpace (M := C) n l) S}
    {D : PresentedSet (keySpace (M := C) 0 k) S} (g : Map A D) :
    Set (Fin (n + l + k) → RV (M := C)) :=
  {u | (fun i => (u i).val) ∈ contractionGraphCodes g}

theorem raw_contractionRVSet {S : Set C} {n l k : ℕ}
    {A : PresentedSet (keySpace (M := C) n l) S}
    {D : PresentedSet (keySpace (M := C) 0 k) S} (g : Map A D) :
    RawRVSet (contractionRVSet g) = contractionGraphCodes g := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hu
  · intro hz
    let u : Fin (n + l + k) → RV (M := C) :=
      fun i => ⟨z i, contractionGraphCodes_sorted g hz i⟩
    exact ⟨u, hz, rfl⟩

/-- The graph premise used in the syntactic assembly is obtained from
the earlier RV normal form and the proved complete contraction graph.
Its definition is chosen once, before the substructure X. -/
theorem qf_contraction_definition (S : LRV.Substructure C) (hdefs : RVQFDefinitions S)
    {n l k : ℕ} {A : PresentedSet (keySpace (M := C) n l) (S : Set C)}
    {D : PresentedSet (keySpace (M := C) 0 k) (S : Set C)} (g : Map A D) :
    ∃ φ : RVBase[[SubRV (S : Set C)]].Formula (Fin (n + l + k)), φ.IsQF ∧
      ∀ (X : LRV.Substructure C) (hSX : S ≤ X)
        (u : Fin (n + l + k) → SubRV (X : Set C)),
        (fun i => (u i).val.val) ∈ contractionGraphCodes g ↔
          @Formula.Realize _ _ (sourceWithParameters S X hSX) _ φ u := by
  have hU : Section4.RawDefinable (S : Set C) (RawRVSet (contractionRVSet g)) := by
    rw [raw_contractionRVSet]
    exact contractionGraphCodes_definable g
  exact qf_definition_on_substructures S hdefs (contractionRVSet g) hU

/-- Decode a flattened complete graph. This equivalence retains the
domain witness when the output tuple is empty. -/
theorem contractionGraphCodes_append {S : Set C} {n l k : ℕ}
    {A : PresentedSet (keySpace (M := C) n l) S}
    {D : PresentedSet (keySpace (M := C) 0 k) S} (g : Map A D)
    (y : Fin (n + l) → RV (M := C)) (z : Fin k → RV (M := C)) :
    (fun i => (Fin.append y z i).val) ∈ contractionGraphCodes g ↔
      ∃ a : A, keyTuple a.val = y ∧ (g a).val.2 = z := by
  let u : Key (M := C) n l :=
    (fun i => y (Fin.castAdd l i), fun j => y (Fin.natAdd n j))
  let w : Key (M := C) 0 k := (Fin.elim0, z)
  let zz : Fin (n + l + k) → C := fun i => (Fin.append y z i).val
  let left := zz ∘ contractionGraphIndex n l k ∘ Sum.inl
  let right := zz ∘ contractionGraphIndex n l k ∘ Sum.inr
  have hleft : left ∈ pDomain (keySpace n l) := by
    constructor
    · intro i
      simpa only [left, zz, Function.comp_apply, contractionGraphIndex, Sum.elim_inl,
        Fin.append_left, sortEval, iRV] using (y (Fin.castAdd l i)).property
    · intro j
      simpa only [left, zz, Function.comp_apply, contractionGraphIndex, Sum.elim_inl,
        Sum.elim_inr, Fin.append_left, sortEval, iRV] using (y (Fin.natAdd n j)).property
  have hright : right ∈ pDomain (keySpace 0 k) := by
    constructor
    · intro i
      exact i.elim0
    · intro i
      simpa only [right, zz, Function.comp_apply, contractionGraphIndex, Sum.elim_inr,
        Fin.append_right, sortEval, iRV] using (z i).property
  have hkey (hu : left ∈ pDomain (keySpace n l)) :
      pDecode (keySpace n l) ⟨left, hu⟩ = u := by
    apply Prod.ext <;> funext i <;> apply Subtype.ext
    · simp only [pDecode, keySpace, DefinableGeometry.Space.prod, Section4.realSpace,
        left, zz, Function.comp_apply, contractionGraphIndex, Sum.elim_inl,
        Fin.append_left, u]
    · simp only [pDecode, keySpace, DefinableGeometry.Space.prod, Section4.realSpace,
        left, zz, Function.comp_apply, contractionGraphIndex, Sum.elim_inl,
        Sum.elim_inr, Fin.append_left, u]
  have hvalue (hw : right ∈ pDomain (keySpace 0 k)) :
      pDecode (keySpace 0 k) ⟨right, hw⟩ = w := by
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · funext i
      apply Subtype.ext
      simp only [pDecode, keySpace, DefinableGeometry.Space.prod, Section4.realSpace,
        right, zz, Function.comp_apply, contractionGraphIndex, Sum.elim_inr,
        Fin.append_right, w]
  have hdecode : (fun i => (Fin.append y z i).val) ∈ contractionGraphCodes g ↔
      ∃ a : A, a.val = u ∧ (g a).val = w := by
    change (∃ hu : left ∈ pDomain (keySpace n l), ∃ hw : right ∈ pDomain (keySpace 0 k),
      ∃ a : A, a.val = pDecode (keySpace n l) ⟨left, hu⟩ ∧
        (g a).val = pDecode (keySpace 0 k) ⟨right, hw⟩) ↔ _
    constructor
    · rintro ⟨hu, hw, a, ha, hg⟩
      exact ⟨a, ha.trans (hkey hu), hg.trans (hvalue hw)⟩
    · rintro ⟨a, ha, hg⟩
      exact ⟨hleft, hright, a, ha.trans (hkey hleft).symm, hg.trans (hvalue hright).symm⟩
  rw [hdecode]
  constructor
  · rintro ⟨a, ha, hg⟩
    refine ⟨a, ?_, congrArg Prod.snd hg⟩
    rw [ha]
    funext i
    cases i using Fin.addCases <;> simp only [keyTuple, u, Fin.append_left, Fin.append_right]
  · rintro ⟨a, ha, hg⟩
    refine ⟨a, Prod.ext ?_ ?_, Prod.ext ?_ hg⟩
    · funext i
      simpa only [keyTuple, Fin.append_left] using congrFun ha (Fin.castAdd l i)
    · funext i
      simpa only [keyTuple, Fin.append_right] using congrFun ha (Fin.natAdd n i)
    · funext i
      exact i.elim0

def graphFormula {L : Language} {β : Type} {q k : ℕ}
    (φ : L.Formula (Fin (q + k))) : L.Formula (Fin q ⊕ Fin k ⊕ β) :=
  φ.relabel (Fin.addCases Sum.inl (fun i => Sum.inr (Sum.inl i)))

theorem graphFormula_realize {L : Language} {β R : Type} [L.Structure R] {q k : ℕ}
    (φ : L.Formula (Fin (q + k))) (y : Fin q → R) (z : Fin k → R) (b : β → R) :
    (graphFormula φ).Realize (Sum.elim y (Sum.elim z b)) ↔
      φ.Realize (Fin.append y z) := by
  rw [graphFormula, Formula.realize_relabel]
  have he : Sum.elim y (Sum.elim z b) ∘
      (Fin.addCases Sum.inl (fun i => Sum.inr (Sum.inl i))) = Fin.append y z := by
    funext i
    cases i using Fin.addCases <;> simp
  rw [he]

/-- The graph interpretation premise of syntactic descent is discharged
by the actual contraction map. The same graph works for every X ≥ S. -/
theorem prepared_graph_formula (S : LRV.Substructure C) (hdefs : RVQFDefinitions S)
    {β : Type} {n m l k : ℕ} {A : DefSet (M := C) (S : Set C) n m}
    {B : DefSet (M := C) (S : Set C) n l} {D : DefSet (M := C) (S : Set C) 0 k}
    (f : Map A D) (T : SpecialBijection A B)
    (hf : Contractible (Map.comp f T.inverseMap)) :
    ∃ ψ : RVBase[[SubRV (S : Set C)]].Formula (Fin (n + l) ⊕ Fin k ⊕ β),
      ∀ (X : LRV.Substructure C) (hSX : S ≤ X),
        @ContractionGraphFormula C _ _ (S : Set C) (X : Set C) n m l k
          RVBase[[SubRV (S : Set C)]] (sourceWithParameters S X hSX) β A B D f T ψ := by
  obtain ⟨φ, _, he⟩ := qf_contraction_definition S hdefs
    (contractionMap (Map.comp f T.inverseMap) hf)
  refine ⟨graphFormula φ, ?_⟩
  intro X hSX y z b
  letI := sourceWithParameters S X hSX
  rw [graphFormula_realize, ← he X hSX (Fin.append y z)]
  have ha : (fun i => (Fin.append y z i).val.val) =
      (fun i => (Fin.append (fun j => (y j).val) (fun j => (z j).val) i).val) := by
    funext i
    cases i using Fin.addCases <;> simp only [Fin.append_left, Fin.append_right]
  rw [ha]
  exact contractionGraphCodes_append (contractionMap (Map.comp f T.inverseMap) hf)
    (fun i => (y i).val) (fun i => (z i).val)

end SpecialTransformations.Section6.RVGraphLanguage
