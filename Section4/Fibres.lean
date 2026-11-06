import Section4.RealPresentations
import Section4.FiniteMaps
import Section3.RawAlgebraicity

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language

noncomputable section

namespace SpecialTransformations.DefinableGeometry.Map

variable {L : Language} {M : Type} [L.Structure M]
variable {P Q : Space L M} {S : Set M} {A : DefSet P S} {B : DefSet Q S}

def fibreCarrier (f : Map A B) (b : B) : Set P.Carrier :=
  {x | ∃ a : A, a.val = x ∧ f a = b}

theorem fibreCarrier_finite (f : Map A B) (hf : f.FiniteFibres) (b : B) :
    (f.fibreCarrier b).Finite := by
  convert (hf b).image (Subtype.val : A → P.Carrier) using 1
  ext x
  constructor
  · rintro ⟨a, ha, he⟩
    exact ⟨a, he, ha⟩
  · rintro ⟨a, he, ha⟩
    exact ⟨a, ha, he⟩

/-- A fibre is definable over the original base and any real code of its
target point. This is parameter specialization, not a choice of section. -/
def fibre (f : Map A B) (b : B) (c : Q.domain) (hc : Q.decode c = b.val) :
    DefSet P (S ∪ Set.range c.val) where
  carrier := f.fibreCarrier b
  definable := by
    let T := S ∪ Set.range c.val
    let F (z : P.Index → M) : P.Index ⊕ Q.Index → M := Sum.elim z c.val
    have hF : T.DefinableMap L F := by
      intro i
      cases i with
      | inl i => exact Set.DefinableFun.proj L
      | inr i => exact L.definableFun_const P.Index (Or.inr (Set.mem_range_self i))
    have hg := (f.graph_definable.mono P Q (Set.subset_union_left)).preimage_map hF
    change T.Definable L (P.preimage (f.fibreCarrier b))
    convert hg using 1
    ext z
    constructor
    · rintro ⟨hz, a, ha, he⟩
      exact ⟨hz, c.property, a, ha, (congrArg (fun v : B => v.val) he).trans hc.symm⟩
    · rintro ⟨hz, ht, a, ha, he⟩
      exact ⟨hz, a, ha, Subtype.ext (he.trans hc)⟩

end SpecialTransformations.DefinableGeometry.Map

open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.DefinableGeometry

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] {S : Set M} {n r : ℕ}

def vfCoordinateSet (A : DefSet (rawMixedSpace (M := M) n r) S) (i : Fin n) : Set M :=
  {x | ∃ a : A, (a.val.1 i).val = x}

theorem vfCoordinateSet_definable (A : DefSet (rawMixedSpace (M := M) n r) S) (i : Fin n) :
    S.Definable₁ LRV (vfCoordinateSet A i) := by
  have h := A.definable.image_comp (fun _ : Fin 1 => Sum.inl i)
  change S.Definable LRV {x : Fin 1 → M | ∃ a : A, (a.val.1 i).val = x 0}
  convert h using 1
  ext x
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨mixedValues a.val, ⟨mixedValues_mem_domain a.val, ?_⟩, ?_⟩
    · simpa only [decode_mixedValues] using a.property
    · funext j
      fin_cases j
      exact ha
  · rintro ⟨z, ⟨hz, hA⟩, he⟩
    refine ⟨⟨(rawMixedSpace (M := M) n r).decode ⟨z, hz⟩, hA⟩, ?_⟩
    exact (congrFun (mixedValues_decode ⟨z, hz⟩) (.inl i)).trans (congrFun he 0)

theorem vfCoordinateSet_finite (A : DefSet (rawMixedSpace (M := M) n r) S)
    (hA : A.carrier.Finite) (i : Fin n) : (vfCoordinateSet A i).Finite := by
  convert hA.image (fun p => (p.1 i).val) using 1
  ext x
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a.val, a.property, ha⟩
  · rintro ⟨a, ha, he⟩
    exact ⟨⟨a, ha⟩, he⟩

/-- A finite-to-one definable map makes every source VF coordinate
algebraic over the base and any code of the image. This is the first step
of the transcendence-degree comparison; no comparison is assumed here. -/
theorem fibre_vf_coordinate_algebraic
    {Q : DefinableGeometry.Space LRV M}
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet Q S}
    (f : Map A B) (hf : f.FiniteFibres) (a : A)
    (c : Q.domain) (hc : Q.decode c = (f a).val) (i : Fin n) :
    RawClosure.AlgebraicOver (S ∪ Set.range c.val) (a.val.1 i).val := by
  let F := f.fibre (f a) c hc
  have hfin : F.carrier.Finite := f.fibreCarrier_finite hf (f a)
  exact ⟨vfCoordinateSet F i, vfCoordinateSet_definable F i,
    vfCoordinateSet_finite F hfin i, ⟨⟨a.val, ⟨a, rfl, rfl⟩⟩, rfl⟩⟩

end SpecialTransformations.Section4

end
