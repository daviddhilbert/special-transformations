import Section4.RVCategories
import Mathlib.Algebra.BigOperators.Fin

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def padRV (t : Fin k → CanonicalRV.RVSort M) : Fin (k + 1) → CanonicalRV.RVSort M :=
  Fin.snoc t ⟨iRVZero, rv_zero_mem hM⟩

theorem padRV_injective : Function.Injective (padRV (M := M) (k := k)) := by
  intro t u he
  simpa only [padRV, Fin.init_snoc] using congrArg Fin.init he

@[simp] theorem rvWeight_padRV (t : Fin k → CanonicalRV.RVSort M) :
    rvWeight (padRV t) = rvWeight t := by
  classical
  simp only [rvWeight, Fin.sum_univ_castSucc, padRV, Fin.snoc_castSucc,
    Fin.snoc_last, ne_eq, not_true_eq_false, ↓reduceIte, add_zero]

noncomputable def rvPadding (S : Set M) :
    Map (DefSet.univ (rawRVSpace (M := M) k) S)
      (DefSet.univ (rawRVSpace (k + 1)) S) := by
  let F (z : Fin k → M) : Fin (k + 1) → M := Fin.snoc z iRVZero
  have hF : S.DefinableMap LRV F := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have hz : S.DefinableFun LRV (fun _ : Fin k → M => iRVZero) :=
        (Set.DefinableFun.of_empty
        (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvZero)).comp
        (show S.DefinableMap LRV (fun _ : Fin k → M => Fin.elim0) from fun j => j.elim0)
      simpa only [F, Fin.snoc_last] using hz
    · simpa only [F, Fin.snoc_castSucc] using
        (Set.DefinableFun.proj (M := M) (L := LRV) (A := S) (i := j))
  have hcode (c : (rawRVSpace (M := M) k).domain) :
      rvValues (padRV ((rawRVSpace (M := M) k).decode c)) = F c.val := by
    have hc : rvValues ((rawRVSpace (M := M) k).decode c) = c.val :=
      Space.ofEmbedding_decode (rvValues (M := M) (n := k)) rvValues_injective
        (rawRVSpace (M := M) k).domain_definable c
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [rvValues, padRV, F, Fin.snoc_last]
    · simpa only [rvValues, padRV, Fin.snoc_castSucc, F] using congrFun hc j
  refine Map.ofCodes _ padRV F hF (fun c => ⟨padRV ((rawRVSpace k).decode c), hcode c⟩) ?_
  intro c
  apply rvValues_injective
  have hc := Space.ofEmbedding_decode (rvValues (M := M) (n := k + 1)) rvValues_injective
    (rawRVSpace (M := M) (k + 1)).domain_definable
    ⟨F c.val, ⟨padRV ((rawRVSpace k).decode c), hcode c⟩⟩
  exact hc.trans (hcode c).symm

theorem rvPadding_injective (S : Set M) :
    Function.Injective (rvPadding (M := M) (k := k) S) := by
  intro a b he
  apply Subtype.ext
  apply padRV_injective
  exact congrArg (fun z : DefSet.univ (rawRVSpace (M := M) (k + 1)) S => z.val) he

noncomputable def rvPadObject (U : RVObject (M := M) S k) : RVObject (M := M) S (k + 1) where
  arity := U.arity
  domain := U.domain
  volume := (rvPadding S).comp U.volume

@[simp] theorem rvPadObject_value (U : RVObject (M := M) S k) (a : U.domain) :
    (rvPadObject U).value a = padRV (U.value a) := rfl

def rvPadHom {U V : RVObject (M := M) S k} (f : RVHom U V) :
    RVHom (rvPadObject U) (rvPadObject V) where
  map := f.map
  volumetric a := by
    simpa only [rvPadObject_value, rvWeight_padRV] using f.volumetric a
  finite_volume_images t := by
    apply ((f.finite_volume_images (Fin.init t)).image padRV).subset
    rintro s ⟨a, ha, he⟩
    have hx : U.value a = Fin.init t := by
      simpa only [rvPadObject_value, padRV, Fin.init_snoc] using congrArg Fin.init ha
    exact ⟨V.value (f.map a), ⟨a, hx, rfl⟩, he⟩

def rvUnpadHom {U V : RVObject (M := M) S k}
    (f : RVHom (rvPadObject U) (rvPadObject V)) : RVHom U V where
  map := f.map
  volumetric a := by
    simpa only [rvPadObject_value, rvWeight_padRV] using f.volumetric a
  finite_volume_images t := by
    apply ((f.finite_volume_images (padRV t)).image Fin.init).subset
    rintro s ⟨a, ha, he⟩
    refine ⟨padRV (V.value (f.map a)), ⟨a, ?_, rfl⟩, ?_⟩
    · simpa only [rvPadObject_value, ha]
    · simpa only [padRV, Fin.init_snoc] using he

/-- The functor E_k of Definition 4.17. -/
noncomputable def rvPaddingFunctor (S : Set M) (k : ℕ) :
    RVObject (M := M) S k ⥤ RVObject (M := M) S (k + 1) where
  obj := rvPadObject
  map := rvPadHom
  map_id _ := by apply RVHom.ext; rfl
  map_comp _ _ := by apply RVHom.ext; rfl

def rvPaddingFullyFaithful (S : Set M) (k : ℕ) :
    (rvPaddingFunctor (M := M) S k).FullyFaithful where
  preimage := rvUnpadHom
  map_preimage _ := by apply RVHom.ext; rfl
  preimage_map _ := by apply RVHom.ext; rfl

theorem rvPadObject_finite_volume (U : RVObject (M := M) S k)
    (hU : U.volume.FiniteFibres) : (rvPadObject U).volume.FiniteFibres :=
  (Map.finiteFibres_of_injective (rvPadding_injective S)).comp hU

theorem rvPadObject_finite_volume_iff (U : RVObject (M := M) S k) :
    (rvPadObject U).volume.FiniteFibres ↔ U.volume.FiniteFibres := by
  constructor
  · intro h t
    apply (h (rvPadding S t)).subset
    intro a ha
    exact congrArg (rvPadding S) ha
  · exact rvPadObject_finite_volume U

noncomputable def rvInitMap (S : Set M) :
    Map (DefSet.univ (rawRVSpace (M := M) (k + 1)) S)
      (DefSet.univ (rawRVSpace k) S) := by
  have hcode (c : (rawRVSpace (M := M) (k + 1)).domain) :
      rvValues (Fin.init ((rawRVSpace (M := M) (k + 1)).decode c)) = Fin.init c.val := by
    have hc := Space.ofEmbedding_decode (rvValues (M := M) (n := k + 1)) rvValues_injective
      (rawRVSpace (M := M) (k + 1)).domain_definable c
    funext i
    exact congrFun hc i.castSucc
  refine Map.ofCodes _ Fin.init (fun z => Fin.init z)
    (fun _ => Set.DefinableFun.proj LRV)
    (fun c => ⟨Fin.init ((rawRVSpace (M := M) (k + 1)).decode c), hcode c⟩) ?_
  intro c
  apply rvValues_injective
  have hc := Space.ofEmbedding_decode (rvValues (M := M) (n := k)) rvValues_injective
    (rawRVSpace (M := M) k).domain_definable
    ⟨Fin.init c.val, ⟨Fin.init ((rawRVSpace (M := M) (k + 1)).decode c), hcode c⟩⟩
  exact hc.trans (hcode c).symm

noncomputable def rvUnpadObject (U : RVObject (M := M) S (k + 1)) : RVObject (M := M) S k where
  arity := U.arity
  domain := U.domain
  volume := (rvInitMap S).comp U.volume

@[simp] theorem rvUnpad_padObject (U : RVObject (M := M) S k) :
    rvUnpadObject (rvPadObject U) = U := by
  cases U with
  | mk arity domain volume =>
    change RVObject.mk arity domain ((rvInitMap S).comp ((rvPadding S).comp volume)) =
      RVObject.mk arity domain volume
    congr 1
    apply Map.ext
    intro a
    apply Subtype.ext
    change Fin.init (padRV ((volume a).val)) = (volume a).val
    exact Fin.init_snoc _ _

theorem rvPadObject_injective (S : Set M) (k : ℕ) :
    Function.Injective (rvPadObject (M := M) (S := S) (k := k)) := by
  intro U V he
  have h := congrArg (fun W : RVObject (M := M) S (k + 1) => rvUnpadObject W) he
  simpa only [rvUnpad_padObject] using h

end SpecialTransformations.Section4

end
