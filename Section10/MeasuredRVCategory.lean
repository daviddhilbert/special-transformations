import Section10.RVVolumeLift
import Section10.GammaVolumeLift
import Section9.GenericRVJacobianChain

/-! The groupoids on the essential parts of finite-volume RV objects.
The RV Jacobian is required on a definable RV co-small subset. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section7 SpecialTransformations.Section9

noncomputable section

namespace SpecialTransformations.Section10

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ} {S : Set M}
local notation "RV" => CanonicalRV.RVSort M
local notation "Γ" => Values.Gamma (M := M)
local notation "n" => (k + 1)

private abbrev ambient {A B : RVFiniteObject (M := M) S n} (e : A ≅ B) : A.obj ≅ B.obj :=
  (finiteVolumeProperty S n).ι.mapIso e

private theorem gammaEquation {G : Type} [Monoid G] (j : Γ →* G)
    {a b : G} {t s : Fin n → RV} {ht : ∀ i, (t i).val ≠ iRVZero}
    {hs : ∀ i, (s i).val ≠ iRVZero} :
    a = b * j (rvGammaJacobian t s ht hs) ↔
      a * j (rvVolumeGamma t ht) = b * j (rvVolumeGamma s hs) := by
  rw [rvGammaJacobian]
  constructor
  · intro h
    rw [h, mul_assoc, ← map_mul, div_eq_mul_inv, mul_assoc, inv_mul_cancel, mul_one]
  · intro h
    -- Multiply the weight equality on the right by the inverse source volume.
    calc
      a = (a * j (rvVolumeGamma t ht)) * j ((rvVolumeGamma t ht)⁻¹) := by
        rw [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
      _ = _ := by rw [h, mul_assoc, ← map_mul, div_eq_mul_inv]

private theorem small_union (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {r : ℕ} {X Y : DefSet (rawRVSpace (M := M) r) (C.base : Set M)}
    (hx : rvDim X < n) (hy : rvDim Y < n) : rvDim (X.union Y) < n :=
  (rvDim_union_le_max hc (rvExchangeInput_of_earlier C.uncountable.le C.saturated C.model00)
    C.saturated C.small X Y).trans_lt (max_lt hx hy)

private def isoPreimage {A B : RVFiniteObject (M := M) S n} (e : A ≅ B)
    (Y : DefSet (rawRVSpace (M := M) B.obj.arity) S) :
    DefSet (rawRVSpace (M := M) A.obj.arity) S :=
  ⟨{x | ∃ u : A.obj.domain, u.val = x ∧ ((ambient e).hom.map u).val ∈ Y.carrier},
    (ambient e).hom.map.definable_preimage Y.definable⟩

private theorem dim_isoPreimage {A B : RVFiniteObject (M := M) S n} (e : A ≅ B)
    (Y : DefSet (rawRVSpace (M := M) B.obj.arity) S) : rvDim (isoPreimage e Y) ≤ rvDim Y := by
  let X := isoPreimage e Y
  have hi : X.carrier ⊆ A.obj.domain.carrier := by
    rintro _ ⟨u, rfl, _⟩
    exact u.property
  let m := (ambient e).hom.map.restrict hi
  have hY (x : X) : (m x).val ∈ Y.carrier := by
    obtain ⟨u, hu, hv⟩ := x.property
    have he : (⟨x.val, hi x.property⟩ : A.obj.domain) = u := Subtype.ext hu.symm
    change ((ambient e).hom.map ⟨x.val, hi x.property⟩).val ∈ Y.carrier
    rwa [he]
  refine rvDim_le_of_finite_map (m.corestrict hY) (Map.finiteFibres_of_injective ?_)
  intro x y he
  have he' : m x = m y := Subtype.ext (congrArg (fun p : Y => p.val) he)
  have hv := (show Function.LeftInverse (ambient e).inv.map (ambient e).hom.map from
    Section7.rvIso_inv_apply (ambient e)).injective he'
  exact Subtype.ext (congrArg (fun p : A.obj.domain => p.val) hv)

private theorem ambient_inverse {A B : RVFiniteObject (M := M) S n} (e : A ≅ B)
    (u : B.obj.domain) : (ambient e).hom.map ((ambient e.symm).hom.map u) = u :=
  Section7.rvIso_inv_apply (ambient e).symm u

private theorem rvIdentityJacobian (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A : RVFiniteObject (M := M) (C.base : Set M) n)
    (hA : ∀ u : A.obj.domain, ∀ i, (A.obj.value u i).val ≠ iRVZero) :
    ∃ X : DefSet (rawRVSpace (M := M) A.obj.arity) (C.base : Set M), rvDim X < n ∧
      ∀ u : A.obj.domain, u.val ∉ X.carrier →
        IsRVJacobianAt (volumeCorrespondence (ambient (Iso.refl A)).hom.map).carrier
          (A.obj.value u) (A.obj.value u) 1 := by
  let e := Iso.refl A
  obtain ⟨X, _, hX, _, h⟩ := rvJacobian_chain_ae_finite_volume hc C (Nat.zero_lt_succ k) e e hA hA hA
  refine ⟨X, hX, fun u hu => ?_⟩
  obtain ⟨J, K, hJ, hK, hprod⟩ := h u hu
  change IsRVJacobianAt (volumeCorrespondence (ambient e).hom.map).carrier
    (A.obj.value u) (A.obj.value u) J at hJ
  change IsRVJacobianAt (volumeCorrespondence (ambient e).hom.map).carrier
    (A.obj.value u) (A.obj.value u) K at hK
  change IsRVJacobianAt (volumeCorrespondence ((ambient e).trans (ambient e)).hom.map).carrier
    (A.obj.value u) (A.obj.value u) (K * J) at hprod
  have hEE : (ambient e).trans (ambient e) = ambient e := by
    simp [e, ambient]
  rw [hEE] at hprod
  have hJ0 : J ≠ 0 := by
    intro hzero
    have hraw := rv_nonzero_of_gammaJacobian_value _ _ (hA u) (hA u) J (hJ.gamma_eq (hA u) (hA u))
    exact hraw ((congrArg Subtype.val hzero).trans RVOperations.zero_val)
  have hK1 : K = 1 := mul_right_cancel₀ hJ0 ((hprod.unique hJ).trans (one_mul J).symm)
  exact hK1 ▸ hK

namespace RVVolumeIso

variable {U V W : RVVolumeObject (M := M) S k}

@[ext] theorem ext {f g : RVVolumeIso U V} (h : f.labels = g.labels) : f = g := by
  cases f
  cases g
  cases h
  rfl

private theorem weight_eq (f : RVVolumeIso U V) (u : U.essential.underlying.obj.domain) :
    Values.vrv (U.essential.form.value u) *
      (rvVolumeGamma (U.essential.underlying.obj.value u) (rvEssential_value_nonzero _ u)).val =
    Values.vrv (V.essential.form.value ((ambient f.labels).hom.map u)) *
      (rvVolumeGamma (V.essential.underlying.obj.value ((ambient f.labels).hom.map u))
        (rvEssential_value_nonzero _ ((ambient f.labels).hom.map u))).val :=
  (gammaEquation Values.gammaValHom).mp (f.gamma_rule u)

def refl (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A : RVVolumeObject (M := M) (C.base : Set M) k) : RVVolumeIso A A where
  labels := Iso.refl A.essential.underlying
  gamma_rule := fun u => (gammaEquation Values.gammaValHom).mpr rfl
  rv_rule := by
    obtain ⟨X, hX, h⟩ := rvIdentityJacobian hc C A.essential.underlying (rvEssential_value_nonzero _)
    exact ⟨X, hX, fun u hu => ⟨1, h u hu, (mul_one _).symm⟩⟩

variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable {A B D : RVVolumeObject (M := M) (C.base : Set M) k}

def trans (f : RVVolumeIso A B) (g : RVVolumeIso B D) : RVVolumeIso A D where
  labels := f.labels.trans g.labels
  gamma_rule := fun u => (gammaEquation Values.gammaValHom).mpr
    ((f.weight_eq u).trans (g.weight_eq ((ambient f.labels).hom.map u)))
  rv_rule := by
    obtain ⟨X, hX, hx⟩ := f.rv_rule
    obtain ⟨Y, hY, hy⟩ := g.rv_rule
    obtain ⟨Z, _, hZ, _, hz⟩ := rvJacobian_chain_ae_finite_volume hc C (Nat.zero_lt_succ k)
      f.labels g.labels (rvEssential_value_nonzero _) (rvEssential_value_nonzero _) (rvEssential_value_nonzero _)
    let Y' := isoPreimage f.labels Y
    refine ⟨X.union (Y'.union Z), small_union hc C hX
      (small_union hc C ((dim_isoPreimage f.labels Y).trans_lt hY) hZ), fun u hu => ?_⟩
    let v := (ambient f.labels).hom.map u
    obtain ⟨J, K, hj, hk, hp⟩ := hz u (fun h => hu (Or.inr (Or.inr h)))
    obtain ⟨j, hj', h₁⟩ := hx u (fun h => hu (Or.inl h))
    obtain ⟨q, hq', h₂⟩ := hy v (fun h => hu (Or.inr (Or.inl ⟨u, rfl, h⟩)))
    refine ⟨K * J, ?_, ?_⟩
    · rw [Functor.mapIso_trans]
      exact hp
    · rw [hj'.unique hj] at h₁
      rw [hq'.unique hk] at h₂
      exact h₁.trans ((congrArg (· * J) h₂).trans (mul_assoc _ _ _))

def symm (f : RVVolumeIso A B) : RVVolumeIso B A where
  labels := f.labels.symm
  gamma_rule := by
    dsimp only
    intro u
    apply (gammaEquation Values.gammaValHom).mpr
    have h := (f.weight_eq ((ambient f.labels.symm).hom.map u)).symm
    simp only [ambient_inverse] at h
    exact h
  rv_rule := by
    obtain ⟨X, hX, hx⟩ := f.rv_rule
    obtain ⟨Y, hY, hy⟩ := rvIdentityJacobian hc C B.essential.underlying (rvEssential_value_nonzero _)
    obtain ⟨Z, _, hZ, _, hz⟩ := rvJacobian_chain_ae_finite_volume hc C (Nat.zero_lt_succ k)
      f.labels.symm f.labels (rvEssential_value_nonzero _) (rvEssential_value_nonzero _) (rvEssential_value_nonzero _)
    let X' := isoPreimage f.labels.symm X
    refine ⟨X'.union (Y.union Z), small_union hc C ((dim_isoPreimage f.labels.symm X).trans_lt hX)
      (small_union hc C hY hZ), fun u hu => ?_⟩
    let v := (ambient f.labels.symm).hom.map u
    obtain ⟨J, K, hj, hk, hp⟩ := hz u (fun h => hu (Or.inr (Or.inr h)))
    obtain ⟨j, hj', h⟩ := hx v (fun h => hu (Or.inl ⟨u, rfl, h⟩))
    have he : (ambient f.labels).hom.map v = u := ambient_inverse f.labels u
    have hcomp : (ambient f.labels.symm).trans (ambient f.labels) =
        ambient (Iso.refl B.essential.underlying) := by
      rw [← Functor.mapIso_trans, Iso.symm_self_id]
      rfl
    change IsRVJacobianAt (volumeCorrespondence ((ambient f.labels.symm).trans (ambient f.labels)).hom.map).carrier
      (B.essential.underlying.obj.value u) (B.essential.underlying.obj.value ((ambient f.labels).hom.map v))
      (K * J) at hp
    rw [hcomp, he] at hp
    have h1 := hp.unique (hy u (fun h => hu (Or.inr (Or.inl h))))
    change A.essential.form.value v = B.essential.form.value ((ambient f.labels).hom.map v) * j at h
    rw [hj'.unique hk, he] at h
    refine ⟨J, hj, ?_⟩
    change B.essential.form.value u = A.essential.form.value v * J
    rw [h, mul_assoc, h1, mul_one]

end RVVolumeIso

namespace GammaVolumeIso

variable {hc : CanonicalStructure.IsCanonical (M := M)}
variable {U V W : GammaVolumeObject hc S k}

@[ext] theorem ext {f g : GammaVolumeIso U V} (h : f.labels = g.labels) : f = g := by
  cases f
  cases g
  cases h
  rfl

private theorem weight_eq (f : GammaVolumeIso U V) (u : U.essential.underlying.obj.domain) :
    gammaFormValue U.essential.form u *
      rvVolumeGamma (U.essential.underlying.obj.value u) (rvEssential_value_nonzero _ u) =
    gammaFormValue V.essential.form ((ambient f.labels).hom.map u) *
      rvVolumeGamma (V.essential.underlying.obj.value ((ambient f.labels).hom.map u))
        (rvEssential_value_nonzero _ ((ambient f.labels).hom.map u)) :=
  (gammaEquation (MonoidHom.id Γ)).mp (f.rule u)

def refl (A : GammaVolumeObject hc S k) : GammaVolumeIso A A where
  labels := Iso.refl A.essential.underlying
  rule := fun _ => (gammaEquation (MonoidHom.id Γ)).mpr rfl

def trans (f : GammaVolumeIso U V) (g : GammaVolumeIso V W) : GammaVolumeIso U W where
  labels := f.labels.trans g.labels
  rule := fun u => (gammaEquation (MonoidHom.id Γ)).mpr
    ((f.weight_eq u).trans (g.weight_eq ((ambient f.labels).hom.map u)))

def symm (f : GammaVolumeIso U V) : GammaVolumeIso V U where
  labels := f.labels.symm
  rule := by
    dsimp only
    intro u
    apply (gammaEquation (MonoidHom.id Γ)).mpr
    have h := (f.weight_eq ((ambient f.labels.symm).hom.map u)).symm
    simp only [ambient_inverse] at h
    exact h

end GammaVolumeIso

/-- The RV-valued category of Definition 10.3 in positive finite-volume degree. -/
@[instance_reducible] def rvVolumeGroupoid (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    Groupoid (RVVolumeObject (M := M) (C.base : Set M) k) where
  Hom := RVVolumeIso
  id := RVVolumeIso.refl hc C
  comp := RVVolumeIso.trans hc C
  inv := RVVolumeIso.symm hc C
  id_comp f := RVVolumeIso.ext (Iso.refl_trans f.labels)
  comp_id f := RVVolumeIso.ext (Iso.trans_refl f.labels)
  assoc f g h := RVVolumeIso.ext (Iso.trans_assoc f.labels g.labels h.labels)
  inv_comp f := RVVolumeIso.ext (Iso.symm_self_id f.labels)
  comp_inv f := RVVolumeIso.ext (Iso.self_symm_id f.labels)

/-- The Gamma-valued category of Definition 10.3 in positive finite-volume degree. -/
@[instance_reducible] def gammaVolumeGroupoid (hc : CanonicalStructure.IsCanonical (M := M)) :
    Groupoid (GammaVolumeObject hc S k) where
  Hom := GammaVolumeIso
  id := GammaVolumeIso.refl
  comp := GammaVolumeIso.trans
  inv := GammaVolumeIso.symm
  id_comp f := GammaVolumeIso.ext (Iso.refl_trans f.labels)
  comp_id f := GammaVolumeIso.ext (Iso.trans_refl f.labels)
  assoc f g h := GammaVolumeIso.ext (Iso.trans_assoc f.labels g.labels h.labels)
  inv_comp f := GammaVolumeIso.ext (Iso.symm_self_id f.labels)
  comp_inv f := GammaVolumeIso.ext (Iso.self_symm_id f.labels)

end SpecialTransformations.Section10
