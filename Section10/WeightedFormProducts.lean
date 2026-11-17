module

public import Section10.WeightedZeroUnit
public import Section4.MapProduct

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Products of the actual forms, on arbitrary definable domains. In
particular a factor of degree zero contributes its supplied density. These
operations make no choice of a definable section from Gamma to RV. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section3.GammaParameters.EndpointLogic

noncomputable section

namespace SpecialTransformations.Section10

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {P Q : Space LRV M} {S : Set M} {A : DefSet P S} {B : DefSet Q S}

private def normalizedGammaMulMap (S : Set M) :
    let N := CanonicalStructure.normalize (M := M)
    let R := @gammaSpace M sM hM
    @Map LRV M N (@Space.prod LRV M N R R) R S
      (DefSet.univ (@Space.prod LRV M N R R) S) (@DefSet.univ LRV M N R S) := by
  let N := @CanonicalStructure.normalize M sM
  let R := @gammaSpace M sM hM
  let mul : (@Values.Gamma M sM hM) → (@Values.Gamma M sM hM) → (@Values.Gamma M sM hM) := (· * ·)
  let cv := @codeValue M sM hM
  have hc (z : @Space.domain LRV M N R) :
      @Space.decode LRV M N R z = cv (z.val (0 : Fin 1)) := by
    change @Values.gammaOf M sM hM ⟨z.val (0 : Fin 1), z.property.1⟩ z.property.2 = _
    have hz : @NonzeroRV M sM (z.val (0 : Fin 1)) := z.property
    simp only [cv, codeValue, dite_eq_left hz, value]
  let I := (Fin 1 ⊕ Fin 1) ⊕ Fin 1
  have h := @GammaSyntax.mul_definable M sM hM I inferInstance S (Sum.inl (Sum.inl 0) : I)
    (Sum.inl (Sum.inr 0)) (Sum.inr 0)
  letI : LRV.Structure M := N
  refine ⟨fun p => ⟨mul p.val.1 p.val.2, Set.mem_univ _⟩, ?_⟩
  change @Set.Definable M S LRV N I _
  change @Set.Definable M S LRV N I _ at h
  convert h using 1
  ext z
  constructor
  · rintro ⟨⟨hx, hy⟩, hz, p, hp, he⟩
    refine ⟨?_, ?_⟩
    · intro i
      cases i with
      | inl i =>
        cases i with
        | inl j => fin_cases j; exact hx
        | inr j => fin_cases j; exact hy
      | inr j => fin_cases j; exact hz
    · change mul (cv (z (.inl (.inl (0 : Fin 1))))) (cv (z (.inl (.inr (0 : Fin 1))))) =
        cv (z (.inr (0 : Fin 1)))
      have he' : mul p.val.1 p.val.2 = R.decode ⟨z ∘ Sum.inr, hz⟩ := he
      rw [hp] at he'
      exact (congrArg₂ mul (hc ⟨_, hx⟩) (hc ⟨_, hy⟩)).symm.trans (he'.trans (hc ⟨_, hz⟩))
  · rintro ⟨hp, he⟩
    let hx : R.domain := ⟨fun i => z (.inl (.inl i)), hp (.inl (.inl 0))⟩
    let hy : R.domain := ⟨fun i => z (.inl (.inr i)), hp (.inl (.inr 0))⟩
    let hz : R.domain := ⟨z ∘ Sum.inr, hp (.inr 0)⟩
    refine ⟨⟨hx.property, hy.property⟩, hz.property,
      ⟨(R.decode hx, R.decode hy), Set.mem_univ _⟩, rfl, ?_⟩
    change mul (R.decode hx) (R.decode hy) = R.decode hz
    rw [hc hx, hc hy, hc hz]
    exact he

private def transportProductMap {T U : LRV.Structure M} (e : T = U) (R : @Space LRV M T)
    (f : @Map LRV M T (@Space.prod LRV M T R R) R S
      (@DefSet.univ LRV M T (@Space.prod LRV M T R R) S) (@DefSet.univ LRV M T R S)) :
    @Map LRV M U (@Space.prod LRV M U (e ▸ R) (e ▸ R)) (e ▸ R) S
      (@DefSet.univ LRV M U (@Space.prod LRV M U (e ▸ R) (e ▸ R)) S) (@DefSet.univ LRV M U (e ▸ R) S) := by
  cases e
  exact f

def gammaVolumeMulMap (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    Map (DefSet.univ ((volumeGammaSpace hc).prod (volumeGammaSpace hc)) S)
      (DefSet.univ (volumeGammaSpace hc) S) :=
  transportProductMap (Section8.normalize_eq_of_isCanonical hc) (@gammaSpace M sM hM)
    (normalizedGammaMulMap S)

theorem gammaVolumeMulMap_value (hc : CanonicalStructure.IsCanonical (M := M))
    (p : DefSet.univ ((volumeGammaSpace hc).prod (volumeGammaSpace hc)) S) :
    cast (gammaCarrier hc) (gammaVolumeMulMap hc S p).val =
      cast (gammaCarrier hc) p.val.1 * cast (gammaCarrier hc) p.val.2 := by
  have transport {T U : LRV.Structure M} (e : T = U) (R : @Space LRV M T)
      (mul : (@Space.Carrier LRV M T R) → (@Space.Carrier LRV M T R) → (@Space.Carrier LRV M T R))
      (f : @Map LRV M T (@Space.prod LRV M T R R) R S
        (@DefSet.univ LRV M T (@Space.prod LRV M T R R) S) (@DefSet.univ LRV M T R S))
      (hf : ∀ p, (f p).val = mul p.val.1 p.val.2) :
      ∀ p : @DefSet.univ LRV M U (@Space.prod LRV M U (e ▸ R) (e ▸ R)) S,
        cast (by cases e; rfl : @Space.Carrier LRV M U (e ▸ R) = @Space.Carrier LRV M T R)
          (transportProductMap e R f p).val =
        mul (cast (by cases e; rfl : @Space.Carrier LRV M U (e ▸ R) = @Space.Carrier LRV M T R) p.val.1)
          (cast (by cases e; rfl : @Space.Carrier LRV M U (e ▸ R) = @Space.Carrier LRV M T R) p.val.2) := by
    cases e
    exact hf
  exact transport (Section8.normalize_eq_of_isCanonical hc) (@gammaSpace M sM hM)
    (fun (a b : @Values.Gamma M sM hM) => a * b) (normalizedGammaMulMap S) (fun _ => rfl) p

namespace ZeroForm

def rvProduct (ω : ZeroForm (rvVolumeScale (M := M)) A)
    (η : ZeroForm (rvVolumeScale (M := M)) B) : ZeroForm rvVolumeScale (A.prod B) where
  map := (Section9.rvCoordinateProductMap S).comp
    (((ω.map.comp (Map.prodFst A B)).pair (η.map.comp (Map.prodSnd A B))).toUniv)
  allowed a := mul_ne_zero (ω.allowed ⟨a.val.1, a.property.1⟩) (η.allowed ⟨a.val.2, a.property.2⟩)

@[simp] theorem rvProduct_weight (ω : ZeroForm (rvVolumeScale (M := M)) A)
    (η : ZeroForm (rvVolumeScale (M := M)) B) (a : A.prod B) :
    (ω.rvProduct η).weight a = ω.weight ⟨a.val.1, a.property.1⟩ *
      η.weight ⟨a.val.2, a.property.2⟩ := rfl

def gammaProduct {hc : CanonicalStructure.IsCanonical (M := M)}
    (ω : ZeroForm (gammaVolumeScale hc) A) (η : ZeroForm (gammaVolumeScale hc) B) :
    ZeroForm (gammaVolumeScale hc) (A.prod B) where
  map := (gammaVolumeMulMap hc S).comp
    (((ω.map.comp (Map.prodFst A B)).pair (η.map.comp (Map.prodSnd A B))).toUniv)
  allowed _ := trivial

@[simp] theorem gammaProduct_weight {hc : CanonicalStructure.IsCanonical (M := M)}
    (ω : ZeroForm (gammaVolumeScale hc) A) (η : ZeroForm (gammaVolumeScale hc) B)
    (a : A.prod B) :
    (ω.gammaProduct η).weight a = ω.weight ⟨a.val.1, a.property.1⟩ *
      η.weight ⟨a.val.2, a.property.2⟩ := by
  change (cast (gammaCarrier hc) (gammaVolumeMulMap hc S _).val).val = _
  rw [gammaVolumeMulMap_value]
  rfl

end ZeroForm
end SpecialTransformations.Section10
