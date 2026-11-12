module

public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Unramified.Finite
public import Mathlib.RingTheory.Valuation.ValuationRing

@[expose] public section

/-! The local flat-ideals argument in the Stacks 0ASK port can also
establish the domain condition, using freeness of principal ideals. -/

namespace SpecialTransformations.Section9

private theorem isDomain_of_local_flat_ideals (R : Type) [CommRing R]
    [IsLocalRing R] (h : ∀ I : Ideal R, Module.Flat R I) : IsDomain R := by
  letI : NoZeroDivisors R := ⟨fun {a b} hab => by
    by_cases hb : b = 0
    · exact Or.inr hb
    left
    let I : Ideal R := Ideal.span {b}
    let b₀ : I := ⟨b, Ideal.mem_span_singleton_self b⟩
    letI : Nontrivial I := ⟨⟨b₀, 0, fun he => hb (congrArg Subtype.val he)⟩⟩
    letI : Module.Flat R I := h I
    letI : Module.Finite R I := Module.Finite.iff_fg.mpr (by
      simpa [I] using (Submodule.fg_span (s := ({b} : Set R)) (by simp)))
    letI : Module.Free R I := Module.free_of_flat_of_isLocalRing
    let basis := Module.Free.chooseBasis R I
    let i := basis.index_nonempty.some
    have hann (x : I) : a • x = 0 := by
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp x.property
      apply Subtype.ext
      change a * (x : R) = 0
      rw [← hr, mul_left_comm, hab, mul_zero]
    have h₀ := congrArg (fun x : I => basis.repr x i) (hann (basis i))
    simpa using h₀⟩
  exact NoZeroDivisors.to_isDomain R

theorem local_valuationRing_of_flat_formallyUnramified (A R : Type) [CommRing A] [IsDomain A]
    [ValuationRing A] [CommRing R] [IsLocalRing R] [Algebra A R] [Module.Flat A R]
    [Algebra.FormallyUnramified A R] [Algebra.EssFiniteType A R] :
    ∃ (_ : IsDomain R), ValuationRing R := by
  have hflat (I : Ideal R) : Module.Flat R I := by
    letI : Module.IsTorsionFree A R := inferInstance
    letI : Module.IsTorsionFree A I := inferInstance
    letI : Module.Flat A I := (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout).mpr
      (Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance)
    exact Algebra.FormallyUnramified.flat_of_restrictScalars A R I
  letI : IsDomain R := isDomain_of_local_flat_ideals R hflat
  refine ⟨inferInstance, ValuationRing.iff_local_bezout_domain.mpr ⟨inferInstance, ?_⟩⟩
  rw [IsBezout.iff_span_pair_isPrincipal]
  intro a b
  let I : Ideal R := Ideal.span {a, b}
  letI : Module.Flat R I := hflat I
  letI : Module.Finite R I := Module.Finite.iff_fg.mpr (by
    simpa [I] using (Submodule.fg_span (s := ({a, b} : Set R)) (by simp)))
  letI : Module.Free R I := Module.free_of_flat_of_isLocalRing
  apply (Submodule.rank_le_one_iff_isPrincipal I).mp
  exact (Submodule.rank_le I).trans_eq (by simp)


end SpecialTransformations.Section9
