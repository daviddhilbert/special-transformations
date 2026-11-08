/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in NYLL-LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Section7.Imported.EtaleLifting
import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing

/-!
# Coprime factor lifting from the simple-root Hensel property

Adapted from NYLL commit `0fbaf705e33806c8482dd85e169de005ba13d762`.
This port uses the already checked residue-point lifting theorem on
Mathlib henselian local rings.

A coprime monic factorization over the residue field gives a point of the
universal coprime factorization algebra. This algebra is etale, so its residue
point lifts over a henselian local ring. The universal factors give the requested
factorization, with their degrees and prescribed reductions.
-/

namespace SpecialTransformations.Section6.Imported

open Polynomial IsLocalRing

variable {R : Type*} [CommRing R] [HenselianLocalRing R]

/-- A coprime monic factorization modulo a maximal Henselian ideal lifts to
a coprime monic factorization over the base ring with the same degrees. -/
theorem exists_coprime_factor_lift
    (f : R[X]) (gbar hbar : (ResidueField R)[X])
    (hf : f.Monic) (hgbar : gbar.Monic) (hhbar : hbar.Monic)
    (hfac : f.map (residue R) = gbar * hbar)
    (hcop : IsCoprime gbar hbar) :
    ∃ g h : R[X], g.Monic ∧ h.Monic ∧ f = g * h ∧
      g.natDegree = gbar.natDegree ∧ h.natDegree = hbar.natDegree ∧
      g.map (residue R) = gbar ∧ h.map (residue R) = hbar ∧
      IsCoprime g h := by
  have hn : f.natDegree = gbar.natDegree + hbar.natDegree := by
    calc
      f.natDegree = (f.map (residue R)).natDegree :=
        (hf.natDegree_map (residue R)).symm
      _ = gbar.natDegree + hbar.natDegree := by
        rw [hfac, hgbar.natDegree_mul hhbar]
  let p : MonicDegreeEq R f.natDegree := MonicDegreeEq.mk f hf rfl
  let g₀ : MonicDegreeEq (ResidueField R) gbar.natDegree := MonicDegreeEq.mk gbar hgbar rfl
  let h₀ : MonicDegreeEq (ResidueField R) hbar.natDegree := MonicDegreeEq.mk hbar hhbar rfl
  let c : { q : MonicDegreeEq (ResidueField R) gbar.natDegree ×
      MonicDegreeEq (ResidueField R) hbar.natDegree //
      q.1.1 * q.2.1 = p.1.map (algebraMap R (ResidueField R)) ∧ IsCoprime q.1.1 q.2.1 } :=
    ⟨(g₀, h₀), hfac.symm, hcop⟩
  let σ : UniversalCoprimeFactorizationRing gbar.natDegree hbar.natDegree hn p →ₐ[R]
      ResidueField R :=
    (UniversalCoprimeFactorizationRing.homEquiv (ResidueField R)
      gbar.natDegree hbar.natDegree hn p).symm c
  obtain ⟨τ, hτ⟩ := Section7.Imported.EtaleLifting.residuePoint_lifts σ
  let factors := UniversalCoprimeFactorizationRing.homEquiv R
    gbar.natDegree hbar.natDegree hn p τ
  have hres : (UniversalCoprimeFactorizationRing.homEquiv (ResidueField R)
      gbar.natDegree hbar.natDegree hn p ((Algebra.ofId R (ResidueField R)).comp τ)).1 = c.1 := by
    rw [hτ]
    exact congrArg Subtype.val
      ((UniversalCoprimeFactorizationRing.homEquiv (ResidueField R)
        gbar.natDegree hbar.natDegree hn p).apply_symm_apply c)
  have hg : factors.1.1.1.map (residue R) = gbar := by
    have heq := UniversalCoprimeFactorizationRing.homEquiv_comp_fst R
      gbar.natDegree hbar.natDegree hn p τ (Algebra.ofId R (ResidueField R))
    have hfst := congrArg (fun q => q.1.1) hres
    rw [heq] at hfst
    exact hfst
  have hh : factors.1.2.1.map (residue R) = hbar := by
    have heq := UniversalCoprimeFactorizationRing.homEquiv_comp_snd R
      gbar.natDegree hbar.natDegree hn p τ (Algebra.ofId R (ResidueField R))
    have hsnd := congrArg (fun q => q.2.1) hres
    rw [heq] at hsnd
    exact hsnd
  refine ⟨factors.1.1.1, factors.1.2.1, factors.1.1.monic, factors.1.2.monic,
    ?_, ?_, ?_, hg, hh, factors.2.2⟩
  · simpa only [Algebra.algebraMap_self, Polynomial.map_id, p, MonicDegreeEq.mk_coe]
      using factors.2.1.symm
  · exact ((factors.1.1.monic.natDegree_map (residue R)).symm).trans
      (congrArg Polynomial.natDegree hg)
  · exact ((factors.1.2.monic.natDegree_map (residue R)).symm).trans
      (congrArg Polynomial.natDegree hh)

end SpecialTransformations.Section6.Imported
