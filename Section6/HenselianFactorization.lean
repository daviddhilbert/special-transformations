module

public import Section6.Imported.CoprimeFactorLifting
public import Mathlib.Algebra.Polynomial.FieldDivision

@[expose] public section

/-!
An irreducible monic polynomial over a henselian valuation ring cannot
have both a zero residue root and a nonzero root over a residue extension.
The factorization argument is adapted from NYLL's `MonicFactorization`
at `0fbaf705e33806c8482dd85e169de005ba13d762`.
Copyright 2026 Naganori Yamaguchi. Apache-2.0, see Imported/NYLL-LICENSE.
-/

open Polynomial IsLocalRing

namespace SpecialTransformations.Section6

theorem false_of_mixed_residue_roots
    {K : Type*} [Field K] {A : ValuationSubring K} [HenselianLocalRing A]
    {Q : A[X]} (hQ : Q.Monic) (hirr : Irreducible (Q.map A.subtype))
    (hz : (Q.map (residue A)).IsRoot 0)
    {k : Type*} [Field k] (ρ : ResidueField A →+* k) {b : k} (hb : b ≠ 0)
    (hroot : ((Q.map (residue A)).map ρ).IsRoot b) : False := by
  let q := Q.map (residue A)
  have hq : q.Monic := hQ.map (residue A)
  obtain ⟨R, hfac, hndvd⟩ := q.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hq.ne_zero 0
  let r := q.rootMultiplicity 0
  have hr : 0 < r := (Polynomial.rootMultiplicity_pos hq.ne_zero).mpr hz
  have hfac' : q = X ^ r * R := by simpa [r] using hfac
  have hndvd' : ¬ X ∣ R := by simpa using hndvd
  have hmX : (X ^ r : (ResidueField A)[X]).Monic := monic_X_pow r
  have hmR : R.Monic := hmX.of_mul_monic_left (hfac' ▸ hq)
  have hcop : IsCoprime (X ^ r) R :=
    ((Polynomial.prime_X (R := ResidueField A)).coprime_iff_not_dvd.mpr hndvd').pow_left
  have hbR : (R.map ρ).IsRoot b := by
    change (q.map ρ).eval b = 0 at hroot
    rw [hfac', Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X] at hroot
    exact (mul_eq_zero.mp hroot).resolve_left (pow_ne_zero r hb)
  have hRpos : 0 < R.natDegree := by
    by_contra hn
    have hRone := Polynomial.eq_one_of_monic_natDegree_zero hmR (Nat.eq_zero_of_not_pos hn)
    simp [hRone, Polynomial.IsRoot] at hbR
  obtain ⟨g, h, hg, hh, hf, hdg, hdh, _, _, _⟩ :=
    Imported.exists_coprime_factor_lift Q (X ^ r) R hQ hmX hmR hfac' hcop
  have nonunit {p : A[X]} (hp : p.Monic) (hd : 0 < p.natDegree) :
      ¬ IsUnit (p.map A.subtype) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero,
      Polynomial.degree_eq_natDegree (hp.map A.subtype).ne_zero,
      hp.natDegree_map]
    exact_mod_cast hd.ne'
  have hu := hirr.isUnit_or_isUnit (show Q.map A.subtype = _ * _ by rw [hf, Polynomial.map_mul])
  exact hu.elim (nonunit hg (by rwa [hdg, natDegree_X_pow])) (nonunit hh (hdh.symm ▸ hRpos))

end SpecialTransformations.Section6
