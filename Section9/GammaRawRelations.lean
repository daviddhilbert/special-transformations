import Section9.GammaLiftObjects

/-! A relation between point spaces whose code set is the trace of a set
definable over the real base is Gamma-definable. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaPointCode
  gammaPointSort vfAt)

namespace SpecialTransformations.Section9.GammaLift

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {B : Base (M := M)}

theorem productTuple_eq_append {X : Type*} {m n : ℕ} (a : Fin m → X) (b : Fin n → X) :
    productTuple a b = Fin.append a b := by
  apply productTuple_ext
  · intro i
    rw [productTuple_left]
    change a i = Fin.append a b (Fin.castAdd n i)
    rw [Fin.append_left]
  · intro i
    rw [productTuple_right]
    change b i = Fin.append a b (Fin.natAdd m i)
    rw [Fin.append_right]

theorem gammaPointCode_sorted {n m : ℕ} (p : Point (M := M) n m) (i : Fin (n + m)) :
    sortEval (gammaPointSort n m i) (gammaPointCode p i) := by
  cases i using Fin.addCases with
  | left i => simpa only [gammaPointSort, gammaPointCode, Fin.append_left, vfAt, sortEval, iVF]
      using (p.1 i).property
  | right i => simpa only [gammaPointSort, gammaPointCode, Fin.append_right, sortEval, iRV]
      using (p.2 i).property

theorem exists_gammaPointCode {n m : ℕ} (x : Fin (n + m) → M)
    (hx : ∀ i, sortEval (gammaPointSort n m i) (x i)) : ∃ p : Point (M := M) n m, gammaPointCode p = x := by
  refine ⟨(fun i => ⟨x (Fin.castAdd m i), by
      simpa only [gammaPointSort, Fin.append_left, sortEval, iVF] using hx (Fin.castAdd m i)⟩,
    fun i => ⟨x (Fin.natAdd n i), by
      simpa only [gammaPointSort, Fin.append_right, sortEval, iRV] using hx (Fin.natAdd n i)⟩), ?_⟩
  funext i
  cases i using Fin.addCases <;> simp [gammaPointCode, vfAt]

theorem gamma_graph_of_raw (hcan : CanonicalStructure.IsCanonical (M := M)) {n m u w : ℕ}
    (r : Point (M := M) n m → Point (M := M) u w → Prop)
    (Z : Set (Fin ((n + m) + (u + w)) → M)) (hZ : B.real.Definable LRV Z)
    (hr : ∀ p q, r p q ↔ Fin.append (gammaPointCode p) (gammaPointCode q) ∈ Z) :
    GammaGraphDefinable B r := by
  let σ := Fin.append (gammaPointSort n m) (gammaPointSort u w)
  let Z' : Set (Fin ((n + m) + (u + w)) → M) := {z | z ∈ Z ∧ ∀ i, sortEval (σ i) (z i)}
  have hZ' : B.real.Definable LRV Z' := hZ.inter (sortedUniverse_definable B.real σ).raw_definable
  have h := real_definableOverBase B σ Z' (raw_definableOver_sorted hcan B.real σ Z' hZ' (fun _ hz => hz.2))
  unfold GammaGraphDefinable
  convert h using 1
  ext z
  constructor
  · rintro ⟨p, q, hpq, rfl⟩
    refine ⟨(hr p q).mp hpq, fun i => ?_⟩
    cases i using Fin.addCases with
    | left i => simpa only [σ, Fin.append_left] using gammaPointCode_sorted p i
    | right i => simpa only [σ, Fin.append_right] using gammaPointCode_sorted q i
  · rintro ⟨hz, hs⟩
    obtain ⟨p, hp⟩ := exists_gammaPointCode (n := n) (m := m) (fun i => z (Fin.castAdd (u + w) i))
      (fun i => by simpa only [σ, Fin.append_left] using hs (Fin.castAdd (u + w) i))
    obtain ⟨q, hq⟩ := exists_gammaPointCode (n := u) (m := w) (fun i => z (Fin.natAdd (n + m) i))
      (fun i => by simpa only [σ, Fin.append_right] using hs (Fin.natAdd (n + m) i))
    have he : Fin.append (gammaPointCode p) (gammaPointCode q) = z := by
      rw [hp, hq]
      funext i
      cases i using Fin.addCases <;> simp
    exact ⟨p, q, (hr p q).mpr (he ▸ hz), he⟩

theorem gamma_set_of_raw (hcan : CanonicalStructure.IsCanonical (M := M)) {n m : ℕ}
    (X : Set (Point (M := M) n m)) (Z : Set (Fin (n + m) → M)) (hZ : B.real.Definable LRV Z)
    (hX : ∀ p, p ∈ X ↔ gammaPointCode p ∈ Z) : GammaSetDefinable B X := by
  let σ := gammaPointSort n m
  let Z' : Set (Fin (n + m) → M) := {z | z ∈ Z ∧ ∀ i, sortEval (σ i) (z i)}
  have hZ' : B.real.Definable LRV Z' := hZ.inter (sortedUniverse_definable B.real σ).raw_definable
  have h := real_definableOverBase B σ Z' (raw_definableOver_sorted hcan B.real σ Z' hZ' (fun _ hz => hz.2))
  unfold GammaSetDefinable
  convert h using 1
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(hX p).mp hp, gammaPointCode_sorted p⟩
  · rintro ⟨hz, hs⟩
    obtain ⟨p, hp⟩ := exists_gammaPointCode z hs
    exact ⟨p, (hX p).mpr (hp ▸ hz), hp⟩

/-- An RV set over the real base, as a set of points, is Gamma-definable. -/
theorem rv_set_gamma_of_raw (hcan : CanonicalStructure.IsCanonical (M := M)) {n : ℕ}
    (Z : Set (Fin n → M)) (hZ : B.real.Definable LRV Z) :
    GammaSetDefinable B {q : Point (M := M) 0 n | rvValues q.2 ∈ Z} := by
  apply gamma_set_of_raw hcan _ ((fun w => w ∘ Fin.natAdd 0) ⁻¹' Z) (hZ.preimage_comp (Fin.natAdd 0))
  intro q
  have : gammaPointCode q ∘ Fin.natAdd 0 = rvValues q.2 := by
    funext i
    simp only [Function.comp_apply, gammaPointCode, Fin.append_right, rvValues]
  change _ ↔ gammaPointCode q ∘ Fin.natAdd 0 ∈ Z
  rw [this]
  rfl

/-- A real RV map between full RV spaces over `B.real` has a Gamma graph. -/
theorem rv_univ_map_gamma (hcan : CanonicalStructure.IsCanonical (M := M)) {a b : ℕ}
    (f : DefinableGeometry.Map (DefinableGeometry.DefSet.univ (rawRVSpace (M := M) a) B.real)
      (DefinableGeometry.DefSet.univ (rawRVSpace (M := M) b) B.real)) :
    GammaGraphDefinable B (fun (p : Point (M := M) 0 a) (q : Point (M := M) 0 b) =>
      (f ⟨p.2, Set.mem_univ _⟩).val = q.2) := by
  let P := rawRVSpace (M := M) a
  let Q := rawRVSpace (M := M) b
  let ι : Fin a ⊕ Fin b → Fin ((0 + a) + (0 + b)) :=
    Sum.elim (fun i => Fin.castAdd (0 + b) (Fin.natAdd 0 i)) (fun i => Fin.natAdd (0 + a) (Fin.natAdd 0 i))
  apply gamma_graph_of_raw hcan _ ((fun w => w ∘ ι) ⁻¹' P.relation Q f.graph)
    (f.graph_definable.preimage_comp ι)
  intro p q
  have h1 : (Fin.append (gammaPointCode p) (gammaPointCode q) ∘ ι) ∘ Sum.inl = rvValues p.2 := by
    funext i
    show Fin.append (gammaPointCode p) (gammaPointCode q) (Fin.castAdd (0 + b) (Fin.natAdd 0 i)) = (p.2 i).val
    rw [Fin.append_left]
    unfold gammaPointCode
    rw [Fin.append_right]
  have h2 : (Fin.append (gammaPointCode p) (gammaPointCode q) ∘ ι) ∘ Sum.inr = rvValues q.2 := by
    funext i
    show Fin.append (gammaPointCode p) (gammaPointCode q) (Fin.natAdd (0 + a) (Fin.natAdd 0 i)) = (q.2 i).val
    rw [Fin.append_right]
    unfold gammaPointCode
    rw [Fin.append_right]
  change _ ↔ ∃ hx : (Fin.append (gammaPointCode p) (gammaPointCode q) ∘ ι) ∘ Sum.inl ∈ P.domain,
    ∃ hy : (Fin.append (gammaPointCode p) (gammaPointCode q) ∘ ι) ∘ Sum.inr ∈ Q.domain,
      f.graph (P.decode ⟨_, hx⟩) (Q.decode ⟨_, hy⟩)
  have hd1 (hx : (Fin.append (gammaPointCode p) (gammaPointCode q) ∘ ι) ∘ Sum.inl ∈ P.domain) :
      P.decode ⟨_, hx⟩ = p.2 := rvValues_injective ((rvValues_decode _).trans h1)
  have hd2 (hy : (Fin.append (gammaPointCode p) (gammaPointCode q) ∘ ι) ∘ Sum.inr ∈ Q.domain) :
      Q.decode ⟨_, hy⟩ = q.2 := rvValues_injective ((rvValues_decode _).trans h2)
  constructor
  · intro h
    refine ⟨h1 ▸ ⟨p.2, rfl⟩, h2 ▸ ⟨q.2, rfl⟩, ?_⟩
    rw [hd1, hd2]
    exact ⟨⟨p.2, Set.mem_univ _⟩, rfl, h⟩
  · rintro ⟨hx, hy, u, hu, hf⟩
    rw [hd1] at hu
    rw [hd2] at hf
    have : u = ⟨p.2, Set.mem_univ _⟩ := Subtype.ext hu
    rw [← this]
    exact hf

end SpecialTransformations.Section9.GammaLift
