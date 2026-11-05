/-
Adapted from Elliot Glazer's `definable-saturated` repository, developed with
agent-assisted Lean implementation (see the upstream README's provenance).
Licensed under Apache License 2.0; see vendor/definable-saturated/LICENSE.
Source: https://github.com/elliotglazer/definable-saturated
Commit: e683bba9e758323b43dd1d6206ed2f6fc9510f06
Palomar: PALOMAR-2026-09-19-000005, version 1.

Extracted from Scotts/ModelTheory/CountableSaturation.lean,
CountableParameterSaturation.lean, and SaturatedExistence.lean. The ordinary
ultrapower proofs are preserved in an isolated namespace. Added the adapter
to MarkerBridge.SatAt and removed unrelated arithmetic and CH/cardinality
results. Ported from Lean 4.34.0-rc1 to this repository's pinned Lean 4.33.1.
-/
import MarkerBridge
import Mathlib.ModelTheory.Ultraproducts
import Mathlib.ModelTheory.Encoding
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Data.Finset.Max

/-!
Countably saturated elementary extensions from nonprincipal ultrapowers.
The base model need only be nonempty. For a countable language, the ultrapower
realizes every finitely satisfiable one-variable type over countably many
parameters. No continuum hypothesis or bound on the resulting cardinality is
used.
-/

open FirstOrder FirstOrder.Language Filter

namespace CountableSaturatedExtension

universe u v w z

noncomputable section

section Types

variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M]
/-- Realization of a one-variable formula with named parameters from `M`. -/
def RealizesWithParameters (m : M) (φ : L.Formula (M ⊕ Unit)) : Prop :=
  φ.Realize (Sum.elim id (fun _ => m))

/-- Finite satisfiability in the given structure, with all parameters fixed. -/
def FinitelySatisfiableIn (p : Set (L.Formula (M ⊕ Unit))) : Prop :=
  ∀ s : Finset (L.Formula (M ⊕ Unit)), (↑s : Set _) ⊆ p →
    ∃ m : M, ∀ φ ∈ s, RealizesWithParameters m φ

/-- Every countable finitely satisfiable partial one-type over `M` is realized.
The formulas and their interpretations are Mathlib first-order formulas. -/
def CountablySaturated (L : FirstOrder.Language.{u, v}) (M : Type w)
    [L.Structure M] : Prop :=
  ∀ p : Set (L.Formula (M ⊕ Unit)), p.Countable →
    FinitelySatisfiableIn p → ∃ m : M, ∀ φ ∈ p, RealizesWithParameters m φ

def RealizesOver {A : Type z} (a : A → M) (x : M) (φ : L.Formula (A ⊕ Unit)) : Prop :=
  φ.Realize (Sum.elim a (fun _ => x))

def FinitelySatisfiableOver {A : Type z} (a : A → M)
    (p : Set (L.Formula (A ⊕ Unit))) : Prop :=
  ∀ s : Finset (L.Formula (A ⊕ Unit)), (↑s : Set _) ⊆ p →
    ∃ x : M, ∀ φ ∈ s, RealizesOver a x φ

theorem CountablySaturated.realize_over (h : CountablySaturated L M)
    {A : Type z} (a : A → M) (p : Set (L.Formula (A ⊕ Unit))) (hp : p.Countable)
    (hf : FinitelySatisfiableOver a p) : ∃ x : M, ∀ φ ∈ p, RealizesOver a x φ := by
  classical
  let f : L.Formula (A ⊕ Unit) → L.Formula (M ⊕ Unit) :=
    fun φ => φ.relabel (Sum.map a id)
  have hr (φ : L.Formula (A ⊕ Unit)) (x : M) :
      RealizesWithParameters x (f φ) ↔ RealizesOver a x φ := by
    simp only [RealizesWithParameters, RealizesOver, f, Formula.realize_relabel]
    apply Iff.of_eq
    apply congrArg φ.Realize
    funext i
    cases i <;> rfl
  have hfin : FinitelySatisfiableIn (f '' p) := by
    intro s hs
    have hpre : ∀ ψ : s, ∃ φ, φ ∈ p ∧ f φ = ψ.val := fun ψ => hs ψ.property
    choose g hgp hgf using hpre
    obtain ⟨x, hx⟩ := hf (Finset.univ.image g) (by
      intro φ hφ
      obtain ⟨ψ, _, rfl⟩ := Finset.mem_image.mp hφ
      exact hgp ψ)
    refine ⟨x, ?_⟩
    intro ψ hψ
    let ψ' : s := ⟨ψ, hψ⟩
    have hreal := (hr (g ψ') x).mpr (hx (g ψ')
      (Finset.mem_image.mpr ⟨ψ', Finset.mem_univ _, rfl⟩))
    simpa only [hgf ψ'] using hreal
  obtain ⟨x, hx⟩ := h (f '' p) (hp.image f) hfin
  exact ⟨x, fun φ hφ => (hr φ x).mp (hx (f φ) ⟨φ, hφ, rfl⟩)⟩


end Types

/-- The ultrapower by a fixed nonprincipal ultrafilter on the natural numbers. -/
def CountableUltrapower (M : Type w) : Type w :=
  ((Filter.hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ).Product (fun _ => M)

namespace CountableUltrapower

variable {L : FirstOrder.Language.{u, v}} {M : Type w}

instance [L.Structure M] : L.Structure (CountableUltrapower M) :=
  inferInstanceAs (L.Structure
    (((Filter.hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ).Product (fun _ => M)))

instance [Nonempty M] : Nonempty (CountableUltrapower M) :=
  inferInstanceAs (Nonempty
    (((Filter.hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ).Product (fun _ => M)))

/-- The quotient map from sequences. -/
def classOf (f : ℕ → M) : CountableUltrapower M :=
  Quotient.mk (((Filter.hyperfilter ℕ) : Filter ℕ).productSetoid (fun _ => M)) f

/-- Representatives are chosen once, including for all named parameters. -/
noncomputable def representative (a : CountableUltrapower M) : ℕ → M := Quotient.out a

@[simp] theorem classOf_representative (a : CountableUltrapower M) :
    classOf (representative a) = a := Quotient.out_eq a

variable [L.Structure M] [Nonempty M]

/-- The diagonal map is an elementary embedding, by Łoś's theorem. -/
def diagonal : M ↪ₑ[L] CountableUltrapower M where
  toFun m := classOf (fun _ => m)
  map_formula' := by
    intro n φ x
    exact (Language.Ultraproduct.realize_formula_cast φ (fun j _ => x j)).trans
      Filter.eventually_const

/-- Evaluate a formula at one coordinate, using the fixed representatives
of all its ultrapower parameters. -/
def atCoordinate (φ : L.Formula (CountableUltrapower M ⊕ Unit)) (i : ℕ) (m : M) : Prop :=
  φ.Realize (Sum.elim (fun a => representative a i) (fun _ => m))

theorem realizes_classOf_iff (φ : L.Formula (CountableUltrapower M ⊕ Unit)) (f : ℕ → M) :
    RealizesWithParameters (classOf f) φ ↔
      ∀ᶠ i in Filter.hyperfilter ℕ, atCoordinate φ i (f i) := by
  have hv : (fun z => classOf (Sum.elim representative (fun _ : Unit => f) z)) =
      Sum.elim id (fun _ => classOf f) := by
    funext z
    cases z with
    | inl a => exact classOf_representative a
    | inr x => rfl
  have hw (i : ℕ) :
      (fun z => Sum.elim representative (fun _ : Unit => f) z i) =
        Sum.elim (fun a => representative a i) (fun _ => f i) := by
    funext z
    cases z <;> rfl
  have h := Language.Ultraproduct.realize_formula_cast
    (u := Filter.hyperfilter ℕ) φ (Sum.elim representative (fun _ : Unit => f))
  change (φ.Realize (fun z => classOf (Sum.elim representative (fun _ : Unit => f) z)) ↔
    ∀ᶠ i in Filter.hyperfilter ℕ,
      φ.Realize (fun z => Sum.elim representative (fun _ : Unit => f) z i)) at h
  simpa only [hv, hw, RealizesWithParameters, atCoordinate] using h

/-- A direct diagonalization realizes any countable sequence of finitely
satisfiable formulas in the nonprincipal ultrapower. -/
theorem realize_sequence (φ : ℕ → L.Formula (CountableUltrapower M ⊕ Unit))
    (hfin : ∀ s : Finset ℕ, ∃ a : CountableUltrapower M,
      ∀ n ∈ s, RealizesWithParameters a (φ n)) :
    ∃ a : CountableUltrapower M, ∀ n, RealizesWithParameters a (φ n) := by
  classical
  let : Inhabited M := Classical.inhabited_of_nonempty inferInstance
  choose a ha using fun n => hfin (Finset.range (n + 1))
  let f (n : ℕ) : ℕ → M := representative (a n)
  let good (n i : ℕ) : Prop := ∀ k ∈ Finset.range (n + 1), atCoordinate (φ k) i (f n i)
  have hgood (n : ℕ) : ∀ᶠ i in Filter.hyperfilter ℕ, good n i := by
    apply (Filter.eventually_all_finset _).mpr
    intro k hk
    apply (realizes_classOf_iff (φ k) (f n)).mp
    simpa only [f, classOf_representative] using ha n k hk
  let choices (i : ℕ) : Finset ℕ := (Finset.range (i + 1)).filter (fun n => good n i)
  let g (i : ℕ) : M :=
    if h : (choices i).Nonempty then f ((choices i).max' h) i else default
  refine ⟨classOf g, fun n => (realizes_classOf_iff (φ n) g).mpr ?_⟩
  have hlarge : ∀ᶠ i in Filter.hyperfilter ℕ, n ≤ i :=
    Nat.hyperfilter_le_atTop (Filter.eventually_ge_atTop n)
  filter_upwards [hlarge, hgood n] with i hi hgi
  have hn : n ∈ choices i := Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hi), hgi⟩
  have hne : (choices i).Nonempty := ⟨n, hn⟩
  have hmax : good ((choices i).max' hne) i :=
    (Finset.mem_filter.mp ((choices i).max'_mem hne)).2
  have hnmax : n ≤ (choices i).max' hne := (choices i).le_max' n hn
  simpa only [g, dif_pos hne] using
    hmax n (Finset.mem_range.mpr (Nat.lt_succ_of_le hnmax))

/-- The nonprincipal ultrapower realizes every countable finitely satisfiable
partial one-type, with its parameters interpreted as the given elements. -/
theorem countablySaturated : CountablySaturated L (CountableUltrapower M) := by
  classical
  intro p hp hfin
  by_cases hne : p.Nonempty
  · obtain ⟨φ, rfl⟩ := hp.exists_eq_range hne
    have hf : ∀ s : Finset ℕ, ∃ a : CountableUltrapower M,
        ∀ n ∈ s, RealizesWithParameters a (φ n) := by
      intro s
      obtain ⟨a, ha⟩ := hfin (s.image φ) (by
        intro ψ hψ
        obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hψ
        exact ⟨n, rfl⟩)
      exact ⟨a, fun n hn => ha (φ n) (Finset.mem_image.mpr ⟨n, hn, rfl⟩)⟩
    obtain ⟨a, ha⟩ := realize_sequence φ hf
    exact ⟨a, fun ψ ⟨n, hn⟩ => hn ▸ ha n⟩
  · exact ⟨Classical.choice inferInstance, fun φ hφ => (hne ⟨φ, hφ⟩).elim⟩

end CountableUltrapower
section SaturationAdapter

variable {L : FirstOrder.Language.{0, 0}} {M : Type} [L.Structure M]

/-- Countability of the language and parameter index makes every partial type
countable. The parameter map may repeat elements, exactly as in SatAt. -/
theorem satAt_of_countablySaturated [Countable L.Symbols]
    (h : CountablySaturated L M) :
    MarkerBridge.SatAt L M (Order.succ Cardinal.aleph0) := by
  intro A g hA p hp
  have hA' : Cardinal.mk A ≤ Cardinal.aleph0 := Order.lt_succ_iff.mp hA
  letI : Countable A := Cardinal.mk_le_aleph0_iff.mp hA'
  apply h.realize_over g p (Set.to_countable p)
  intro s hs
  obtain ⟨x, hx⟩ := hp (s : Set (L.Formula (A ⊕ Unit))) s.finite_toSet hs
  exact ⟨x, fun φ hφ => hx φ hφ⟩

namespace CountableUltrapower

variable [Nonempty M] [Countable L.Symbols]

/-- The ultrapower is genuinely aleph-one saturated in the existing SatAt
interface; the countability restriction concerns the language, not the model. -/
theorem satAt :
    MarkerBridge.SatAt L (CountableUltrapower M) (Order.succ Cardinal.aleph0) :=
  satAt_of_countablySaturated (countablySaturated (L := L) (M := M))

/-- The same ultrapower is saturated enough for every countable source model. -/
theorem satAt_of_countable (K : Type) [Countable K] :
    MarkerBridge.SatAt L (CountableUltrapower M) (Order.succ (Cardinal.mk K)) := by
  have hK : Cardinal.mk K ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0_iff.mpr inferInstance
  intro A g hA p hp
  exact satAt (L := L) (M := M) A g
    (lt_of_lt_of_le hA (Order.succ_le_succ hK)) p hp

end CountableUltrapower

/-- Every nonempty structure in a countable language has a genuinely
aleph-one saturated elementary extension. This does not assert that the
extension has cardinality aleph one. -/
theorem exists_saturated_elementary_extension (L : FirstOrder.Language.{0, 0})
    [Countable L.Symbols] (M : Type) [L.Structure M] [Nonempty M] :
    ∃ (N : Type) (sN : L.Structure N),
      @MarkerBridge.SatAt L N sN (Order.succ Cardinal.aleph0) ∧
        Nonempty (@ElementaryEmbedding L M N inferInstance sN) := by
  exact ⟨CountableUltrapower M, inferInstance,
    CountableUltrapower.satAt, ⟨CountableUltrapower.diagonal⟩⟩

end SaturationAdapter

end
end CountableSaturatedExtension

#print axioms CountableSaturatedExtension.CountableUltrapower.diagonal
#print axioms CountableSaturatedExtension.CountableUltrapower.countablySaturated
#print axioms CountableSaturatedExtension.CountableUltrapower.satAt
#print axioms CountableSaturatedExtension.exists_saturated_elementary_extension
