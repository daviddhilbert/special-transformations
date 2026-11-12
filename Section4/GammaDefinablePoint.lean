module

public import Section4.GammaControllerDefinability
public import Section4.GammaFiniteDefinablePoints
public import Section4.GammaDefinableClosure
public import Section4.FiniteOrderSamples

@[expose] public section

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

noncomputable section

namespace SpecialTransformations.Section4

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

/-- The point is definable over the original real base. The standing
nontrivial named value is retained; no order-completeness assumption or
temporary RV representative is included among the parameters. -/
theorem gamma_definable_point (h00 : M ⊨ Axioms.ACVF00)
    (δ : Values.Gamma (M := M)) (hδ : Values.GammaDefinable S {δ}) (hδ1 : 1 < δ)
    (A : Set (Values.Gamma (M := M))) (hA : Values.GammaDefinable S A)
    (hne : A.Nonempty) : ∃ γ ∈ A, Values.GammaDefinable S {γ} := by
  obtain ⟨F, hF, hFd, _⟩ := exists_definable_minimal_gamma_controller h00 A hA
  have hFD : (F : Set (Values.Gamma (M := M))) ⊆ GammaDcl S :=
    fun c hc => gamma_finset_element_definable F hFd c hc
  obtain ⟨hbelow, habove, hbetween⟩ := gammaDcl_samples δ hδ hδ1
  obtain ⟨γ, hγA, hγD⟩ := FiniteOrder.nonempty_inter_of_controls F A (GammaDcl S)
    hF hne ⟨1, gammaDcl_one⟩ hFD hbelow habove hbetween
  exact ⟨γ, hγA, hγD⟩

/-- Iterating projection and fibres supplies an original-base definable
point in every nonempty definable finite-dimensional Gamma set. -/
theorem gamma_tuple_definable_point (h00 : M ⊨ Axioms.ACVF00)
    (δ : Values.Gamma (M := M)) (hδ : Values.GammaDefinable S {δ}) (hδ1 : 1 < δ)
    {n : ℕ} (A : Set (Fin n → Values.Gamma (M := M)))
    (hA : GammaSyntax.Definable S (fun a => a ∈ A)) (hne : A.Nonempty) :
    ∃ γ ∈ A, ∀ i, Values.GammaDefinable S {γ i} := by
  induction n with
  | zero =>
    obtain ⟨a, ha⟩ := hne
    exact ⟨a, ha, fun i => i.elim0⟩
  | succ n ih =>
    let idx : Fin (n + 1) → Fin n ⊕ Fin 1 := Fin.lastCases (.inr 0) Sum.inl
    have hidx (a : Fin n → Values.Gamma (M := M)) (b : Fin 1 → Values.Gamma (M := M)) :
        Sum.elim a b ∘ idx = Fin.snoc a (b 0) := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Function.comp_apply, idx, Fin.lastCases_last, Sum.elim_inr, Fin.snoc_last]
      · simp only [Function.comp_apply, idx, Fin.lastCases_castSucc, Sum.elim_inl, Fin.snoc_castSucc]
    let P : Set (Fin n → Values.Gamma (M := M)) := {a | ∃ b, Fin.snoc a b ∈ A}
    have hP : GammaSyntax.Definable S (fun a => a ∈ P) := by
      have h := (hA.reindex idx).exists_block
      exact h.congr (fun a => by
        constructor
        · rintro ⟨b, hb⟩
          exact ⟨b 0, by rwa [hidx] at hb⟩
        · rintro ⟨b, hb⟩
          exact ⟨fun _ => b, by rwa [hidx]⟩)
    have hPne : P.Nonempty := by
      obtain ⟨a, ha⟩ := hne
      exact ⟨Fin.init a, a (Fin.last n), by simpa only [Fin.snoc_init_self] using ha⟩
    obtain ⟨a, ⟨b, hab⟩, had⟩ := ih P hP hPne
    let T : Set (Values.Gamma (M := M)) := {b | Fin.snoc a b ∈ A}
    let ι := Fin 1 ⊕ Fin n
    let idx' : Fin (n + 1) → ι := Fin.lastCases (.inl 0) Sum.inr
    have hidx' (z : Fin 1 → Values.Gamma (M := M)) (t : Fin n → Values.Gamma (M := M)) :
        Sum.elim z t ∘ idx' = Fin.snoc t (z 0) := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Function.comp_apply, idx', Fin.lastCases_last, Sum.elim_inl, Fin.snoc_last]
      · simp only [Function.comp_apply, idx', Fin.lastCases_castSucc, Sum.elim_inr, Fin.snoc_castSucc]
    have hnames : GammaSyntax.Definable S
        (fun z : ι → Values.Gamma (M := M) => ∀ i, z (.inr i) = a i) :=
      GammaSyntax.Definable.forall_finite (fun i => GammaSyntax.unary_at (had i) (Sum.inr i))
    have hT : Values.GammaDefinable S T := by
      have h := ((hA.reindex idx').and hnames).exists_block
      apply (GammaSyntax.scalar_definable_iff T).mp
      exact h.congr (fun z => by
        simp only [hidx', Sum.elim_inr]
        change (∃ t : Fin n → Values.Gamma (M := M),
          Fin.snoc t (z 0) ∈ A ∧ ∀ i, t i = a i) ↔ Fin.snoc a (z 0) ∈ A
        constructor
        · rintro ⟨t, ht, he⟩
          have hta : t = a := funext he
          rwa [hta] at ht
        · intro hz
          exact ⟨a, hz, fun _ => rfl⟩)
    obtain ⟨c, hc, hcd⟩ := gamma_definable_point h00 δ hδ hδ1 T hT ⟨b, hab⟩
    refine ⟨Fin.snoc a c, hc, ?_⟩
    exact Fin.lastCases (by simpa only [Fin.snoc_last] using hcd)
      (fun i => by simpa only [Fin.snoc_castSucc] using had i)

end SpecialTransformations.Section4

end
