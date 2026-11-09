import Section9.FiniteLimitSeparation
import Section9.LimitBallDefinable
import Section8.UnaryGerm

/-! Lemma 9.4. A finite minimal limit set injects into an actual nearby
fibre. The unary definable germ theorem makes the hits of all of its
separated neighbourhoods simultaneous. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace SpecialTransformations.Section9

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

local notation "VF" => VFType (M := M)

/-- Lemma 9.4 for the actual VF graph of the set-valued function. If the
finite minimal limit set is nonempty, the proof obtains a suitable input
in the punctured domain from minimality itself. -/
theorem lemma_9_4 {m k : ℕ} {A : Set (Fin 1 → VF)} {a : Fin 1 → VF}
    {f : (Fin 1 → VF) → Set (Fin m → VF)} {L : Set (Fin m → LimitPoint M)}
    (hG : @Set.Definable M (Set.univ : Set M) LRV (CanonicalStructure.normalize (M := M))
      (Fin 1 ⊕ Fin m) (unaryLimitGraph A f))
    (hfin : ∀ x ∈ A, (f x).Finite) (hk : ∀ x ∈ A, (f x).ncard ≤ k)
    (hL : IsMinimalLimitSet A a f L) (hLf : L.Finite) : L.ncard ≤ k := by
  classical
  by_cases hLne : L.Nonempty
  · letI : Valued VF (Values.presentationType (M := M)) :=
      Valued.mk' Values.presentationValuation
    have hv (x y : VF) : VFValued.predV x y ↔ Valued.v x ≤ Valued.v y :=
      Values.presentation_compatible x y
    have hbasis {U : Set VF} (hU : U ∈ 𝓝 (a 0)) :
        ∃ δ : Values.Gamma (M := M), ∀ x : Fin 1 → VF, x ∈ vfBall a δ → x 0 ∈ U := by
      obtain ⟨r, hr, h⟩ := exists_nonzero_ball_subset (a 0) hU
      let δ := Values.gammaOf (CanonicalRV.encodedRv r)
        (fun he => hr ((CanonicalRV.encodedRv_zero_iff r).mp he))
      refine ⟨δ, fun x hx => h ?_⟩
      exact (Section8.vfValue_lt_iff_presentation r (x 0 - a 0)).mp (hx 0)
    have hne {x : Fin 1 → VF} (hx : x ≠ a) : x 0 ≠ a 0 := by
      intro h
      exact hx (funext (fun i => by fin_cases i; exact h))
    obtain ⟨ε, hε⟩ := exists_pairwise_disjoint_limitBall hLf
    have hhitNear (b : L) : ∀ᶠ x in 𝓝 (a 0), x ≠ a 0 → x.val ∈ limitHits A f b.val ε := by
      obtain ⟨c, hc⟩ := Section8.unary_definable_punctured_germ hv
        (limitHits_definable A f hG b.val ε) (a 0)
      obtain ⟨δ, hδ⟩ := hbasis hc
      obtain ⟨x, hx, hxδ, y, hy, hyb⟩ := hL.frequently_hits b.property ε δ
      have hc' : c := (hδ x hxδ (hne hx.2)).mp ⟨x, hx.1, rfl, y, hy, hyb⟩
      exact hc.mono (fun _ h hxa => (h hxa).mpr hc')
    letI := hLf.fintype
    obtain ⟨δ, hδ⟩ := hbasis (Filter.eventually_all.mpr hhitNear)
    obtain ⟨b₀, hb₀⟩ := hLne
    obtain ⟨x, hx, hxδ, _⟩ := hL.frequently_hits hb₀ ε δ
    have hy (b : L) : ∃ y ∈ f x, y ∈ limitBall b.val ε := by
      obtain ⟨x', _, he, y, hy', hyb⟩ := hδ x hxδ b (hne hx.2)
      have hx' : x' = x := funext (fun i => by fin_cases i; exact Subtype.ext he)
      exact ⟨y, hx' ▸ hy', hyb⟩
    choose y hyf hyb using hy
    let q (b : Fin m → LimitPoint M) : Fin m → VF := if h : b ∈ L then y ⟨b, h⟩ else 0
    have hq (b : Fin m → LimitPoint M) (hb : b ∈ L) : q b = y ⟨b, hb⟩ := dif_pos hb
    apply (Set.ncard_le_ncard_of_injOn q (fun b hb => (hq b hb).symm ▸ hyf ⟨b, hb⟩)
      ?_ (hfin x hx.1)).trans (hk x hx.1)
    intro b hb c hc hbc
    by_contra hne'
    have hdis := Set.disjoint_left.mp (hε hb hc hne')
    have hqb : q b ∈ limitBall b ε := (hq b hb).symm ▸ hyb ⟨b, hb⟩
    have hqc : q c ∈ limitBall c ε := (hq c hc).symm ▸ hyb ⟨c, hc⟩
    exact hdis hqb (hbc.symm ▸ hqc)
  · rw [Set.not_nonempty_iff_eq_empty.mp hLne, Set.ncard_empty]
    exact Nat.zero_le _

end SpecialTransformations.Section9
