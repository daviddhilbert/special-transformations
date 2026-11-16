module

public import Mathlib.Order.Closure
public import Mathlib.Combinatorics.Matroid.IndepAxioms
public import Mathlib.Combinatorics.Matroid.Closure

@[expose] public section

/-!
# Finitary exchange closures and Mathlib matroids

The independent-set convention and insertion argument follow the public-domain
Lean 3 development `adamtopaz/comb_geom`, revision
`e16b629d6de3fbdea54a528755e7305dfb51e902`,
`src/pregeom/basis.lean::is_indep, insert_indep`. Source credit belongs to
that development's contributors; see Imported/CombGeom-UNLICENSE.
The remaining bridge uses Mathlib's existing `IndepMatroid.ofFinitary`.
This is a generic construction, not an assumption of RV dimension results.
-/

open Classical

noncomputable section

namespace SpecialTransformations.Section4.FinitaryClosure

variable {α : Type} (c : ClosureOperator (Set α))

def Independent (I : Set α) : Prop := ∀ x ∈ I, x ∉ c (I \ {x})

def Exchange : Prop := ∀ (I : Set α) (x y : α),
  x ∈ c (insert y I) → x ∉ c I → y ∈ c (insert x I)

def FiniteCharacter : Prop := ∀ (I : Set α) (x : α), x ∈ c I →
  ∃ J : Set α, J ⊆ I ∧ J.Finite ∧ x ∈ c J

theorem independent_empty : Independent c ∅ := by
  intro x hx
  exact False.elim hx

theorem independent_subset {I J : Set α} (hJ : Independent c J) (hIJ : I ⊆ J) :
    Independent c I := by
  intro x hx hcl
  apply hJ x (hIJ hx)
  apply c.monotone (show I \ {x} ⊆ J \ {x} from fun _ h => ⟨hIJ h.1, h.2⟩)
  exact hcl

theorem independent_insert (hex : Exchange c) {I : Set α} {x : α}
    (hI : Independent c I) (hx : x ∉ c I) : Independent c (insert x I) := by
  intro y hy hcl
  by_cases hyx : y = x
  · subst y
    apply hx
    exact c.monotone (by intro z hz; exact hz.1.resolve_left (fun h => hz.2 (h ▸ rfl))) hcl
  · have hyI : y ∈ I := hy.resolve_left hyx
    have he : insert x I \ {y} = insert x (I \ {y}) := by
      ext z
      simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
      aesop
    rw [he] at hcl
    have hswap := hex (I \ {y}) y x hcl (hI y hyI)
    have hback : insert y (I \ {y}) = I := by
      ext z
      simp only [Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff]
      aesop
    exact hx (hback ▸ hswap)

theorem maximal_independent_spans (hex : Exchange c) {B : Set α}
    (hB : Maximal (Independent c) B) : ∀ x, x ∈ c B := by
  intro x
  by_contra hx
  have hxB : x ∉ B := fun h => hx (c.le_closure B h)
  exact hB.not_prop_of_ssuperset (Set.ssubset_insert hxB) (independent_insert c hex hB.1 hx)

theorem independent_augmentation (hex : Exchange c) {I B : Set α}
    (hI : Independent c I) (hnot : ¬ Maximal (Independent c) I)
    (hB : Maximal (Independent c) B) :
    ∃ x ∈ B \ I, Independent c (insert x I) := by
  obtain ⟨J, hIJ, hJ⟩ := exists_gt_of_not_maximal hI hnot
  obtain ⟨x, hxJ, hxI⟩ := Set.exists_of_ssubset hIJ
  have hx : x ∉ c I := by
    intro hcl
    apply hJ x hxJ
    apply c.monotone (show I ⊆ J \ {x} from by
      intro y hy
      exact ⟨hIJ.le hy, fun he => hxI (he ▸ hy)⟩)
    exact hcl
  by_contra! hno
  have hBC : B ⊆ c I := by
    intro b hb
    by_cases hbI : b ∈ I
    · exact c.le_closure I hbI
    · by_contra hbcl
      exact hno b ⟨hb, hbI⟩ (independent_insert c hex hI hbcl)
  have hmono : c B ⊆ c I := by
    have h := c.monotone hBC
    rwa [c.idempotent] at h
  exact hx (hmono (maximal_independent_spans c hex hB x))

theorem independent_finite_character (hfin : FiniteCharacter c) (I : Set α)
    (hI : ∀ J, J ⊆ I → J.Finite → Independent c J) : Independent c I := by
  intro x hx hcl
  obtain ⟨J, hJI, hJfin, hxJ⟩ := hfin (I \ {x}) x hcl
  have hxnot : x ∉ J := fun h => (hJI h).2 rfl
  have hins := hI (insert x J) (Set.insert_subset hx (hJI.trans Set.sdiff_subset)) (hJfin.insert x)
  apply hins x (Set.mem_insert x J)
  exact c.monotone (by intro y hy; exact ⟨Or.inr hy, fun he => hxnot (he ▸ hy)⟩) hxJ

def matroid (hex : Exchange c) (hfin : FiniteCharacter c) : Matroid α :=
  (IndepMatroid.ofFinitary Set.univ (Independent c) (independent_empty c)
    (fun {I J} hJ hIJ => independent_subset c hJ hIJ)
    (fun {I B} hI hnot hB => independent_augmentation c hex hI hnot hB)
    (independent_finite_character c hfin) (fun _ _ => Set.subset_univ _)).matroid

@[simp] theorem matroid_indep_iff (hex : Exchange c) (hfin : FiniteCharacter c) (I : Set α) :
    (matroid c hex hfin).Indep I ↔ Independent c I := Iff.rfl

@[simp] theorem matroid_ground (hex : Exchange c) (hfin : FiniteCharacter c) :
    (matroid c hex hfin).E = Set.univ := rfl

theorem matroid_closure_of_independent (hex : Exchange c) (hfin : FiniteCharacter c)
    {I : Set α} (hI : (matroid c hex hfin).Indep I) :
    (matroid c hex hfin).closure I = c I := by
  ext x
  rw [hI.mem_closure_iff']
  constructor
  · rintro ⟨_, h⟩
    by_contra hx
    have hi : (matroid c hex hfin).Indep (insert x I) :=
      independent_insert c hex hI hx
    exact hx (c.le_closure I (h hi))
  · intro hx
    refine ⟨Set.mem_univ _, ?_⟩
    intro hi
    by_contra hxI
    apply hi x (Set.mem_insert x I)
    exact c.monotone (by
      intro y hy
      exact ⟨Or.inr hy, fun he => hxI (he ▸ hy)⟩) hx

/-- The constructed matroid's closure is exactly the original closure
operator. This bridge prevents substituting an unrelated rank geometry. -/
theorem matroid_closure (hex : Exchange c) (hfin : FiniteCharacter c) (X : Set α) :
    (matroid c hex hfin).closure X = c X := by
  obtain ⟨I, hI⟩ := (matroid c hex hfin).exists_isBasis X (by
    rw [matroid_ground]
    exact Set.subset_univ _)
  have hcI := matroid_closure_of_independent c hex hfin hI.indep
  have hX : X ⊆ c I := by simpa only [hcI] using hI.subset_closure
  have he : c I = c X := by
    apply (c.monotone hI.subset).antisymm
    have h := c.monotone hX
    rwa [c.idempotent] at h
  exact hI.closure_eq_closure.symm.trans (hcI.trans he)

end SpecialTransformations.Section4.FinitaryClosure

end
