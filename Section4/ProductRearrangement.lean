import Section4.MapProduct

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language

noncomputable section

namespace SpecialTransformations.DefinableGeometry.Map

variable {L : Language} {M : Type} [L.Structure M]

/-- The middle interchange of four presented factors is definable using
the original codes, including every representative of imaginary factors. -/
def shuffle (P Q R T : Space L M) (S : Set M) :
    Map (DefSet.univ ((P.prod Q).prod (R.prod T)) S)
      (DefSet.univ ((P.prod R).prod (Q.prod T)) S) :=
  Map.ofCodes _ (fun x => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
    (fun z => Sum.elim
      (Sum.elim (fun i => z (.inl (.inl i))) (fun i => z (.inr (.inl i))))
      (Sum.elim (fun i => z (.inl (.inr i))) (fun i => z (.inr (.inr i)))))
    (fun i => by cases i with
      | inl j => cases j <;> exact Set.DefinableFun.proj L
      | inr j => cases j <;> exact Set.DefinableFun.proj L)
    (fun c => ⟨⟨c.property.1.1, c.property.2.1⟩, c.property.1.2, c.property.2.2⟩)
    (fun _ => rfl)

theorem shuffle_bijective (P Q R T : Space L M) (S : Set M) :
    Function.Bijective (shuffle P Q R T S) := by
  constructor
  · intro a b he
    apply Subtype.ext
    exact congrArg (fun z : DefSet.univ ((P.prod R).prod (Q.prod T)) S =>
      ((z.val.1.1, z.val.2.1), (z.val.1.2, z.val.2.2))) he
  · intro b
    exact ⟨⟨((b.val.1.1, b.val.2.1), (b.val.1.2, b.val.2.2)), Set.mem_univ _⟩,
      Subtype.ext rfl⟩

def prodUnivMap {P Q R T : Space L M} {S : Set M}
    (f : Map (DefSet.univ P S) (DefSet.univ R S))
    (g : Map (DefSet.univ Q S) (DefSet.univ T S)) :
    Map (DefSet.univ (P.prod Q) S) (DefSet.univ (R.prod T) S) :=
  ((f.comp (Map.fst P Q S _)).pair (g.comp (Map.snd P Q S _))).toUniv

theorem prodUnivMap_bijective {P Q R T : Space L M} {S : Set M}
    (f : Map (DefSet.univ P S) (DefSet.univ R S))
    (g : Map (DefSet.univ Q S) (DefSet.univ T S))
    (hf : Function.Bijective f) (hg : Function.Bijective g) :
    Function.Bijective (prodUnivMap f g) := by
  constructor
  · intro a b he
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val (hf.1 (Subtype.ext
        (congrArg (fun z : DefSet.univ (R.prod T) S => z.val.1) he)))
    · exact congrArg Subtype.val (hg.1 (Subtype.ext
        (congrArg (fun z : DefSet.univ (R.prod T) S => z.val.2) he)))
  · intro b
    obtain ⟨a, ha⟩ := hf.2 ⟨b.val.1, Set.mem_univ _⟩
    obtain ⟨c, hc⟩ := hg.2 ⟨b.val.2, Set.mem_univ _⟩
    refine ⟨⟨(a.val, c.val), Set.mem_univ _⟩, Subtype.ext ?_⟩
    exact Prod.ext (congrArg Subtype.val ha) (congrArg Subtype.val hc)

end SpecialTransformations.DefinableGeometry.Map

end
