module

public import Section3.DefinableMeans
public import Section3.FiniteBarycentricCode

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
namespace SpecialTransformations.Section3.Barycentre
open RawClosure.Tuple
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable def rawHead {m : ℕ}
    (F : (Fin m → M) → Finset (VFType (M := M))) (t : Fin m → M) (x : M) : M :=
  iRv (iVFAdd x (iVFNeg (mean (F t)).val))

theorem rawHead_eq {m : ℕ} (F : (Fin m → M) → Finset (VFType (M := M)))
    (t : Fin m → M) (x : VFType (M := M)) :
    rawHead F t x.val = iRv (x - mean (F t)).val := by
  rw [sub_eq_add_neg]
  rfl

noncomputable def childFamily {m : ℕ}
    (F : (Fin m → M) → Finset (VFType (M := M)))
    (u : Fin (m + 1) → M) : Finset (VFType (M := M)) :=
  (F (Fin.init u)).filter (fun y =>
    iRv (y - mean (F (Fin.init u))).val = u (Fin.last m))

noncomputable def rawCode : (d : ℕ) → {m : ℕ} →
    ((Fin m → M) → Finset (VFType (M := M))) → (Fin m → M) → M → Fin d → M
  | 0, _, _, _, _ => Fin.elim0
  | d + 1, _, F, t, x => Fin.cons (rawHead F t x)
      (rawCode d (childFamily F) (Fin.snoc t (rawHead F t x)) x)

theorem rawHead_definable (h00 : M ⊨ Axioms.ACVF00) (S : Set M) {m : ℕ}
    (F : (Fin m → M) → Finset (VFType (M := M)))
    (hF : RelationDefinable S (finiteFibreRelation F))
    (N : ℕ) (hbound : ∀ t, (F t).card ≤ N) :
    S.DefinableFun LRV (fun w : Fin m ⊕ Fin 1 → M =>
      rawHead F (w ∘ Sum.inl) (w (.inr 0))) := by
  have hmean := (mean_definable h00 S F hF N hbound).comp
    (show S.DefinableMap LRV (fun w : Fin m ⊕ Fin 1 → M => w ∘ Sum.inl) from
      fun _ => Set.DefinableFun.proj LRV)
  have hneg : S.DefinableFun LRV (fun w : Fin m ⊕ Fin 1 → M =>
      iVFNeg (mean (F (w ∘ Sum.inl))).val) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV)
      Fn.vfNeg)).comp (by intro i; fin_cases i; exact hmean)
  have hadd : S.DefinableFun LRV (fun w : Fin m ⊕ Fin 1 → M =>
      iVFAdd (w (.inr 0)) (iVFNeg (mean (F (w ∘ Sum.inl))).val)) := by
    have hf : S.DefinableFun LRV (Structure.funMap (L := LRV) Fn.vfAdd) :=
      Set.DefinableFun.of_empty
      (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfAdd)
    apply hf.comp
    intro i
    fin_cases i
    · exact Set.DefinableFun.proj LRV
    · exact hneg
  exact (Set.DefinableFun.of_empty
    (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMap)).comp
      (by intro i; fin_cases i; exact hadd)

theorem childFamily_definable (h00 : M ⊨ Axioms.ACVF00) (S : Set M) {m : ℕ}
    (F : (Fin m → M) → Finset (VFType (M := M)))
    (hF : RelationDefinable S (finiteFibreRelation F))
    (N : ℕ) (hbound : ∀ t, (F t).card ≤ N) :
    RelationDefinable S (finiteFibreRelation (childFamily F)) := by
  let π : Fin m ⊕ Fin 1 → Fin (m + 1) ⊕ Fin 1 := Sum.map Fin.castSucc id
  have hparent := hF.preimage_comp π
  have hhead := (rawHead_definable h00 S F hF N hbound).comp
    (show S.DefinableMap LRV (fun w : Fin (m + 1) ⊕ Fin 1 → M => w ∘ π) from
      fun _ => Set.DefinableFun.proj LRV)
  have hs := Set.DefinableFun.proj (M := M) (L := LRV) (A := S)
    (i := (.inl (Fin.last m) : Fin (m + 1) ⊕ Fin 1))
  have h := hparent.inter (hhead.ofPred_eq hs)
  change S.Definable LRV _
  convert h using 1
  ext w
  change (∃ y ∈ childFamily F (w ∘ Sum.inl), y.val = w (.inr 0)) ↔
    (∃ y ∈ F (Fin.init (w ∘ Sum.inl)), y.val = w (.inr 0)) ∧
      rawHead F (Fin.init (w ∘ Sum.inl)) (w (.inr 0)) = w (.inl (Fin.last m))
  constructor
  · rintro ⟨y, hy, he⟩
    obtain ⟨hy, hs⟩ := Finset.mem_filter.mp hy
    refine ⟨⟨y, hy, he⟩, ?_⟩
    rw [← he, rawHead_eq]
    exact hs
  · rintro ⟨⟨y, hy, he⟩, hs⟩
    refine ⟨y, Finset.mem_filter.mpr ⟨hy, ?_⟩, he⟩
    rw [← he, rawHead_eq] at hs
    exact hs

theorem childFamily_card_le {m : ℕ}
    (F : (Fin m → M) → Finset (VFType (M := M)))
    (N : ℕ) (hbound : ∀ t, (F t).card ≤ N) (u : Fin (m + 1) → M) :
    (childFamily F u).card ≤ N :=
  (Finset.card_filter_le _ _).trans (hbound (Fin.init u))

theorem rawCode_definable (h00 : M ⊨ Axioms.ACVF00) (S : Set M) (d : ℕ)
    {m : ℕ} (F : (Fin m → M) → Finset (VFType (M := M)))
    (hF : RelationDefinable S (finiteFibreRelation F))
    (N : ℕ) (hbound : ∀ t, (F t).card ≤ N) (i : Fin d) :
    S.DefinableFun LRV (fun w : Fin m ⊕ Fin 1 → M =>
      rawCode d F (w ∘ Sum.inl) (w (.inr 0)) i) := by
  induction d generalizing m F with
  | zero => exact i.elim0
  | succ d ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact rawHead_definable h00 S F hF N hbound
    · have hF' := childFamily_definable h00 S F hF N hbound
      have hb' := childFamily_card_le F N hbound
      have hc := ih (childFamily F) hF' hb' j
      let H (w : Fin m ⊕ Fin 1 → M) :=
        rawHead F (w ∘ Sum.inl) (w (.inr 0))
      let G (w : Fin m ⊕ Fin 1 → M) : Fin (m + 1) ⊕ Fin 1 → M :=
        Sum.elim (Fin.snoc (w ∘ Sum.inl) (H w)) (fun _ => w (.inr 0))
      have hG : S.DefinableMap LRV G := by
        intro u
        cases u with
        | inl k =>
          refine Fin.lastCases ?_ (fun l => ?_) k
          · simpa only [G, Sum.elim_inl, Fin.snoc_last] using
              (rawHead_definable h00 S F hF N hbound)
          · simpa only [G, Sum.elim_inl, Fin.snoc_castSucc, Function.comp_apply] using
              (Set.DefinableFun.proj (L := LRV) (A := S) (i := Sum.inl l))
        | inr k => exact Set.DefinableFun.proj LRV
      exact hc.comp hG

theorem rawCode_eq_code (d : ℕ) {m : ℕ}
    (F : (Fin m → M) → Finset (VFType (M := M))) (t : Fin m → M)
    (x : VFType (M := M)) : rawCode d F t x.val = code d (F t) x := by
  induction d generalizing m F t with
  | zero => rfl
  | succ d ih =>
    rw [rawCode, code, ih]
    simp only [rawHead_eq]
    congr 1
    congr 1
    simp only [childFamily, fibre, Fin.init_snoc, Fin.snoc_last]

theorem rawCode_injective (h00 : M ⊨ Axioms.ACVF00) {m : ℕ}
    (F : (Fin m → M) → Finset (VFType (M := M))) (t : Fin m → M) :
    Set.InjOn (fun x : VFType (M := M) => rawCode (F t).card F t x.val)
      ((F t) : Set (VFType (M := M))) := by
  simpa only [rawCode_eq_code] using code_injective h00 (F t)

end SpecialTransformations.Section3.Barycentre
