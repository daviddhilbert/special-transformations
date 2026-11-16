/-
Extracted from https://github.com/daviddhilbert/diamond-integral/blob/ba6249a11b39e8e71fd0130ab0087e7185b95433/section%205/GammaQERVVariableMaps.lean
Original declaration namespaces and notices are retained.
-/
import Section3.GammaQERVBasics
import Section4.GammaPredicates

/-! Reindexing free RV slots in the checked original-language parser.
When all free variables are RV, its VF polynomial arguments are fixed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.GammaQE
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open CanonicalRV GuardedRVNormalForm
variable {I R V W : Type}

def mapRVVariables (f : V → W) : RVExpr I R V → RVExpr I R W
  | .zero => .zero
  | .one => .one
  | .vf P => .vf P
  | .parameter i => .parameter i
  | .ofVariable i => .ofVariable (f i)
  | .mul P Q => .mul (mapRVVariables f P) (mapRVVariables f Q)
  | .inv P => .inv (mapRVVariables f P)
  | .addK P Q => .addK (mapRVVariables f P) (mapRVVariables f Q)
  | .negK P => .negK (mapRVVariables f P)

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem mapRVVariables_eval (f : V → W) (P : RVExpr I R V)
    (a : I → VFType (M := M)) (r : R → RVSort M) (x : W → RVSort M) :
    (mapRVVariables f P).eval a r x = P.eval a r (x ∘ f) := by
  induction P <;> simp_all only [mapRVVariables,RVExpr.eval,Function.comp_apply]

def mapRVAtomVariables (f : V → W) : RVAtom I R V → RVAtom I R W
  | .equality P Q => .equality (mapRVVariables f P) (mapRVVariables f Q)
  | .order P Q => .order (mapRVVariables f P) (mapRVVariables f Q)

theorem mapRVAtomVariables_eval (f : V → W) (P : RVAtom I R V)
    (a : I → VFType (M := M)) (r : R → RVSort M) (x : W → RVSort M) :
    (mapRVAtomVariables f P).eval a r x ↔ P.eval a r (x ∘ f) := by
  cases P <;> simp only [mapRVAtomVariables,RVAtom.eval,mapRVVariables_eval]

def mapRVBooleanVariables (f : V → W) :
    PolarityDNF.Expr (RVAtom I R V) → PolarityDNF.Expr (RVAtom I R W)
  | .falsum => .falsum
  | .atom A => .atom (mapRVAtomVariables f A)
  | .imp P Q => .imp (mapRVBooleanVariables f P) (mapRVBooleanVariables f Q)

theorem mapRVBooleanVariables_eval (f : V → W) (P : PolarityDNF.Expr (RVAtom I R V))
    (a : I → VFType (M := M)) (r : R → RVSort M) (x : W → RVSort M) :
    (mapRVBooleanVariables f P).eval (RVAtom.eval a r x) ↔ P.eval (RVAtom.eval a r (x ∘ f)) := by
  induction P with
  | falsum => rfl
  | atom A => exact mapRVAtomVariables_eval f A a r x
  | imp P Q hP hQ => exact imp_congr hP hQ

theorem sourceVFValues_allRV {A : Type} {n : ℕ} (sa : A → SortTag)
    (v : A → M) (hv : ∀ i,sortEval (sa i) (v i))
    (x y : Fin n → M) (hx : ∀ i,sortEval SortTag.rv (x i)) (hy : ∀ i,sortEval SortTag.rv (y i)) :
    SourceAssignment.vfValues sa (fun _ : Fin n => .rv) v x hv hx =
      SourceAssignment.vfValues sa (fun _ : Fin n => .rv) v y hv hy := by
  funext i
  apply Subtype.ext
  rcases i with ⟨i,hi⟩
  cases i with
  | inl j => rfl
  | inr j => cases hi

theorem rvGamma_codeValue (t : RVSort M) (ht : t ≠ 0) :
    GammaParameters.codeValue t.val = rvGamma t ht := by
  let c : GammaParameters.Code (M := M) :=
    ⟨t,fun h => ht (Subtype.ext (h.trans RVOperations.zero_val.symm))⟩
  exact GammaParameters.codeValue_raw c

end DiamondIntegral.Section5.GammaQE
