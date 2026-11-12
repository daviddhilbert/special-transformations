module

/-
**The §3 corollary `acl:VF:transfer:acl:RV` in the corrected form.**

`QE/Sec3Infra.lean` derives the paper's corollary from the `Prop` `SP.AclConstOfFibres`, which is
false as stated (`A = ∅`; see `AclFibres.lean`).  Here the same derivation is repeated from the
*corrected* `Prop` `SP.AclConstOfFibresNonempty` (with `A ≠ ∅`), which is the shape the paper's proof
uses (`⋂_{a∈A} U_a` and the application of the hypothesis at an `a ∈ A`).

Nothing here proves `SP.AclConstOfFibresNonempty`; it is the remaining compactness/uniformity step.
For the `RV`-sorted use of the corollary, `A.Nonempty` is automatic (an `rv`-fibre is `{0}` at
`t = rv 0` and otherwise contains `VF`-elements of value `t`), which is why the paper does not state
it.
-/
public import Sec3Infra
public import AclFibres

@[expose] public section
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open scoped FirstOrder

namespace SpecialTransformations.Milestone0
open LRV

namespace SP

variable {M : Type*} [LRV.Structure M]

/-- §3's first lemma at the `VF` sort (the frozen `swl_acl_const_of_fibres`'s statement) from the
*corrected* compactness hypothesis. -/
theorem acl_const_of_fibres_nonempty (hC : AclConstOfFibresNonempty M) (S : SP M) (A : Set M)
    (x : M) (hA : DefinableVF S A) (hne : A.Nonempty)
    (h : ∀ a : M, (ha : iVF a) → a ∈ A → acl (S.extendVFParam a ha) x) :
    acl S x :=
  hC S (fun _ => SortTag.vf) A x ((definableVF_iff_definableAt S A).mp hA) hne h

/-- **`acl:VF:transfer:acl:RV`** (paper §3), from the corrected compactness hypothesis. -/
theorem acl_transfer_acl_RV_nonempty (hC : AclConstOfFibresNonempty M) (S : SP M) (A : Set M)
    (hA : DefinableRV S A) (hne : A.Nonempty) (x : M)
    (h : ∀ a : M, (ha : iRV a) → a ∈ A → acl (S.extendRVParam a ha) x) :
    acl S x :=
  hC S (fun _ => SortTag.rv) A x ((definableRV_iff_definableAt S A).mp hA) hne h

end SP

end SpecialTransformations.Milestone0
