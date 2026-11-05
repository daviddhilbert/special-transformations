# `L_RV`, `ACVF`, `ACVF_S(0,0)`: transcription of Yin, APAL 2010

**Sources of every quotation.** (i) arXiv:1006.2467v1 ("ST"), `\section{Preliminaries}` (source
lines 443–660); (ii) its companion arXiv:1006.1393v1 ("QE"), which ST cites for both theorems and
which states the same Definition of `L_RV` — kept unmodified as `src/qe.tex`. Line numbers are
line numbers of the arXiv `.tex` files.
The arXiv e-print is a single file `ST_20_FV.tex` (44 039 bytes, 2367 lines, last modified 2010-06-10),
kept unmodified as `src/paper.tex` in this directory. Line numbers below are line numbers of that
file; quotes are verbatim LaTeX, including the paper's own typos.

**Theorem numbering.** The paper gives its environments one shared counter
(`\newtheorem{thm}{Theorem}[section]`, `\newtheorem{defn}[thm]{Definition}`, `\newtheorem{conv}[thm]{Convention}`,
`\newtheorem{nota}[thm]{Notation}`). Counting the section-2 environments in source order:

| # | source line | environment |
|---|---|---|
| 2.1 | 447 | Definition (the language `L_RV`) |
| 2.2 | 467 | Definition (the theory `ACVF`), `\label{defn:acvf}` |
| 2.3 | 508 | Theorem (quantifier elimination) |
| 2.4 | 514 | Definition (`K`-term, `RV`-literal), `\label{def:normal:form}` |
| 2.5 | 533 | Convention (definable = 0-definable in `ACVF_S(0,0)`) |
| 2.6 | 540 | Definition (balls, polydiscs) |
| 2.7 | 561 | Definition (`C`-minimal) |
| 2.8 | 565 | Theorem (`ACVF` is `C`-minimal), `\label{c:min:acvf}` |

This matches the milestone brief ("Theorem 2.3", "Theorem 2.8") and the repo's own
`SpecialTransformations/{Language,Definable}.lean`. The numbering is *derived* here, not printed
in the arXiv source; a referee should check it against the published pagination.

---

## 1. The sorts

> line 368: `The language $\lan{RV}$ has two sorts: the $\VF$-sort and the $\RV$-sort.`

> line 506: `Semantically we shall treat $\Gamma$ as an imaginary sort and write $\RV_{\Gamma}$ for $\RV \cup \Gamma$. However, syntactically any reference to $\Gamma$ may be eliminated in the usual way and we shall still work with $\lan{RV}$-formulas.`

> line 661: `In this section we shall list a number of structural properties concerning the relation among the three sorts $\VF$, $\RV$, and $\Gamma$. Some simple ones are just consequences of variations of compactness, for example:`

So: **syntactically two sorts (`VF`, `RV`); semantically three (`VF`, `RV`, `Γ`), with `Γ` imaginary.**
There is no `Γ` sort in `L_RV`. This is a correction to the milestone brief, which lists
"plus a sort Γ for the value group used by the substructure S"; see §7, item D1.

## 2. Definition 2.1: the signature (source lines 447–463)

> `The language $\lan{RV}$ has the following sorts and symbols:`
> `1. a $\VF$-sort, which uses the language of rings $\lan{R} = \set{0, 1, +, -, \times}$;`
> `2. an $\RV$-sort, which uses`
> `   (a) the group language $\set{1, \times}$,`
> `   (b) two constant symbols $0$ and $\infty$,`
> `   (c) a unary predicate $\K^{\times}$,`
> `   (d) a binary function $+ : \K^2 \fun \K$ and a unary function $-: \K \fun \K$, where $\K = \K^{\times} \cup \set{0}$,`
> `   (e) a binary relation $\leq$;`
> `3. a function symbol $\rv$ from the $\VF$-sort into the $\RV$-sort.`

Transcribed as a table (`Signature.lean` records the same data and `#eval`s it):

| symbol | sort profile | kind |
|---|---|---|
| `0`, `1` | `VF` | constants |
| `+`, `×` | `VF² → VF` | binary functions |
| `-` | `VF → VF` | unary function |
| `1` | `RV` | constant |
| `×` | `RV² → RV` | binary function (total) |
| `0`, `∞` | `RV` | constants |
| `K^×` | `RV → Prop` | unary **relation** (a predicate, not a sort) |
| `+` | `RV² → RV` **partial** (`K² → K`) | binary function |
| `-` | `RV → RV` **partial** (`K → K`) | unary function |
| `≤` | `RV² → Prop` | binary relation |
| `rv` | `VF → RV` | unary function |

Notation (line 465, quoted verbatim, *sic*):

> `The two sorts without the zero elements are respectively denoted by $\VF^{\times}$ and $\RV$; $\RV \mi \set{\infty}$ is denoted by $\RV^{\times}$; and $\RV \cup \set{0}$ is denoted by $\RV_0$.`

The first clause is a typo (as printed it identifies `RV` both with the whole sort and with the
sort-without-zero); the readings forced by 2.2(6) are `VF^× = VF ∖ {0}`, `RV^× = RV ∖ {∞}`,
`RV_0 = RV ∪ {0}`. Note `0 ∉ RV` and `∞ ∈ RV`.

## 3. Definition 2.2: the theory `ACVF` (source lines 467–505)

> `The theory $\ACVF$ of algebraically closed valued fields in $\lan{RV}$ states the following:`
> `(1) $(\VF, 0, 1, +, -, \times)$ is an algebraically close field;`   [sic: "close"]
> `(2) $(\RV^{\times}, 1, \times)$ is a divisible abelian group, where multiplication $\times$ is augmented by $t \times 0 = 0$ for all $t \in \K$ and $t \times \infty = \infty$ for all $t \in \RV_0$;`
> `(3) $(\K, 0, 1, +, -, \times)$ is an algebraically closed field;`
> `(4) the relation $\leq$ is a preordering on $\RV$ with $\infty$ the top element and $\K^{\times}$ the equivalence class of 1;`
> `(5) the quotient $\RV / \K^{\times}$, denoted as $\Gamma \cup \set{\infty}$, is a divisible ordered abelian group with a top element, where the ordering and the group operation are induced by $\leq$ and $\times$, respectively, and the quotient map $\RV \fun \Gamma \cup \set{\infty}$ is denoted as $\vrv$;`
> `(6) the function $\rv : \VF^{\times} \fun \RV^{\times}$ is a surjective group homomorphism augmented by $\rv(0) = \infty$ such that the composite function $\vv = \vrv \circ \rv : \VF \fun \Gamma \cup \set{\infty}$ is a valuation with the valuation ring $\OO = \rv^{-1}(\RV^{\geq 1})$ and its maximal ideal $\MM = \rv^{-1}(\RV^{> 1})$, where $\RV^{\geq 1} = \set{x \in \RV: 1 \leq x}$ and $\RV^{> 1} = \set{x \in \RV: 1 < x}$.`

Shape of each item, as written (this drives what an encoding must do; see §7):

| item | first-order as written? | why |
|---|---|---|
| (1) | scheme over $n$ | "algebraically closed" = one sentence per degree $n$; plus the char-0 sentences |
| (2) | scheme over $n$ | "divisible" = $\forall x\, \exists y\, y^n = x$, one per $n \ge 1$ |
| (3) | scheme over $n$ | same as (1), on the definable subset `K ⊆ RV` |
| (4) | single sentence | finite conjunction of preorder axioms + `∞` top + `K^× = class of 1` |
| (5) | scheme **and** mentions Γ | "divisible ordered abelian group" is again one sentence per $n$; and the item quantifies over the quotient `RV/K^×`, which is not a sort of `L_RV` |
| (6) | finite, but mentions Γ | `vv = vrv ∘ rv` is a function into `Γ ∪ {∞}`; a transcription into `L_RV`-terms must be supplied (the paper does not supply it) |

## 4. `K`, `K^×`: the reading forced by the text

The paper overloads `K`. Introduction, lines 370–372:

> `Let $(K, \vv)$ be a valued field and $\OO$, $\MM$, $\K$ the corresponding valuation ring, its maximal ideal, and the residue field.`

So `K` is the **residue field**. Consistently, in 2.1–2.2 `K^×` is a *subset of the `RV`-sort*,
`K = K^× ∪ {0}` and (3) says `K` is an algebraically closed field: `K` is the residue field
internalised in `RV`. Formally this is forced by (4)+(5)+(6):

* (4) says `K^×` is the equivalence class of `1` for `≤`, and (5) says `RV/K^× = Γ ∪ {∞}`;
  hence `K^× = {x ∈ RV : vrv(x) = 1} = ker(vrv)`.
* (6) says `O = rv^{-1}(RV^{≥1})` and `M = rv^{-1}(RV^{>1})`; hence
  `rv^{-1}(K^×) = rv^{-1}(RV^{≥1}) ∖ rv^{-1}(RV^{>1}) = O ∖ M = O^×`, so `K^× = rv(O^×) ≅ k^×`.

**The trap.** The other reading — `K^× := rv(VF^×)`, "the field elements sitting inside `RV`" —
gives `K^× = RV^×` because `rv` is surjective (2.2(6)). Then `RV/K^×` is trivial, contradicting
(5) and the standing hypothesis that `Γ(S)` is nontrivial (line 531). An encoding that identifies
`K^×` with `rv(VF^×)` is therefore inconsistent with `ACVF_S(0,0)`.

## 5. `ACVF(0,0)` and `ACVF_S(0,0)` (source line 531)

> `Let $\ACVF(0, 0)$ denote $\ACVF$ with pure characteristic $0$. From now on we shall work in a sufficiently saturated model $\gC$ of $\ACVF(0, 0)$. Let $S \sub \gC$ be a small substructure such that $\Gamma(S)$ is nontrivial. Let $\ACVF_S(0, 0)$ be the theory that extends $\ACVF(0, 0)$ with the atomic diagram of $S$. For notational simplicity we shall still refer to the language of $\ACVF_S(0, 0)$ as $\lan{RV}$. Although we do not include the multiplicative inverse function in the $\VF$-sort and the $\RV$-sort, we always assume that, without loss of generality, $\VF(S)$ is a field and $\RV^{\times}(S)$ is a group.`

Related, lines 337–338 and 432–433:

> `valued fields of pure characteristic $0$ expanded by a $(\VF, \Gamma)$-generated substructure $S$ in the language $\lan{RV}$`

> `... expanded by a substructure $S$, where $S$ is generated by elements in the field sort and the (imaginary) value group sort.`

and lines 1573–1574 (what `(VF,Γ)`-generated is used for):

> `Since $S$ is $(\VF, \Gamma)$-generated, we may assume that $\phi(\lbar X)$ does not contain parameters from $\RV(S) \mi \rv(\VF(S))$.`

Points an encoding must fix, none of them stated by the paper:
`ACVF(0,0)` is glossed only as "pure characteristic 0"; the pair notation `(p,q)` is used but
defined in the companion paper, not here. (For a valued field, `char K = 0` already forces
`char k = 0`, so the pair `(0,0)` carries no extra information beyond `char K = 0`.)
`ACVF_S(0,0)` is `ACVF(0,0)` **plus the atomic diagram of a substructure `S`**: an expansion by
constants, not a new sort. "Γ(S) nontrivial" is a hypothesis on `S`; `S` is required to be
small (a set, in the ambient universe).

## 6. The two targets

**Theorem 2.3** (line 508, attributed to `[Yin:QE:ACVF:min, Theorem 3.10]`):

> `The theory $\ACVF$ admits quantifier elimination.`

No qualification of the formula class appears; the context of §2 is `L_RV`-formulas (line 506:
"we shall still work with `L_RV`-formulas"). QE is therefore claimed for `L_RV`, hence for
**both** sorts, and it is imported, not proved, in this paper.

**Definition 2.6** (balls, lines 540–559), needed for 2.8:

> `A subset $\gb$ of $\VF$ is an open ball if there is a $\gamma \in \Gamma$ and a $b \in \gb$ such that $a \in \gb$ if and only if $\vv(a - b) > \gamma$. It is a closed ball if $a \in \gb$ if and only if $\vv(a - b) \geq \gamma$. It is an $\rv$-ball if $\gb = \rv^{-1}(t)$ for some $t \in \RV$.`

(plus: radius `rad(𝔟)`, valuative center `vcr(𝔟)`, polydiscs in `VF^n × RV^m`, degeneracy).

**Definition 2.7** (lines 561–563):

> `Let $\LL$ be a language expanding $\lan{RV}$. Let $M$ be a structure of $\LL$ that satisfies the axioms for valued fields. We say that $M$ is $C$-minimal if every parametrically definable subset of $\VF(M)$ is a boolean combination of balls. An $\LL$-theory $T$ is $C$-minimal if every model of $T$ is $C$-minimal.`

**Definition 2.7 vs. the standard `C`-minimality definition.** ST defines `C`-minimality by
*balls*, not by a ternary `C`-relation. The definition in the literature (Haskell–Macpherson,
following Macpherson–Steinhorn) is: a structure `(M, C, …)` is `C`-minimal if `C` is a
`C`-relation — a ternary relation satisfying four axioms (exchange, irreflexivity, a
tree/ultrametric axiom, and density) — and every unary definable subset of `M` is a Boolean
combination of instances `C(x; b, c)`. Two points for the encoding:

* ST's ball form and the `C`-relation form are equivalent for models of `ACVF` (a valuation
  induces `C(x; y, z) ⟺ vv(x − y) < vv(y − z)`, and the instances `C(x; b, c)` are balls), but ST
  neither states the `C`-relation axioms nor identifies the two forms. Any formalisation that
  defines `CMinimal` from a `C`-relation must either prove the equivalence or state it as a
  hypothesis.
* The density axiom is part of Haskell–Macpherson's definition and is *dropped* in Delon's
  variant; ST's Def 2.7 is silent on it. For `ACVF` it holds (the value group is divisible), but
  a definition of `C`-minimality from the `C`-side must say which convention it uses.

*Caveat:* this paragraph rests on secondary sources (the Wikipedia article "C-minimal theory" and
W. Johnson's survey quoting Haskell–Macpherson), not on the primary Haskell–Macpherson paper,
which I did not obtain. The line-referenced claims elsewhere in this file do not depend on it.

**Theorem 2.8** (line 565, attributed to `[Yin:QE:ACVF:min, Theorem 4.2]`):

> `The theory $\ACVF$ is $C$-minimal.`

Read through 2.7, 2.8 is the statement: *for every model `M ⊨ ACVF` and every subset `A ⊆ VF(M)`
definable with parameters in `M`, `A` is a finite boolean combination of balls in the sense of 2.6.*
Note (i) it is the one-variable form (subsets of `VF(M)`, not `VF(M)^n`), (ii) the balls of 2.6 are
defined with `γ ∈ Γ`, i.e. through the imaginary sort, and (iii) as with 2.3 the theorem is imported.

## 7. What the paper leaves to the encoding (inference list)

Each item is a decision an encoding must make; the paper's text does not make it.

* **D1 (sorts).** `L_RV` is two-sorted; `Γ` is imaginary. Consequences: (i) a primitive `Γ` sort is
  a *definitional expansion*, and must be shown to be one (every `Γ`-term eliminated); (ii) Theorem
  2.3 as stated says nothing about `Γ`-quantifiers, so "QE in a 3-sorted language" is a different
  statement — the paper's `Γ`-elimination is a separate result (line 1465, for Henselian fields);
  (iii) `Γ` does occur in the *statement* of 2.8 via 2.6.
* **D2 (partial functions).** `+` and `-` on the `RV`-sort are `K² → K` and `K → K` with
  `K = K^× ∪ {0}` a *definable subset* of `RV`; they are not total on `RV`. Three encodings:
  partial function symbols; totalisation by a default value (conservative on `K`, but needs proof);
  or a subsort `K`. Any framework with only total function symbols must totalise.
* **D3 (subsort).** `K` is a definable subset of `RV` (not a sort). If an encoding introduces `K`
  as a third sort with an injection, conservativity of that definitional expansion must be shown.
* **D4 (`≤` is a preorder; where is the constant `0`?** — settled by the author).** `K^×` is the
  class of 1. The paper prints two constants, `0` and `∞`, but they are **one element**: writing
  `rv(0) = 0` makes `0` the absorbing element of `RV`, and `∞` is another name for it. Axiom (2)
  forces this reading — `(RV^×, 1, ×)` is a divisible abelian *group* and `RV^× = RV ∖ {∞}`, a
  set that is a group only if the element removed is the absorbing one. So `RV = {rv 0} ∪ RV^×`,
  the absorbing element is the top of the preorder, and it is also the residue field's zero. The
  encoding has ONE constant (`rvZero`), `tRVInfty` as a definition for it, and `rvSurj` as the
  paper's surjectivity `t ≠ rv(0) → ∃x, rv x = t`; see the revision section of `DECISION.md`.
* **D5 (direction of `≤`, and its compatibility with `×`).** (5) says the order on `Γ` is
  "induced by" `≤` and the group operation "induced by" `×`, but states no compatibility axioms
  and no sign. Forced reading: (6) gives `rv(x) ≥ 1 ⟺ vv(x) ≥ 0` for `x ∈ VF^×`; reading the
  "induced" of (5) as compatibility of `≤` with `×` (so `z ≤ 1 ⟺ z·w ≤ w` for `w > 0`) gives, for
  `y ≠ 0`, `rv(x) ≤ rv(y) ⟺ rv(x/y) ≤ 1 ⟺ vv(x) ≤ vv(y)`. So `≤` on `RV` **agrees** with `≤` on
  `Γ`: `x ≤ y ⟺ vv(x) ≤ vv(y)`. This is consistent with (4), which makes `∞ = rv(0)` the top
  (`vv(0) = vrv(∞)` must be the top, as `vv` is a valuation); the reversed reading would put `∞`
  at the bottom. Then `x ∣ y` on `O` is `rv(x) ≤ rv(y)`. An encoding must add the compatibility
  axioms of (5) and fix the sign.
* **D6 (what `rv` is a map of).** 2.1 declares `rv : VF → RV`; (6) uses `rv : VF^× → RV^×` with
  `rv(0) = ∞`. A total symbol is correct, but note `∞` is in the range of `rv` and `0` is not.
* **D7 (the quotient).** (5) quantifies over `RV/K^×`. With `K^×` definable, `Γ` is a definable
  quotient; either the encoding has quotients, or (5) is rephrased as a scheme about the preorder.
* **D8 (`S` and its diagram).** `S` is a two-sorted substructure of a model, closed under the
  symbols; `ACVF_S(0,0)` adds its atomic diagram, i.e. constants for the elements of `S`. The
  hypothesis `Γ(S)` nontrivial means: `S`'s `RV`-part contains two elements not equivalent under
  `K^×`. The paper's WLOG assumptions `VF(S)` a field and `RV^×(S)` a group need to be built in
  or proved; the paper asserts them without proof.
* **D9 (`ACVF(0,0)`).** Only "pure characteristic 0" is stated; no `(p,q)` definition here.
* **D10 (formula class in 2.3).** QE for which formulas? The paper's usage (Definition 2.4 and
  following) is `L_RV`-formulas with parameters from the ambient model; Theorem 2.3 itself is
  stated for `ACVF`, i.e. for sentences/`∅`-definable sets modulo the theory, and parameters enter
  through `ACVF_S(0,0)`. An encoding must pick one and say so.


## 7bis. Cross-check against the companion paper, arXiv:1006.1393 (`src/qe.tex`)

ST cites `[Yin:QE:ACVF:min]` for both targets. That paper is arXiv:1006.1393v1, *Quantifier
elimination and minimality conditions in algebraically closed valued fields*; it is where the
language is actually introduced, and it resolves three things ST leaves implicit.

**(a) The signature is verbatim identical.** `qe.tex` lines 402–418 repeat Def 2.1 word for word
(same five `\VF` symbols, same `RV` symbols `1, ×, 0, ∞, K^×, + : K^2 → K, - : K → K, ≤`, same
`rv : VF → RV`). So the transcription in §2 is confirmed by two independent sources.

**(b) ST/Def 2.1's `+`, `-` in the `RV`-sort are partial, and the author says they are relations.**
`qe.tex` lines 420–421, immediately after the definition:

> `Technically speaking, the constant $0$ and the functions $+$, $-$ in the $\RV$-sort should all be relations.`

This is decisive for the encoding (spec.md, D2): the `RV`-sort's `0`, `+`, `-` are not total
functions; the faithful reading is
`+_{RV} ⊆ RV^3` (the graph of `+ : K^2 → K`), `-_{RV} ⊆ RV^2`, and `0` as a distinguished element
of `K` (a 0-ary relation / predicate). A framework with only total function symbols must either
totalise them (and prove conservativity on `K`) or declare them as relations. Mathlib's
`FirstOrder.Language` supports relations of arbitrary arity, so the relational reading is available
in candidate (a) without any new machinery; what is *not* available there is a partial function.

**(c) `ACVF(p,q)` and `K` = residue field.** `qe.tex` line 368:

> `The corresponding theory is called $\ACVF(p,q)$, where $(p,q)$ indicates the characteristics of the field and the residue field.`

So `ACVF(0,0)` = both characteristics `0`; the pair notation is *defined in QE, not in ST* (ST
only says "pure characteristic 0"). And `qe.tex` lines 439–441:

> `We see that $\K$ and $\Gamma$ are naturally wrapped together in this one sort $\RV(K)$. Note that the existence of an angular component $\ac : K^{\times} \fun \K^{\times}$ is equivalent to the existence of a group homomorphism from $\RV(K)$ onto $\K^{\times}$ in the diagram.`

An angular component is a map *to the residue field's units*; this confirms §4: `K^×` is the
residue field's units (`= ker vrv`), not `rv(VF^×)`. A homomorphism `RV(K) → K^×` splitting
`1 → k^× → RV(K) → Γ → 1` is exactly what `ac` gives — impossible if `K^× = RV^×`.

**(d) The two citations check out.** Counting the shared-counter environments of `qe.tex`:
section 3 (line 547 onwards) has `rem`=3.1, `lem`=3.2–3.8, `prop`=3.9, `thm \label{qe:acvf}`=**3.10**
("The theory ACVF admits quantifier elimination"), `lem`=3.11–3.12, `thm`=3.13–3.14; section 4
(line 879 onwards) has `defn`=**4.1** (VF-literal / K-term / RV-literal), `thm \label{c:min:acvf}`=**4.2**
("The theory ACVF is C-minimal"). So ST's citations `[Theorem 3.10]` and `[Theorem 4.2]` are
correct.

**(e) C-minimality is used in the 1-variable form.** The proof of `qe:acvf`'s companion 4.2
(`qe.tex` line 911) begins: `Let $X$ be a $\VF$-sort variable and $\phi(X)$ a quantifier-free
$\lan{RV}$-formula with parameters, where $X$ is the only variable in $\phi(X)$.` This confirms
that Def 2.7 / ST 2.7 is meant in one variable, and that QE is applied to formulas *with
parameters*.

**(f) Mathlib API behind the claims above** (checked in `MathlibChecks.lean`; `lean` output in
`verify.txt`):

* `FirstOrder.Language.Functions : Language → ℕ → Type` and `.Relations : Language → ℕ → Type`:
  relations of any arity are first-class, so the paper's `+`, `-` (and the constant `0`) on the
  `RV`-sort can be declared as relations, per QE 420–421.
* `FirstOrder.Language.Term` has exactly two constructors, `var` and `func`
  (`term_iff_var_or_func`): every function symbol is total, so a partial `+ : K² → K` is not
  directly hostable as a function symbol.
* `Language.withConstants L α = L.sum (Language.constantsOn α)` by `rfl` (`withConstants_eq`):
  the expansion by constants that `ACVF_S(0,0)` needs — the atomic diagram of `S` — is
  `L.withConstants S`.
* `Set.Definable (s : Set M) (L : Language) [L.Structure M] {α : Type} (A : Set (α → M)) : Prop`
  and `Language.DefinableSet`: definability with parameters from `s`, i.e. exactly the distinction
  D11 needs (`s` = the constants of `S`, or `s` = all of `M` for "parametrically definable").

## 7ter. Two further decisions the text forces (added after the cross-check)

* **D11 ("definable" = `S`-definable, vs. "parametrically definable").** ST Convention 2.5
  (source line 533): `By a definable subset of $\gC$ we mean a $\0$-definable subset in the theory $\ACVF_S(0, 0)$.`
  A `0`-definable subset of `ACVF_S(0,0)` is definable with parameters from `S` (they are constants
  of the theory), not with arbitrary parameters from `C`. But Def 2.7 says "every *parametrically*
  definable subset of `VF(M)`". So the paper has two notions in play: `S`-definable (its default
  "definable") and parametrically definable. An encoding must state which one Thm 2.8 uses.
  The literal statement of 2.8 is the parametric one (via 2.7); the paper's later uses are for
  `S`-definable sets, which is weaker. Stating the parametric version is correct and stronger;
  stating only the `S`-definable version would be weaker than 2.8 as printed.
* **D12 (`Γ(S)` nontrivial is a hypothesis, not a theorem).** `ACVF_S(0,0)` is only considered for
  substructures `S` with `Γ(S)` nontrivial (line 531). An encoding of `ACVF_S(0,0)` must either
  carry this as a hypothesis on `S` or note that the theorems are stated for all `S` while the
  paper's uses need it. It also constrains the substructure: `S` must contain two `RV`-elements
  with different images in `Γ`.


## 8. Statement templates (what "means what the paper means" amounts to)

Not an encoding, but the quantifier shape each target must have, so that a referee can check a
candidate statement against it. `M ⊨ φ(ā)` means satisfaction in the structure `M` with the
assignment `ā`; `Definable` is definability with parameters.

**Theorem 2.3 (QE).** The paper's `ACVF` is a set of `L_RV`-sentences. The statement is:

```
for every n : ℕ and every L_RV-formula φ with n free variables,
there is an L_RV-formula ψ with the same n free variables such that
  (i)  ψ is quantifier-free, and
  (ii) ACVF ⊢ ∀ x̄, φ(x̄) ↔ ψ(x̄).
```

Three things must not be dropped: `ACVF ⊢` (not `⊢` in the empty theory, and not "true in the
standard model"); *both sorts* (`φ` may have free variables of either sort); and the fact that
`ACVF(0,0)` and `ACVF_S(0,0)` inherit QE, since they extend `ACVF` by sentences and by constants
(a definitional expansion by constants preserves QE). Parameters enter only through
`ACVF_S(0,0)`, whose constants name the elements of `S`.

**Theorem 2.8 (C-minimality).** With `IsBall` the three families of Definition 2.6 —

```
IsBall(b)  :=  (∃ (γ ∈ Γ)(a ∈ b), b = {x ∈ VF : vv(x - a) > γ})       -- open
            ∨  (∃ (γ ∈ Γ)(a ∈ b), b = {x ∈ VF : vv(x - a) ≥ γ})       -- closed
            ∨  (∃ t ∈ RV,         b = {x ∈ VF : rv(x) = t})           -- rv-ball
```

— the statement is:

```
for every model M of ACVF, for every subset A ⊆ VF(M):
  if A is definable in M with parameters, then
  A is a finite boolean combination of sets b ⊆ VF(M) with IsBall(b).
```

Vacuity traps to avoid: (i) quantifying over a *fixed* structure instead of over all models of
`ACVF` (the paper's theorem is about the theory); (ii) leaving `IsBall` abstract or empty —
with `IsBall := ∅` the property holds only for `A ∈ {∅, VF}`, but with `IsBall := {VF}` it holds
for *every* `A`, so an unconstrained `IsBall` makes the statement either false or trivial;
(iii) stating it only for `S`-definable `A` when the paper's Definition 2.7 says *parametrically*
definable (see D11; the parametric version is the literal one and implies the `S`-definable one);
(iv) forgetting that `Γ` occurs in `IsBall` (D1) — it must be eliminated through `rv` and `≤`
to be an `L_RV`-statement, which is what line 506 licenses.

**Theorem 2.3 vs 2.8 are independent imports.** Neither is proved in ST; both are attributed to
QE (3.10, 4.2). A formalization must either take them as hypotheses/theorems-to-be-proved or cite
a later milestone; it must not present them as proved by the definitions.

## 9. What I did **not** verify

* The *published* APAL versions of either paper and their pagination. I derived 2.1–2.8 and the
  QE 3.10/4.2 citations from the shared counters in the arXiv sources, by counting environments;
  the journal numbering may differ. I did not open either journal PDF (paywalled).
* That QE for `ACVF` is *true*. I only checked that the paper states it (and that the companion
  states it as its 3.10); no proof of it is reproduced or formalised here.
* That the companion's `lem`/`thm` counting is right for its own published version (same caveat).
* That `ACVF` as axiomatised by 2.2(1)–(6) is consistent, or that (1)–(6) force `≤` to be
  *interpretable* as `vv`'s order rather than merely compatible with it. §7 D4–D5 lists what I
  believe is missing, but I did not prove that the missing axioms are consequences of the stated
  ones.
* Any Lean formalisation of the above beyond the data table in `Signature.lean` and the
  API facts in `MathlibChecks.lean`.
* Whether `ACVF_S(0,0)` is complete (the paper works in a "sufficiently saturated model", which
  presupposes saturation, not completeness).
* The equivalence between ST's ball form of `C`-minimality (Def 2.7) and the standard
  `C`-relation form. I quoted the standard axioms from secondary sources only (see §6) and did not
  read Haskell–Macpherson or Delon.

## 10. Appendix: the downstream definitions, quoted (milestone 1+)

Added because they constrain any encoding even before the theorems are stated. Line numbers in
`src/paper.tex`.

Fibres and projections (Notation 2.10, lines 599–612):
> `We write $\pr_E(A)$ for the projection of $A$ to the coordinates in $E$. For any $\lbar a \in \pr_{\tilde{E}} (A)$, the fiber $\{\lbar b : (\lbar b, \lbar a) \in A \}$ is denoted by $\fib(A, \lbar a)$. ... If $E$ contains exactly the $\VF$-indices (respectively $\RV$-indices) then $\pr_E$ is written as $\pvf$ (respectively $\prv$).`

`dim_VF` (Definition 3.1, line 809), for a definable `A ⊆ VF^n × RV^m`:
> `The $\VF$-dimension of $A$, denoted by $\dim_{\VF}(A)$, is the smallest number $k$ such that there is a definable finite-to-one function $f: A \fun \VF^k \times \RV_{\Gamma}^l$.`

`dim_RV` (Definition 3.9, line 906), for a definable `B ⊆ RV^m`:
> `The $\RV$-dimension of $B$, denoted by $\dim_{\RV}(B)$, is the smallest number $k$ such that there is a definable finite-to-one function $f: B \fun \RV^k$ ($\RV^0$ is taken to be the singleton $\{\infty\}$).`

`dim^fib_RV` (Definition 3.12, line 939):
> `The $\RV$-fiber dimension of $A$, denoted by $\dim^{\fib}_{\RV}(A)$, is $\max \set{\dim_{\RV} (\fib(A, \lbar a)) : \lbar a \in \pvf(A)}.$`

Two consequences for the encoding choice, independent of which candidate is picked:
(i) the codomain of the dimension-minimising map is `VF^k × RV_Γ^l` with `RV_Γ = RV ∪ Γ`
(ST line 506), so `Γ` enters the *statement* of `dim_VF`, not only its proofs — a candidate that
cannot form `RV ∪ Γ` as a type cannot state Definition 3.1 at all;
(ii) `dim^fib_RV` is a maximum over the VF-projection of `A`, so the statement type needs the fibre
`fib(A, ā)` as a set of `RV`-tuples together with `pvf(A)`; both are Grundy notions on the
product `VF^n × RV^m`, i.e. a mixed-sort product type is needed before any dimension is defined.

These are recorded, not formalised: the interface belongs to the downstream direction.
