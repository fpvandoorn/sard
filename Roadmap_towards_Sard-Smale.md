# Roadmap towards the Sard-Smale theorem in mathlib
by Michael Rothgang, as of September 20, 2023

## Part 1: Sard's theorem (for finite-dimensional manifolds)
In the form "The set of regular values is residual, hence dense".

## Part 2: prerequisites
### 2.1 Fredholm operators
- Definition of Fredholm operators. (Oliver Nash wrote one for the LftCM 23 project.)
- Splitting of Fredholm operators. (already there; use `ComplementedSpace.lean`)
- Linear operators between finite-dimensional spaces are Fredholm.
- Fredholm index of a linear map $L:ℝ^m\to ℝ^n$ is $m-n$. (Uses just the rank-nullity theorem.)
- Fredholm index is continuous, hence locally constant: might not be required for Sard-Smale.

For my setting, Banach spaces are sufficient. (Normed space with closedness of the image works for the definition.)
Probably, can generalise these to topological vector spaces --- requires e.g. generalizing the Hahn-Banach theorem to TVS.
Would not embark on this myself (but would be a good contribution to mathlib!).

### 2.2 Invertible linear operators are open (exists)
Linear isomorphisms are open.
Holds for bounded linear maps $E\to F$ between normed spaces, as long as `E` is complete. (`F` is not required to be.)
Is already in mathlib, at `docs#ContinuousLinearEquiv.isOpen` and `docs#ContinuousLinearEquiv.nbhds`.
For each map, get a neighbourhood of linear isomorphisms around it.

### 2.3 Definition: comeagre subsets (exists)
mathlib has comeagre sets (called [*residual* set](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/GDelta.html#residual)) and [Baire spaces](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/MetricSpace/Baire.html#BaireSpace).

**Recall.** Comeagre subsets of ℝ need not have Lebesgue measure zero; the converse is also false.
- recall that a set is comeagre iff its complement is meagre
- nowhere dense sets are meagre (Rudin '91)
- fat Cantor sets are closed nowhere dense, but can have measure approaching $1$
  taking the union of countably many of these, with measures approaching $1$, yields a meagre subsets of $[0,1]$ of measure 1
- conversely: if $S\subset [0,1]$ is meagre of measure $1$, its complement has measure $0$ and is comeagre (by definition). In particular, it's not meagre, as $[0,1]$ is a Baire space. (A Baire space is nonmeager (as a subset in itself); in a nonmeagre space, no set is both meagre and comeagre at the same time.)

## Part 3: proving Sard-Smale's theorem
**Sard-Smale theorem.** Let `M` and `N` be infinite-dimensional second countable $C^r$ Banach manifolds.
  Let $F\colon M\to N$ be a $C^r$ map such that each differential $dF_x\colon T_pM\to T_{f(p)}N$ is a Fredholm operator.   Suppose $r>\max{0,\text{ind}(dF_x)}$ for all $x\in M$. Then the set of regular values of $dF$ is a comeagre subset.

**Corollary.** The set of regular values is dense.
(just apply the Baire category theorem)

Deduce Sard as a special case: state as an `example`.
The proof uses Smale's version: the point is that its hypotheses reduce to the familiar ones in the finite-dimensional case.
(Details: finite-dimensional normed spaces are Banach. A linear map between finite-dimensional spaces is Fredholm with index $m-n$.)

**Proof sketch.**
For each point $x\in E$, choose a splitting of the differential $dF_x$.
Choose a neighbourhood $U$ of $x$ on which the first part is an isomorphism.
These neighbourhoods are an open cover $U_i$ of $M$, which admits a countable subcover.
Refine these further to ensure each $U_i$ lies in a chart domain; then compose with that chart to assume we're in a Banach space. (Detail: each chart is an isomorphism, hence preserves being a critical value.)
It suffices to show that singular values are meagre for each such chart.
Now: differential splits; a point is critical iff the first component is.

(This is slightly lying, need to consider the non-linear map instead of just the differential. But only slightly.)

