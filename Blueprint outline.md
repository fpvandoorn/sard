## Blueprint outline
**Goal.** Sard's theorem (for finite-dimensional manifolds).
**possible extension**: Brouwer's fixed point theorem (Theorem 1.4 in Hirsch) -> needs smooth approximation
**different extension**: Sard-Smale theorem -> based on this

**Lemma 1 (Hirsch, Lemma 1.1).**
  $U\subset R^n$ open, $f:U\to R^n$ is $C^1$. If $X\subset U$ has measure zero, so has $f(X)$
should be in mathlib, but seems it isn't

**Definition 2.** measure zero subset of a manifold

**Lemma 3.** Closed measure zero subset of R^n is nowhere dense
is in mathlib: measure_pos_of_nonempty_interior in `MeasureTheory.Measure.OpenPos`

**Corollary 4.** closed measure zero subset of M is nowhere dense       done
should follow easily from Lemma 3

**Prop 5 (Hirsch, Proposition 1.2).**
  Let M, N be C^1 manifolds with dim M < dim N.
  If f:M\to N is a C¹ map then f(M) is nowhere dense.
Essentially follows from Lemma 1 and Corollary 4.

Def. critical points, regular values of a differentiable map $f\colon M\to N$.
Nothing to do; just can expand the definition.

**Main Theorem (Hirsch, Theorem 1.3).**
  Let M, N be manifolds of dimensions m, n and f:M\to N a C^r map.
  If r > max {O,m - n} then f(\Sigma_f) has measure zero in N.
  The set of regular values of f is residual and therefore dense.

-------

mathlib has this local version of Sard (in `Mathlib.MeasureTheory.Function.Jacobian.lean`, line 659
For a $C^1$ function $f:E\to E$ on a finite-dimensional real vector space $E$,
if $S\subset E$ is a set of critical points (non-invertible differential), then $f(S)$ has measure zero.

easy Corollary. regular values are full measure.
another Corollary. regular values are comeagre.


## follow-up questions
- does this hold over other fields? I don't think so (but haven't really checked)
- can we include boundary or corners?
