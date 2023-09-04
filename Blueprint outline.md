## Blueprint outline
**Goal.** Sard's theorem (for finite-dimensional manifolds).
**possible extension**: Brouwer's fixed point theorem (Theorem 1.4 in Hirsch) -> needs smooth approximation
**different extension**: Sard-Smale theorem -> based on this

Lemma 1 (H1.1): should be in mathlib
  $U\subset R^n$ open, $f:U\to R^n$ is $C^1$
  If $X\subset U$ has measure zero, so has $f(X)$

Definition 2: measure zero subset of a manifold
(is independent of the choice of atlas; by Lemma 1.1)

Lemma 3. closed measure zero subset of R^n is nowhere dense
Cor 4. closed measure zero subset of M is nowhere dense

Prop 5 (H1.2). M, N manifolds with dim M < dim N. If f:M\to N is a C¹ map then f(M) is nowhere dense.
  mostly a corollary of Lemma 1 and Cor 4.

Def. critical points, regular values of a differentiable map $f\colon M\to N$ --- can state explicitly

**Main Theorem (H1.3).** Let M, N be manifolds of dimensions m, n and f:M\to N a C^r map.
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
