# Towards the Sard-Smale theorem
In this repository, we work towards the proof of the Morse-Sard and Sard-Smale theorems.

**Morse-Sard theorem.** Let $M$ and $N$ be $C^r$-manifolds of dimensions $m$ and $n$, respectively and $f\colon M\to N$ a $C^r$ map.
  If $r > \max {O,m - n}$, the set $f(\Sigma_f)$ of critical values of $f$ has measure zero in $N$.
  Moreover, the set of regular values of f is residual and therefore dense.

The **Sard-Smale** theorem is a generalisation to infinite-dimensional Banach manifolds. Stating it requires a theory of Fredholm operators. See a [separate file](Roadmap towards Sard-Smale.md) for detail and a roadmap towards that.

**Applications** of Sard's theorem.
- stronger version of Whitney's approximation theorem
- proving Brouwer's fixed point theorem: there is no retraction $D^n\to S^{n-1}$
  - needs smooth approximation during the proof; otherwise it just shows this for smooth retractions
- transversality theorem (the local part uses Sard's theorem)
  - already the theorem statement requires defining the strong and weak $C^\infty$-topologies -> separate project
  - global part of the proof uses new ideas

## Necessary steps
- define measure zero subsets of a manifold: first version complete [and PRed](https://github.com/leanprover-community/mathlib4/pull/7076). Needs rework to a more conceptual approach
   - define Lebesgue measure on a C¹ manifold (pull back Lebesgue measure on each chart, use a partition of unity)
   - re-define: a measure zero subset of a manifold is a null set w.r.t. one (or any) Lebesgue measure
   - show well-definedness: null sets are preserved by coordinate changes (see below)
   - show: $A\subset M$ has measure zero iff for each chart $(\phi,U)$, the set $\phi(U\cap A)\subset R^n$ is a null set
   - define the almost everywhere filter on a manifold, show it's a CountableIntersectionFilter
   - show the ae filter is induced from the charts
   - perhaps not all of these are truly required

- define: locally Lipschitz maps; show C¹ maps are locally Lipschitz      in progress
- show: locally Lipschitz maps preserve null sets                       in progress; many sorries; not refactored as above yet

- meager sets and relation to measure zero
  - define nowhere dense and meagre sets: complete, [PRed](https://github.com/leanprover-community/mathlib4/pull/7180)
  - define $\sigma$-compact subsets (similar to $\sigma$-compact spaces) and show basic properties
  - $\sigma$-compact measure zero sets are meagre
  - mention counterexamples (nowhere dense but not measure zero, measure zero but not nowhere dense) in docstring

- **Corollary.** if $A\subset M$ is a measure zero subset and `f` is $C^1$, then $f(A)\subset N$ has measure zero
- Corollary. If $m < n$, then $f(M)$ has measure zero. Hence, Sard's theorem holds.

- reduce Sard's theorem to a local statement                    mostly done, a few sorries remain
- "hard" case "m\geq n" not started yet
- update statement of Sard's theorems to mention meagre sets: TODO, should be easy

- formalise the main argument of the proof: hard work
  - show Sigma_1 has measure zero, separate lemma
  - inductive proof: base case is that lemma
  - Sigma_2\setminus Sigma_3 also works, measure zero
  - remaining argument: induction proof, using a coord change and Fubini -> need to work out the details

## Status
This project was initiated during Lean for the Curious Mathematician 2023, mentored by @fpvandoorn and continued thereafter.
A fair amount of groundwork is done, but significant parts of that remain (and the "hard part" of the proof hasn't been started yet).
I'm pausing this project for now (except possibly upstreaming the parts which are complete to mathlib) since my Lean time is limited; I intend to return to and complete this project if possible.

That said, help is very welcome! Feel free to make a PR filling in some sorry, or working towards the proof of the "hard" case.

## follow-up questions
- does this hold over other fields? I don't think so (but haven't really checked)
- can we include boundary or corners?
