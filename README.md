# Dirichlet space and the analytic Poincaré inequality: a Lean 4 formalization

This repository formalizes, in Lean 4 with Mathlib, the main results of the Pro gradu thesis

> Jarno Varis, *Dirichlet space and analytic Poincaré inequality*, University of Helsinki, 2013
> (written in Finnish).

For a region `G ⊂ ℂ`, the Dirichlet space `D(G)` consists of the holomorphic functions `f` on `G`
with `f(z₀) = 0` and `∫_G |f'|² dA < ∞`. The *analytic Poincaré (2,2) inequality* says
`∫_G |f|² dA ≤ K ∫_G |f'|² dA` for all `f ∈ D(G)`. The thesis shows that it holds on starlike and
piecewise starlike regions, characterizes it through the Riemann map, and constructs a bounded
region with rectifiable boundary where it fails, together with a region where the (2,2) inequality
holds but its `L^q` and `L^∞` versions fail.

**Status:** every theorem listed below is fully proved. There is no `sorry`, and the main theorems
depend only on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`). The build has no
warnings.

## Building

The toolchain is pinned in [`lean-toolchain`](lean-toolchain) (Lean `v4.36.0`, Mathlib `v4.36.0`).

```
lake build
```

The first build also compiles Mathlib's dependencies if you have no cache. Building needs several
GB of memory; close the editor's Lean server first if memory is tight.

## Layout

| File | Contents |
| --- | --- |
| [`Definitions.lean`](DirichletPoincare/Definitions.lean) | Dirichlet energy, Bergman norm, `D(G)`, the Poincaré inequalities, regions, starlike and piecewise starlike regions, multipliers, Riemann maps |
| [`Section2/Basics.lean`](DirichletPoincare/Section2/Basics.lean) | Lemma 2.4, Theorem 2.5, Lemma 2.10, Corollary 2.12 (statements and top-level proofs) |
| [`Section2/InclusionAux.lean`](DirichletPoincare/Section2/InclusionAux.lean) | Proof of Lemma 2.10: point-evaluation bounds, `L²` limits of derivatives, open mapping argument |
| [`Section2/RiemannAux.lean`](DirichletPoincare/Section2/RiemannAux.lean) | Proof of Theorem 2.5: injective holomorphic maps have nonvanishing derivative, change of variables, multiplier criterion |
| [`Section2/AreaMeanValue.lean`](DirichletPoincare/Section2/AreaMeanValue.lean) | Area mean-value inequality `|g(w)|² · area(B) ≤ ∫_B |g|²` for holomorphic `g` (not in Mathlib) |
| [`Section2/StarlikeAux.lean`](DirichletPoincare/Section2/StarlikeAux.lean), [`StarlikeMain.lean`](DirichletPoincare/Section2/StarlikeMain.lean), [`Starlike.lean`](DirichletPoincare/Section2/Starlike.lean) | Theorem 2.13 |
| [`Section2/PiecewiseStarlike.lean`](DirichletPoincare/Section2/PiecewiseStarlike.lean) | Lemma 2.20, Theorem 2.22 |
| [`Section3/Sequences.lean`](DirichletPoincare/Section3/Sequences.lean) | Lemma 3.1 |
| [`Section3/Params.lean`](DirichletPoincare/Section3/Params.lean), [`Region.lean`](DirichletPoincare/Section3/Region.lean), [`Estimates.lean`](DirichletPoincare/Section3/Estimates.lean), [`Mass.lean`](DirichletPoincare/Section3/Mass.lean), [`NoPoincare.lean`](DirichletPoincare/Section3/NoPoincare.lean), [`Boundary.lean`](DirichletPoincare/Section3/Boundary.lean), [`Counterexample.lean`](DirichletPoincare/Section3/Counterexample.lean) | Theorems 3.2 and 3.14 |
| [`Section3/LpFailures.lean`](DirichletPoincare/Section3/LpFailures.lean), [`LpPoincare.lean`](DirichletPoincare/Section3/LpPoincare.lean) | Lemmas 3.15, 3.18 and Theorem 3.21 |
| [`Spiral.lean`](DirichletPoincare/Spiral.lean) | Partial formalization of the spiral domain (thesis Section 4) |
| [`Basic.lean`](DirichletPoincare/Basic.lean) | A "hello world" smoke test (`2 ∣ 4`) |

## Thesis results and their Lean names

| Thesis | Lean declaration | File |
| --- | --- | --- |
| Lemma 2.4 | `dirichletSubsetBergman_basepoint_change` | `Section2/Basics` |
| Theorem 2.5 | `riemann_map_characterization` | `Section2/Basics` |
| Lemma 2.10 | `inclusion_bounded` | `Section2/Basics` |
| Corollary 2.12 | `dirichletSubsetBergman_iff_poincare` | `Section2/Basics` |
| Theorem 2.13 | `poincare_of_starlike` | `Section2/Starlike` |
| Lemma 2.20 | `dirichlet_iff_on_pieces` | `Section2/PiecewiseStarlike` |
| Theorem 2.22 | `poincare_of_piecewise_starlike` | `Section2/PiecewiseStarlike` |
| Lemma 3.1 | `exists_good_index` | `Section3/Sequences` |
| Theorem 3.2 | `exists_bounded_region_without_poincare` | `Section3/Counterexample` |
| Theorem 3.14 | `exists_rectifiable_boundary_without_poincare` | `Section3/Counterexample` |
| Lemma 3.15 | `tendsto_eLpNorm_atTop` | `Section3/LpPoincare` |
| Lemma 3.18 | `exists_visibility_point` | `Section3/LpPoincare` |
| Theorem 3.21 | `exists_region_with_lp_poincare_failures` | `Section3/LpPoincare` |

## Conventions

* `ℂ` carries Lebesgue measure; all integrals are lower Lebesgue integrals with values in `ℝ≥0∞`,
  so "finite" means `< ⊤` and no integrability hypotheses are needed.
* Norms are **squared**: `bergmanNormSq G f = ∫_G |f|²` and `dirichletEnergy G f = ∫_G |f'|²`.
  The constant `K` in `PoincareInequality` therefore bounds the squared norms, as in the thesis'
  inequality `∫_G |f|² ≤ K ∫_G |f'|²`.
* A *region* is a connected open set (`IsRegion`). `D(G)` is `IsInDirichletSpace G z₀`, which
  includes `f(z₀) = 0`.
* The `(p, q)` Poincaré inequality is stated with Mathlib's `eLpNorm` over `volume.restrict G`.
* Rectifiability of a boundary is expressed as finite one-dimensional Hausdorff measure of the
  frontier.

## Where the formalization deviates from the thesis

### Different proofs

* **Theorem 2.13 (starlike).** The thesis argument goes through Lemma 2.10, which is itself deep.
  The Lean proof avoids it: polar coordinates around the star centre reduce the claim to a
  one-dimensional Hardy-type estimate along rays, and the singularity at the centre is controlled
  by the area mean-value inequality. The Poincaré constant depends on the region and the base point.
* **Theorem 2.22 (piecewise starlike).** The thesis proves that `z` is a multiplier of `D(G)` via
  Theorem 2.5. The Lean proof applies Theorem 2.13 on every piece and bounds the value of an
  `f ∈ D(G)` at each piece's base point by a chain of discs across the connected region.
  Lemma 2.20 is proved but is not needed for this argument.
* **Lemma 2.10.** The thesis uses the closed graph theorem. The Lean proof applies the open
  mapping theorem to the graph `{([f'], [f])}` inside `L²(G) × L²(G)` (injective with closed
  range, via Mathlib's `antilipschitz_of_injective_of_isClosed_range`). It needs a
  point-evaluation bound for `D(G)` and the `L²`-limit lemma proved from the area mean-value
  inequality.
* **Theorem 2.5.** Injectivity of the Riemann map implies `φ' ≠ 0` and a holomorphic inverse;
  neither is in Mathlib, so both are proved here (local normal form `φ − φ(a) = ((z−a)h)^k`,
  local open mapping property, and roots of unity).
* **Theorem 3.2.** The Lean region `regionT` is a chain of discs `B(cₖ, cₖ/4)` along the real
  axis joined by thin rectangles of half-height `hₖ = mₖ⁻¹⁰`, with `cₖ = mₖ⁻²` and a recursively
  chosen sequence `mₖ` (`Params.lean`). The thesis uses a sequence of circular sectors. The test
  functions are the thesis' `gₘ(z) = (1 − z²)ᵐ`, but the contradiction is derived directly
  (energy `O(m⁻⁵)` against `L²` distance `≳ m⁻²` from every constant) instead of through
  Corollary 2.12 and Lemma 2.10.
* **Theorem 3.21.** The Lean region `regionStar` is a disc around `1` together with thin
  rectangles; it is starlike, so Theorem 2.13 gives the (2,2) inequality. The thesis region `G⁺`
  is a staircase of sectors.

### Stronger or modified statements

* **Theorem 3.21.** The Lean version proves that a *single* `p₀ = 8/5` works for every constant
  `K`, because `2p/(2−p) ≥ 8` already suffices. The thesis only claims a `p₀` that depends on `K`.
  The `L^∞` failure is shown for every basepoint. Lemmas 3.15 and 3.18 are not needed.
* **Lemma 2.10.** The statement has the added hypothesis `IsRegion G`. Without connectedness it is
  false: a function can be constant on a component not containing `z₀`, where its energy
  vanishes.
* **Lemma 3.15.** The hypothesis `0 < q` is added (Mathlib sets `‖f‖₀ = 0`, so the statement is
  false at `q = 0`), and the thesis assumption `‖f‖_∞ > 0` is dropped because it is not needed.
* **Lemma 3.18.** The first part is as in the thesis. For smaller radii `r₀ < r` the Lean
  statement gives an existential point `a₀` for each `r₀` instead of one shared point `a`, which
  is weaker than what the thesis uses.
* **Lemma 3.1.** The hypothesis `1 ≤ n` is added, since the index `2n − 1` would otherwise be
  truncated in `ℕ`. The decimal `0,8` of the thesis is the real number `0.8`. The lemma is
  formalized on its own: the Lean construction of Theorems 3.2 and 3.14 uses its own parameter
  choice in `Params.lean`.
* **Theorems 3.2 and 3.14** are existential statements. Theorem 3.14 states that the witness has
  both properties (Poincaré failure and finite boundary length), proved for `regionT`.
* **Unused hypotheses.** Some thesis hypotheses are kept for fidelity although the proofs do not
  need them: connectedness and basepoints in Lemma 2.4, boundedness in Lemma 2.10, the hypotheses
  of Lemma 3.1, and `SimplyConnectedSpace G` in Theorem 2.5 (the Riemann map is given, so simple
  connectivity is not used). They are underscore-prefixed (for example `_hR`) where Lean would
  otherwise report an unused variable.

### Not formalized

* **Corollary 2.24** (a bound on the Poincaré constant on discs) is omitted, since nothing else
  depends on it.
* **Spiral domain (thesis Section 4).** [`Spiral.lean`](DirichletPoincare/Spiral.lean) only
  formalizes the strip `Δ`, the domain `exp(iΔ)` and the injectivity of `w ↦ exp(iw)` on the
  strip. The remainder of that section is not formalized.
* The thesis' material outside the results listed above (introductory remarks, background
  citations and examples) is not part of the formalization.

## Other files

[`docs/index.html`](docs/index.html) is a self-contained, interactive tour of the formalization (dependency
map, simulations of the main estimates, and a searchable source browser). Open it in a browser; to
regenerate it after changing the Lean files or `docs/src/`, run `python docs/build.py`.
