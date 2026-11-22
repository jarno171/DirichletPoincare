import Mathlib

/-!
# Dirichlet space, Bergman-type integral and the Poincaré (2,2) inequality

Definitions from Section 2 of Varis (2013), "Dirichlet space and analytic Poincaré inequality"
(Pro gradu thesis, University of Helsinki). Thesis equation numbers are given in each docstring.

All integrals are Lebesgue integrals over `ℂ ≅ ℝ²` with values in `ℝ≥0∞`. An integral equal to
`⊤` means "not finite", so no separate integrability hypotheses are needed.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace DirichletPoincare

/-- The Dirichlet energy `∫_G |f'|² dA` (thesis (2.1)). -/
noncomputable def dirichletEnergy (G : Set ℂ) (f : ℂ → ℂ) : ℝ≥0∞ :=
  ∫⁻ z in G, ENNReal.ofReal (‖deriv f z‖ ^ 2)

/-- The squared L² norm `∫_G |f|² dA` (thesis (2.2), the Bergman-space norm). -/
noncomputable def bergmanNormSq (G : Set ℂ) (f : ℂ → ℂ) : ℝ≥0∞ :=
  ∫⁻ z in G, ENNReal.ofReal (‖f z‖ ^ 2)

/-- `f` belongs to the Dirichlet class `D(G)` (thesis (2.1)): `f` is analytic on `G`,
vanishes at the basepoint `z₀`, and has finite Dirichlet energy. -/
def IsInDirichletSpace (G : Set ℂ) (z₀ : ℂ) (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f G ∧ f z₀ = 0 ∧ dirichletEnergy G f < ⊤

/-- The Poincaré (2,2) inequality on `G` with basepoint `z₀` (thesis (2.9)): there is a finite
constant `K` with `∫_G |f|² ≤ K ∫_G |f'|²` for every `f ∈ D(G)`. -/
def PoincareInequality (G : Set ℂ) (z₀ : ℂ) : Prop :=
  ∃ K : ℝ≥0∞, K < ⊤ ∧
    ∀ f : ℂ → ℂ, IsInDirichletSpace G z₀ f → bergmanNormSq G f ≤ K * dirichletEnergy G f

/-- `D_{z₀}(G) ⊂ B_{z₀}(G)` (thesis Section 2.1): every `f ∈ D_{z₀}(G)` has finite Bergman norm. -/
def DirichletSubsetBergman (G : Set ℂ) (z₀ : ℂ) : Prop :=
  ∀ f : ℂ → ℂ, IsInDirichletSpace G z₀ f → bergmanNormSq G f < ⊤

/-- A region is an open connected set (thesis Section 2). -/
def IsRegion (G : Set ℂ) : Prop := IsOpen G ∧ IsConnected G

/-- The Poincaré `(p, q)` inequality with constant `K` (thesis Section 3.2):
`‖f‖_{L^p(G)} ≤ K ‖f'‖_{L^q(G)}` for all `f ∈ D_{z₀}(G)`. -/
def PoincareLpWithConst (G : Set ℂ) (z₀ : ℂ) (p q : ℝ≥0∞) (K : ℝ≥0) : Prop :=
  ∀ f : ℂ → ℂ, IsInDirichletSpace G z₀ f →
    eLpNorm f p (volume.restrict G) ≤ K * eLpNorm (deriv f) q (volume.restrict G)

/-- The Poincaré `(p, q)` inequality with some finite constant (thesis Section 3.2). -/
def PoincareLp (G : Set ℂ) (z₀ : ℂ) (p q : ℝ≥0∞) : Prop :=
  ∃ K : ℝ≥0, PoincareLpWithConst G z₀ p q K

/-- `h` is a multiplier of `D_{z₀}(G)` (thesis Section 2.2): `h · f ∈ D_{z₀}(G)` for all
`f ∈ D_{z₀}(G)`. -/
def IsMultiplier (G : Set ℂ) (z₀ : ℂ) (h : ℂ → ℂ) : Prop :=
  ∀ f : ℂ → ℂ, IsInDirichletSpace G z₀ f → IsInDirichletSpace G z₀ (fun z => h z * f z)

/-- The unit disc `U` (thesis Section 2.2). -/
noncomputable def unitDisc : Set ℂ := Metric.ball 0 1

/-- `φ` is a Riemann map from `U` onto `G` with `φ(0) = z₀` (thesis Section 2.2). -/
def IsRiemannMap (G : Set ℂ) (z₀ : ℂ) (φ : ℂ → ℂ) : Prop :=
  φ 0 = z₀ ∧ DifferentiableOn ℂ φ unitDisc ∧ Set.InjOn φ unitDisc ∧ φ '' unitDisc = G

/-- A starlike region (thesis Section 2.4): there is a point `w₀ ∈ S` such that every segment
from `w₀` to a point of `S` lies in `S`. -/
def IsStarlikeRegion (S : Set ℂ) : Prop :=
  IsRegion S ∧ ∃ w₀ ∈ S, ∀ z ∈ S, segment ℝ w₀ z ⊆ S

/-- `E` is the trace of a simple path, possibly closed (thesis Section 2.5). -/
def IsSimplePathTrace (E : Set ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc 0 1) ∧ Set.InjOn γ (Set.Ico 0 1) ∧
    γ '' Set.Icc 0 1 = E

/-- `G = E ∪ G₁ ∪ … ∪ Gₙ` (thesis Section 2.5): disjoint starlike pieces `Gᵢ` and a null set `E`
that is a finite union of simple path traces. -/
def IsPiecewiseDecomposition (G : Set ℂ) (n : ℕ) (Gs : Fin n → Set ℂ) (E : Set ℂ) : Prop :=
  (∀ i, IsStarlikeRegion (Gs i)) ∧
  Pairwise (fun i j => Disjoint (Gs i) (Gs j)) ∧
  (∃ (m : ℕ) (paths : Fin m → Set ℂ), (∀ j, IsSimplePathTrace (paths j)) ∧ E = ⋃ j, paths j) ∧
  volume E = 0 ∧
  G = E ∪ ⋃ i, Gs i

/-- A bounded region is piecewise starlike if it admits a piecewise decomposition
(thesis Section 2.5). -/
def IsPiecewiseStarlike (G : Set ℂ) : Prop :=
  ∃ (n : ℕ) (Gs : Fin n → Set ℂ) (E : Set ℂ), IsPiecewiseDecomposition G n Gs E

end DirichletPoincare
