import DirichletPoincare.Definitions
import DirichletPoincare.Section3.Boundary

/-!
# Bounded region without the Poincaré (2,2) inequality (thesis Section 3.1)

The region is `regionT` of `Section3/Region.lean`; the Poincaré failure is proved in
`NoPoincare.lean` and the boundary length estimate in `Boundary.lean`.
-/

open MeasureTheory

namespace DirichletPoincare

/-- **Theorem 3.2** (thesis p. 21). There is a bounded region in `ℂ` on which the analytic
Poincaré (2,2) inequality fails. -/
theorem exists_bounded_region_without_poincare :
    ∃ G : Set ℂ, Bornology.IsBounded G ∧ IsRegion G ∧
      ∀ z₀ ∈ G, ¬ PoincareInequality G z₀ :=
  ⟨regionT, isBounded_regionS.subset regionT_subset_regionS, isRegion_regionT,
    fun _ _ => not_poincare_regionT⟩

/-- **Theorem 3.14** (thesis p. 27). The boundary of the region of Theorem 3.2 is rectifiable.
Rectifiability is expressed as finite one-dimensional Hausdorff measure of the frontier.
The statement is existential; the witness is `regionT`. -/
theorem exists_rectifiable_boundary_without_poincare :
    ∃ G : Set ℂ, Bornology.IsBounded G ∧ IsRegion G ∧
      (∀ z₀ ∈ G, ¬ PoincareInequality G z₀) ∧
      Measure.hausdorffMeasure 1 (frontier G) < ⊤ :=
  ⟨regionT, isBounded_regionS.subset regionT_subset_regionS, isRegion_regionT,
    fun _ _ => not_poincare_regionT, hausdorff_frontier_regionT_lt_top⟩

end DirichletPoincare
