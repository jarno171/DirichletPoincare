import DirichletPoincare.Definitions
import DirichletPoincare.Section2.InclusionAux
import DirichletPoincare.Section2.RiemannAux

/-!
# Basic facts on the Dirichlet and Bergman spaces

Lean statements for Section 2.1–2.3 of Varis (2013): Lemma 2.4, Theorem 2.5, Lemma 2.10 and
Corollary 2.12.
-/

open MeasureTheory
open scoped ENNReal

namespace DirichletPoincare

/-- **Lemma 2.4** (thesis p. 7). For a bounded region, the inclusion `D(G) ⊂ B(G)` does not
depend on the basepoint. The hypotheses `_hR`, `_hz₀`, `_hz₁` are part of the thesis statement but
are not needed by the proof. -/
theorem dirichletSubsetBergman_basepoint_change {G : Set ℂ} (_hR : IsRegion G)
    (hbdd : Bornology.IsBounded G) {z₀ z₁ : ℂ} (_hz₀ : z₀ ∈ G) (_hz₁ : z₁ ∈ G)
    (h : DirichletSubsetBergman G z₀) : DirichletSubsetBergman G z₁ := by
  intro f hf
  -- `f - f(z₀)` lies in `D_{z₀}(G)` and has the same Dirichlet energy as `f`.
  have hg : IsInDirichletSpace G z₀ (fun z => f z - f z₀) := by
    refine ⟨hf.1.sub_const _, sub_self _, ?_⟩
    simpa [dirichletEnergy, deriv_sub_const] using hf.2.2
  have hgB : ∫⁻ z in G, ENNReal.ofReal (‖f z - f z₀‖ ^ 2) < ⊤ := h _ hg
  have hfin : volume G < ⊤ := hbdd.measure_lt_top
  -- Pointwise `|f|² ≤ 2|f - f(z₀)|² + 2|f(z₀)|²`, then integrate over `G`.
  have hpt : ∀ z, ENNReal.ofReal (‖f z‖ ^ 2) ≤
      ENNReal.ofReal (2 * ‖f z - f z₀‖ ^ 2) + ENNReal.ofReal (2 * ‖f z₀‖ ^ 2) := by
    intro z
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h1 : ‖f z‖ ≤ ‖f z - f z₀‖ + ‖f z₀‖ := by
      calc ‖f z‖ = ‖(f z - f z₀) + f z₀‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    nlinarith [mul_le_mul h1 h1 (norm_nonneg _) (by positivity), sq_nonneg (‖f z - f z₀‖ - ‖f z₀‖)]
  have hA : ∫⁻ z in G, ENNReal.ofReal (2 * ‖f z - f z₀‖ ^ 2) < ⊤ := by
    simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hgB
  have hB : ∫⁻ _ in G, ENNReal.ofReal (2 * ‖f z₀‖ ^ 2) < ⊤ := by
    rw [setLIntegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  calc bergmanNormSq G f ≤ ∫⁻ z in G,
        (ENNReal.ofReal (2 * ‖f z - f z₀‖ ^ 2) + ENNReal.ofReal (2 * ‖f z₀‖ ^ 2)) :=
          lintegral_mono hpt
    _ = (∫⁻ z in G, ENNReal.ofReal (2 * ‖f z - f z₀‖ ^ 2)) +
          ∫⁻ _ in G, ENNReal.ofReal (2 * ‖f z₀‖ ^ 2) :=
          lintegral_add_right' _ aemeasurable_const
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hA, hB⟩

/-- **Lemma 2.10** (thesis p. 12). If `D(G) ⊂ B(G)`, the canonical inclusion `i : D(G) → B(G)` is
bounded. Norms are squared (see `bergmanNormSq`), so `C` bounds `‖g‖²_B` by `C ‖g‖²_D`.
The region hypothesis is needed: on a disconnected set, a function can be constant on a component
not containing `z₀`, where its energy vanishes. Boundedness (`_hbdd`) is part of the thesis
statement but is not needed by the proof. -/
theorem inclusion_bounded {G : Set ℂ} (hR : IsRegion G) (_hbdd : Bornology.IsBounded G)
    {z₀ : ℂ} (hz₀ : z₀ ∈ G) (h : DirichletSubsetBergman G z₀) :
    ∃ C : ENNReal, C < ⊤ ∧
      ∀ f : ℂ → ℂ, IsInDirichletSpace G z₀ f → bergmanNormSq G f ≤ C * dirichletEnergy G f :=
  inclusion_bounded_aux hR hz₀ h

/-- **Corollary 2.12** (thesis p. 12). The inclusion `D(G) ⊂ B(G)` is equivalent to the analytic
Poincaré (2,2) inequality on the bounded region `G`. -/
theorem dirichletSubsetBergman_iff_poincare {G : Set ℂ} (hR : IsRegion G)
    (hbdd : Bornology.IsBounded G) {z₀ : ℂ} (hz₀ : z₀ ∈ G) :
    DirichletSubsetBergman G z₀ ↔ PoincareInequality G z₀ := by
  constructor
  · intro h
    exact inclusion_bounded hR hbdd hz₀ h
  · rintro ⟨K, hK, hineq⟩ f hf
    exact lt_of_le_of_lt (hineq f hf) (ENNReal.mul_lt_top hK hf.2.2)

/-- **Theorem 2.5** (thesis p. 8). For a bounded, simply connected region `G` with Riemann map
`φ : U → G`, `φ(0) = z₀`, the following are equivalent:
1. `D(G) ⊂ B(G)`;
2. `h D(G) ⊂ D(G)`, where `h(z) = z`;
3. `φ D(U) ⊂ D(U)`;
4. `φ' D(U) ⊂ B(U)`.
The chain of `↔` below follows the numbering 1 ↔ 2 ↔ 3 ↔ 4. -/
theorem riemann_map_characterization {G : Set ℂ} (hbdd : Bornology.IsBounded G)
    (hR : IsRegion G) [SimplyConnectedSpace G] {z₀ : ℂ} {φ : ℂ → ℂ}
    (hφ : IsRiemannMap G z₀ φ) :
    (DirichletSubsetBergman G z₀ ↔ IsMultiplier G z₀ id) ∧
    (IsMultiplier G z₀ id ↔ IsMultiplier unitDisc 0 φ) ∧
    (IsMultiplier unitDisc 0 φ ↔
      ∀ g : ℂ → ℂ, IsInDirichletSpace unitDisc 0 g →
        bergmanNormSq unitDisc (fun z => deriv φ z * g z) < ⊤) :=
  riemann_map_characterization_aux hbdd hR hφ

end DirichletPoincare
