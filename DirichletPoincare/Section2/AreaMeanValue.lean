import Mathlib

/-!
# Area mean-value estimate for holomorphic functions

Auxiliary facts used in the proof of Theorem 2.13: for `g` holomorphic on a disc,
`‖g w‖² · area(disc) ≤ ∫_disc ‖g‖²`.
-/

open MeasureTheory Complex Metric Real Set
open scoped ENNReal

namespace DirichletPoincare

/-- Polar coordinates on the whole plane, with the angle as the outer variable. -/
theorem lintegral_polar_angle_first {F : ℂ → ℝ≥0∞} (hF : Measurable F) (w : ℂ) :
    ∫⁻ z, F z =
      ∫⁻ θ in Ioo (-π) π, ∫⁻ ρ in Ioi 0, ENNReal.ofReal ρ * F (circleMap w ρ θ) := by
  have hcirc : Continuous fun p : ℝ × ℝ => circleMap w p.1 p.2 := by
    simp only [circleMap]
    fun_prop
  have hcm : ∀ p : ℝ × ℝ, w + Complex.polarCoord.symm p = circleMap w p.1 p.2 := by
    intro p
    rw [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]
    simp [Complex.ofReal_cos, Complex.ofReal_sin]
  rw [← lintegral_add_left_eq_self (μ := volume) F w,
    ← Complex.lintegral_comp_polarCoord_symm (fun z => F (w + z))]
  have hprod : (volume : Measure (ℝ × ℝ)).restrict polarCoord.target =
      (volume.restrict (Ioi 0)).prod (volume.restrict (Ioo (-π) π)) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
    rfl
  have hm : Measurable fun p : ℝ × ℝ => ENNReal.ofReal p.1 • F (w + Complex.polarCoord.symm p) := by
    simp_rw [hcm]
    exact (ENNReal.measurable_ofReal.comp measurable_fst).smul (hF.comp hcirc.measurable)
  rw [hprod, lintegral_prod_symm _ hm.aemeasurable]
  refine lintegral_congr fun θ => lintegral_congr fun ρ => ?_
  simp only [smul_eq_mul, hcm]

/-- Polar coordinates on a disc, for functions continuous on the disc. -/
theorem lintegral_ball_polar {H : ℂ → ℝ≥0∞} {w : ℂ} {r : ℝ}
    (hH : ContinuousOn H (ball w r)) :
    ∫⁻ z in ball w r, H z =
      ∫⁻ ρ in Ioo 0 r, ENNReal.ofReal ρ * ∫⁻ θ in Ioo (-π) π, H (circleMap w ρ θ) := by
  classical
  set F : ℂ → ℝ≥0∞ := (ball w r).piecewise H 0 with hF
  have hFm : Measurable F :=
    hH.measurable_piecewise continuousOn_const isOpen_ball.measurableSet
  have h1 : ∫⁻ z in ball w r, H z = ∫⁻ z, F (w + z) := by
    rw [lintegral_add_left_eq_self (μ := volume) F w,
      ← lintegral_indicator isOpen_ball.measurableSet]
    refine lintegral_congr fun z => ?_
    by_cases hz : z ∈ ball w r <;> simp [F, hz, Set.indicator]
  set S : Set (ℝ × ℝ) := Ioo 0 r ×ˢ Ioo (-π) π with hS
  set ψ : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal p.1 * H (circleMap w p.1 p.2) with hψ
  have hST : S ⊆ polarCoord.target := by
    intro p hp
    exact ⟨hp.1.1, hp.2⟩
  have hSm : MeasurableSet S := measurableSet_Ioo.prod measurableSet_Ioo
  have hTm : MeasurableSet polarCoord.target :=
    measurableSet_Ioi.prod measurableSet_Ioo
  have hA : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 • F (w + Complex.polarCoord.symm p) = S.indicator ψ p := by
    intro p hp
    have hcm : w + Complex.polarCoord.symm p = circleMap w p.1 p.2 := by
      rw [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]
      simp [Complex.ofReal_cos, Complex.ofReal_sin]
    have hmem : circleMap w p.1 p.2 ∈ ball w r ↔ p.1 < r := by
      rw [mem_ball, mem_sphere.1 (circleMap_mem_sphere' w p.1 p.2), abs_of_pos hp.1]
    rw [hcm]
    by_cases hr : p.1 < r
    · have hpS : p ∈ S := ⟨⟨hp.1, hr⟩, hp.2⟩
      rw [Set.indicator_of_mem hpS]
      simp [F, hmem.2 hr, hψ]
    · have hpS : p ∉ S := fun h => hr h.1.2
      rw [Set.indicator_of_notMem hpS]
      simp [F, hmem, hr]
  have hint : ∫⁻ p in polarCoord.target,
      ENNReal.ofReal p.1 • F (w + Complex.polarCoord.symm p) = ∫⁻ p in S, ψ p := by
    rw [setLIntegral_congr_fun hTm hA, lintegral_indicator hSm, Measure.restrict_restrict hSm,
      inter_eq_left.2 hST]
  have hprod : (volume : Measure (ℝ × ℝ)).restrict S =
      (volume.restrict (Ioo 0 r)).prod (volume.restrict (Ioo (-π) π)) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have hcirc : Continuous fun p : ℝ × ℝ => circleMap w p.1 p.2 := by
    simp only [circleMap]
    fun_prop
  have hψm : AEMeasurable ψ ((volume.restrict (Ioo 0 r)).prod (volume.restrict (Ioo (-π) π))) := by
    rw [← hprod]
    refine (ENNReal.measurable_ofReal.comp measurable_fst).aemeasurable.mul ?_
    refine (hH.comp hcirc.continuousOn fun p hp => ?_).aemeasurable hSm
    rw [mem_ball, mem_sphere.1 (circleMap_mem_sphere' w p.1 p.2), abs_of_pos hp.1.1]
    exact hp.1.2
  rw [h1, ← Complex.lintegral_comp_polarCoord_symm (fun z => F (w + z)), hint, hprod,
    lintegral_prod _ hψm]
  refine lintegral_congr fun ρ => ?_
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Mean-value inequality on a circle: `2π ‖g w‖² ≤ ∫ ‖g‖²` over the circle of radius `ρ`. -/
theorem circle_sq_le {g : ℂ → ℂ} {w : ℂ} {r ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r)
    (hg : DifferentiableOn ℂ g (ball w r)) :
    ENNReal.ofReal (2 * π * ‖g w‖ ^ 2) ≤
      ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal (‖g (circleMap w ρ θ)‖ ^ 2) := by
  have hsub : closedBall w ρ ⊆ ball w r := closedBall_subset_ball hρr
  have hDC : DiffContOnCl ℂ g (ball w |ρ|) := by
    rw [abs_of_pos hρ]
    refine ⟨hg.mono (ball_subset_ball hρr.le), ?_⟩
    rw [closure_ball w hρ.ne']
    exact hg.continuousOn.mono hsub
  have hmean := hDC.circleAverage
  rw [circleAverage_def] at hmean
  have hcont : Continuous fun θ : ℝ => g (circleMap w ρ θ) := by
    refine hg.continuousOn.comp_continuous (continuous_circleMap w ρ) fun θ => ?_
    exact hsub (circleMap_mem_closedBall w hρ.le θ)
  set u : ℝ → ℝ := fun θ => ‖g (circleMap w ρ θ)‖ with hu
  have hucont : Continuous u := hcont.norm
  have hper : Function.Periodic u (2 * π) := fun θ => by
    simp [hu, periodic_circleMap w ρ θ]
  have hshift : ∫ θ in (-π)..π, u θ = ∫ θ in (0)..(2 * π), u θ := by
    have := hper.intervalIntegral_add_eq (-π) 0
    rw [show -π + 2 * π = π by ring, show (0 : ℝ) + 2 * π = 2 * π by ring] at this
    exact this
  have hnorm : 2 * π * ‖g w‖ ≤ ∫ θ in (0)..(2 * π), u θ := by
    have h2 : ∫ θ in (0)..(2 * π), g (circleMap w ρ θ) = (2 * π : ℂ) * g w := by
      have : ((2 * π)⁻¹ : ℝ) • ∫ θ in (0)..(2 * π), g (circleMap w ρ θ) = g w := hmean
      rw [← this, Complex.real_smul]
      push_cast
      field_simp
    calc 2 * π * ‖g w‖ = ‖∫ θ in (0)..(2 * π), g (circleMap w ρ θ)‖ := by
          rw [h2, norm_mul]
          simp [abs_of_pos pi_pos]
      _ ≤ ∫ θ in (0)..(2 * π), ‖g (circleMap w ρ θ)‖ :=
          intervalIntegral.norm_integral_le_integral_norm two_pi_pos.le
  set c := ‖g w‖ with hc
  have hsq : 2 * π * c ^ 2 ≤ ∫ θ in (-π)..π, u θ ^ 2 := by
    have hmono : ∫ θ in (-π)..π, (2 * c * u θ - c ^ 2) ≤ ∫ θ in (-π)..π, u θ ^ 2 :=
      intervalIntegral.integral_mono_on (by linarith [pi_pos])
        (((continuous_const.mul hucont).sub continuous_const).intervalIntegrable _ _)
        ((hucont.pow 2).intervalIntegrable _ _) fun θ _ => by nlinarith [sq_nonneg (u θ - c)]
    have hlin : ∫ θ in (-π)..π, (2 * c * u θ - c ^ 2) =
        2 * c * (∫ θ in (-π)..π, u θ) - 2 * π * c ^ 2 := by
      have e1 : ∫ θ in (-π)..π, (2 * c * u θ - c ^ 2) =
          (∫ θ in (-π)..π, 2 * c * u θ) - ∫ _ in (-π)..π, c ^ 2 :=
        intervalIntegral.integral_sub ((continuous_const.mul hucont).intervalIntegrable _ _)
          intervalIntegrable_const
      rw [e1, intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    have h3 : 2 * π * c ≤ ∫ θ in (-π)..π, u θ := by rw [hshift]; exact hnorm
    rw [hlin] at hmono
    have hc0 : 0 ≤ c := norm_nonneg _
    nlinarith [mul_nonneg hc0 (sub_nonneg.2 h3)]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · refine ENNReal.ofReal_le_ofReal ?_
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [pi_pos])]
    exact hsq
  · exact ((hucont.pow 2).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  · exact Filter.Eventually.of_forall fun θ => sq_nonneg _

/-- **Area mean-value estimate.** For `g` holomorphic on a disc,
`‖g w‖² · area ≤ ∫_disc ‖g‖²`. -/
theorem sq_mul_volume_le {g : ℂ → ℂ} {w : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (ball w r)) :
    ENNReal.ofReal (‖g w‖ ^ 2) * volume (ball w r) ≤
      ∫⁻ z in ball w r, ENNReal.ofReal (‖g z‖ ^ 2) := by
  have hH : ContinuousOn (fun z => ENNReal.ofReal (‖g z‖ ^ 2)) (ball w r) :=
    ENNReal.continuous_ofReal.comp_continuousOn (hg.continuousOn.norm.pow 2)
  rw [lintegral_ball_polar hH]
  have hvol : volume (ball w r) = ENNReal.ofReal (π * r ^ 2) := by
    rw [Complex.volume_ball, ENNReal.ofReal_mul pi_pos.le, ENNReal.ofReal_pow hr.le, mul_comm]
    congr 1
    exact (ENNReal.ofReal_eq_coe_nnreal pi_pos.le).symm
  have hint : ∫⁻ ρ in Ioo 0 r, ENNReal.ofReal ρ = ENNReal.ofReal (r ^ 2 / 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · congr 1
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le, integral_id]
      ring
    · exact (continuous_id.integrableOn_Icc).mono_set Ioo_subset_Icc_self
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with ρ hρ using hρ.1.le
  calc ENNReal.ofReal (‖g w‖ ^ 2) * volume (ball w r)
      = ENNReal.ofReal (2 * π * ‖g w‖ ^ 2) * ∫⁻ ρ in Ioo 0 r, ENNReal.ofReal ρ := by
        rw [hvol, hint, ← ENNReal.ofReal_mul (sq_nonneg ‖g w‖),
          ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * π * ‖g w‖ ^ 2)]
        congr 1
        ring
    _ = ∫⁻ ρ in Ioo 0 r, ENNReal.ofReal ρ * ENNReal.ofReal (2 * π * ‖g w‖ ^ 2) := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm]
    _ ≤ _ := by
        refine setLIntegral_mono' measurableSet_Ioo fun ρ hρ => ?_
        gcongr
        exact circle_sq_le hρ.1 hρ.2 hg

end DirichletPoincare
