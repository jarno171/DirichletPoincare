import DirichletPoincare.Section2.AreaMeanValue

/-!
# One-dimensional estimates for the starlike Poincaré inequality (thesis Section 2.4)
-/

open MeasureTheory Metric Real Set
open scoped ENNReal

namespace DirichletPoincare

/-- Radial bound: if `A(ρ) ≤ ρ ∫₀^ρ W` where `A` is supported in `(0, R]`, and `W ≤ m` on
`(0, δ)`, then `∫ ρ A(ρ) dρ` is bounded by `R³ (δ m + δ⁻¹ ∫ s W(s) ds)`. -/
theorem radial_bound {A W : ℝ → ℝ≥0∞} {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) {m : ℝ≥0∞}
    (h1 : ∀ ρ, 0 < ρ → A ρ ≠ 0 →
      ρ ≤ R ∧ A ρ ≤ ENNReal.ofReal ρ * ∫⁻ s in Ioo 0 ρ, W s)
    (h2 : ∀ s ∈ Ioo 0 δ, W s ≤ m) :
    ∫⁻ ρ in Ioi 0, ENNReal.ofReal ρ * A ρ ≤
      ENNReal.ofReal (R ^ 3) * (ENNReal.ofReal δ * m +
        (ENNReal.ofReal δ)⁻¹ * ∫⁻ s in Ioi 0, ENNReal.ofReal s * W s) := by
  set J := ∫⁻ s in Ioi 0, ENNReal.ofReal s * W s with hJ
  set Q := ENNReal.ofReal δ * m + (ENNReal.ofReal δ)⁻¹ * J with hQ
  have hδ0 : ENNReal.ofReal δ ≠ 0 := (ENNReal.ofReal_pos.2 hδ).ne'
  have hsub : ∀ ρ, ∫⁻ s in Ioo 0 ρ, W s ≤ Q := by
    intro ρ
    have hA : ∫⁻ s in Ioo 0 δ, W s ≤ ENNReal.ofReal δ * m := by
      calc ∫⁻ s in Ioo 0 δ, W s ≤ ∫⁻ _ in Ioo 0 δ, m := setLIntegral_mono' measurableSet_Ioo h2
        _ = ENNReal.ofReal δ * m := by
          rw [setLIntegral_const, Real.volume_Ioo, sub_zero, mul_comm]
    have hB : ∫⁻ s in Ici δ, W s ≤ (ENNReal.ofReal δ)⁻¹ * J := by
      calc ∫⁻ s in Ici δ, W s
          ≤ ∫⁻ s in Ici δ, (ENNReal.ofReal δ)⁻¹ * (ENNReal.ofReal s * W s) := by
            refine setLIntegral_mono' measurableSet_Ici fun s hs => ?_
            rw [← mul_assoc]
            refine le_mul_of_one_le_left zero_le ?_
            calc (1 : ℝ≥0∞) = (ENNReal.ofReal δ)⁻¹ * ENNReal.ofReal δ :=
                  (ENNReal.inv_mul_cancel hδ0 ENNReal.ofReal_ne_top).symm
              _ ≤ _ := by gcongr; exact hs
        _ ≤ ∫⁻ s in Ioi 0, (ENNReal.ofReal δ)⁻¹ * (ENNReal.ofReal s * W s) :=
            lintegral_mono_set (fun s hs => lt_of_lt_of_le hδ hs)
        _ = (ENNReal.ofReal δ)⁻¹ * J := lintegral_const_mul' _ _ (by simpa using hδ0)
    have hcov : Ioo 0 ρ ⊆ Ioo 0 δ ∪ Ici δ := fun s hs => by
      by_cases h : s < δ
      · exact Or.inl ⟨hs.1, h⟩
      · exact Or.inr (not_lt.1 h)
    calc ∫⁻ s in Ioo 0 ρ, W s ≤ ∫⁻ s in Ioo 0 δ ∪ Ici δ, W s := lintegral_mono_set hcov
      _ ≤ (∫⁻ s in Ioo 0 δ, W s) + ∫⁻ s in Ici δ, W s := lintegral_union_le _ _ _
      _ ≤ Q := add_le_add hA hB
  have hpt : ∀ ρ ∈ Ioi (0 : ℝ), ENNReal.ofReal ρ * A ρ ≤
      (Ioc 0 R).indicator (fun _ => ENNReal.ofReal R * (ENNReal.ofReal R * Q)) ρ := by
    intro ρ hρ
    by_cases hA : A ρ = 0
    · simp [hA]
    · obtain ⟨hρR, hAρ⟩ := h1 ρ hρ hA
      rw [Set.indicator_of_mem (show ρ ∈ Ioc 0 R from ⟨hρ, hρR⟩)]
      calc ENNReal.ofReal ρ * A ρ ≤ ENNReal.ofReal ρ * (ENNReal.ofReal ρ * Q) := by
            gcongr
            exact hAρ.trans (by gcongr; exact hsub ρ)
        _ ≤ _ := by gcongr
  calc ∫⁻ ρ in Ioi 0, ENNReal.ofReal ρ * A ρ
      ≤ ∫⁻ ρ in Ioi 0, (Ioc 0 R).indicator
          (fun _ => ENNReal.ofReal R * (ENNReal.ofReal R * Q)) ρ :=
        setLIntegral_mono' measurableSet_Ioi hpt
    _ = ENNReal.ofReal R * (ENNReal.ofReal R * Q) * ENNReal.ofReal R := by
        rw [lintegral_indicator_const measurableSet_Ioc,
          Measure.restrict_apply measurableSet_Ioc, inter_eq_left.2 Ioc_subset_Ioi_self,
          Real.volume_Ioc, sub_zero]
    _ = ENNReal.ofReal (R ^ 3) * Q := by
        rw [ENNReal.ofReal_pow hR.le]
        ring

/-- Cauchy–Schwarz for an interval integral of a continuous function. -/
theorem sq_integral_le {v : ℝ → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hv : ContinuousOn v (Icc 0 ρ)) :
    (∫ s in (0 : ℝ)..ρ, v s) ^ 2 ≤ ρ * ∫ s in (0 : ℝ)..ρ, v s ^ 2 := by
  rcases hρ.eq_or_lt with rfl | hpos
  · simp
  have hv' : ContinuousOn v (uIcc 0 ρ) := by rwa [uIcc_of_le hρ]
  have hi1 : IntervalIntegrable v volume 0 ρ := hv'.intervalIntegrable
  have hi2 : IntervalIntegrable (fun s => v s ^ 2) volume 0 ρ :=
    (hv'.pow 2).intervalIntegrable
  set I := ∫ s in (0 : ℝ)..ρ, v s with hI
  set m := I / ρ with hm
  have hmono : ∫ s in (0 : ℝ)..ρ, (2 * m * v s - m ^ 2) ≤ ∫ s in (0 : ℝ)..ρ, v s ^ 2 :=
    intervalIntegral.integral_mono_on hρ
      ((hi1.const_mul (2 * m)).sub intervalIntegrable_const) hi2
      fun s _ => by nlinarith [sq_nonneg (v s - m)]
  have hlin : ∫ s in (0 : ℝ)..ρ, (2 * m * v s - m ^ 2) = 2 * m * I - ρ * m ^ 2 := by
    rw [intervalIntegral.integral_sub (hi1.const_mul (2 * m)) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    simp only [smul_eq_mul, sub_zero]
    rfl
  rw [hlin] at hmono
  have : 2 * m * I - ρ * m ^ 2 = I ^ 2 / ρ := by
    rw [hm]
    field_simp
    ring
  rw [this, div_le_iff₀ hpos] at hmono
  linarith

/-- Estimate of the increment of a holomorphic function along a ray in the domain. -/
theorem ray_estimate {f : ℂ → ℂ} {G : Set ℂ} (hG : IsOpen G) (hf : DifferentiableOn ℂ f G)
    {w₀ u : ℂ} (hu : ‖u‖ = 1) {ρ : ℝ} (hρ : 0 ≤ ρ) (hseg : ∀ s ∈ Icc 0 ρ, w₀ + s * u ∈ G) :
    ENNReal.ofReal (‖f (w₀ + ρ * u) - f w₀‖ ^ 2) ≤
      ENNReal.ofReal ρ * ∫⁻ s in Ioo 0 ρ, ENNReal.ofReal (‖deriv f (w₀ + s * u)‖ ^ 2) := by
  have hcont : ContinuousOn (fun s : ℝ => ‖deriv f (w₀ + s * u)‖) (Icc 0 ρ) := by
    refine ContinuousOn.norm ((hf.deriv hG).continuousOn.comp ?_ hseg)
    fun_prop
  have hcont' : ContinuousOn (fun s : ℝ => deriv f (w₀ + s * u) * u) (Icc 0 ρ) := by
    refine ContinuousOn.mul ((hf.deriv hG).continuousOn.comp ?_ hseg) continuousOn_const
    fun_prop
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) ρ,
      HasDerivAt (fun s : ℝ => f (w₀ + s * u)) (deriv f (w₀ + s * u) * u) s := by
    intro s hs
    rw [uIcc_of_le hρ] at hs
    have hfd : DifferentiableAt ℂ f (w₀ + s * u) := hf.differentiableAt (hG.mem_nhds (hseg s hs))
    have h1 : HasDerivAt (fun z : ℂ => w₀ + z * u) u (s : ℂ) := by
      simpa using ((hasDerivAt_id (s : ℂ)).mul_const u).const_add w₀
    exact (hfd.hasDerivAt.comp (s : ℂ) h1).comp_ofReal
  have hftc : ∫ s in (0 : ℝ)..ρ, deriv f (w₀ + s * u) * u = f (w₀ + ρ * u) - f w₀ := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcont'.intervalIntegrable_of_Icc hρ)
    simpa using this
  have hnorm : ‖f (w₀ + ρ * u) - f w₀‖ ≤ ∫ s in (0 : ℝ)..ρ, ‖deriv f (w₀ + s * u)‖ := by
    rw [← hftc]
    refine (intervalIntegral.norm_integral_le_integral_norm hρ).trans_eq ?_
    simp [hu]
  have hreal : ‖f (w₀ + ρ * u) - f w₀‖ ^ 2 ≤
      ρ * ∫ s in (0 : ℝ)..ρ, ‖deriv f (w₀ + s * u)‖ ^ 2 :=
    calc ‖f (w₀ + ρ * u) - f w₀‖ ^ 2 ≤ (∫ s in (0 : ℝ)..ρ, ‖deriv f (w₀ + s * u)‖) ^ 2 := by
          gcongr
      _ ≤ _ := sq_integral_le hρ hcont
  calc ENNReal.ofReal (‖f (w₀ + ρ * u) - f w₀‖ ^ 2)
      ≤ ENNReal.ofReal (ρ * ∫ s in (0 : ℝ)..ρ, ‖deriv f (w₀ + s * u)‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = _ := by
        rw [ENNReal.ofReal_mul hρ, intervalIntegral.integral_of_le hρ,
          integral_Ioc_eq_integral_Ioo, ofReal_integral_eq_lintegral_ofReal]
        · exact ((hcont.pow 2).integrableOn_Icc).mono_set Ioo_subset_Icc_self
        · exact Filter.Eventually.of_forall fun s => sq_nonneg _

end DirichletPoincare
