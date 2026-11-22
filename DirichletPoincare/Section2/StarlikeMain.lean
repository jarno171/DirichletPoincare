import DirichletPoincare.Section2.StarlikeAux

/-!
# Poincaré inequality on starlike regions (thesis Section 2.4)

The proof avoids Lemma 2.10. Polar coordinates around the star centre `w₀` reduce
`∫_G ‖f - f(w₀)‖²` to a one-dimensional Hardy-type estimate along rays. The singularity at `w₀` is
controlled with the area mean-value estimate applied to `f'`, and the value `f(w₀)` is then
controlled by the normalisation `f(z₀) = 0` and the same estimate applied to `f - f(w₀)`.
-/

open MeasureTheory Metric Real Set
open scoped ENNReal

namespace DirichletPoincare

theorem measurable_indicator_of_continuousOn {G : Set ℂ} (hG : IsOpen G) {H : ℂ → ℝ≥0∞}
    (hH : ContinuousOn H G) : Measurable (G.indicator H) := by
  classical
  have := hH.measurable_piecewise (g := fun _ => 0) continuousOn_const hG.measurableSet
  convert this using 1
  ext z
  by_cases hz : z ∈ G <;> simp [hz]

theorem mem_of_starlike_ray {G : Set ℂ} {w₀ u : ℂ} (hstar : ∀ z ∈ G, segment ℝ w₀ z ⊆ G)
    {ρ : ℝ} (hρ : 0 < ρ) (hz : w₀ + ρ * u ∈ G) {s : ℝ} (hs : s ∈ Icc 0 ρ) :
    w₀ + s * u ∈ G := by
  refine hstar _ hz ⟨1 - s / ρ, s / ρ, ?_, div_nonneg hs.1 hρ.le, by ring, ?_⟩
  · rw [sub_nonneg, div_le_one hρ]
    exact hs.2
  · rw [Complex.real_smul, Complex.real_smul]
    have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
    push_cast
    field_simp
    ring

/-- Key estimate: on a bounded starlike open set with centre `w₀`, the integral of
`‖f - f(w₀)‖²` is controlled by the Dirichlet energy of `f`. -/
theorem lintegral_sub_center_le {G : Set ℂ} (hG : IsOpen G) {w₀ : ℂ}
    (hstar : ∀ z ∈ G, segment ℝ w₀ z ⊆ G) {δ : ℝ} (hδ : 0 < δ) (hball : ball w₀ (2 * δ) ⊆ G)
    {R : ℝ} (hR : 0 < R) (hRb : ∀ z ∈ G, ‖z - w₀‖ ≤ R) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f G) :
    ∫⁻ z in G, ENNReal.ofReal (‖f z - f w₀‖ ^ 2) ≤
      ENNReal.ofReal (R ^ 3) * (ENNReal.ofReal (2 * π) * ENNReal.ofReal δ *
        (volume (ball (0 : ℂ) δ))⁻¹ + (ENNReal.ofReal δ)⁻¹) *
      ∫⁻ z in G, ENNReal.ofReal (‖deriv f z‖ ^ 2) := by
  set E := ∫⁻ z in G, ENNReal.ofReal (‖deriv f z‖ ^ 2) with hE
  set V₀ := volume (ball (0 : ℂ) δ) with hV₀
  have hV₀ne : V₀ ≠ 0 := (measure_ball_pos volume (0 : ℂ) hδ).ne'
  have hV₀top : V₀ ≠ ∞ := measure_ball_lt_top.ne
  have hvol : ∀ u : ℂ, volume (ball u δ) = V₀ := fun u => by
    rw [hV₀, Complex.volume_ball, Complex.volume_ball]
  have hfd : DifferentiableOn ℂ (deriv f) G := hf.deriv hG
  -- pointwise bound on `f'` near the centre
  have hM : ∀ u ∈ ball w₀ δ, ENNReal.ofReal (‖deriv f u‖ ^ 2) ≤ E / V₀ := by
    intro u hu
    have hsub : ball u δ ⊆ G := fun x hx => hball (by
      rw [mem_ball] at hu hx ⊢
      calc dist x w₀ ≤ dist x u + dist u w₀ := dist_triangle _ _ _
        _ < 2 * δ := by linarith)
    rw [ENNReal.le_div_iff_mul_le (Or.inl hV₀ne) (Or.inl hV₀top)]
    calc ENNReal.ofReal (‖deriv f u‖ ^ 2) * V₀
        = ENNReal.ofReal (‖deriv f u‖ ^ 2) * volume (ball u δ) := by rw [hvol]
      _ ≤ ∫⁻ z in ball u δ, ENNReal.ofReal (‖deriv f z‖ ^ 2) :=
          sq_mul_volume_le hδ (hfd.mono hsub)
      _ ≤ E := lintegral_mono_set hsub
  have hH₁ : ContinuousOn (fun z => ENNReal.ofReal (‖f z - f w₀‖ ^ 2)) G :=
    ENNReal.continuous_ofReal.comp_continuousOn
      ((hf.continuousOn.sub continuousOn_const).norm.pow 2)
  have hH₂ : ContinuousOn (fun z => ENNReal.ofReal (‖deriv f z‖ ^ 2)) G :=
    ENNReal.continuous_ofReal.comp_continuousOn (hfd.continuousOn.norm.pow 2)
  set Atil := G.indicator (fun z => ENNReal.ofReal (‖f z - f w₀‖ ^ 2)) with hAtil
  set Wtil := G.indicator (fun z => ENNReal.ofReal (‖deriv f z‖ ^ 2)) with hWtil
  have hAtilm : Measurable Atil := measurable_indicator_of_continuousOn hG hH₁
  have hWtilm : Measurable Wtil := measurable_indicator_of_continuousOn hG hH₂
  set J : ℝ → ℝ≥0∞ := fun θ => ∫⁻ ρ in Ioi 0, ENNReal.ofReal ρ * Wtil (circleMap w₀ ρ θ) with hJ
  have hJint : ∫⁻ θ in Ioo (-π) π, J θ = E := by
    rw [hE, ← lintegral_indicator hG.measurableSet, ← lintegral_polar_angle_first hWtilm w₀]
  have hper : ∀ θ : ℝ, ∫⁻ ρ in Ioi 0, ENNReal.ofReal ρ * Atil (circleMap w₀ ρ θ) ≤
      ENNReal.ofReal (R ^ 3) * (ENNReal.ofReal δ * (E / V₀) + (ENNReal.ofReal δ)⁻¹ * J θ) := by
    intro θ
    refine radial_bound (W := fun s => Wtil (circleMap w₀ s θ)) hR hδ (m := E / V₀) ?_ ?_
    · intro ρ hρ hA
      have hzG : circleMap w₀ ρ θ ∈ G := by
        by_contra hnot
        exact hA (by simp [hAtil, Set.indicator_of_notMem hnot])
      have hnorm : ‖circleMap w₀ ρ θ - w₀‖ = ρ := by
        rw [← dist_eq_norm, mem_sphere.1 (circleMap_mem_sphere' w₀ ρ θ), abs_of_pos hρ]
      refine ⟨by have := hRb _ hzG; rwa [hnorm] at this, ?_⟩
      have hu : ‖Complex.exp (θ * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
      have hseg : ∀ s ∈ Icc 0 ρ, w₀ + s * Complex.exp (θ * Complex.I) ∈ G :=
        fun s hs => mem_of_starlike_ray hstar hρ hzG hs
      have hray := ray_estimate hG hf hu hρ.le hseg
      have hAeq : Atil (circleMap w₀ ρ θ) =
          ENNReal.ofReal (‖f (w₀ + ρ * Complex.exp (θ * Complex.I)) - f w₀‖ ^ 2) := by
        simp only [hAtil, Set.indicator_of_mem hzG]
        rfl
      rw [hAeq]
      refine hray.trans (mul_le_mul' le_rfl
        (setLIntegral_congr_fun measurableSet_Ioo fun s hs => ?_).le)
      have hsG : circleMap w₀ s θ ∈ G :=
        mem_of_starlike_ray hstar hρ hzG ⟨hs.1.le, hs.2.le⟩
      simp only [hWtil, Set.indicator_of_mem hsG]
      rfl
    · intro s hs
      have hsb : circleMap w₀ s θ ∈ ball w₀ δ := by
        rw [mem_ball, mem_sphere.1 (circleMap_mem_sphere' w₀ s θ), abs_of_pos hs.1]
        exact hs.2
      have hsG : circleMap w₀ s θ ∈ G := hball (ball_subset_ball (by linarith) hsb)
      simpa [hWtil, Set.indicator_of_mem hsG] using hM _ hsb
  calc ∫⁻ z in G, ENNReal.ofReal (‖f z - f w₀‖ ^ 2)
      = ∫⁻ z, Atil z := (lintegral_indicator hG.measurableSet _).symm
    _ = ∫⁻ θ in Ioo (-π) π, ∫⁻ ρ in Ioi 0, ENNReal.ofReal ρ * Atil (circleMap w₀ ρ θ) :=
        lintegral_polar_angle_first hAtilm w₀
    _ ≤ ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal (R ^ 3) *
          (ENNReal.ofReal δ * (E / V₀) + (ENNReal.ofReal δ)⁻¹ * J θ) :=
        lintegral_mono hper
    _ = ENNReal.ofReal (R ^ 3) * (ENNReal.ofReal δ * (E / V₀) * ENNReal.ofReal (2 * π) +
          (ENNReal.ofReal δ)⁻¹ * E) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_left measurable_const, setLIntegral_const, Real.volume_Ioo,
          lintegral_const_mul' _ _ (by simpa using (ENNReal.ofReal_pos.2 hδ).ne'), hJint]
        congr 3
        ring_nf
    _ = _ := by
        rw [div_eq_mul_inv]
        ring

end DirichletPoincare
