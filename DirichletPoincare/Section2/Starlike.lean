import DirichletPoincare.Definitions
import DirichletPoincare.Section2.StarlikeMain

/-!
# Poincaré inequality on starlike regions (thesis Section 2.4)
-/

open MeasureTheory Metric Real Set
open scoped ENNReal

namespace DirichletPoincare

/-- **Theorem 2.13** (thesis p. 15). Every bounded starlike region satisfies the analytic
Poincaré (2,2) inequality. -/
theorem poincare_of_starlike {G : Set ℂ} (hbdd : Bornology.IsBounded G)
    (hS : IsStarlikeRegion G) {z₀ : ℂ} (hz₀ : z₀ ∈ G) :
    PoincareInequality G z₀ := by
  obtain ⟨⟨hG, -⟩, w₀, hw₀, hstar⟩ := hS
  obtain ⟨ε, hε, hεG⟩ := Metric.isOpen_iff.1 hG w₀ hw₀
  obtain ⟨ε₂, hε₂, hε₂G⟩ := Metric.isOpen_iff.1 hG z₀ hz₀
  obtain ⟨δ, hδ, hball⟩ : ∃ δ : ℝ, 0 < δ ∧ ball w₀ (2 * δ) ⊆ G :=
    ⟨ε / 2, by positivity, by rwa [show 2 * (ε / 2) = ε by ring]⟩
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall w₀).1 hbdd
  have hR : 0 < max r 1 := lt_max_of_lt_right one_pos
  have hRb : ∀ z ∈ G, ‖z - w₀‖ ≤ max r 1 := fun z hz => by
    rw [← dist_eq_norm]
    exact (mem_closedBall.1 (hr hz)).trans (le_max_left _ _)
  set c₁ := ENNReal.ofReal (max r 1 ^ 3) * (ENNReal.ofReal (2 * π) * ENNReal.ofReal δ *
    (volume (ball (0 : ℂ) δ))⁻¹ + (ENNReal.ofReal δ)⁻¹) with hc₁
  have hc₁top : c₁ < ⊤ := by
    have h1 : (volume (ball (0 : ℂ) δ))⁻¹ < ⊤ :=
      ENNReal.inv_lt_top.2 (measure_ball_pos volume _ hδ)
    have h2 : (ENNReal.ofReal δ)⁻¹ < ⊤ := ENNReal.inv_lt_top.2 (ENNReal.ofReal_pos.2 hδ)
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2
      ⟨ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) h1, h2⟩)
  set V₁ := volume (ball z₀ ε₂) with hV₁
  have hV₁0 : V₁ ≠ 0 := (measure_ball_pos volume z₀ hε₂).ne'
  have hV₁top : V₁ ≠ ⊤ := measure_ball_lt_top.ne
  have hGtop : volume G < ⊤ := hbdd.measure_lt_top
  refine ⟨2 * c₁ + 2 * volume G * c₁ * V₁⁻¹, ?_, ?_⟩
  · have hinv : V₁⁻¹ < ⊤ := ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hV₁0)
    have h2 : (2 : ℝ≥0∞) < ⊤ := by simp
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top h2 hc₁top,
      ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top h2 hGtop) hc₁top) hinv⟩
  · rintro f ⟨hf, hz, -⟩
    set a := f w₀ with ha
    have hI : ∫⁻ z in G, ENNReal.ofReal (‖f z - a‖ ^ 2) ≤ c₁ * dirichletEnergy G f :=
      lintegral_sub_center_le hG hstar hδ hball hR hRb hf
    have hIa : ENNReal.ofReal (‖a‖ ^ 2) * V₁ ≤ ∫⁻ z in G, ENNReal.ofReal (‖f z - a‖ ^ 2) := by
      have := sq_mul_volume_le (g := fun z => f z - a) (w := z₀) hε₂
        ((hf.mono hε₂G).sub_const a)
      simp only [hz, zero_sub, norm_neg] at this
      exact this.trans (lintegral_mono_set hε₂G)
    have hab : ENNReal.ofReal (‖a‖ ^ 2) ≤ c₁ * dirichletEnergy G f / V₁ :=
      (ENNReal.le_div_iff_mul_le (Or.inl hV₁0) (Or.inl hV₁top)).2 (hIa.trans hI)
    have hpt : ∀ z, ENNReal.ofReal (‖f z‖ ^ 2) ≤
        2 * ENNReal.ofReal (‖f z - a‖ ^ 2) + 2 * ENNReal.ofReal (‖a‖ ^ 2) := by
      intro z
      have h1 := norm_add_le (f z - a) a
      rw [sub_add_cancel] at h1
      have h2 : ‖f z‖ ^ 2 ≤ (‖f z - a‖ + ‖a‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      have h3 : ‖f z‖ ^ 2 ≤ 2 * ‖f z - a‖ ^ 2 + 2 * ‖a‖ ^ 2 := by
        nlinarith [sq_nonneg (‖f z - a‖ - ‖a‖)]
      calc ENNReal.ofReal (‖f z‖ ^ 2) ≤ ENNReal.ofReal (2 * ‖f z - a‖ ^ 2 + 2 * ‖a‖ ^ 2) :=
            ENNReal.ofReal_le_ofReal h3
        _ = _ := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
            simp
    unfold bergmanNormSq
    calc ∫⁻ z in G, ENNReal.ofReal (‖f z‖ ^ 2)
        ≤ ∫⁻ z in G, (2 * ENNReal.ofReal (‖f z - a‖ ^ 2) + 2 * ENNReal.ofReal (‖a‖ ^ 2)) :=
          lintegral_mono hpt
      _ = 2 * (∫⁻ z in G, ENNReal.ofReal (‖f z - a‖ ^ 2)) +
            2 * ENNReal.ofReal (‖a‖ ^ 2) * volume G := by
          rw [lintegral_add_right' _ aemeasurable_const,
            lintegral_const_mul' _ _ (by simp), setLIntegral_const]
      _ ≤ 2 * (c₁ * dirichletEnergy G f) +
            2 * (c₁ * dirichletEnergy G f / V₁) * volume G := by gcongr
      _ = _ := by
          rw [div_eq_mul_inv]
          ring

end DirichletPoincare
