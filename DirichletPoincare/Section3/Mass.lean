import DirichletPoincare.Section3.Estimates

/-!
# Lower bounds for `‖g_m - c‖` (thesis estimates (3.13)–(3.14))
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace DirichletPoincare

theorem norm_gm (m : ℕ) (z : ℂ) : ‖gm m z‖ = ‖1 - z ^ 2‖ ^ m := by
  unfold gm
  rw [norm_pow]

theorem norm_gm_le_of_mem_Dsc_zero {m : ℕ} (hm : 4 ≤ m) {z : ℂ} (hz : z ∈ Dsc 0) :
    ‖gm m z‖ ≤ 1 / 8 := by
  rw [Dsc_zero_eq] at hz
  have h := norm_one_sub_sq_le_of_mem_ball hz
  rw [norm_gm]
  calc ‖1 - z ^ 2‖ ^ m ≤ (9 / 16 : ℝ) ^ m := pow_le_pow_left₀ (norm_nonneg _) h m
    _ ≤ (9 / 16 : ℝ) ^ 4 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
    _ ≤ 1 / 8 := by norm_num

theorem norm_gm_ge {m : ℕ} (hm : 4 ≤ m) {z : ℂ} (hz : ‖z‖ ^ 2 ≤ 3 / (m : ℝ) ^ 4) :
    1 / 2 ≤ ‖gm m z‖ := by
  have hm' : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hpos : 0 < (m : ℝ) ^ 4 := by positivity
  have h1 : 1 - 3 / (m : ℝ) ^ 4 ≤ ‖1 - z ^ 2‖ := by
    have := norm_sub_norm_le (1 : ℂ) (z ^ 2)
    rw [norm_one, norm_pow] at this
    linarith
  have hm4 : (256 : ℝ) ≤ (m : ℝ) ^ 4 := by
    calc (256 : ℝ) = 4 ^ 4 := by norm_num
      _ ≤ (m : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) hm' 4
  have hdiv : 3 / (m : ℝ) ^ 4 ≤ 1 := by
    rw [div_le_one hpos]
    linarith
  have h0 : 0 ≤ 1 - 3 / (m : ℝ) ^ 4 := by linarith
  have hbern : 1 + (m : ℝ) * (-(3 / (m : ℝ) ^ 4)) ≤ (1 + -(3 / (m : ℝ) ^ 4)) ^ m :=
    one_add_mul_le_pow (by linarith) m
  have hlow : 1 / 2 ≤ 1 + (m : ℝ) * (-(3 / (m : ℝ) ^ 4)) := by
    have : (m : ℝ) * (3 / (m : ℝ) ^ 4) = 3 / (m : ℝ) ^ 3 := by
      field_simp
    have h3 : 3 / (m : ℝ) ^ 3 ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (64 : ℝ) ≤ (m : ℝ) ^ 3 := by
        calc (64 : ℝ) = 4 ^ 3 := by norm_num
          _ ≤ (m : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hm' 3
      linarith
    nlinarith
  rw [norm_gm]
  calc (1 / 2 : ℝ) ≤ (1 + -(3 / (m : ℝ) ^ 4)) ^ m := hlow.trans hbern
    _ = (1 - 3 / (m : ℝ) ^ 4) ^ m := by rw [← sub_eq_add_neg]
    _ ≤ ‖1 - z ^ 2‖ ^ m := pow_le_pow_left₀ h0 h1 m

theorem norm_gm_ge_of_mem_Dsc {m n : ℕ} (hm : 4 ≤ m) (hcn : cc n = 1 / (m : ℝ) ^ 2) {z : ℂ}
    (hz : z ∈ Dsc n) : 1 / 2 ≤ ‖gm m z‖ := by
  refine norm_gm_ge hm ?_
  have h := norm_lt_of_mem_Dsc hz
  have hc := cc_pos n
  rw [hcn] at h
  have h2 : ‖z‖ ^ 2 ≤ (5 * (1 / (m : ℝ) ^ 2) / 4) ^ 2 := by
    gcongr
  refine h2.trans ?_
  have : (5 * (1 / (m : ℝ) ^ 2) / 4) ^ 2 = 25 / 16 / (m : ℝ) ^ 4 := by
    field_simp
    ring
  rw [this]
  have : 0 < (m : ℝ) ^ 4 := by
    have : (4 : ℝ) ≤ m := by exact_mod_cast hm
    positivity
  gcongr
  norm_num

/-- For any constant `c`, `g_m - c` is at least `1/8` on one of two sets, where `g_m` is small
on the first and large on the second. -/
theorem big_diff_or {m : ℕ} {A₀ A₁ : Set ℂ} (h0 : ∀ z ∈ A₀, ‖gm m z‖ ≤ 1 / 8)
    (h1 : ∀ z ∈ A₁, 1 / 2 ≤ ‖gm m z‖) (c : ℂ) :
    (∀ z ∈ A₀, 1 / 8 ≤ ‖gm m z - c‖) ∨ (∀ z ∈ A₁, 1 / 8 ≤ ‖gm m z - c‖) := by
  by_cases hc : 1 / 4 ≤ ‖c‖
  · left
    intro z hz
    have := norm_sub_norm_le c (gm m z)
    rw [norm_sub_rev] at this
    linarith [h0 z hz]
  · right
    intro z hz
    have := norm_sub_norm_le (gm m z) c
    linarith [h1 z hz]

/-- Lower bound for the integral of `‖g_m - c‖²` from a set where `‖g_m - c‖ ≥ 1/8`. -/
theorem lintegral_sq_ge {G A : Set ℂ} (hA : MeasurableSet A) (hAG : A ⊆ G) {f : ℂ → ℂ}
    (h : ∀ z ∈ A, 1 / 8 ≤ ‖f z‖) :
    ENNReal.ofReal (1 / 64) * volume A ≤ ∫⁻ z in G, ENNReal.ofReal (‖f z‖ ^ 2) := by
  calc ENNReal.ofReal (1 / 64) * volume A = ∫⁻ _ in A, ENNReal.ofReal (1 / 64) :=
        (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ z in A, ENNReal.ofReal (‖f z‖ ^ 2) := by
        refine setLIntegral_mono' hA fun z hz => ENNReal.ofReal_le_ofReal ?_
        have := h z hz
        nlinarith
    _ ≤ _ := lintegral_mono_set hAG

end DirichletPoincare
