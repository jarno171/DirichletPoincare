import DirichletPoincare.Section3.Region

/-!
# Pointwise estimates for `g_m(z) = (1 - z²)^m` (thesis Section 3.1)
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace DirichletPoincare

/-- The test functions `g_m(z) = (1 - z²)^m`. -/
noncomputable def gm (m : ℕ) (z : ℂ) : ℂ := (1 - z ^ 2) ^ m

theorem gm_differentiable (m : ℕ) : Differentiable ℂ (gm m) := by
  unfold gm
  fun_prop

theorem hasDerivAt_gm (m : ℕ) (z : ℂ) :
    HasDerivAt (gm m) (m * (1 - z ^ 2) ^ (m - 1) * (-(2 * z))) z := by
  have h1 : HasDerivAt (fun z : ℂ => 1 - z ^ 2) (-(2 * z)) z := by
    simpa using ((hasDerivAt_pow 2 z).const_sub 1)
  exact h1.pow m

theorem norm_deriv_gm_sq (m : ℕ) (z : ℂ) :
    ‖deriv (gm m) z‖ ^ 2 = 4 * (m : ℝ) ^ 2 * ‖z‖ ^ 2 * (‖1 - z ^ 2‖ ^ 2) ^ (m - 1) := by
  rw [(hasDerivAt_gm m z).deriv, norm_mul, norm_mul, norm_neg, norm_mul, norm_pow]
  simp only [Complex.norm_natCast, Complex.norm_ofNat]
  rw [mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm (m - 1) 2, pow_mul]
  ring

theorem sq_norm_one_sub_sq (z : ℂ) :
    ‖1 - z ^ 2‖ ^ 2 = (1 - z.re ^ 2 + z.im ^ 2) ^ 2 + (2 * z.re * z.im) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [pow_two, Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.sub_im,
    Complex.one_im, Complex.mul_im]
  ring

/-- Points of the thin cone `|y| ≤ x/3`, `0 < x ≤ 1`. -/
def Cone (z : ℂ) : Prop := 0 < z.re ∧ z.re ≤ 1 ∧ 9 * z.im ^ 2 ≤ z.re ^ 2

theorem Cone.norm_sq_le {z : ℂ} (h : Cone z) : ‖z‖ ^ 2 ≤ 2 := by
  obtain ⟨h0, h1, h2⟩ := h
  rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith

theorem Cone.sq_norm_one_sub_sq_le {z : ℂ} (h : Cone z) :
    ‖1 - z ^ 2‖ ^ 2 ≤ 1 - z.re ^ 2 / 2 := by
  obtain ⟨h0, h1, h2⟩ := h
  rw [sq_norm_one_sub_sq]
  have hx2 : z.re ^ 2 ≤ 1 := by nlinarith
  have hx4 : z.re ^ 4 ≤ z.re ^ 2 := by nlinarith
  have hy : 0 ≤ z.im ^ 2 := sq_nonneg _
  nlinarith [sq_nonneg (z.im ^ 2 - z.re ^ 2 / 9), mul_nonneg hy (sq_nonneg z.re)]

theorem Cone.sq_norm_one_sub_sq_le_one {z : ℂ} (h : Cone z) : ‖1 - z ^ 2‖ ^ 2 ≤ 1 := by
  refine h.sq_norm_one_sub_sq_le.trans ?_
  linarith [sq_nonneg z.re]

/-- Near `1` the function `1 - z²` is small. -/
theorem norm_one_sub_sq_le_of_mem_ball {z : ℂ} (hz : z ∈ ball (1 : ℂ) (1 / 4)) :
    ‖1 - z ^ 2‖ ≤ 9 / 16 := by
  rw [mem_ball, dist_eq_norm] at hz
  have h1 : ‖1 - z‖ < 1 / 4 := by rwa [norm_sub_rev]
  have h2 : ‖1 + z‖ ≤ 9 / 4 := by
    have : 1 + z = 2 + (z - 1) := by ring
    rw [this]
    calc ‖(2 : ℂ) + (z - 1)‖ ≤ ‖(2 : ℂ)‖ + ‖z - 1‖ := norm_add_le _ _
      _ ≤ 9 / 4 := by norm_num; linarith
  have : 1 - z ^ 2 = (1 - z) * (1 + z) := by ring
  rw [this, norm_mul]
  nlinarith [norm_nonneg (1 - z), norm_nonneg (1 + z)]

theorem norm_sq_of_mem_ball_one {z : ℂ} (hz : z ∈ ball (1 : ℂ) (1 / 4)) : ‖z‖ ^ 2 ≤ 25 / 16 := by
  rw [mem_ball, dist_eq_norm] at hz
  have : ‖z‖ ≤ 5 / 4 := by
    calc ‖z‖ = ‖(z - 1) + 1‖ := by ring_nf
      _ ≤ ‖z - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 5 / 4 := by simp; linarith
  nlinarith [norm_nonneg z]

theorem volume_ball_eq (w : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume (ball w r) = ENNReal.ofReal (Real.pi * r ^ 2) := by
  rw [Complex.volume_ball, ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hr, mul_comm]
  congr 1
  exact (ENNReal.ofReal_eq_coe_nnreal Real.pi_pos.le).symm

/-- Area of an axis-parallel rectangle centred on the real axis. -/
theorem volume_rect (a b h : ℝ) :
    volume {z : ℂ | a < z.re ∧ z.re < b ∧ |z.im| < h} =
      ENNReal.ofReal (b - a) * ENNReal.ofReal (2 * h) := by
  have hset : {z : ℂ | a < z.re ∧ z.re < b ∧ |z.im| < h} =
      Complex.measurableEquivRealProd ⁻¹' (Ioo a b ×ˢ Ioo (-h) h) := by
    ext z
    simp only [mem_ofPred_eq, mem_preimage, mem_prod, mem_Ioo, abs_lt]
    simp [Complex.measurableEquivRealProd]
    tauto
  rw [hset, Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Ioo.prod measurableSet_Ioo).nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
  congr 2
  ring

theorem lintegral_le_of_pointwise {S : Set ℂ} (hS : MeasurableSet S) {F : ℂ → ℝ≥0∞}
    {B : ℝ≥0∞} (h : ∀ z ∈ S, F z ≤ B) : ∫⁻ z in S, F z ≤ B * volume S := by
  calc ∫⁻ z in S, F z ≤ ∫⁻ _ in S, B := setLIntegral_mono' hS h
    _ = B * volume S := setLIntegral_const _ _

/-- The integrand of the Dirichlet energy of `g_m`. -/
noncomputable def en (m : ℕ) (z : ℂ) : ℝ≥0∞ := ENNReal.ofReal (‖deriv (gm m) z‖ ^ 2)

theorem cone_of_mem_Dsc {k : ℕ} (hk : 1 ≤ k) {z : ℂ} (hz : z ∈ Dsc k) :
    Cone z ∧ 3 * cc k / 4 < z.re := by
  have hc := cc_pos k
  have hc1 := cc_le_quarter k hk
  have hd : ‖z - ((cc k : ℝ) : ℂ)‖ < cc k / 4 := by
    rwa [Dsc, mem_ball, dist_eq_norm] at hz
  have hre : |z.re - cc k| < cc k / 4 := by
    have := Complex.abs_re_le_norm (z - ((cc k : ℝ) : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    linarith
  have him : |z.im| < cc k / 4 := by
    have := Complex.abs_im_le_norm (z - ((cc k : ℝ) : ℂ))
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
    linarith
  rw [abs_lt] at hre
  have him2 : z.im ^ 2 < (cc k / 4) ^ 2 := by
    have := sq_lt_sq' (abs_lt.1 him).1 (abs_lt.1 him).2
    exact this
  have hre0 : 3 * cc k / 4 < z.re := by linarith
  refine ⟨⟨by linarith, by linarith, ?_⟩, hre0⟩
  nlinarith

theorem cone_of_mem_Sk {k : ℕ} (hk : 1 ≤ k) {z : ℂ} (hz : z ∈ Sk k) :
    Cone z ∧ 3 * cc k / 4 < z.re := by
  have hc := cc_pos k
  have hh1 := hh_le k hk
  obtain ⟨h1, h2, h3⟩ := hz
  have him2 : z.im ^ 2 < (cc k / 4) ^ 2 := by
    have := sq_lt_sq' (abs_lt.1 (h3.trans_le hh1)).1 (abs_lt.1 (h3.trans_le hh1)).2
    exact this
  refine ⟨⟨by linarith, h2.le, ?_⟩, by linarith⟩
  nlinarith

theorem Dsc_zero_eq : Dsc 0 = ball (1 : ℂ) (1 / 4) := by
  simp [Dsc, cc_zero]

theorem volume_Dsc_zero_le : volume (Dsc 0) ≤ 1 := by
  rw [Dsc_zero_eq, volume_ball_eq _ (by norm_num), ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [Real.pi_lt_four])

theorem volume_Dsc_le (k : ℕ) : volume (Dsc k) ≤ 1 := by
  have hc := cc_pos k
  have hc1 := cc_le_one k
  rw [Dsc, volume_ball_eq _ (by positivity), ← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  have : (cc k / 4) ^ 2 ≤ 1 / 16 := by nlinarith
  nlinarith [Real.pi_lt_four, sq_nonneg (cc k / 4)]

theorem volume_Sk_le (k : ℕ) : volume (Sk k) ≤ 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Sk_zero, measure_empty]
    exact zero_le
  have hc := cc_pos k
  have hc1 := cc_le_quarter k hk
  have hh1 := hh_le k hk
  have := volume_rect (cc k) 1 (hh k)
  rw [Sk, this, ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  have := hh_pos k
  nlinarith
theorem energy_D0 (m : ℕ) :
    ∫⁻ z in Dsc 0, en m z ≤ ENNReal.ofReal (7 * (m : ℝ) ^ 2 * ((9 / 16 : ℝ) ^ 2) ^ (m - 1)) := by
  calc ∫⁻ z in Dsc 0, en m z
      ≤ ENNReal.ofReal (7 * (m : ℝ) ^ 2 * ((9 / 16 : ℝ) ^ 2) ^ (m - 1)) * volume (Dsc 0) := by
        refine lintegral_le_of_pointwise (isOpen_Dsc 0).measurableSet fun z hz => ?_
        rw [Dsc_zero_eq] at hz
        unfold en
        refine ENNReal.ofReal_le_ofReal ?_
        rw [norm_deriv_gm_sq]
        have h1 := norm_one_sub_sq_le_of_mem_ball hz
        have h2 := norm_sq_of_mem_ball_one hz
        have h3 : (‖1 - z ^ 2‖ ^ 2) ^ (m - 1) ≤ ((9 / 16 : ℝ) ^ 2) ^ (m - 1) := by
          gcongr
        have h4 : 0 ≤ (‖1 - z ^ 2‖ ^ 2) ^ (m - 1) := by positivity
        have h5 : 0 ≤ ((9 / 16 : ℝ) ^ 2) ^ (m - 1) := by positivity
        have hm2 : 0 ≤ (m : ℝ) ^ 2 := by positivity
        calc 4 * (m : ℝ) ^ 2 * ‖z‖ ^ 2 * (‖1 - z ^ 2‖ ^ 2) ^ (m - 1)
            ≤ 4 * (m : ℝ) ^ 2 * (25 / 16) * ((9 / 16 : ℝ) ^ 2) ^ (m - 1) := by gcongr
          _ ≤ _ := by nlinarith [mul_nonneg hm2 h5]
    _ ≤ ENNReal.ofReal (7 * (m : ℝ) ^ 2 * ((9 / 16 : ℝ) ^ 2) ^ (m - 1)) * 1 :=
        mul_le_mul' le_rfl volume_Dsc_zero_le
    _ = _ := mul_one _

/-- Energy of a piece contained in the cone, at distance at least `ξ` from the imaginary axis. -/
theorem energy_cone_piece {S : Set ℂ} (hS : MeasurableSet S) (hvol : volume S ≤ 1) (m : ℕ)
    {ξ : ℝ} (hξ : 0 < ξ) (hcone : ∀ z ∈ S, Cone z ∧ ξ < z.re) :
    ∫⁻ z in S, en m z ≤ ENNReal.ofReal (8 * (m : ℝ) ^ 2 * (1 - ξ ^ 2 / 2) ^ (m - 1)) := by
  calc ∫⁻ z in S, en m z
      ≤ ENNReal.ofReal (8 * (m : ℝ) ^ 2 * (1 - ξ ^ 2 / 2) ^ (m - 1)) * volume S := by
        refine lintegral_le_of_pointwise hS fun z hz => ?_
        obtain ⟨hc, hx⟩ := hcone z hz
        unfold en
        refine ENNReal.ofReal_le_ofReal ?_
        rw [norm_deriv_gm_sq]
        have h1 : ‖1 - z ^ 2‖ ^ 2 ≤ 1 - ξ ^ 2 / 2 := by
          refine hc.sq_norm_one_sub_sq_le.trans ?_
          nlinarith
        have h3 : (‖1 - z ^ 2‖ ^ 2) ^ (m - 1) ≤ (1 - ξ ^ 2 / 2) ^ (m - 1) := by gcongr
        have h2 := hc.norm_sq_le
        have h4 : 0 ≤ (‖1 - z ^ 2‖ ^ 2) ^ (m - 1) := by positivity
        have hm2 : 0 ≤ (m : ℝ) ^ 2 := by positivity
        have h6 : 0 ≤ (1 - ξ ^ 2 / 2) ^ (m - 1) := h4.trans h3
        calc 4 * (m : ℝ) ^ 2 * ‖z‖ ^ 2 * (‖1 - z ^ 2‖ ^ 2) ^ (m - 1)
            ≤ 4 * (m : ℝ) ^ 2 * 2 * (1 - ξ ^ 2 / 2) ^ (m - 1) := by gcongr
          _ = _ := by ring
    _ ≤ ENNReal.ofReal (8 * (m : ℝ) ^ 2 * (1 - ξ ^ 2 / 2) ^ (m - 1)) * 1 :=
        mul_le_mul' le_rfl hvol
    _ = _ := mul_one _

theorem norm_lt_of_mem_Dsc {k : ℕ} {z : ℂ} (hz : z ∈ Dsc k) : ‖z‖ < 5 * cc k / 4 := by
  have hd : ‖z - ((cc k : ℝ) : ℂ)‖ < cc k / 4 := by
    rwa [Dsc, mem_ball, dist_eq_norm] at hz
  have h2 : ‖((cc k : ℝ) : ℂ)‖ = cc k := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (cc_pos k)]
  calc ‖z‖ = ‖(z - ((cc k : ℝ) : ℂ)) + ((cc k : ℝ) : ℂ)‖ := by ring_nf
    _ ≤ ‖z - ((cc k : ℝ) : ℂ)‖ + ‖((cc k : ℝ) : ℂ)‖ := norm_add_le _ _
    _ < 5 * cc k / 4 := by rw [h2]; linarith

theorem energy_inner_D (m n : ℕ) (hn : 1 ≤ n) :
    ∫⁻ z in ⋃ k, ⋃ (_ : n ≤ k), Dsc k, en m z ≤
      ENNReal.ofReal (31 * (m : ℝ) ^ 2 * cc n ^ 4) := by
  have hVo : IsOpen (⋃ k, ⋃ (_ : n ≤ k), Dsc k) :=
    isOpen_iUnion fun k => isOpen_iUnion fun _ => isOpen_Dsc k
  have hn0 := cc_pos n
  have hVsub : (⋃ k, ⋃ (_ : n ≤ k), Dsc k) ⊆ ball (0 : ℂ) (5 * cc n / 4) := by
    intro z hz
    obtain ⟨k, hkn, hz⟩ := mem_iUnion₂.1 hz
    rw [mem_ball, dist_zero_right]
    have := norm_lt_of_mem_Dsc hz
    have := cc_antitone hkn
    linarith
  have hvol : volume (⋃ k, ⋃ (_ : n ≤ k), Dsc k) ≤ ENNReal.ofReal (Real.pi * (5 * cc n / 4) ^ 2) :=
    (measure_mono hVsub).trans_eq (volume_ball_eq _ (by positivity))
  calc ∫⁻ z in ⋃ k, ⋃ (_ : n ≤ k), Dsc k, en m z
      ≤ ENNReal.ofReal (4 * (m : ℝ) ^ 2 * (5 * cc n / 4) ^ 2) *
          volume (⋃ k, ⋃ (_ : n ≤ k), Dsc k) := by
        refine lintegral_le_of_pointwise hVo.measurableSet fun z hz => ?_
        obtain ⟨k, hkn, hz⟩ := mem_iUnion₂.1 hz
        obtain ⟨hc, -⟩ := cone_of_mem_Dsc (hn.trans hkn) hz
        have hzn : ‖z‖ < 5 * cc n / 4 := by
          have := norm_lt_of_mem_Dsc hz
          have := cc_antitone hkn
          linarith
        unfold en
        refine ENNReal.ofReal_le_ofReal ?_
        rw [norm_deriv_gm_sq]
        have h1 : (‖1 - z ^ 2‖ ^ 2) ^ (m - 1) ≤ 1 :=
          pow_le_one₀ (by positivity) hc.sq_norm_one_sub_sq_le_one
        have h2 : ‖z‖ ^ 2 ≤ (5 * cc n / 4) ^ 2 := by
          gcongr
        have h4 : 0 ≤ (‖1 - z ^ 2‖ ^ 2) ^ (m - 1) := by positivity
        have hm2 : 0 ≤ (m : ℝ) ^ 2 := by positivity
        calc 4 * (m : ℝ) ^ 2 * ‖z‖ ^ 2 * (‖1 - z ^ 2‖ ^ 2) ^ (m - 1)
            ≤ 4 * (m : ℝ) ^ 2 * (5 * cc n / 4) ^ 2 * 1 := by gcongr
          _ = _ := mul_one _
    _ ≤ ENNReal.ofReal (4 * (m : ℝ) ^ 2 * (5 * cc n / 4) ^ 2) *
          ENNReal.ofReal (Real.pi * (5 * cc n / 4) ^ 2) := mul_le_mul' le_rfl hvol
    _ = ENNReal.ofReal (4 * (m : ℝ) ^ 2 * (5 * cc n / 4) ^ 2 * (Real.pi * (5 * cc n / 4) ^ 2)) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hpi := Real.pi_lt_d2
        have hm2 : 0 ≤ (m : ℝ) ^ 2 * cc n ^ 4 := by positivity
        nlinarith [mul_nonneg hm2 (sub_nonneg.2 hpi.le)]

theorem energy_inner_S (m n : ℕ) (hn : 1 ≤ n) :
    ∫⁻ z in ⋃ k, ⋃ (_ : n ≤ k), Sk k, en m z ≤ ENNReal.ofReal (16 * (m : ℝ) ^ 2 * hh n) := by
  have hUo : IsOpen (⋃ k, ⋃ (_ : n ≤ k), Sk k) :=
    isOpen_iUnion fun k => isOpen_iUnion fun _ => isOpen_Sk k
  have hhn := hh_pos n
  have hUsub : (⋃ k, ⋃ (_ : n ≤ k), Sk k) ⊆ {z : ℂ | 0 < z.re ∧ z.re < 1 ∧ |z.im| < hh n} := by
    intro z hz
    obtain ⟨k, hkn, hz⟩ := mem_iUnion₂.1 hz
    obtain ⟨h1, h2, h3⟩ := hz
    exact ⟨(cc_pos k).trans h1, h2, h3.trans_le (hh_antitone hkn)⟩
  have hvol : volume (⋃ k, ⋃ (_ : n ≤ k), Sk k) ≤
      ENNReal.ofReal (1 - 0) * ENNReal.ofReal (2 * hh n) :=
    (measure_mono hUsub).trans_eq (volume_rect 0 1 (hh n))
  calc ∫⁻ z in ⋃ k, ⋃ (_ : n ≤ k), Sk k, en m z
      ≤ ENNReal.ofReal (8 * (m : ℝ) ^ 2) * volume (⋃ k, ⋃ (_ : n ≤ k), Sk k) := by
        refine lintegral_le_of_pointwise hUo.measurableSet fun z hz => ?_
        obtain ⟨k, hkn, hz⟩ := mem_iUnion₂.1 hz
        obtain ⟨hc, -⟩ := cone_of_mem_Sk (hn.trans hkn) hz
        unfold en
        refine ENNReal.ofReal_le_ofReal ?_
        rw [norm_deriv_gm_sq]
        have h1 : (‖1 - z ^ 2‖ ^ 2) ^ (m - 1) ≤ 1 :=
          pow_le_one₀ (by positivity) hc.sq_norm_one_sub_sq_le_one
        have h2 := hc.norm_sq_le
        have h4 : 0 ≤ (‖1 - z ^ 2‖ ^ 2) ^ (m - 1) := by positivity
        have hm2 : 0 ≤ (m : ℝ) ^ 2 := by positivity
        calc 4 * (m : ℝ) ^ 2 * ‖z‖ ^ 2 * (‖1 - z ^ 2‖ ^ 2) ^ (m - 1)
            ≤ 4 * (m : ℝ) ^ 2 * 2 * 1 := by gcongr
          _ = _ := by ring
    _ ≤ ENNReal.ofReal (8 * (m : ℝ) ^ 2) *
          (ENNReal.ofReal (1 - 0) * ENNReal.ofReal (2 * hh n)) := mul_le_mul' le_rfl hvol
    _ = ENNReal.ofReal (8 * (m : ℝ) ^ 2 * ((1 - 0) * (2 * hh n))) := by
        rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]
    _ = _ := by
        congr 1
        ring

/-- Energy of `g_m`, `m = m_{n+1}`, over the large region `regionS` (thesis estimate (3.12)). -/
theorem energy_regionS_le (n : ℕ) :
    ∫⁻ z in regionS, en (mm (n + 1)) z ≤ ENNReal.ofReal (10 / (mm (n + 1) : ℝ) ^ 5) := by
  obtain ⟨hN, h2M, h4, ha, hb⟩ := mm_spec n
  set m := mm (n + 1) with hm
  have hm4 : (4 : ℝ) ≤ m := by exact_mod_cast h4
  have hmpos : (0 : ℝ) < m := by linarith
  have hm6 : (0 : ℝ) < (m : ℝ) ^ 6 := by positivity
  have hcn : 0 < cc n := cc_pos n
  have hξ : 3 * cc n / 4 = 3 / (4 * (mm n : ℝ) ^ 2) := by
    unfold cc
    field_simp
  rw [← hξ] at hb
  have hpiece : ∀ k : Fin (n + 1),
      ∫⁻ z in Dsc k ∪ Sk k, en m z ≤ ENNReal.ofReal (1 / (m : ℝ) ^ 6) := by
    rintro ⟨k, hk⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · rw [Sk_zero, union_empty]
      refine (energy_D0 m).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [le_div_iff₀ hm6]
      have : 7 * (m : ℝ) ^ 2 * ((9 / 16 : ℝ) ^ 2) ^ (m - 1) * (m : ℝ) ^ 6 =
          7 * (m : ℝ) ^ 8 * ((9 / 16 : ℝ) ^ 2) ^ (m - 1) := by ring
      rw [this]
      exact ha
    · have hkn : k ≤ n := by omega
      have hξpos : 0 < 3 * cc n / 4 := by positivity
      have hDk := energy_cone_piece (isOpen_Dsc k).measurableSet (volume_Dsc_le k) m hξpos
        (ξ := 3 * cc n / 4) fun z hz => by
          obtain ⟨hc, hx⟩ := cone_of_mem_Dsc hk1 hz
          have := cc_antitone hkn
          exact ⟨hc, by linarith⟩
      have hSk := energy_cone_piece (isOpen_Sk k).measurableSet (volume_Sk_le k) m hξpos
        (ξ := 3 * cc n / 4) fun z hz => by
          obtain ⟨hc, hx⟩ := cone_of_mem_Sk hk1 hz
          have := cc_antitone hkn
          exact ⟨hc, by linarith⟩
      have hpow : 0 ≤ (1 - (3 * cc n / 4) ^ 2 / 2) ^ (m - 1) := by
        refine pow_nonneg ?_ _
        have h1 : cc n ≤ 1 := cc_le_one n
        nlinarith
      have hA : 0 ≤ 8 * (m : ℝ) ^ 2 * (1 - (3 * cc n / 4) ^ 2 / 2) ^ (m - 1) :=
        mul_nonneg (by positivity) hpow
      calc ∫⁻ z in Dsc k ∪ Sk k, en m z
          ≤ (∫⁻ z in Dsc k, en m z) + ∫⁻ z in Sk k, en m z := lintegral_union_le _ _ _
        _ ≤ ENNReal.ofReal (8 * (m : ℝ) ^ 2 * (1 - (3 * cc n / 4) ^ 2 / 2) ^ (m - 1)) +
            ENNReal.ofReal (8 * (m : ℝ) ^ 2 * (1 - (3 * cc n / 4) ^ 2 / 2) ^ (m - 1)) :=
            add_le_add hDk hSk
        _ = ENNReal.ofReal (16 * (m : ℝ) ^ 2 * (1 - (3 * cc n / 4) ^ 2 / 2) ^ (m - 1)) := by
            rw [← ENNReal.ofReal_add hA hA]
            congr 1
            ring
        _ ≤ _ := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [le_div_iff₀ hm6]
            have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
              exact_mod_cast Nat.succ_pos n
            have h8 : 0 ≤ (m : ℝ) ^ 8 * (1 - (3 * cc n / 4) ^ 2 / 2) ^ (m - 1) := by positivity
            have : 16 * (m : ℝ) ^ 2 * (1 - (3 * cc n / 4) ^ 2 / 2) ^ (m - 1) * (m : ℝ) ^ 6 =
                16 * ((m : ℝ) ^ 8 * (1 - (3 * cc n / 4) ^ 2 / 2) ^ (m - 1)) := by ring
            rw [this]
            nlinarith [mul_le_mul_of_nonneg_right hn1 (by positivity :
              (0 : ℝ) ≤ 16 * ((m : ℝ) ^ 8 * (1 - (3 * cc n / 4) ^ 2 / 2) ^ (m - 1)))]
  have hA : ∫⁻ z in ⋃ k : Fin (n + 1), (Dsc k ∪ Sk k), en m z ≤
      ENNReal.ofReal (1 / (m : ℝ) ^ 5) := by
    calc ∫⁻ z in ⋃ k : Fin (n + 1), (Dsc k ∪ Sk k), en m z
        ≤ ∑' k : Fin (n + 1), ∫⁻ z in Dsc k ∪ Sk k, en m z := lintegral_iUnion_le _ _
      _ = ∑ k : Fin (n + 1), ∫⁻ z in Dsc k ∪ Sk k, en m z := tsum_fintype _
      _ ≤ ∑ _k : Fin (n + 1), ENNReal.ofReal (1 / (m : ℝ) ^ 6) :=
          Finset.sum_le_sum fun k _ => hpiece k
      _ = ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * (1 / (m : ℝ) ^ 6)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hnm : ((n + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hN.le
          rw [mul_one_div, div_le_div_iff₀ hm6 (by positivity)]
          have h5 : (0 : ℝ) ≤ (m : ℝ) ^ 5 := by positivity
          nlinarith [mul_le_mul_of_nonneg_right hnm h5]
  have hsub : regionS ⊆ ((⋃ k : Fin (n + 1), (Dsc k ∪ Sk k)) ∪ (⋃ k, ⋃ (_ : n + 1 ≤ k), Dsc k)) ∪
      (⋃ k, ⋃ (_ : n + 1 ≤ k), Sk k) := by
    intro z hz
    obtain ⟨k, hk⟩ := mem_iUnion.1 hz
    by_cases hkn : k < n + 1
    · exact Or.inl (Or.inl (mem_iUnion.2 ⟨⟨k, hkn⟩, hk⟩))
    · rcases hk with hk | hk
      · exact Or.inl (Or.inr (mem_iUnion₂.2 ⟨k, not_lt.1 hkn, hk⟩))
      · exact Or.inr (mem_iUnion₂.2 ⟨k, not_lt.1 hkn, hk⟩)
  have hV := energy_inner_D m (n + 1) (by omega)
  have hU := energy_inner_S m (n + 1) (by omega)
  have hccN : cc (n + 1) = 1 / (m : ℝ) ^ 2 := rfl
  have hhhN : hh (n + 1) = 1 / (m : ℝ) ^ 10 := rfl
  have hreal : 1 / (m : ℝ) ^ 5 + 31 * (m : ℝ) ^ 2 * cc (n + 1) ^ 4 +
      16 * (m : ℝ) ^ 2 * hh (n + 1) ≤ 10 / (m : ℝ) ^ 5 := by
    rw [hccN, hhhN]
    have hnum : 0 ≤ 9 * (m : ℝ) ^ 3 - 31 * (m : ℝ) ^ 2 - 16 := by
      nlinarith [sq_nonneg (m : ℝ)]
    have : 10 / (m : ℝ) ^ 5 - (1 / (m : ℝ) ^ 5 + 31 * (m : ℝ) ^ 2 * (1 / (m : ℝ) ^ 2) ^ 4 +
        16 * (m : ℝ) ^ 2 * (1 / (m : ℝ) ^ 10)) =
        (9 * (m : ℝ) ^ 3 - 31 * (m : ℝ) ^ 2 - 16) / (m : ℝ) ^ 8 := by
      field_simp
      ring
    have h8 : 0 ≤ (9 * (m : ℝ) ^ 3 - 31 * (m : ℝ) ^ 2 - 16) / (m : ℝ) ^ 8 :=
      div_nonneg hnum (by positivity)
    linarith
  calc ∫⁻ z in regionS, en m z
      ≤ ∫⁻ z in ((⋃ k : Fin (n + 1), (Dsc k ∪ Sk k)) ∪ (⋃ k, ⋃ (_ : n + 1 ≤ k), Dsc k)) ∪
          (⋃ k, ⋃ (_ : n + 1 ≤ k), Sk k), en m z := lintegral_mono_set hsub
    _ ≤ (∫⁻ z in (⋃ k : Fin (n + 1), (Dsc k ∪ Sk k)) ∪ (⋃ k, ⋃ (_ : n + 1 ≤ k), Dsc k), en m z) +
          ∫⁻ z in (⋃ k, ⋃ (_ : n + 1 ≤ k), Sk k), en m z := lintegral_union_le _ _ _
    _ ≤ ((∫⁻ z in ⋃ k : Fin (n + 1), (Dsc k ∪ Sk k), en m z) +
          ∫⁻ z in (⋃ k, ⋃ (_ : n + 1 ≤ k), Dsc k), en m z) +
          ∫⁻ z in (⋃ k, ⋃ (_ : n + 1 ≤ k), Sk k), en m z :=
        add_le_add (lintegral_union_le _ _ _) le_rfl
    _ ≤ (ENNReal.ofReal (1 / (m : ℝ) ^ 5) + ENNReal.ofReal (31 * (m : ℝ) ^ 2 * cc (n + 1) ^ 4)) +
          ENNReal.ofReal (16 * (m : ℝ) ^ 2 * hh (n + 1)) :=
        add_le_add (add_le_add hA hV) hU
    _ = ENNReal.ofReal (1 / (m : ℝ) ^ 5 + 31 * (m : ℝ) ^ 2 * cc (n + 1) ^ 4 +
          16 * (m : ℝ) ^ 2 * hh (n + 1)) := by
        have h1 := cc_pos (n + 1)
        have h2 := hh_pos (n + 1)
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

end DirichletPoincare
