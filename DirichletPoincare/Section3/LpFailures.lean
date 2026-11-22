import DirichletPoincare.Definitions
import DirichletPoincare.Section3.NoPoincare

/-!
# Failure of the `L^q` and `L^∞` Poincaré inequalities on `regionStar` (thesis Theorem 3.21)

The region `regionStar` is starlike (`Region.lean`) and the functions `g_m(z) = (1 - z²)^m` have
Dirichlet energy `O(m⁻⁵)` on it (`energy_regionS_le`). For every constant `c` the function
`g_m - c` is at least `1/8` in absolute value on a subset of volume `≥ 1/(8 m¹²)`, which gives
a lower bound on its `L^q` norm that beats the energy for `q ≥ 8`, and on its `L^∞` norm.
-/

open MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace DirichletPoincare

theorem eLpNorm_ofReal_eq' {f : ℂ → ℂ} {μ : Measure ℂ} (hf : AEStronglyMeasurable f μ)
    {p : ℝ} (hp : 0 < p) :
    eLpNorm f (ENNReal.ofReal p) μ = (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ p⁻¹ := by
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (ENNReal.ofReal_pos.2 hp).ne'
    ENNReal.ofReal_ne_top hf, ENNReal.toReal_ofReal hp.le, one_div]

/-- Lower bound for an `L^q` norm from a set where `|f| ≥ a`. -/
theorem eLpNorm_ge_of_set {f : ℂ → ℂ} (hf : Measurable f) {G A : Set ℂ} (hA : MeasurableSet A)
    (hAG : A ⊆ G) {a w q : ℝ} (hq : 0 < q) (hw : ENNReal.ofReal w ≤ volume A)
    (h : ∀ z ∈ A, a ≤ ‖f z‖) :
    ENNReal.ofReal a * ENNReal.ofReal w ^ q⁻¹ ≤
      eLpNorm f (ENNReal.ofReal q) (volume.restrict G) := by
  rw [eLpNorm_ofReal_eq' hf.aestronglyMeasurable hq]
  have h1 : ENNReal.ofReal a ^ q * ENNReal.ofReal w ≤
      ∫⁻ x, ‖f x‖ₑ ^ q ∂(volume.restrict G) := by
    calc ENNReal.ofReal a ^ q * ENNReal.ofReal w ≤ ENNReal.ofReal a ^ q * volume A := by
          gcongr
      _ = ∫⁻ _ in A, ENNReal.ofReal a ^ q := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in A, ‖f x‖ₑ ^ q := by
          refine setLIntegral_mono' hA fun z hz => ?_
          refine ENNReal.rpow_le_rpow ?_ hq.le
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (h z hz)
      _ ≤ ∫⁻ x in G, ‖f x‖ₑ ^ q := lintegral_mono_set hAG
  calc ENNReal.ofReal a * ENNReal.ofReal w ^ q⁻¹
      = (ENNReal.ofReal a ^ q * ENNReal.ofReal w) ^ q⁻¹ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hq.le), ENNReal.rpow_rpow_inv hq.ne']
    _ ≤ _ := ENNReal.rpow_le_rpow h1 (inv_nonneg.2 hq.le)

/-- Lower bound for an `L^∞` norm from a set of positive measure where `|f| ≥ a`. -/
theorem eLpNorm_top_ge_of_set {f : ℂ → ℂ} (hf : Measurable f) {G A : Set ℂ}
    (hG : MeasurableSet G) (hAG : A ⊆ G) {a : ℝ} (hA : volume A ≠ 0)
    (h : ∀ z ∈ A, a ≤ ‖f z‖) :
    ENNReal.ofReal a ≤ eLpNorm f ∞ (volume.restrict G) := by
  by_contra hlt
  rw [not_le] at hlt
  have hfa : AEStronglyMeasurable f (volume.restrict G) := hf.aestronglyMeasurable
  have hae : ∀ᵐ x ∂(volume.restrict G), ‖f x‖ₑ < ENNReal.ofReal a := by
    have h1 : ∀ᵐ x ∂(volume.restrict G), ‖f x‖ₑ ≤ eLpNorm f ∞ (volume.restrict G) := by
      rw [eLpNorm_exponent_top hfa]
      exact ENNReal.ae_le_essSup _
    filter_upwards [h1] with x hx using lt_of_le_of_lt hx hlt
  rw [ae_restrict_iff' hG] at hae
  have hnull := ae_iff.1 hae
  refine hA (measure_mono_null (fun z hz => ?_) hnull)
  simp only [mem_ofPred_eq, not_imp, not_lt]
  refine ⟨hAG hz, ?_⟩
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (h z hz)

/-- Upper bound for the `L²` norm of the derivative from the Dirichlet energy. -/
theorem eLpNorm_deriv_two_le {G : Set ℂ} {f : ℂ → ℂ} {E : ℝ} (hE : 0 ≤ E)
    (h : dirichletEnergy G f ≤ ENNReal.ofReal E) :
    eLpNorm (deriv f) 2 (volume.restrict G) ≤ ENNReal.ofReal (Real.sqrt E) := by
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  rw [h2, eLpNorm_ofReal_eq' (measurable_deriv f).aestronglyMeasurable (by norm_num)]
  have hI : ∫⁻ x, ‖deriv f x‖ₑ ^ (2 : ℝ) ∂(volume.restrict G) = dirichletEnergy G f := by
    unfold dirichletEnergy
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
      Real.rpow_two]
  rw [hI]
  calc dirichletEnergy G f ^ (2 : ℝ)⁻¹ ≤ ENNReal.ofReal E ^ (2 : ℝ)⁻¹ :=
        ENNReal.rpow_le_rpow h (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt E) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hE (by norm_num), Real.sqrt_eq_rpow, one_div]

theorem isOpen_rect (a b h : ℝ) : IsOpen {z : ℂ | a < z.re ∧ z.re < b ∧ |z.im| < h} := by
  have : {z : ℂ | a < z.re ∧ z.re < b ∧ |z.im| < h} =
      {z : ℂ | a < z.re} ∩ ({z : ℂ | z.re < b} ∩ {z : ℂ | |z.im| < h}) := rfl
  rw [this]
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_lt Complex.continuous_im.abs continuous_const))

/-- A thin rectangle at scale `1/m²`, where `g_m` is at least `1/2` in absolute value. -/
noncomputable def bigRect (n : ℕ) : Set ℂ :=
  {z | cc (n + 1) < z.re ∧ z.re < 5 * cc (n + 1) / 4 ∧ |z.im| < hh (n + 1)}

theorem exists_big_set (n : ℕ) (c : ℂ) :
    ∃ A : Set ℂ, MeasurableSet A ∧ A ⊆ regionStar ∧
      ENNReal.ofReal (1 / (8 * (mm (n + 1) : ℝ) ^ 12)) ≤ volume A ∧
      ∀ z ∈ A, 1 / 8 ≤ ‖gm (mm (n + 1)) z - c‖ := by
  obtain ⟨hN, h2M, h4, -, -⟩ := mm_spec n
  set m := mm (n + 1) with hm
  have hm4 : (4 : ℝ) ≤ m := by exact_mod_cast h4
  have hmpos : (0 : ℝ) < m := by linarith
  have hcn : cc (n + 1) = 1 / (m : ℝ) ^ 2 := rfl
  have hhn : hh (n + 1) = 1 / (m : ℝ) ^ 10 := rfl
  have hhle := hh_le (n + 1) (by omega)
  have hcq := cc_le_quarter (n + 1) (by omega)
  have hcpos := cc_pos (n + 1)
  have hhpos := hh_pos (n + 1)
  have hm12 : (1 : ℝ) ≤ (m : ℝ) ^ 12 := one_le_pow₀ (by linarith)
  have hsub : bigRect n ⊆ regionStar := fun z hz =>
    Or.inr (mem_iUnion.2 ⟨n + 1, hz.1, by have := hz.2.1; linarith, hz.2.2⟩)
  have hg : ∀ z ∈ bigRect n, 1 / 2 ≤ ‖gm m z‖ := by
    intro z hz
    obtain ⟨h1, h2, h3⟩ := hz
    refine norm_gm_ge h4 ?_
    have hc2 : 3 / (m : ℝ) ^ 4 = 3 * cc (n + 1) ^ 2 := by
      rw [hcn]
      field_simp
    rw [hc2, Complex.sq_norm, Complex.normSq_apply]
    have hre : z.re * z.re ≤ (5 * cc (n + 1) / 4) ^ 2 := by
      have := pow_le_pow_left₀ (by linarith) h2.le 2
      nlinarith
    have him : z.im * z.im ≤ (cc (n + 1) / 4) ^ 2 := by
      have := abs_lt.1 h3
      nlinarith
    nlinarith
  have hvol : ENNReal.ofReal (1 / (8 * (m : ℝ) ^ 12)) ≤ volume (bigRect n) := by
    have := volume_rect (cc (n + 1)) (5 * cc (n + 1) / 4) (hh (n + 1))
    change ENNReal.ofReal _ ≤ volume {z : ℂ | _ < z.re ∧ z.re < _ ∧ |z.im| < _}
    rw [this, ← ENNReal.ofReal_mul (by linarith)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : (5 * cc (n + 1) / 4 - cc (n + 1)) * (2 * hh (n + 1)) = 1 / (2 * (m : ℝ) ^ 12) := by
      rw [hcn, hhn]
      field_simp
      ring
    rw [e]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  rcases big_diff_or (m := m) (A₀ := Dsc 0) (A₁ := bigRect n)
      (fun z hz => norm_gm_le_of_mem_Dsc_zero h4 hz) hg c with h | h
  · refine ⟨Dsc 0, (isOpen_Dsc 0).measurableSet, fun z hz => Or.inl hz, ?_, h⟩
    rw [Dsc_zero_eq, volume_ball_eq _ (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : 1 / (8 * (m : ℝ) ^ 12) ≤ 1 / 8 :=
      one_div_le_one_div_of_le (by norm_num) (by nlinarith)
    have := Real.pi_gt_three
    nlinarith
  · exact ⟨bigRect n, (isOpen_rect _ _ _).measurableSet, hsub, hvol, h⟩

theorem exists_big_m (x : ℝ) : ∃ n : ℕ, x ≤ (mm (n + 1) : ℝ) := by
  refine ⟨⌈x⌉₊, ?_⟩
  have h1 := (mm_spec ⌈x⌉₊).1
  have h2 : (⌈x⌉₊ : ℝ) + 1 < mm (⌈x⌉₊ + 1) := by exact_mod_cast h1
  have h3 := Nat.le_ceil x
  linarith

theorem isInDirichletSpace_gm (n : ℕ) (z₀ : ℂ) :
    IsInDirichletSpace regionStar z₀ (fun z => gm (mm (n + 1)) z - gm (mm (n + 1)) z₀) :=
  ⟨(gm_differentiable _).differentiableOn.sub_const _, sub_self _,
    (dirichletEnergy_gm_le regionStar_subset_regionS n _).trans_lt ENNReal.ofReal_lt_top⟩

theorem eLpNorm_deriv_gm_le (n : ℕ) (c : ℂ) :
    eLpNorm (deriv fun z => gm (mm (n + 1)) z - c) 2 (volume.restrict regionStar) ≤
      ENNReal.ofReal (Real.sqrt (10 / (mm (n + 1) : ℝ) ^ 5)) :=
  eLpNorm_deriv_two_le (by positivity) (dirichletEnergy_gm_le regionStar_subset_regionS n c)

theorem measurable_gm_sub (m : ℕ) (c : ℂ) : Measurable fun z => gm m z - c :=
  ((gm_differentiable m).continuous.sub continuous_const).measurable

theorem not_lq_ineq {K : ℝ} (hK : 0 ≤ K) {M q : ℝ} (hM : 64 * (K + 1) ≤ M) (hq : 8 ≤ q)
    (h : 1 / 8 * (1 / (8 * M ^ 12)) ^ q⁻¹ ≤ K * Real.sqrt (10 / M ^ 5)) : False := by
  have hMpos : 0 < M := by linarith
  set w : ℝ := 1 / (8 * M ^ 12) with hw
  have hM1 : 1 ≤ M := by linarith
  have hw0 : 0 < w := by positivity
  have hw1 : w ≤ 1 := by
    rw [hw, div_le_one (by positivity)]
    nlinarith [one_le_pow₀ (n := 12) hM1]
  have hqpos : 0 < q := by linarith
  have h18 : w ^ (8 : ℝ)⁻¹ ≤ w ^ q⁻¹ :=
    Real.rpow_le_rpow_of_exponent_ge hw0 hw1 (inv_anti₀ (by norm_num) hq)
  set t := w ^ (8 : ℝ)⁻¹ with ht
  have ht8 : t ^ 8 = w := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hw0.le]
    norm_num
  have ht0 : 0 ≤ t := by positivity
  have H1 : 1 / 8 * t ≤ K * Real.sqrt (10 / M ^ 5) := by
    refine le_trans ?_ h
    gcongr
  have H2 := pow_le_pow_left₀ (by positivity) H1 8
  have hE : 0 ≤ 10 / M ^ 5 := by positivity
  have hs8 : Real.sqrt (10 / M ^ 5) ^ 8 = (10 / M ^ 5) ^ 4 := by
    have : Real.sqrt (10 / M ^ 5) ^ 8 = (Real.sqrt (10 / M ^ 5) ^ 2) ^ 4 := by ring
    rw [this, Real.sq_sqrt hE]
  rw [mul_pow, mul_pow, ht8, hs8, hw] at H2
  have e1 : (1 / 8 : ℝ) ^ 8 * (1 / (8 * M ^ 12)) = 1 / (8 ^ 9 * M ^ 12) := by
    field_simp
  have e2 : K ^ 8 * (10 / M ^ 5) ^ 4 = K ^ 8 * 10 ^ 4 / M ^ 20 := by
    field_simp
  rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)] at H2
  have H3 : M ^ 8 * M ^ 12 ≤ (8 ^ 9 * 10 ^ 4 * K ^ 8) * M ^ 12 := by
    have : M ^ 8 * M ^ 12 = M ^ 20 := by ring
    rw [this]
    nlinarith [H2]
  have H4 := le_of_mul_le_mul_right H3 (by positivity)
  have H5 : (64 * (K + 1)) ^ 8 ≤ M ^ 8 := pow_le_pow_left₀ (by positivity) hM 8
  rw [mul_pow] at H5
  have H6 : K ^ 8 ≤ (K + 1) ^ 8 := pow_le_pow_left₀ hK (by linarith) 8
  have H7 : 0 < (K + 1) ^ 8 := by positivity
  nlinarith

theorem not_linf_ineq {K : ℝ} (hK : 0 ≤ K) {M : ℝ} (hM : 64 * (K + 1) ≤ M)
    (h : 1 / 8 ≤ K * Real.sqrt (10 / M ^ 5)) : False := by
  have hMpos : 0 < M := by linarith
  have hE : 0 ≤ 10 / M ^ 5 := by positivity
  have H2 := pow_le_pow_left₀ (by norm_num) h 2
  rw [mul_pow, Real.sq_sqrt hE] at H2
  have e : K ^ 2 * (10 / M ^ 5) = K ^ 2 * 10 / M ^ 5 := by ring
  rw [e, le_div_iff₀ (by positivity)] at H2
  have H5 : (64 * (K + 1)) ^ 5 ≤ M ^ 5 := pow_le_pow_left₀ (by positivity) hM 5
  rw [mul_pow] at H5
  have H6 : K ^ 2 ≤ (K + 1) ^ 5 :=
    calc K ^ 2 ≤ (K + 1) ^ 2 := pow_le_pow_left₀ hK (by linarith) 2
      _ ≤ (K + 1) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have H7 : 0 < (K + 1) ^ 5 := by positivity
  nlinarith

/-- For `q ≥ 8` the `(q, 2)` Poincaré inequality with constant `K` fails on `regionStar`. -/
theorem not_poincareLp_regionStar (K : ℝ≥0) :
    ∀ q : ℝ, 8 ≤ q → ∀ z₀ : ℂ,
      ¬ PoincareLpWithConst regionStar z₀ (ENNReal.ofReal q) 2 K := by
  obtain ⟨n, hn⟩ := exists_big_m (64 * ((K : ℝ) + 1))
  refine fun q hq z₀ hP => ?_
  have hqpos : 0 < q := by linarith
  have hf := hP _ (isInDirichletSpace_gm n z₀)
  obtain ⟨A, hAm, hAG, hAv, hAbig⟩ := exists_big_set n (gm (mm (n + 1)) z₀)
  have hlow := eLpNorm_ge_of_set (measurable_gm_sub (mm (n + 1)) (gm (mm (n + 1)) z₀)) hAm hAG
    hqpos hAv hAbig
  have hup := eLpNorm_deriv_gm_le n (gm (mm (n + 1)) z₀)
  have hchain := hlow.trans (hf.trans (mul_le_mul' le_rfl hup))
  have hm0 : (0 : ℝ) < mm (n + 1) := by exact_mod_cast one_le_mm (n + 1)
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (inv_nonneg.2 hqpos.le),
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hchain
  exact not_lq_ineq K.coe_nonneg hn hq hchain

/-- The `(‖·‖_∞, 2)` Poincaré inequality fails on `regionStar` for every basepoint. -/
theorem not_poincareLp_top_regionStar (z₀ : ℂ) : ¬ PoincareLp regionStar z₀ ∞ 2 := by
  rintro ⟨K, hP⟩
  obtain ⟨n, hn⟩ := exists_big_m (64 * ((K : ℝ) + 1))
  have hf := hP _ (isInDirichletSpace_gm n z₀)
  obtain ⟨A, hAm, hAG, hAv, hAbig⟩ := exists_big_set n (gm (mm (n + 1)) z₀)
  have hm0 : (0 : ℝ) < mm (n + 1) := by exact_mod_cast one_le_mm (n + 1)
  have hAne : volume A ≠ 0 :=
    (lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by positivity)) hAv).ne'
  have hlow := eLpNorm_top_ge_of_set (measurable_gm_sub (mm (n + 1)) (gm (mm (n + 1)) z₀))
    isOpen_regionStar.measurableSet hAG hAne hAbig
  have hup := eLpNorm_deriv_gm_le n (gm (mm (n + 1)) z₀)
  have hchain := hlow.trans (hf.trans (mul_le_mul' le_rfl hup))
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul K.coe_nonneg,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hchain
  exact not_linf_ineq K.coe_nonneg hn hchain

end DirichletPoincare
