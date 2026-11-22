import DirichletPoincare.Definitions
import DirichletPoincare.Section2.Starlike
import DirichletPoincare.Section3.LpFailures

/-!
# Poincaré inequalities in `L^p` norms (thesis Section 3.2)

Lemma 3.15 (limit of `L^p` norms), Lemma 3.18 (visibility from a point outside an arc) and
Theorem 3.21 (a region where the (2,2) inequality holds but the `(‖·‖_∞, 2)` one fails).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DirichletPoincare

/-- The arc `R_r = {r e^{it} : |t| < α}` (thesis Lemma 3.18, Figure 3.3). -/
def sectorArc (r α : ℝ) : Set ℂ :=
  {z | ∃ t : ℝ, |t| < α ∧ z = r * Complex.exp (t * Complex.I)}

/-- `c ^ y` is continuous in the exponent `y` when `0 < c < ∞`. -/
private theorem tendsto_ennrpow_exponent {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) (y₀ : ℝ) :
    Tendsto (fun y : ℝ => c ^ y) (𝓝 y₀) (𝓝 (c ^ y₀)) := by
  have hx : 0 < c.toReal := ENNReal.toReal_pos hc0 hc
  have key : ∀ y : ℝ, c ^ y = ENNReal.ofReal (c.toReal ^ y) := fun y => by
    conv_lhs => rw [← ENNReal.ofReal_toReal hc]
    exact ENNReal.ofReal_rpow_of_pos hx
  simp_rw [key]
  exact (ENNReal.continuous_ofReal.tendsto _).comp
    (Real.continuousAt_const_rpow (b := y₀) hx.ne').tendsto

private theorem eLpNorm_ofReal_eq {f : ℂ → ℂ} {μ : Measure ℂ} (hf : AEStronglyMeasurable f μ)
    {p : ℝ} (hp : 0 < p) :
    eLpNorm f (ENNReal.ofReal p) μ = (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ p⁻¹ := by
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (ENNReal.ofReal_pos.2 hp).ne'
    ENNReal.ofReal_ne_top hf, ENNReal.toReal_ofReal hp.le, one_div]

/-- **Lemma 3.15** (thesis p. 28). If `‖f‖_q < ∞` for some finite `q`, then `‖f‖_p → ‖f‖_∞` as
`p → ∞`. The hypothesis `0 < q` is needed: for `q = 0` Mathlib sets `eLpNorm f 0 = 0`, so the
statement would be false (e.g. `f = 1` on `ℂ`). The thesis' assumption `0 < ‖f‖_∞` is not needed. -/
theorem tendsto_eLpNorm_atTop {X : Set ℂ} {f : ℂ → ℂ} (hf : Measurable f)
    {q : ℝ≥0∞} (hq0 : 0 < q) (hq : q ≠ ∞)
    (hfq : eLpNorm f q (volume.restrict X) < ∞) :
    Tendsto (fun p : ℝ => eLpNorm f (ENNReal.ofReal p) (volume.restrict X)) atTop
      (𝓝 (eLpNorm f ∞ (volume.restrict X))) := by
  set μ : Measure ℂ := volume.restrict X with hμ
  have hfa : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
  set q' : ℝ := q.toReal with hq'
  have hq'pos : 0 < q' := ENNReal.toReal_pos hq0.ne' hq
  set C : ℝ≥0∞ := ∫⁻ x, ‖f x‖ₑ ^ q' ∂μ with hCdef
  have hC : C < ∞ := (eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top hq0.ne' hq hfa).1 hfq
  have hess : ∀ c : ℝ≥0∞, (∀ᵐ x ∂μ, ‖f x‖ₑ ≤ c) → eLpNorm f ∞ μ ≤ c := by
    intro c hc
    rw [eLpNorm_exponent_top hfa]
    exact essSup_le_of_ae_le c hc
  have hae : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ eLpNorm f ∞ μ := by
    rw [eLpNorm_exponent_top hfa]
    exact ENNReal.ae_le_essSup _
  have hF : ∀ p : ℝ, 0 < p → eLpNorm f (ENNReal.ofReal p) μ = (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ p⁻¹ :=
    fun p hp => eLpNorm_ofReal_eq hfa hp
  -- Lower bound: for `a < ‖f‖_∞`, the set where `‖f‖ₑ > r` has positive measure.
  have hlow : ∀ a < eLpNorm f ∞ μ, ∀ᶠ p : ℝ in atTop, a < eLpNorm f (ENNReal.ofReal p) μ := by
    intro a ha
    obtain ⟨r, har, hrN⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ha
    have hr0 : (r : ℝ≥0∞) ≠ 0 := ((zero_le : (0 : ℝ≥0∞) ≤ a).trans_lt har).ne'
    have hApos : μ {x | (r : ℝ≥0∞) < ‖f x‖ₑ} ≠ 0 := by
      intro h0
      have hle : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ (r : ℝ≥0∞) := by
        rw [ae_iff]
        simpa only [not_le] using h0
      exact lt_irrefl _ (hrN.trans_le (hess _ hle))
    have hlowp : ∀ p : ℝ, 0 < p →
        (r : ℝ≥0∞) * μ {x | (r : ℝ≥0∞) < ‖f x‖ₑ} ^ p⁻¹ ≤ eLpNorm f (ENNReal.ofReal p) μ := by
      intro p hp
      have hsub : μ {x | (r : ℝ≥0∞) < ‖f x‖ₑ} ≤ μ {x | (r : ℝ≥0∞) ^ p ≤ ‖f x‖ₑ ^ p} :=
        measure_mono fun x (hx : (r : ℝ≥0∞) < ‖f x‖ₑ) => ENNReal.rpow_le_rpow hx.le hp.le
      have hmark : (r : ℝ≥0∞) ^ p * μ {x | (r : ℝ≥0∞) < ‖f x‖ₑ} ≤ ∫⁻ x, ‖f x‖ₑ ^ p ∂μ :=
        le_trans (mul_le_mul_right hsub _)
          (mul_meas_ge_le_lintegral₀ (hf.eNorm.pow_const p).aemeasurable _)
      rw [hF p hp]
      calc (r : ℝ≥0∞) * μ {x | (r : ℝ≥0∞) < ‖f x‖ₑ} ^ p⁻¹
          = ((r : ℝ≥0∞) ^ p) ^ p⁻¹ * μ {x | (r : ℝ≥0∞) < ‖f x‖ₑ} ^ p⁻¹ := by
            rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hp.ne', ENNReal.rpow_one]
        _ = ((r : ℝ≥0∞) ^ p * μ {x | (r : ℝ≥0∞) < ‖f x‖ₑ}) ^ p⁻¹ :=
            (ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hp.le)).symm
        _ ≤ (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ p⁻¹ := ENNReal.rpow_le_rpow hmark (inv_nonneg.2 hp.le)
    by_cases htop : μ {x | (r : ℝ≥0∞) < ‖f x‖ₑ} = ∞
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with p hp
      refine lt_of_lt_of_le ?_ (hlowp p hp)
      rw [htop, ENNReal.top_rpow_of_pos (inv_pos.2 hp), ENNReal.mul_top hr0]
      exact har.trans ENNReal.coe_lt_top
    · have hlimA : Tendsto (fun p : ℝ => (r : ℝ≥0∞) * μ {x | (r : ℝ≥0∞) < ‖f x‖ₑ} ^ p⁻¹)
          atTop (𝓝 ((r : ℝ≥0∞) * μ {x | (r : ℝ≥0∞) < ‖f x‖ₑ} ^ (0 : ℝ))) :=
        ENNReal.Tendsto.const_mul
          ((tendsto_ennrpow_exponent hApos htop 0).comp tendsto_inv_atTop_zero)
          (Or.inr ENNReal.coe_ne_top)
      rw [ENNReal.rpow_zero, mul_one] at hlimA
      filter_upwards [(tendsto_order.1 hlimA).1 a har, eventually_gt_atTop (0 : ℝ)] with p h1 h2
      exact lt_of_lt_of_le h1 (hlowp p h2)
  -- Upper bound: for `b > ‖f‖_∞`, pick a finite `t` with `‖f‖_∞ < t < b` and use Hölder-type
  -- splitting `‖f‖ₑ^p ≤ ‖f‖ₑ^{q'} t^{p-q'}` a.e.
  have hup : ∀ b > eLpNorm f ∞ μ, ∀ᶠ p : ℝ in atTop, eLpNorm f (ENNReal.ofReal p) μ < b := by
    intro b hb
    obtain ⟨t, hNt, htb⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hb
    have ht0 : (t : ℝ≥0∞) ≠ 0 := ((zero_le : (0 : ℝ≥0∞) ≤ eLpNorm f ∞ μ).trans_lt hNt).ne'
    have hbound : ∀ p : ℝ, q' ≤ p → 0 < p →
        eLpNorm f (ENNReal.ofReal p) μ ≤ (C + 1) ^ p⁻¹ * (t : ℝ≥0∞) ^ ((p - q') * p⁻¹) := by
      intro p hqp hp
      have hat : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ (t : ℝ≥0∞) := hae.mono fun x hx => hx.trans hNt.le
      have hpt : ∫⁻ x, ‖f x‖ₑ ^ p ∂μ ≤ C * (t : ℝ≥0∞) ^ (p - q') := by
        calc ∫⁻ x, ‖f x‖ₑ ^ p ∂μ ≤ ∫⁻ x, ‖f x‖ₑ ^ q' * (t : ℝ≥0∞) ^ (p - q') ∂μ := by
              refine lintegral_mono_ae ?_
              filter_upwards [hat] with x hx
              calc ‖f x‖ₑ ^ p = ‖f x‖ₑ ^ q' * ‖f x‖ₑ ^ (p - q') := by
                    rw [← ENNReal.rpow_add_of_nonneg q' (p - q') hq'pos.le (sub_nonneg.2 hqp)]
                    congr 1
                    ring
                _ ≤ ‖f x‖ₑ ^ q' * (t : ℝ≥0∞) ^ (p - q') :=
                    mul_le_mul_right (ENNReal.rpow_le_rpow hx (sub_nonneg.2 hqp)) _
          _ = C * (t : ℝ≥0∞) ^ (p - q') :=
              lintegral_mul_const' _ _
                (ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.2 hqp) ENNReal.coe_ne_top)
      rw [hF p hp]
      calc (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ p⁻¹ ≤ (C * (t : ℝ≥0∞) ^ (p - q')) ^ p⁻¹ :=
            ENNReal.rpow_le_rpow hpt (inv_nonneg.2 hp.le)
        _ ≤ ((C + 1) * (t : ℝ≥0∞) ^ (p - q')) ^ p⁻¹ :=
            ENNReal.rpow_le_rpow (mul_le_mul_left le_self_add _) (inv_nonneg.2 hp.le)
        _ = (C + 1) ^ p⁻¹ * ((t : ℝ≥0∞) ^ (p - q')) ^ p⁻¹ :=
            ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hp.le)
        _ = (C + 1) ^ p⁻¹ * (t : ℝ≥0∞) ^ ((p - q') * p⁻¹) := by rw [← ENNReal.rpow_mul]
    have hC1 : C + 1 ≠ 0 := (lt_of_lt_of_le zero_lt_one le_add_self).ne'
    have hC2 : C + 1 ≠ ∞ := ENNReal.add_ne_top.2 ⟨hC.ne, ENNReal.one_ne_top⟩
    have hlimC : Tendsto (fun p : ℝ => (C + 1) ^ p⁻¹) atTop (𝓝 1) := by
      have h : Tendsto (fun p : ℝ => (C + 1) ^ p⁻¹) atTop (𝓝 ((C + 1) ^ (0 : ℝ))) :=
        (tendsto_ennrpow_exponent hC1 hC2 0).comp tendsto_inv_atTop_zero
      rwa [ENNReal.rpow_zero] at h
    have he : Tendsto (fun p : ℝ => (p - q') * p⁻¹) atTop (𝓝 1) := by
      have h0 : Tendsto (fun p : ℝ => 1 - q' * p⁻¹) atTop (𝓝 (1 - q' * 0)) :=
        tendsto_const_nhds.sub (tendsto_const_nhds.mul tendsto_inv_atTop_zero)
      rw [mul_zero, sub_zero] at h0
      refine h0.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with p hp
      rw [sub_mul, mul_inv_cancel₀ hp.ne']
    have hte : Tendsto (fun p : ℝ => (t : ℝ≥0∞) ^ ((p - q') * p⁻¹)) atTop (𝓝 (t : ℝ≥0∞)) := by
      have h : Tendsto (fun p : ℝ => (t : ℝ≥0∞) ^ ((p - q') * p⁻¹)) atTop
          (𝓝 ((t : ℝ≥0∞) ^ (1 : ℝ))) :=
        (tendsto_ennrpow_exponent ht0 ENNReal.coe_ne_top 1).comp he
      rwa [ENNReal.rpow_one] at h
    have hprod : Tendsto (fun p : ℝ => (C + 1) ^ p⁻¹ * (t : ℝ≥0∞) ^ ((p - q') * p⁻¹))
        atTop (𝓝 (1 * (t : ℝ≥0∞))) :=
      ENNReal.Tendsto.mul hlimC (Or.inl one_ne_zero) hte (Or.inl ht0)
    rw [one_mul] at hprod
    filter_upwards [(tendsto_order.1 hprod).2 b htb, eventually_ge_atTop q',
      eventually_gt_atTop (0 : ℝ)] with p h1 h2 h3
    exact lt_of_le_of_lt (hbound p h2 h3) h1
  exact tendsto_order.2 ⟨fun a ha => hlow a ha, fun b hb => hup b hb⟩

/-- Points of `R_r` lie on the circle `|z| = r` and have real part at least `r cos α`. -/
private theorem sectorArc_props {r α : ℝ} (hr : 0 < r) (hα0 : 0 < α) (hα : α < Real.pi / 2) {z : ℂ}
    (hz : z ∈ sectorArc r α) :
    z.re ^ 2 + z.im ^ 2 = r ^ 2 ∧ r * Real.cos α ≤ z.re := by
  obtain ⟨t, ht, rfl⟩ := hz
  have hre : (r * Complex.exp (t * Complex.I)).re = r * Real.cos t := by
    simp [Complex.exp_ofReal_mul_I_re]
  have him : (r * Complex.exp (t * Complex.I)).im = r * Real.sin t := by
    simp [Complex.exp_ofReal_mul_I_im]
  rw [hre, him]
  refine ⟨by linear_combination r ^ 2 * Real.sin_sq_add_cos_sq t, ?_⟩
  refine mul_le_mul_of_nonneg_left ?_ hr.le
  rw [← Real.cos_abs t]
  exact (Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg t)
    (by linarith [Real.pi_pos]) ht).le

/-- If `a > r` and `a cos α = 2r`, the line through `(a, 0)` and `p ∈ R_r` meets `R_r` only at `p`.
Writing the line as `a + s (p - a)`, the circle condition factors as `(s - 1) (s D - (a² - r²)) = 0`
with `D = |p - a|²`. The second root has real part `≤ 0`, so it is not on the arc. -/
private theorem line_meets_sectorArc_only_at {r α a : ℝ} (hr : 0 < r) (hα0 : 0 < α)
    (hα : α < Real.pi / 2) (hra : r < a) (ha : a * Real.cos α = 2 * r) {p : ℂ}
    (hp : p ∈ sectorArc r α) {z : ℂ}
    (hzl : z ∈ affineSpan ℝ ({(a : ℂ), p} : Set ℂ)) (hz : z ∈ sectorArc r α) : z = p := by
  obtain ⟨s, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.1 hzl
  obtain ⟨hpc, hpx⟩ := sectorArc_props hr hα0 hα hp
  obtain ⟨hzc, hzx⟩ := sectorArc_props hr hα0 hα hz
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hα⟩
  have hre : (AffineMap.lineMap (a : ℂ) p s).re = a + s * (p.re - a) := by
    simp [AffineMap.lineMap_apply]; ring
  have him : (AffineMap.lineMap (a : ℂ) p s).im = s * p.im := by
    simp [AffineMap.lineMap_apply]
  rw [hre, him] at hzc
  rw [hre] at hzx
  have hfac : (s - 1) * (s * ((p.re - a) ^ 2 + p.im ^ 2) - (a ^ 2 - r ^ 2)) = 0 := by
    linear_combination hzc - s * hpc
  rcases mul_eq_zero.1 hfac with h1 | h2
  · have hs : s = 1 := by linarith
    subst hs
    simp
  · exfalso
    have hxa : p.re < a := by
      by_contra h
      replace h := le_of_not_gt h
      have hr2 : r ^ 2 < a ^ 2 := by nlinarith
      nlinarith [sq_nonneg p.im, mul_le_mul h h (by linarith) (by linarith)]
    have hD : 0 < (p.re - a) ^ 2 + p.im ^ 2 := by
      have h0 : 0 < (p.re - a) ^ 2 := by nlinarith
      nlinarith [sq_nonneg p.im]
    have hDX : ((p.re - a) ^ 2 + p.im ^ 2) * (a + s * (p.re - a))
        = 2 * a * r ^ 2 - (a ^ 2 + r ^ 2) * p.re := by
      linear_combination (p.re - a) * h2 + a * hpc
    have k1 : (a ^ 2 + r ^ 2) * (r * Real.cos α) ≤ (a ^ 2 + r ^ 2) * p.re :=
      mul_le_mul_of_nonneg_left hpx (by positivity)
    have k2 : (a ^ 2 + r ^ 2) * (r * Real.cos α) - 2 * a * r ^ 2 = r ^ 3 * Real.cos α := by
      linear_combination (a * r) * ha
    have k3 : 0 < r ^ 3 * Real.cos α := mul_pos (by positivity) hc
    have hpos : 0 < ((p.re - a) ^ 2 + p.im ^ 2) * (a + s * (p.re - a)) :=
      mul_pos hD (lt_of_lt_of_le (mul_pos hr hc) hzx)
    linarith

/-- **Lemma 3.18** (thesis p. 29). For `0 < α < π/2` and `r > 0`, there is `a > r` such that every
point of `R_r` is joined to `(a, 0)` by a line meeting `R_r` only at that point. The same holds
for every `0 < r₀ < r` with some `a₀ > r₀`; the proof applies the first part with `r₀` in place
of `r`. -/
theorem exists_visibility_point {r α : ℝ} (hr : 0 < r) (hα : 0 < α) (hα2 : α < Real.pi / 2) :
    (∃ a : ℝ, r < a ∧
      ∀ p ∈ sectorArc r α,
        (affineSpan ℝ ({((a : ℝ) : ℂ), p} : Set ℂ) : Set ℂ) ∩ sectorArc r α = {p}) ∧
    (∀ r₀ : ℝ, 0 < r₀ → r₀ < r →
      ∃ a₀ : ℝ, r₀ < a₀ ∧
        ∀ p ∈ sectorArc r₀ α,
          (affineSpan ℝ ({((a₀ : ℝ) : ℂ), p} : Set ℂ) : Set ℂ) ∩ sectorArc r₀ α = {p}) := by
  have key : ∀ r : ℝ, 0 < r → ∃ a : ℝ, r < a ∧
      ∀ p ∈ sectorArc r α,
        (affineSpan ℝ ({((a : ℝ) : ℂ), p} : Set ℂ) : Set ℂ) ∩ sectorArc r α = {p} := by
    intro r hr
    have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hα2⟩
    obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = 2 * r / Real.cos α := ⟨_, rfl⟩
    have ha : a * Real.cos α = 2 * r := by rw [ha_def]; exact div_mul_cancel₀ _ hc.ne'
    have hra : r < a := by
      rw [ha_def, lt_div_iff₀ hc]
      nlinarith [Real.cos_le_one α]
    refine ⟨a, hra, fun p hp => ?_⟩
    ext z
    constructor
    · rintro ⟨hzl, hz⟩
      exact Set.mem_singleton_iff.2 (line_meets_sectorArc_only_at hr hα hα2 hra ha hp hzl hz)
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨SetLike.mem_coe.2 (right_mem_affineSpan_pair ℝ _ _), hp⟩
  exact ⟨key r hr |>.imp fun _ h => h, fun r₀ hr₀ _ => key r₀ hr₀⟩

/-- **Theorem 3.21** (thesis p. 30). There is a bounded region `G` such that:
* the Poincaré (2,2) inequality holds on `G`;
* for every constant `K`, there is `p₀ ∈ (1, 2)` such that for `p₀ ≤ p < 2` the Poincaré
  `(2p/(2-p), 2)` inequality with constant `K` fails on `G`;
* the Poincaré `(‖·‖_∞, 2)` inequality fails on `G`. -/
theorem exists_region_with_lp_poincare_failures :
    ∃ G : Set ℂ, Bornology.IsBounded G ∧ IsRegion G ∧
      (∀ z₀ ∈ G, PoincareInequality G z₀) ∧
      (∀ K : ℝ≥0, ∃ p₀ : ℝ, 1 < p₀ ∧ p₀ < 2 ∧
        ∀ p : ℝ, p₀ ≤ p → p < 2 → ∀ z₀ ∈ G,
          ¬ PoincareLpWithConst G z₀ (ENNReal.ofReal (2 * p / (2 - p))) 2 K) ∧
      (∀ z₀ ∈ G, ¬ PoincareLp G z₀ ∞ 2) := by
  have hbdd : Bornology.IsBounded regionStar :=
    isBounded_regionS.subset regionStar_subset_regionS
  refine ⟨regionStar, hbdd, isStarlikeRegion_regionStar.1,
    fun z₀ hz₀ => poincare_of_starlike hbdd isStarlikeRegion_regionStar hz₀, ?_,
    fun z₀ _ => not_poincareLp_top_regionStar z₀⟩
  -- `p₀ = 8/5` works for every `K`: it gives `2p/(2-p) ≥ 8`.
  intro K
  have hn := not_poincareLp_regionStar K
  refine ⟨8 / 5, by norm_num, by norm_num, fun p hp hp2 z₀ _ => hn _ ?_ z₀⟩
  have h2p : 0 < 2 - p := by linarith
  rw [le_div_iff₀ h2p]
  linarith

end DirichletPoincare
