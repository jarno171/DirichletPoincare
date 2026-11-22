import DirichletPoincare.Definitions
import DirichletPoincare.Section2.InclusionAux

/-!
# Auxiliary results for Theorem 2.5 (Riemann map characterization)

* an injective holomorphic function has nonvanishing derivative, hence a holomorphic inverse;
* `D(U) → D(G)`, `f ↦ f ∘ φ` preserves the Dirichlet energy for a conformal map `φ : U → G`.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace DirichletPoincare

/-- An injective holomorphic function on an open set has nonvanishing derivative. -/
theorem deriv_ne_zero_of_injOn {U : Set ℂ} (hU : IsOpen U) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ U) (hinj : InjOn φ U) {a : ℂ} (ha : a ∈ U) :
    deriv φ a ≠ 0 := by
  intro h0
  have hA : AnalyticAt ℂ φ a := hφ.analyticAt (hU.mem_nhds ha)
  set F : ℂ → ℂ := fun z => φ z - φ a with hF
  have hFA : AnalyticAt ℂ F a := hA.sub analyticAt_const
  have hne : analyticOrderAt F a ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    have h1 : ∀ᶠ z in 𝓝[≠] a, F z = 0 ∧ z ∈ U :=
      (htop.and (hU.mem_nhds ha)).filter_mono nhdsWithin_le_nhds
    obtain ⟨z, ⟨hz0, hzU⟩, hza⟩ := (h1.and self_mem_nhdsWithin).exists
    exact hza (hinj hzU ha (sub_eq_zero.1 hz0))
  obtain ⟨g, hg, hg0, hfg⟩ := hFA.analyticOrderAt_ne_top.1 hne
  set k := analyticOrderNatAt F a with hk
  have hk0 : k ≠ 0 := by
    intro hk0
    have := hfg.self_of_nhds
    simp [hF, hk0] at this
    exact hg0 this.symm
  have hk1 : k ≠ 1 := by
    intro hk1
    rw [hk1] at hfg
    have hgd : HasDerivAt g (deriv g a) a := hg.differentiableAt.hasDerivAt
    have h1 : HasDerivAt (fun z => φ a + (z - a) * g z) (1 * g a + (a - a) * deriv g a) a :=
      (((hasDerivAt_id a).sub_const a).mul hgd).const_add (φ a)
    have h2 : HasDerivAt φ (1 * g a + (a - a) * deriv g a) a := by
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [hfg] with z hz
      show φ z = φ a + (z - a) * g z
      have : φ z - φ a = (z - a) ^ 1 • g z := hz
      simp only [pow_one, smul_eq_mul] at this
      linear_combination this
    have := h2.deriv
    rw [h0] at this
    simp at this
    exact hg0 this.symm
  have hk2 : 2 ≤ k := by omega
  -- an analytic `k`-th root of `g`
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (g a) (Nat.pos_of_ne_zero hk0)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hg0 (by simpa [hk0] using hc.symm)
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
  set q : ℂ → ℂ := fun z => g z / g a with hq
  have hqA : AnalyticAt ℂ q a := hg.div analyticAt_const hg0
  have hqa : q a = 1 := div_self hg0
  set h : ℂ → ℂ := fun z => c * Complex.exp ((k : ℂ)⁻¹ * Complex.log (q z)) with hh
  have hhA : AnalyticAt ℂ h a := by
    refine analyticAt_const.mul (AnalyticAt.cexp' (analyticAt_const.mul ?_))
    exact hqA.clog (by rw [hqa]; exact Complex.one_mem_slitPlane)
  have hha : h a = c := by simp [hh, hqa]
  have hpow : ∀ᶠ z in 𝓝 a, g z = h z ^ k := by
    filter_upwards [hqA.continuousAt.eventually_ne (by rw [hqa]; exact one_ne_zero)] with z hz
    rw [hh]
    simp only
    rw [mul_pow, hc, ← Complex.exp_nat_mul, ← mul_assoc, mul_inv_cancel₀ hkc, one_mul,
      Complex.exp_log hz, hq]
    simp only
    field_simp
  set w : ℂ → ℂ := fun z => (z - a) * h z with hw
  have hwA : AnalyticAt ℂ w a := (analyticAt_id.sub analyticAt_const).mul hhA
  have hwa : w a = 0 := by simp [hw]
  have hderiv : deriv w a = h a := by
    have hw' : HasDerivAt w (1 * h a + (a - a) * deriv h a) a :=
      ((hasDerivAt_id a).sub_const a).mul hhA.differentiableAt.hasDerivAt
    rw [hw'.deriv]
    simp
  have hstrict : HasStrictDerivAt w (h a) a := by
    have := hwA.hasStrictDerivAt
    rwa [hderiv] at this
  have hmap := hstrict.map_nhds_eq (by rw [hha]; exact hc0)
  have hN : {z | z ∈ U ∧ φ z - φ a = (w z) ^ k} ∈ 𝓝 a := by
    filter_upwards [hU.mem_nhds ha, hfg, hpow] with z hzU hz1 hz2
    refine ⟨hzU, ?_⟩
    have : φ z - φ a = (z - a) ^ k • g z := hz1
    rw [this, smul_eq_mul, hz2]
    change (z - a) ^ k * h z ^ k = ((z - a) * h z) ^ k
    exact (mul_pow _ _ _).symm
  have himg : w '' {z | z ∈ U ∧ φ z - φ a = (w z) ^ k} ∈ 𝓝 (0 : ℂ) := by
    have : w '' {z | z ∈ U ∧ φ z - φ a = (w z) ^ k} ∈ map w (𝓝 a) := image_mem_map hN
    rwa [hmap, hwa] at this
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 himg
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / k) with hζ
  have hprim : IsPrimitiveRoot ζ k := Complex.isPrimitiveRoot_exp k hk0
  have hζ1 : ζ ≠ 1 := hprim.ne_one (by omega)
  have hζk : ζ ^ k = 1 := hprim.pow_eq_one
  have hζn : ‖ζ‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg ζ) hk0).1 (by rw [← norm_pow, hζk, norm_one])
  set u₁ : ℂ := ((ε / 2 : ℝ) : ℂ) with hu₁
  have hu₁n : ‖u₁‖ = ε / 2 := by
    rw [hu₁, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hu₁0 : u₁ ≠ 0 := by
    intro h; rw [h, norm_zero] at hu₁n; linarith
  have hm₁ : u₁ ∈ ball (0 : ℂ) ε := by
    rw [mem_ball, dist_zero_right, hu₁n]; linarith
  have hm₂ : ζ * u₁ ∈ ball (0 : ℂ) ε := by
    rw [mem_ball, dist_zero_right, norm_mul, hζn, hu₁n]; linarith
  obtain ⟨z₁, ⟨hz₁U, hz₁⟩, hwz₁⟩ := hball hm₁
  obtain ⟨z₂, ⟨hz₂U, hz₂⟩, hwz₂⟩ := hball hm₂
  have hφeq : φ z₁ = φ z₂ := by
    have h1 : φ z₁ - φ a = u₁ ^ k := by rw [hz₁, hwz₁]
    have h2 : φ z₂ - φ a = u₁ ^ k := by rw [hz₂, hwz₂, mul_pow, hζk, one_mul]
    linear_combination h1 - h2
  have hzz := hinj hz₁U hz₂U hφeq
  have : u₁ = ζ * u₁ := calc
    u₁ = w z₁ := hwz₁.symm
    _ = w z₂ := by rw [hzz]
    _ = ζ * u₁ := hwz₂
  apply hu₁0
  have h3 : (ζ - 1) * u₁ = 0 := by linear_combination -this
  rcases mul_eq_zero.1 h3 with h | h
  · exact absurd (sub_eq_zero.1 h) hζ1
  · exact h


/-- An injective holomorphic function on an open set has a holomorphic left inverse. -/
theorem exists_holomorphic_inverse {U : Set ℂ} (hU : IsOpen U) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ U) (hinj : InjOn φ U) :
    ∃ ψ : ℂ → ℂ, (∀ z ∈ U, ψ (φ z) = z) ∧ DifferentiableOn ℂ ψ (φ '' U) := by
  refine ⟨Function.invFunOn φ U, fun z hz => hinj.leftInvOn_invFunOn hz, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  have hA : AnalyticAt ℂ φ a := hφ.analyticAt (hU.mem_nhds ha)
  have hne := deriv_ne_zero_of_injOn hU hφ hinj ha
  have hs : HasStrictDerivAt φ (deriv φ a) a := hA.hasStrictDerivAt
  set r := hs.localInverse φ (deriv φ a) a hne with hr
  have hr' : HasStrictDerivAt r (deriv φ a)⁻¹ (φ a) := hs.to_localInverse hne
  have h1 : ∀ᶠ y in 𝓝 (φ a), φ (r y) = y := hs.eventually_right_inverse hne
  have hra : r (φ a) = a := (hs.eventually_left_inverse hne).self_of_nhds
  have h2 : ∀ᶠ y in 𝓝 (φ a), r y ∈ U :=
    hr'.hasDerivAt.continuousAt.eventually_mem (by rw [hra]; exact hU.mem_nhds ha)
  have h3 : Function.invFunOn φ U =ᶠ[𝓝 (φ a)] r := by
    filter_upwards [h1, h2] with y hy1 hy2
    have := hinj.leftInvOn_invFunOn hy2
    rwa [hy1] at this
  exact (hr'.hasDerivAt.differentiableAt.congr_of_eventuallyEq h3).differentiableWithinAt

theorem det_restrictScalars_fderiv (c : ℂ) :
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ).det = ‖c‖ ^ 2 := by
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq,
    Complex.normSq_eq_norm_sq]


/-- Change of variables for an injective holomorphic map: the Jacobian is `|φ'|²`. -/
theorem lintegral_image_complex {U : Set ℂ} (hU : IsOpen U) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ U) (hinj : InjOn φ U) (H : ℂ → ℝ≥0∞) :
    ∫⁻ w in φ '' U, H w = ∫⁻ z in U, ENNReal.ofReal (‖deriv φ z‖ ^ 2) * H (φ z) := by
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hU.measurableSet
    (f := φ)
    (f' := fun z =>
      (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv φ z)).restrictScalars ℝ)
    (fun z hz => ((hφ.differentiableAt (hU.mem_nhds hz)).hasDerivAt.hasFDerivAt.restrictScalars
      ℝ).hasFDerivWithinAt) hinj H
  rw [h]
  refine lintegral_congr fun z => ?_
  rw [det_restrictScalars_fderiv, abs_of_nonneg (sq_nonneg _)]

/-- The Dirichlet energy is invariant under composition with a conformal map. -/
theorem dirichletEnergy_comp {U : Set ℂ} (hU : IsOpen U) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ U) (hinj : InjOn φ U) (hG : IsOpen (φ '' U)) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (φ '' U)) :
    dirichletEnergy (φ '' U) f = dirichletEnergy U (fun z => f (φ z)) := by
  unfold dirichletEnergy
  rw [lintegral_image_complex hU hφ hinj (fun w => ENNReal.ofReal (‖deriv f w‖ ^ 2))]
  refine setLIntegral_congr_fun hU.measurableSet fun z hz => ?_
  have hfz : DifferentiableAt ℂ f (φ z) := hf.differentiableAt (hG.mem_nhds ⟨z, hz, rfl⟩)
  have hφz : DifferentiableAt ℂ φ z := hφ.differentiableAt (hU.mem_nhds hz)
  have hc : deriv (fun z => f (φ z)) z = deriv f (φ z) * deriv φ z := deriv_comp z hfz hφz
  rw [hc, norm_mul, mul_pow, ENNReal.ofReal_mul (sq_nonneg _), mul_comm]


theorem bergmanNormSq_congr {S : Set ℂ} (hS : MeasurableSet S) {u v : ℂ → ℂ}
    (h : ∀ z ∈ S, u z = v z) : bergmanNormSq S u = bergmanNormSq S v :=
  setLIntegral_congr_fun hS fun z hz => by rw [h z hz]

theorem dirichletEnergy_congr {S : Set ℂ} (hS : IsOpen S) {u v : ℂ → ℂ} (h : EqOn u v S) :
    dirichletEnergy S u = dirichletEnergy S v := by
  unfold dirichletEnergy
  refine setLIntegral_congr_fun hS.measurableSet fun z hz => ?_
  rw [Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (hS.mem_nhds hz) h)]

theorem bergmanNormSq_lt_top_of_le {S : Set ℂ} (hS : MeasurableSet S) {w u v : ℂ → ℂ}
    (hu : ContinuousOn u S) (hw : ∀ z ∈ S, ‖w z‖ ^ 2 ≤ 2 * ‖u z‖ ^ 2 + 2 * ‖v z‖ ^ 2)
    (hU : bergmanNormSq S u < ⊤) (hV : bergmanNormSq S v < ⊤) : bergmanNormSq S w < ⊤ := by
  have hum : AEMeasurable (fun z => 2 * ENNReal.ofReal (‖u z‖ ^ 2)) (volume.restrict S) :=
    ((ENNReal.continuous_ofReal.comp_continuousOn (hu.norm.pow 2)).aemeasurable hS).const_mul 2
  calc bergmanNormSq S w
      ≤ ∫⁻ z in S, (2 * ENNReal.ofReal (‖u z‖ ^ 2) + 2 * ENNReal.ofReal (‖v z‖ ^ 2)) := by
        refine setLIntegral_mono' hS fun z hz => ?_
        calc ENNReal.ofReal (‖w z‖ ^ 2) ≤ ENNReal.ofReal (2 * ‖u z‖ ^ 2 + 2 * ‖v z‖ ^ 2) :=
              ENNReal.ofReal_le_ofReal (hw z hz)
          _ = _ := by
              rw [ENNReal.ofReal_add (by positivity) (by positivity),
                ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
              simp
    _ = 2 * bergmanNormSq S u + 2 * bergmanNormSq S v := by
        rw [lintegral_add_left' hum, lintegral_const_mul' _ _ (by simp),
          lintegral_const_mul' _ _ (by simp)]
        rfl
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) hU,
        ENNReal.mul_lt_top (by simp) hV⟩

theorem bergmanNormSq_mul_lt_top {S : Set ℂ} (hS : MeasurableSet S) {c u : ℂ → ℂ} {R : ℝ}
    (hc : ∀ z ∈ S, ‖c z‖ ≤ R) (hu : bergmanNormSq S u < ⊤) :
    bergmanNormSq S (fun z => c z * u z) < ⊤ := by
  calc bergmanNormSq S (fun z => c z * u z)
      ≤ ∫⁻ z in S, ENNReal.ofReal (R ^ 2) * ENNReal.ofReal (‖u z‖ ^ 2) := by
        refine setLIntegral_mono' hS fun z hz => ?_
        rw [← ENNReal.ofReal_mul (sq_nonneg R)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [norm_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hc z hz) 2)
          (sq_nonneg _)
    _ = ENNReal.ofReal (R ^ 2) * bergmanNormSq S u :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu

/-- Multiplier criterion: `c` multiplies `D(S)` into itself iff `c' f ∈ B(S)` for all `f ∈ D(S)`,
for a bounded holomorphic `c`. -/
theorem isMultiplier_iff {S : Set ℂ} (hS : IsOpen S) {c : ℂ → ℂ} (hc : DifferentiableOn ℂ c S)
    {R : ℝ} (hR : ∀ z ∈ S, ‖c z‖ ≤ R) (z₀ : ℂ) :
    IsMultiplier S z₀ c ↔ ∀ f : ℂ → ℂ, IsInDirichletSpace S z₀ f →
      bergmanNormSq S (fun z => deriv c z * f z) < ⊤ := by
  have hSm := hS.measurableSet
  have hcd := hc.deriv hS
  have hderiv : ∀ f : ℂ → ℂ, DifferentiableOn ℂ f S → ∀ z ∈ S,
      deriv (fun z => c z * f z) z = deriv c z * f z + c z * deriv f z :=
    fun f hf z hz => deriv_mul (hc.differentiableAt (hS.mem_nhds hz))
      (hf.differentiableAt (hS.mem_nhds hz))
  constructor
  · intro hM f hf
    have h1 : bergmanNormSq S (deriv fun z => c z * f z) < ⊤ := (hM f hf).2.2
    have h2 : bergmanNormSq S (fun z => c z * deriv f z) < ⊤ :=
      bergmanNormSq_mul_lt_top hSm hR hf.2.2
    refine bergmanNormSq_lt_top_of_le hSm (u := deriv fun z => c z * f z)
      (v := fun z => c z * deriv f z) ((hc.mul hf.1).deriv hS).continuousOn ?_ h1 h2
    intro z hz
    have e : deriv c z * f z = deriv (fun z => c z * f z) z - c z * deriv f z := by
      rw [hderiv f hf.1 z hz]; ring
    rw [e]
    have := sq_norm_add_le (deriv (fun z => c z * f z) z) (-(c z * deriv f z))
    rwa [← sub_eq_add_neg, norm_neg] at this
  · intro H f hf
    refine ⟨hc.mul hf.1, by simp [hf.2.1], ?_⟩
    have e : dirichletEnergy S (fun z => c z * f z) =
        bergmanNormSq S (fun z => deriv c z * f z + c z * deriv f z) :=
      bergmanNormSq_congr hSm fun z hz => hderiv f hf.1 z hz
    rw [e]
    exact bergmanNormSq_lt_top_of_le hSm (u := fun z => deriv c z * f z)
      (v := fun z => c z * deriv f z) (hcd.continuousOn.mul hf.1.continuousOn)
      (fun z _ => sq_norm_add_le _ _) (H f hf) (bergmanNormSq_mul_lt_top hSm hR hf.2.2)

theorem isOpen_unitDisc : IsOpen unitDisc := by
  unfold unitDisc
  exact isOpen_ball

/-- **Theorem 2.5**, proof. -/
theorem riemann_map_characterization_aux {G : Set ℂ} (hbdd : Bornology.IsBounded G)
    (hR : IsRegion G) {z₀ : ℂ} {φ : ℂ → ℂ} (hφ : IsRiemannMap G z₀ φ) :
    (DirichletSubsetBergman G z₀ ↔ IsMultiplier G z₀ id) ∧
    (IsMultiplier G z₀ id ↔ IsMultiplier unitDisc 0 φ) ∧
    (IsMultiplier unitDisc 0 φ ↔
      ∀ g : ℂ → ℂ, IsInDirichletSpace unitDisc 0 g →
        bergmanNormSq unitDisc (fun z => deriv φ z * g z) < ⊤) := by
  obtain ⟨hφ0, hφd, hφinj, hφG⟩ := hφ
  obtain ⟨R, hRb⟩ := hbdd.exists_norm_le
  have hUo := isOpen_unitDisc
  have h0U : (0 : ℂ) ∈ unitDisc := by unfold unitDisc; exact mem_ball_self one_pos
  refine ⟨?_, ?_, ?_⟩
  · rw [isMultiplier_iff hR.1 differentiableOn_id (R := R) (fun z hz => hRb z hz) z₀]
    unfold DirichletSubsetBergman
    have e : ∀ f : ℂ → ℂ, (fun z => deriv id z * f z) = f := fun f => by funext z; simp
    simp only [e]
  · subst hφG
    obtain ⟨ψ, hψφ, hψd⟩ := exists_holomorphic_inverse hUo hφd hφinj
    constructor
    · intro hM g hg
      have hmaps : MapsTo ψ (φ '' unitDisc) unitDisc := by
        rintro _ ⟨z, hz, rfl⟩
        rw [hψφ z hz]; exact hz
      have hψ0 : ψ z₀ = 0 := by rw [← hφ0, hψφ 0 h0U]
      have hfd : DifferentiableOn ℂ (fun w => g (ψ w)) (φ '' unitDisc) := hg.1.comp hψd hmaps
      have hcomp : EqOn (fun z => g (ψ (φ z))) g unitDisc := fun z hz => by
        simp only [hψφ z hz]
      have hf : IsInDirichletSpace (φ '' unitDisc) z₀ (fun w => g (ψ w)) := by
        refine ⟨hfd, by simp [hψ0, hg.2.1], ?_⟩
        rw [dirichletEnergy_comp hUo hφd hφinj hR.1 hfd, dirichletEnergy_congr hUo hcomp]
        exact hg.2.2
      have hmul := hM _ hf
      refine ⟨hφd.mul hg.1, by simp [hg.2.1], ?_⟩
      have h1 := dirichletEnergy_comp hUo hφd hφinj hR.1 hmul.1
      have h2 : EqOn (fun z => (fun w => id w * g (ψ w)) (φ z)) (fun z => φ z * g z) unitDisc :=
        fun z hz => by simp only [id, hψφ z hz]
      rw [← dirichletEnergy_congr hUo h2, ← h1]
      exact hmul.2.2
    · intro hM f hf
      have hg : IsInDirichletSpace unitDisc 0 (fun z => f (φ z)) := by
        refine ⟨hf.1.comp hφd (mapsTo_image φ unitDisc), by simp [hφ0, hf.2.1], ?_⟩
        rw [← dirichletEnergy_comp hUo hφd hφinj hR.1 hf.1]
        exact hf.2.2
      have hmul := hM _ hg
      have hd : DifferentiableOn ℂ (fun w => id w * f w) (φ '' unitDisc) :=
        differentiableOn_id.mul hf.1
      refine ⟨hd, by simp [hf.2.1], ?_⟩
      rw [dirichletEnergy_comp hUo hφd hφinj hR.1 hd]
      exact hmul.2.2
  · refine isMultiplier_iff hUo hφd (R := R) (fun z hz => hRb _ (hφG ▸ mem_image_of_mem φ hz)) 0

end DirichletPoincare
