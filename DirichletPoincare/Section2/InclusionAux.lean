import DirichletPoincare.Definitions
import DirichletPoincare.Section2.AreaMeanValue

/-!
# Auxiliary results for Lemma 2.10 (inclusion `D(G) ⊂ B(G)` is bounded)

The proof applies the open mapping theorem in `L²(G)`. This file contains the analytic input:
a point-evaluation bound `|f(x)|² ≤ C_x ∫_G |f'|²` for `f ∈ D(G)` on a region `G`, and the fact that
`L²` limits of derivatives of elements of `D(G)` are again such derivatives.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

namespace DirichletPoincare

theorem volume_ball_pi_mul (w : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume (ball w r) = ENNReal.ofReal (Real.pi * r ^ 2) := by
  rw [Complex.volume_ball, ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hr, mul_comm]
  congr 1
  exact (ENNReal.ofReal_eq_coe_nnreal Real.pi_pos.le).symm

theorem sq_norm_add_le (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

/-- Local oscillation bound: on `B(p, r/2)` with `B(p, r) ⊆ G`, `|f(y) - f(p)|² ≤ E / π`. -/
theorem sq_norm_sub_le_of_ball {G : Set ℂ} (hG : IsOpen G) {p : ℂ} {r : ℝ} (hr : 0 < r)
    (hball : ball p r ⊆ G) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f G)
    (hE : dirichletEnergy G f ≠ ⊤) {y : ℂ} (hy : y ∈ ball p (r / 2)) :
    ‖f y - f p‖ ^ 2 ≤ (dirichletEnergy G f).toReal / Real.pi := by
  set E := (dirichletEnergy G f).toReal with hEdef
  have hfd : DifferentiableOn ℂ (deriv f) G := hf.deriv hG
  have hr2 : 0 < r / 2 := by positivity
  have hpt : ∀ u ∈ ball p (r / 2), ‖deriv f u‖ ^ 2 * (Real.pi * (r / 2) ^ 2) ≤ E := by
    intro u hu
    have hsub : ball u (r / 2) ⊆ ball p r := by
      intro x hx
      rw [mem_ball] at hu hx ⊢
      calc dist x p ≤ dist x u + dist u p := dist_triangle _ _ _
        _ < r := by linarith
    have h1 := sq_mul_volume_le hr2 (hfd.mono (hsub.trans hball))
    rw [volume_ball_pi_mul _ hr2.le, ← ENNReal.ofReal_mul (sq_nonneg _)] at h1
    have h2 : ENNReal.ofReal (‖deriv f u‖ ^ 2 * (Real.pi * (r / 2) ^ 2)) ≤ dirichletEnergy G f :=
      h1.trans (lintegral_mono_set (hsub.trans hball))
    exact (ENNReal.ofReal_le_iff_le_toReal hE).1 h2
  set M := E / (Real.pi * (r / 2) ^ 2) with hM
  have hM0 : 0 ≤ M := by positivity
  have hC : ∀ u ∈ ball p (r / 2), ‖deriv f u‖ ≤ Real.sqrt M := by
    intro u hu
    have h' : ‖deriv f u‖ ^ 2 ≤ M := by
      rw [hM, le_div_iff₀ (by positivity)]
      exact hpt u hu
    simpa [abs_of_nonneg (norm_nonneg _)] using Real.abs_le_sqrt h'
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (s := ball p (r / 2))
    (x := p) (y := y)
    (fun x hx => hf.differentiableAt (hG.mem_nhds (hball (ball_subset_ball (by linarith) hx))))
    hC (convex_ball _ _) (mem_ball_self hr2) hy
  have hyp : ‖y - p‖ ≤ r / 2 := by
    rw [mem_ball, dist_eq_norm] at hy
    exact hy.le
  calc ‖f y - f p‖ ^ 2 ≤ (Real.sqrt M * ‖y - p‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hmv 2
    _ = M * ‖y - p‖ ^ 2 := by rw [mul_pow, Real.sq_sqrt hM0]
    _ ≤ M * (r / 2) ^ 2 := by gcongr
    _ = E / Real.pi := by
        rw [hM]
        field_simp

/-- The pointwise evaluation `f ↦ f(x)` is controlled by the Dirichlet energy on `D(G)`. -/
def PtBound (G : Set ℂ) (z₀ x : ℂ) : Prop :=
  ∃ C : ℝ, ∀ f : ℂ → ℂ, IsInDirichletSpace G z₀ f →
    ‖f x‖ ^ 2 ≤ C * (dirichletEnergy G f).toReal

theorem ptBound_iff {G : Set ℂ} (hG : IsOpen G) {z₀ p y : ℂ} {r : ℝ} (hr : 0 < r)
    (hball : ball p r ⊆ G) (hy : y ∈ ball p (r / 2)) : PtBound G z₀ p ↔ PtBound G z₀ y := by
  have hpi := Real.pi_pos
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨2 * C + 2 / Real.pi, fun f hf => ?_⟩
    have h1 := sq_norm_sub_le_of_ball hG hr hball hf.1 hf.2.2.ne hy
    have h2 := hC f hf
    have h3 := sq_norm_add_le (f y - f p) (f p)
    rw [sub_add_cancel] at h3
    have : 2 / Real.pi * (dirichletEnergy G f).toReal = 2 * ((dirichletEnergy G f).toReal /
        Real.pi) := by ring
    nlinarith
  · rintro ⟨C, hC⟩
    refine ⟨2 * C + 2 / Real.pi, fun f hf => ?_⟩
    have h1 := sq_norm_sub_le_of_ball hG hr hball hf.1 hf.2.2.ne hy
    have h2 := hC f hf
    have h3 := sq_norm_add_le (f p - f y) (f y)
    rw [sub_add_cancel, norm_sub_rev] at h3
    have : 2 / Real.pi * (dirichletEnergy G f).toReal = 2 * ((dirichletEnergy G f).toReal /
        Real.pi) := by ring
    nlinarith

theorem ptBound_of_region {G : Set ℂ} (hR : IsRegion G) {z₀ : ℂ} (hz₀ : z₀ ∈ G) {x : ℂ}
    (hx : x ∈ G) : PtBound G z₀ x := by
  have hG := hR.1
  have hz : PtBound G z₀ z₀ := ⟨0, fun f hf => by rw [hf.2.1]; simp⟩
  have hopen : ∀ P : Prop, ∀ (S : Set ℂ), S = {x | x ∈ G ∧ (PtBound G z₀ x ↔ P)} → IsOpen S := by
    intro P S hS
    rw [hS, Metric.isOpen_iff]
    rintro x ⟨hxG, hxP⟩
    obtain ⟨r, hr, hrG⟩ := Metric.isOpen_iff.1 hG x hxG
    refine ⟨r / 2, by positivity, fun y hy => ⟨hrG (ball_subset_ball (by linarith) hy), ?_⟩⟩
    rw [← hxP]
    exact (ptBound_iff hG hr hrG hy).symm
  set S₁ : Set ℂ := {x | x ∈ G ∧ (PtBound G z₀ x ↔ True)} with hS₁
  set S₂ : Set ℂ := {x | x ∈ G ∧ (PtBound G z₀ x ↔ False)} with hS₂
  have hdisj : Disjoint S₁ S₂ := by
    rw [Set.disjoint_left]
    rintro y ⟨-, h1⟩ ⟨-, h2⟩
    exact h2.1 (h1.2 trivial)
  have hcover : G ⊆ S₁ ∪ S₂ := by
    intro y hy
    by_cases h : PtBound G z₀ y
    · exact Or.inl ⟨hy, iff_true_intro h⟩
    · exact Or.inr ⟨hy, iff_false_intro h⟩
  rcases hR.2.isPreconnected.subset_or_subset (hopen True S₁ hS₁) (hopen False S₂ hS₂) hdisj
    hcover with h | h
  · exact (h hx).2.2 trivial
  · exact absurd ((h hz₀).2.1 hz) (by simp)

theorem local_bound {G : Set ℂ} (hR : IsRegion G) {z₀ : ℂ} (hz₀ : z₀ ∈ G) {x : ℂ} (hx : x ∈ G) :
    ∃ r > 0, ∃ C : ℝ, ball x r ⊆ G ∧ ∀ f : ℂ → ℂ, IsInDirichletSpace G z₀ f →
      ∀ y ∈ ball x r, ‖f y‖ ^ 2 ≤ C * (dirichletEnergy G f).toReal := by
  obtain ⟨r₀, hr₀, hrG⟩ := Metric.isOpen_iff.1 hR.1 x hx
  obtain ⟨C₀, hC₀⟩ := ptBound_of_region hR hz₀ hx
  have hpi := Real.pi_pos
  refine ⟨r₀ / 2, by positivity, 2 * C₀ + 2 / Real.pi, ?_, fun f hf y hy => ?_⟩
  · exact (ball_subset_ball (by linarith)).trans hrG
  · have h1 := sq_norm_sub_le_of_ball hR.1 hr₀ hrG hf.1 hf.2.2.ne hy
    have h2 := hC₀ f hf
    have h3 := sq_norm_add_le (f y - f x) (f x)
    rw [sub_add_cancel] at h3
    have : 2 / Real.pi * (dirichletEnergy G f).toReal = 2 * ((dirichletEnergy G f).toReal /
        Real.pi) := by ring
    nlinarith


/-- `eLpNorm h 2` as a power of the integral of `|h|²`. -/
theorem eLpNorm_two_eq {h : ℂ → ℂ} {μ : Measure ℂ} (hm : AEStronglyMeasurable h μ) :
    eLpNorm h 2 μ = (∫⁻ x, ENNReal.ofReal (‖h x‖ ^ 2) ∂μ) ^ (2 : ℝ)⁻¹ := by
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  rw [h2, eLpNorm_eq_lintegral_rpow_eNorm_toReal (ENNReal.ofReal_pos.2 (by norm_num)).ne'
    ENNReal.ofReal_ne_top hm, ENNReal.toReal_ofReal (by norm_num), one_div]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
    Real.rpow_two]

theorem lintegral_sq_eq {h : ℂ → ℂ} {μ : Measure ℂ} (hm : AEStronglyMeasurable h μ) :
    ∫⁻ x, ENNReal.ofReal (‖h x‖ ^ 2) ∂μ = eLpNorm h 2 μ ^ (2 : ℝ) := by
  rw [eLpNorm_two_eq hm, ENNReal.rpow_inv_rpow (by norm_num)]

theorem dirichletEnergy_eq_rpow {G : Set ℂ} {f : ℂ → ℂ} (h : Lp ℂ 2 (volume.restrict G))
    (hae : h =ᵐ[volume.restrict G] deriv f) :
    dirichletEnergy G f = eLpNorm h 2 (volume.restrict G) ^ (2 : ℝ) := by
  rw [← lintegral_sq_eq (Lp.aestronglyMeasurable h)]
  unfold dirichletEnergy
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [hx]

theorem dirichletEnergy_ne_top {G : Set ℂ} {f : ℂ → ℂ} (h : Lp ℂ 2 (volume.restrict G))
    (hae : h =ᵐ[volume.restrict G] deriv f) : dirichletEnergy G f ≠ ⊤ := by
  rw [dirichletEnergy_eq_rpow h hae]
  exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (Lp.eLpNorm_ne_top h)

theorem dirichletEnergy_toReal_eq {G : Set ℂ} {f : ℂ → ℂ} (h : Lp ℂ 2 (volume.restrict G))
    (hae : h =ᵐ[volume.restrict G] deriv f) : (dirichletEnergy G f).toReal = ‖h‖ ^ 2 := by
  rw [dirichletEnergy_eq_rpow h hae, ← ENNReal.toReal_rpow, Real.rpow_two, Lp.norm_def]

theorem isInDirichletSpace_of_lp {G : Set ℂ} {z₀ : ℂ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f G) (hz : f z₀ = 0) (h : Lp ℂ 2 (volume.restrict G))
    (hae : h =ᵐ[volume.restrict G] deriv f) : IsInDirichletSpace G z₀ f :=
  ⟨hf, hz, lt_top_iff_ne_top.2 (dirichletEnergy_ne_top h hae)⟩

/-- An `L²` limit that is a pointwise limit a.e. along a subsequence of representatives. -/
theorem ae_eq_of_lp_tendsto {μ : Measure ℂ} {u : ℕ → Lp ℂ 2 μ} {v : Lp ℂ 2 μ}
    (h : Tendsto u atTop (𝓝 v)) {φ : ℕ → ℂ → ℂ} (hu : ∀ k, u k =ᵐ[μ] φ k) {w : ℂ → ℂ}
    (hw : ∀ᵐ x ∂μ, Tendsto (fun k => φ k x) atTop (𝓝 (w x))) : v =ᵐ[μ] w := by
  have h1 : Tendsto (fun n => eLpNorm (⇑(u n) - ⇑v) 2 μ) atTop (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm' u v).1 h
  have hm := tendstoInMeasure_of_tendsto_eLpNorm (f := fun n => ⇑(u n)) (g := ⇑v)
    (by norm_num) h1
  obtain ⟨ns, hns, hae⟩ := hm.exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂μ, ∀ k, u k x = φ k x := ae_all_iff.2 hu
  filter_upwards [hae, hall, hw] with x h1 h2 h3
  have h4 : Tendsto (fun i => u (ns i) x) atTop (𝓝 (w x)) := by
    simp_rw [h2]
    exact h3.comp hns.tendsto_atTop
  exact tendsto_nhds_unique h1 h4

/-- Differences of primitives have the difference of the `L²` derivatives as derivative. -/
theorem sub_isInDirichlet {G : Set ℂ} (hG : IsOpen G) {z₀ : ℂ} {F : ℕ → ℂ → ℂ}
    (hF : ∀ k, DifferentiableOn ℂ (F k) G) (hF0 : ∀ k, F k z₀ = 0)
    {g : ℕ → Lp ℂ 2 (volume.restrict G)} (hg : ∀ k, g k =ᵐ[volume.restrict G] deriv (F k))
    (k l : ℕ) :
    IsInDirichletSpace G z₀ (fun z => F k z - F l z) ∧
      (dirichletEnergy G (fun z => F k z - F l z)).toReal = ‖g k - g l‖ ^ 2 := by
  have hae : ⇑(g k - g l) =ᵐ[volume.restrict G] deriv (fun z => F k z - F l z) := by
    filter_upwards [Lp.coeFn_sub (g k) (g l), hg k, hg l, ae_restrict_mem hG.measurableSet]
      with x h1 h2 h3 hx
    rw [h1, Pi.sub_apply, h2, h3]
    exact (deriv_sub (((hF k).differentiableAt (hG.mem_nhds hx)))
      (((hF l).differentiableAt (hG.mem_nhds hx)))).symm
  exact ⟨isInDirichletSpace_of_lp ((hF k).sub (hF l)) (by simp [hF0]) _ hae,
    dirichletEnergy_toReal_eq _ hae⟩


/-- If primitives `F k` (vanishing at `z₀`) have derivatives converging in `L²`, they converge
locally uniformly to a primitive of the limit. -/
theorem exists_limit_primitive {G : Set ℂ} (hR : IsRegion G) {z₀ : ℂ} (hz₀ : z₀ ∈ G)
    {F : ℕ → ℂ → ℂ} (hF : ∀ k, DifferentiableOn ℂ (F k) G) (hF0 : ∀ k, F k z₀ = 0)
    {g : ℕ → Lp ℂ 2 (volume.restrict G)} {g' : Lp ℂ 2 (volume.restrict G)}
    (hg : ∀ k, g k =ᵐ[volume.restrict G] deriv (F k)) (hlim : Tendsto g atTop (𝓝 g')) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f G ∧ f z₀ = 0 ∧ g' =ᵐ[volume.restrict G] deriv f ∧
      ∀ x ∈ G, Tendsto (fun k => F k x) atTop (𝓝 (f x)) := by
  have hGm : MeasurableSet G := hR.1.measurableSet
  have hdiff := sub_isInDirichlet hR.1 hF hF0 hg
  have hcg : CauchySeq g := hlim.cauchySeq
  have hunif : ∀ x₀ ∈ G, ∃ r > 0, ball x₀ r ⊆ G ∧ UniformCauchySeqOn F atTop (ball x₀ r) := by
    intro x₀ hx₀
    obtain ⟨r, hr, C, hball, hbd⟩ := local_bound hR hz₀ hx₀
    refine ⟨r, hr, hball, ?_⟩
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    set C' := max C 0 with hC'
    have hC'0 : 0 ≤ C' := le_max_right _ _
    have hδ : 0 < ε / (C' + 1) := by positivity
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hcg (ε / (C' + 1)) hδ
    refine ⟨N, fun m hm n hn y hy => ?_⟩
    have h1 := hbd _ (hdiff m n).1 y hy
    rw [(hdiff m n).2] at h1
    have h2 : C * ‖g m - g n‖ ^ 2 ≤ C' * ‖g m - g n‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    have h3 : ‖g m - g n‖ < ε / (C' + 1) := by
      have := hN m hm n hn
      rwa [dist_eq_norm] at this
    have h4 : ‖g m - g n‖ ^ 2 ≤ (ε / (C' + 1)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h3.le 2
    have h5 : C' * (ε / (C' + 1)) ^ 2 < ε ^ 2 := by
      rw [div_pow, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
      nlinarith [sq_pos_of_pos hε, mul_pos (sq_pos_of_pos hε) (by positivity : (0 : ℝ) < C' + 1)]
    have h6 : ‖F m y - F n y‖ ^ 2 < ε ^ 2 := by
      calc ‖F m y - F n y‖ ^ 2 ≤ C' * ‖g m - g n‖ ^ 2 := h1.trans h2
        _ ≤ C' * (ε / (C' + 1)) ^ 2 := mul_le_mul_of_nonneg_left h4 hC'0
        _ < ε ^ 2 := h5
    rw [dist_eq_norm]
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h6
  have hcau : ∀ x ∈ G, CauchySeq fun k => F k x := by
    intro x hx
    obtain ⟨r, hr, hb, hU⟩ := hunif x hx
    exact hU.cauchySeq (mem_ball_self hr)
  set f : ℂ → ℂ := fun x => limUnder atTop fun k => F k x with hf
  have hpt : ∀ x ∈ G, Tendsto (fun k => F k x) atTop (𝓝 (f x)) :=
    fun x hx => (hcau x hx).tendsto_limUnder
  have hloc : TendstoLocallyUniformlyOn F f atTop G := by
    refine tendstoLocallyUniformlyOn_of_forall_exists_nhds fun x hx => ?_
    obtain ⟨r, hr, hb, hU⟩ := hunif x hx
    exact ⟨ball x r, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hr),
      hU.tendstoUniformlyOn_of_tendsto fun y hy => hpt y (hb hy)⟩
  have hfd : DifferentiableOn ℂ f G :=
    hloc.differentiableOn (Eventually.of_forall hF) hR.1
  have hder := hloc.deriv (Eventually.of_forall hF) hR.1
  refine ⟨f, hfd, ?_, ?_, hpt⟩
  · exact tendsto_nhds_unique (hpt z₀ hz₀) (by simp [hF0])
  · refine ae_eq_of_lp_tendsto hlim hg ?_
    filter_upwards [ae_restrict_mem hGm] with x hx
    exact hder.tendsto_at hx


/-- The graph `{([f'], [f]) : f ∈ D(G)}` inside `L²(G) × L²(G)`. -/
def graphSub {G : Set ℂ} (hG : IsOpen G) (z₀ : ℂ) :
    Submodule ℂ (Lp ℂ 2 (volume.restrict G) × Lp ℂ 2 (volume.restrict G)) where
  carrier := {p | ∃ f : ℂ → ℂ, DifferentiableOn ℂ f G ∧ f z₀ = 0 ∧
    p.1 =ᵐ[volume.restrict G] deriv f ∧ p.2 =ᵐ[volume.restrict G] f}
  zero_mem' := by
    refine ⟨fun _ => 0, differentiableOn_const 0, rfl, ?_, ?_⟩
    · filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict G)] with x hx
      exact hx.trans (by simp)
    · filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict G)] with x hx
      exact hx
  add_mem' := by
    rintro p q ⟨f, hf, hf0, hp1, hp2⟩ ⟨k, hk, hk0, hq1, hq2⟩
    refine ⟨fun z => f z + k z, hf.add hk, by simp [hf0, hk0], ?_, ?_⟩
    · filter_upwards [Lp.coeFn_add p.1 q.1, hp1, hq1, ae_restrict_mem hG.measurableSet]
        with x h1 h2 h3 hx
      have e : (p + q).1 = p.1 + q.1 := rfl
      rw [e, h1, Pi.add_apply, h2, h3]
      exact (deriv_add (hf.differentiableAt (hG.mem_nhds hx))
        (hk.differentiableAt (hG.mem_nhds hx))).symm
    · filter_upwards [Lp.coeFn_add p.2 q.2, hp2, hq2] with x h1 h2 h3
      have e : (p + q).2 = p.2 + q.2 := rfl
      rw [e, h1, Pi.add_apply, h2, h3]
  smul_mem' := by
    rintro c p ⟨f, hf, hf0, hp1, hp2⟩
    refine ⟨fun z => c • f z, hf.const_smul c, by simp [hf0], ?_, ?_⟩
    · filter_upwards [Lp.coeFn_smul c p.1, hp1, ae_restrict_mem hG.measurableSet]
        with x h1 h2 hx
      have e : (c • p).1 = c • p.1 := rfl
      rw [e, h1, Pi.smul_apply, h2]
      exact (deriv_const_smul c (hf.differentiableAt (hG.mem_nhds hx))).symm
    · filter_upwards [Lp.coeFn_smul c p.2, hp2] with x h1 h2
      have e : (c • p).2 = c • p.2 := rfl
      rw [e, h1, Pi.smul_apply, h2]

theorem memLp_of_bergman {G : Set ℂ} (hG : IsOpen G) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f G) (hB : bergmanNormSq G f < ⊤) :
    MemLp f 2 (volume.restrict G) := by
  have hm : AEStronglyMeasurable f (volume.restrict G) :=
    hf.continuousOn.aestronglyMeasurable hG.measurableSet
  refine memLp_iff.2 ?_
  rw [eLpNorm_two_eq hm]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hB.ne

theorem memLp_deriv_of_energy {G : Set ℂ} {f : ℂ → ℂ} (hE : dirichletEnergy G f < ⊤) :
    MemLp (deriv f) 2 (volume.restrict G) := by
  have hm : AEStronglyMeasurable (deriv f) (volume.restrict G) :=
    (measurable_deriv f).aestronglyMeasurable
  refine memLp_iff.2 ?_
  rw [eLpNorm_two_eq hm]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hE.ne

/-- **Lemma 2.10**, with an explicit finite constant. -/
theorem inclusion_bounded_aux {G : Set ℂ} (hR : IsRegion G) {z₀ : ℂ} (hz₀ : z₀ ∈ G)
    (h : DirichletSubsetBergman G z₀) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ f : ℂ → ℂ, IsInDirichletSpace G z₀ f →
      bergmanNormSq G f ≤ C * dirichletEnergy G f := by
  have hG := hR.1
  have hGm : MeasurableSet G := hG.measurableSet
  set Γ := graphSub hG z₀ with hΓ
  have hΓclosed : IsClosed (Γ : Set (Lp ℂ 2 (volume.restrict G) × Lp ℂ 2 (volume.restrict G))) := by
    rw [← isSeqClosed_iff_isClosed]
    intro p q hp hpq
    have hp' : ∀ n, ∃ f : ℂ → ℂ, DifferentiableOn ℂ f G ∧ f z₀ = 0 ∧
        (p n).1 =ᵐ[volume.restrict G] deriv f ∧ (p n).2 =ᵐ[volume.restrict G] f := hp
    choose F hF hF0 hg ha using hp'
    have h1 : Tendsto (fun k => (p k).1) atTop (𝓝 q.1) :=
      (continuous_fst.tendsto q).comp hpq
    have h2 : Tendsto (fun k => (p k).2) atTop (𝓝 q.2) :=
      (continuous_snd.tendsto q).comp hpq
    obtain ⟨f, hfd, hf0, hgq, hlimf⟩ := exists_limit_primitive hR hz₀ hF hF0 hg h1
    refine ⟨f, hfd, hf0, hgq, ae_eq_of_lp_tendsto h2 ha ?_⟩
    filter_upwards [ae_restrict_mem hGm] with x hx
    exact hlimf x hx
  have : CompleteSpace Γ := hΓclosed.isComplete.completeSpace_coe
  let P : Γ →L[ℂ] Lp ℂ 2 (volume.restrict G) :=
    (ContinuousLinearMap.fst ℂ (Lp ℂ 2 (volume.restrict G)) (Lp ℂ 2 (volume.restrict G))).comp
      Γ.subtypeL
  have hPγ : ∀ γ : Γ, P γ = (γ : Lp ℂ 2 (volume.restrict G) × Lp ℂ 2 (volume.restrict G)).1 :=
    fun γ => rfl
  have hPinj : Function.Injective P := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨⟨g, a⟩, f, hfd, hf0, hg, ha⟩ hγ
    rw [hPγ] at hγ
    have hg0 : g = 0 := hγ
    subst hg0
    have hder : (deriv f) =ᵐ[volume.restrict G] (0 : ℂ → ℂ) := by
      filter_upwards [hg, Lp.coeFn_zero ℂ 2 (volume.restrict G)] with x h1 h2
      rw [← h1, h2]
    have hder' := Measure.eqOn_open_of_ae_eq hder hG (hfd.deriv hG).continuousOn
      continuousOn_const
    have hdc : ∀ x ∈ G, f x = 0 := fun x hx =>
      (hG.is_const_of_deriv_eq_zero hR.2.isPreconnected hfd hder' hx hz₀).trans hf0
    refine Subtype.ext (Prod.ext rfl (Lp.ext ?_))
    change ⇑a =ᵐ[volume.restrict G] ⇑(0 : Lp ℂ 2 (volume.restrict G))
    filter_upwards [ha, Lp.coeFn_zero ℂ 2 (volume.restrict G), ae_restrict_mem hGm]
      with x h1 h2 hx
    rw [h1, h2]
    exact hdc x hx
  have hrange : IsClosed (Set.range P) := by
    rw [← isSeqClosed_iff_isClosed]
    intro u v hu huv
    choose γ hγ using hu
    have hγ' : ∀ n, ∃ f : ℂ → ℂ, DifferentiableOn ℂ f G ∧ f z₀ = 0 ∧
        (γ n : Lp ℂ 2 (volume.restrict G) × Lp ℂ 2 (volume.restrict G)).1 =ᵐ[volume.restrict G]
          deriv f ∧
        (γ n : Lp ℂ 2 (volume.restrict G) × Lp ℂ 2 (volume.restrict G)).2 =ᵐ[volume.restrict G]
          f := fun n => (γ n).2
    choose F hF hF0 hg ha using hγ'
    have hu' : ∀ n, u n =ᵐ[volume.restrict G] deriv (F n) := fun n => by
      rw [← hγ n, hPγ]
      exact hg n
    obtain ⟨f, hfd, hf0, hgq, -⟩ := exists_limit_primitive hR hz₀ hF hF0 hu' huv
    have hfD := isInDirichletSpace_of_lp hfd hf0 v hgq
    have hmem := memLp_of_bergman hG hfd (h f hfD)
    exact ⟨⟨(v, hmem.toLp f), f, hfd, hf0, hgq, hmem.coeFn_toLp⟩, rfl⟩
  obtain ⟨K, hK⟩ := P.antilipschitz_of_injective_of_isClosed_range hPinj hrange
  refine ⟨(K : ℝ≥0∞) ^ (2 : ℝ), ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.coe_ne_top,
    fun f hf => ?_⟩
  have hmemf := memLp_of_bergman hG hf.1 (h f hf)
  have hmemd := memLp_deriv_of_energy hf.2.2
  let γ : Γ := ⟨(hmemd.toLp (deriv f), hmemf.toLp f),
    f, hf.1, hf.2.1, hmemd.coeFn_toLp, hmemf.coeFn_toLp⟩
  have h1 := hK.le_mul_dist γ 0
  rw [dist_zero_right, map_zero, dist_zero_right, hPγ] at h1
  have h2 : ‖hmemf.toLp f‖ ≤ ‖(γ : Lp ℂ 2 (volume.restrict G) × Lp ℂ 2 (volume.restrict G))‖ :=
    norm_snd_le (γ : Lp ℂ 2 (volume.restrict G) × Lp ℂ 2 (volume.restrict G))
  have h3 : ‖hmemf.toLp f‖ ≤ K * ‖hmemd.toLp (deriv f)‖ := by
    refine h2.trans (h1.trans ?_)
    rw [Submodule.norm_coe] at *
  rw [Lp.norm_toLp, Lp.norm_toLp] at h3
  have ha : eLpNorm f 2 (volume.restrict G) ≠ ⊤ := (memLp_iff.1 hmemf).ne
  have hb : eLpNorm (deriv f) 2 (volume.restrict G) ≠ ⊤ := (memLp_iff.1 hmemd).ne
  have h4 : eLpNorm f 2 (volume.restrict G) ≤ K * eLpNorm (deriv f) 2 (volume.restrict G) := by
    rw [← ENNReal.toReal_le_toReal ha (ENNReal.mul_ne_top ENNReal.coe_ne_top hb),
      ENNReal.toReal_mul, ENNReal.coe_toReal]
    exact h3
  have hbf : bergmanNormSq G f = eLpNorm f 2 (volume.restrict G) ^ (2 : ℝ) :=
    lintegral_sq_eq hmemf.aestronglyMeasurable
  have hdf : dirichletEnergy G f = eLpNorm (deriv f) 2 (volume.restrict G) ^ (2 : ℝ) :=
    lintegral_sq_eq hmemd.aestronglyMeasurable
  rw [hbf, hdf, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  exact ENNReal.rpow_le_rpow h4 (by norm_num)

end DirichletPoincare
