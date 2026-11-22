import DirichletPoincare.Section3.NoPoincare

/-!
# The boundary of `regionT` is rectifiable (thesis Theorem 3.14)

The frontier of `regionT` is contained in `{0}`, the circles `∂Dsc k` and the boundaries of the
rectangles `Tk k`. Each is a Lipschitz image of an interval, and the total length is finite since
`cₖ ≤ 4⁻ᵏ`.
-/

open MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace DirichletPoincare

theorem cc_le_pow (k : ℕ) : cc k ≤ (1 / 4 : ℝ) ^ k := by
  induction k with
  | zero => simp [cc_zero]
  | succ k ih =>
    calc cc (k + 1) ≤ cc k / 4 := cc_succ_le k
      _ ≤ (1 / 4 : ℝ) ^ k / 4 := by linarith
      _ = (1 / 4 : ℝ) ^ (k + 1) := by ring

theorem hh_le_cc (k : ℕ) : hh k ≤ cc k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [hh, cc, mm_zero]
  · have := hh_le k hk
    have := cc_pos k
    linarith

theorem hausdorff_image_Icc {f : ℝ → ℂ} (hf : LipschitzWith 1 f) (lo hi : ℝ) :
    Measure.hausdorffMeasure 1 (f '' Icc lo hi) ≤ ENNReal.ofReal (hi - lo) := by
  have := hf.hausdorffMeasure_image_le zero_le_one (Icc lo hi)
  simp only [ENNReal.coe_one, ENNReal.one_rpow, one_mul] at this
  refine this.trans ?_
  rw [hausdorffMeasure_real, Real.volume_Icc]

/-- Vertical segment `{a + y i}`. -/
noncomputable def vmap (a : ℝ) (y : ℝ) : ℂ := (a : ℂ) + (y : ℂ) * Complex.I

/-- Horizontal segment `{x + b i}`. -/
noncomputable def hmap (b : ℝ) (x : ℝ) : ℂ := (x : ℂ) + (b : ℂ) * Complex.I

theorem lipschitz_vmap (a : ℝ) : LipschitzWith 1 (vmap a) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [vmap, Complex.dist_eq, NNReal.coe_one, one_mul, Real.dist_eq]
  rw [add_sub_add_left_eq_sub, ← sub_mul, norm_mul, Complex.norm_I, mul_one,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

theorem lipschitz_hmap (b : ℝ) : LipschitzWith 1 (hmap b) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [hmap, Complex.dist_eq, NNReal.coe_one, one_mul, Real.dist_eq]
  rw [add_sub_add_right_eq_sub, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

theorem hausdorff_sphere_le (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    Measure.hausdorffMeasure 1 (sphere c r) ≤ ENNReal.ofReal (r * (2 * Real.pi)) := by
  have h := (lipschitzWith_circleMap c r).hausdorffMeasure_image_le zero_le_one
    (Ioc 0 (2 * Real.pi))
  rw [image_circleMap_Ioc, abs_of_nonneg hr] at h
  refine h.trans ?_
  have hn : (Real.nnabs r : ℝ≥0∞) = ENNReal.ofReal r := by
    rw [ENNReal.ofReal_eq_coe_nnreal hr]
    congr 1
    exact Subtype.ext (abs_of_nonneg hr)
  rw [hausdorffMeasure_real, Real.volume_Ioc, ENNReal.rpow_one, sub_zero, hn,
    ← ENNReal.ofReal_mul hr]

/-- The pieces of the frontier of the rectangle `Tk k`. -/
noncomputable def rectBoundary (k : ℕ) : Set ℂ :=
  (vmap (cc k) '' Icc (-hh k) (hh k)) ∪ (vmap (cc (k - 1)) '' Icc (-hh k) (hh k)) ∪
    (hmap (hh k) '' Icc (cc k) (cc (k - 1))) ∪ (hmap (-hh k) '' Icc (cc k) (cc (k - 1)))

theorem frontier_Tk_subset (k : ℕ) : frontier (Tk k) ⊆ rectBoundary k := by
  intro z hz
  rw [(isOpen_Tk k).frontier_eq] at hz
  obtain ⟨hcl, hnot⟩ := hz
  have hclosed : IsClosed {z : ℂ | cc k ≤ z.re ∧ z.re ≤ cc (k - 1) ∧ |z.im| ≤ hh k} := by
    have : {z : ℂ | cc k ≤ z.re ∧ z.re ≤ cc (k - 1) ∧ |z.im| ≤ hh k} =
        {z : ℂ | cc k ≤ z.re} ∩ ({z : ℂ | z.re ≤ cc (k - 1)} ∩ {z : ℂ | |z.im| ≤ hh k}) := rfl
    rw [this]
    refine (isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le Complex.continuous_re continuous_const).inter ?_)
    exact isClosed_le Complex.continuous_im.abs continuous_const
  have hsub : Tk k ⊆ {z : ℂ | cc k ≤ z.re ∧ z.re ≤ cc (k - 1) ∧ |z.im| ≤ hh k} :=
    fun w hw => ⟨hw.1.le, hw.2.1.le, hw.2.2.le⟩
  obtain ⟨h1, h2, h3⟩ := closure_minimal hsub hclosed hcl
  have hz' : z = vmap z.re z.im ∧ z = hmap z.im z.re := by
    constructor <;> apply Complex.ext <;> simp [vmap, hmap]
  have him : z.im ∈ Icc (-hh k) (hh k) := abs_le.1 h3
  by_cases hre1 : z.re = cc k
  · left; left; left
    exact ⟨z.im, him, by rw [vmap, ← hre1]; exact hz'.1.symm⟩
  by_cases hre2 : z.re = cc (k - 1)
  · left; left; right
    exact ⟨z.im, him, by rw [vmap, ← hre2]; exact hz'.1.symm⟩
  have hre : z.re ∈ Icc (cc k) (cc (k - 1)) := ⟨h1, h2⟩
  have hlt1 : cc k < z.re := lt_of_le_of_ne h1 (Ne.symm hre1)
  have hlt2 : z.re < cc (k - 1) := lt_of_le_of_ne h2 hre2
  have him' : |z.im| = hh k := by
    by_contra hne
    exact hnot ⟨hlt1, hlt2, lt_of_le_of_ne h3 hne⟩
  have hpm : z.im = hh k ∨ z.im = -hh k := by
    rcases abs_choice z.im with h | h
    · left; linarith
    · right; linarith
  rcases hpm with h | h
  · left; right
    refine ⟨z.re, hre, ?_⟩
    rw [← h]
    exact hz'.2.symm
  · right
    refine ⟨z.re, hre, ?_⟩
    rw [← h]
    exact hz'.2.symm


theorem Tk_subset_regionT (k : ℕ) : Tk k ⊆ regionT := fun _ hz => mem_iUnion.2 ⟨k, Or.inr hz⟩

theorem frontier_regionT_subset :
    frontier regionT ⊆ {0} ∪ ⋃ k, (sphere ((cc k : ℝ) : ℂ) (cc k / 4) ∪ rectBoundary k) := by
  intro x hx
  rw [isOpen_regionT.frontier_eq] at hx
  obtain ⟨hcl, hnot⟩ := hx
  by_cases hx0 : x = 0
  · exact Or.inl hx0
  right
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < ‖x‖ / 2)
    (by norm_num : (1 / 4 : ℝ) < 1)
  have hcN : 2 * cc N < ‖x‖ := by
    have := cc_le_pow N
    linarith
  have hcNpos := cc_pos N
  let P : ℕ → Set ℂ := fun k => Dsc k ∪ Tk k
  have hBsub : (⋃ k ∈ Ioi N, P k) ⊆ ball (0 : ℂ) (2 * cc N) := by
    intro z hz
    obtain ⟨k, hk, hz⟩ := mem_iUnion₂.1 hz
    have hk' : N < k := hk
    rw [mem_ball, dist_zero_right]
    have hck : cc k ≤ cc N := cc_antitone hk'.le
    rcases hz with hz | hz
    · have := norm_lt_of_mem_Dsc hz
      linarith
    · obtain ⟨h1, h2, h3⟩ := hz
      have hk1 : 1 ≤ k := by omega
      have hh1 := hh_le k hk1
      have hck1 : cc (k - 1) ≤ cc N := cc_antitone (by omega)
      have hre0 : 0 < z.re := (cc_pos k).trans h1
      have := Complex.norm_le_abs_re_add_abs_im z
      rw [abs_of_pos hre0] at this
      linarith
  have hxB : x ∉ closure (⋃ k ∈ Ioi N, P k) := by
    intro h
    have := closure_minimal (hBsub.trans ball_subset_closedBall) isClosed_closedBall h
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  have hsplit : regionT ⊆ (⋃ k ∈ Iic N, P k) ∪ (⋃ k ∈ Ioi N, P k) := by
    intro z hz
    obtain ⟨k, hk⟩ := mem_iUnion.1 hz
    by_cases hkN : k ≤ N
    · exact Or.inl (mem_iUnion₂.2 ⟨k, hkN, hk⟩)
    · exact Or.inr (mem_iUnion₂.2 ⟨k, not_le.1 hkN, hk⟩)
  have hxA : x ∈ closure (⋃ k ∈ Iic N, P k) := by
    have := closure_mono hsplit hcl
    rw [closure_union] at this
    exact this.resolve_right hxB
  rw [(Set.finite_Iic N).closure_biUnion] at hxA
  obtain ⟨k, -, hk⟩ := mem_iUnion₂.1 hxA
  refine mem_iUnion.2 ⟨k, ?_⟩
  rw [closure_union] at hk
  have hxD : x ∉ Dsc k := fun h => hnot (Dsc_subset_regionT k h)
  have hxT : x ∉ Tk k := fun h => hnot (Tk_subset_regionT k h)
  rcases hk with hk | hk
  · left
    have hr : cc k / 4 ≠ 0 := (by have := cc_pos k; positivity)
    have : x ∈ frontier (Dsc k) := by
      rw [(isOpen_Dsc k).frontier_eq]
      exact ⟨hk, hxD⟩
    rwa [Dsc, frontier_ball _ hr] at this
  · right
    exact frontier_Tk_subset k (by rw [(isOpen_Tk k).frontier_eq]; exact ⟨hk, hxT⟩)

theorem hausdorff_rectBoundary_le (k : ℕ) :
    Measure.hausdorffMeasure 1 (rectBoundary k) ≤
      ENNReal.ofReal (4 * hh k + 2 * (cc (k - 1) - cc k)) := by
  have hh0 := hh_pos k
  have hc : cc k ≤ cc (k - 1) := cc_antitone (Nat.sub_le k 1)
  have e1 := hausdorff_image_Icc (lipschitz_vmap (cc k)) (-hh k) (hh k)
  have e2 := hausdorff_image_Icc (lipschitz_vmap (cc (k - 1))) (-hh k) (hh k)
  have e3 := hausdorff_image_Icc (lipschitz_hmap (hh k)) (cc k) (cc (k - 1))
  have e4 := hausdorff_image_Icc (lipschitz_hmap (-hh k)) (cc k) (cc (k - 1))
  calc Measure.hausdorffMeasure 1 (rectBoundary k)
      ≤ ENNReal.ofReal (hh k - -hh k) + ENNReal.ofReal (hh k - -hh k) +
          ENNReal.ofReal (cc (k - 1) - cc k) + ENNReal.ofReal (cc (k - 1) - cc k) := by
        refine (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
          (add_le_add ((measure_union_le _ _).trans (add_le_add e1 e2)) e3)) e4)
    _ = ENNReal.ofReal (4 * hh k + 2 * (cc (k - 1) - cc k)) := by
        have a1 : 0 ≤ hh k - -hh k := by linarith
        have a2 : 0 ≤ cc (k - 1) - cc k := by linarith
        rw [← ENNReal.ofReal_add a1 a1, ← ENNReal.ofReal_add (by linarith) a2,
          ← ENNReal.ofReal_add (by linarith) a2]
        congr 1
        ring

theorem hausdorff_frontier_regionT_lt_top :
    Measure.hausdorffMeasure 1 (frontier regionT) < ⊤ := by
  set b : ℕ → ℝ := fun k => cc k / 4 * (2 * Real.pi) + (4 * hh k + 2 * (cc (k - 1) - cc k))
    with hb
  have hnn : ∀ k, 0 ≤ b k := fun k => by
    have := cc_pos k
    have := hh_pos k
    have : cc k ≤ cc (k - 1) := cc_antitone (Nat.sub_le k 1)
    simp only [hb]
    positivity
  have hbd : ∀ k, b k ≤ 40 * (1 / 4 : ℝ) ^ k := fun k => by
    have h1 := cc_le_pow k
    have h2 := hh_le_cc k
    have h3 : cc (k - 1) ≤ 4 * (1 / 4 : ℝ) ^ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [cc_zero]
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        have := cc_le_pow j
        simp only [Nat.add_sub_cancel, pow_succ]
        linarith
    have hpi := Real.pi_lt_four
    have hc := cc_pos k
    have hcc : cc k ≤ cc (k - 1) := cc_antitone (Nat.sub_le k 1)
    simp only [hb]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 4) k]
  have hsum : Summable b :=
    Summable.of_nonneg_of_le hnn hbd
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 40)
  have hE : ∀ k, Measure.hausdorffMeasure 1
      (sphere ((cc k : ℝ) : ℂ) (cc k / 4) ∪ rectBoundary k) ≤ ENNReal.ofReal (b k) := fun k => by
    have := cc_pos k
    refine (measure_union_le _ _).trans ?_
    refine (add_le_add (hausdorff_sphere_le _ (by positivity))
      (hausdorff_rectBoundary_le k)).trans ?_
    have hA : 0 ≤ cc k / 4 * (2 * Real.pi) := by positivity
    have hB : 0 ≤ 4 * hh k + 2 * (cc (k - 1) - cc k) := by
      have := hh_pos k
      have : cc k ≤ cc (k - 1) := cc_antitone (Nat.sub_le k 1)
      linarith
    rw [← ENNReal.ofReal_add hA hB]
  have h0 : Measure.hausdorffMeasure 1 ({0} : Set ℂ) = 0 := by
    refine le_antisymm ?_ zero_le
    have : ({0} : Set ℂ) ⊆ vmap 0 '' Icc 0 0 := by
      intro z hz
      rw [mem_singleton_iff] at hz
      exact ⟨0, ⟨le_rfl, le_rfl⟩, by simp [vmap, hz]⟩
    refine (measure_mono this).trans ((hausdorff_image_Icc (lipschitz_vmap 0) 0 0).trans ?_)
    simp
  calc Measure.hausdorffMeasure 1 (frontier regionT)
      ≤ Measure.hausdorffMeasure 1
          ({0} ∪ ⋃ k, (sphere ((cc k : ℝ) : ℂ) (cc k / 4) ∪ rectBoundary k)) :=
        measure_mono frontier_regionT_subset
    _ ≤ Measure.hausdorffMeasure 1 ({0} : Set ℂ) +
          Measure.hausdorffMeasure 1 (⋃ k, (sphere ((cc k : ℝ) : ℂ) (cc k / 4) ∪ rectBoundary k)) :=
        measure_union_le _ _
    _ ≤ 0 + ∑' k, ENNReal.ofReal (b k) := by
        rw [h0]
        have hsum' : ∑' k, Measure.hausdorffMeasure 1
            (sphere ((cc k : ℝ) : ℂ) (cc k / 4) ∪ rectBoundary k) ≤
            ∑' k, ENNReal.ofReal (b k) := tsum_le_tsum hE
        exact add_le_add le_rfl ((measure_iUnion_le _).trans hsum')
    _ < ⊤ := by
        rw [zero_add, ← ENNReal.ofReal_tsum_of_nonneg hnn hsum]
        exact ENNReal.ofReal_lt_top

end DirichletPoincare
