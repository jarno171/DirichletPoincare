import DirichletPoincare.Definitions
import DirichletPoincare.Section3.Params

/-!
# The counterexample regions (thesis Sections 3.1 and 3.2)

* `Dsc k` is the *chamber* `B(cₖ, cₖ/4)` around the point `cₖ ∈ ℝ`.
* `Tk k` and `Sk k` are thin rectangular *necks* of half-height `hₖ` along the real axis.
* `regionT = ⋃ (Dsc k ∪ Tk k)` has necks `(cₖ, cₖ₋₁)`; it is the region of Theorem 3.2.
* `regionS = ⋃ (Dsc k ∪ Sk k)` has necks `(cₖ, 1)`; it contains `regionStar`, which is starlike
  with respect to `1` and is used for Theorem 3.21.
-/

open MeasureTheory Metric Set

namespace DirichletPoincare

/-- The chamber around `cₖ`. -/
noncomputable def Dsc (k : ℕ) : Set ℂ := ball ((cc k : ℝ) : ℂ) (cc k / 4)

/-- The neck between `cₖ` and `cₖ₋₁`. -/
noncomputable def Tk (k : ℕ) : Set ℂ := {z | cc k < z.re ∧ z.re < cc (k - 1) ∧ |z.im| < hh k}

/-- The neck between `cₖ` and `1`. -/
noncomputable def Sk (k : ℕ) : Set ℂ := {z | cc k < z.re ∧ z.re < 1 ∧ |z.im| < hh k}

/-- The region of Theorem 3.2. -/
noncomputable def regionT : Set ℂ := ⋃ k, (Dsc k ∪ Tk k)

/-- A larger region containing the starlike region `regionStar`. -/
noncomputable def regionS : Set ℂ := ⋃ k, (Dsc k ∪ Sk k)

/-- The starlike region used in Theorem 3.21. -/
noncomputable def regionStar : Set ℂ := Dsc 0 ∪ ⋃ k, Sk k

theorem isOpen_Dsc (k : ℕ) : IsOpen (Dsc k) := isOpen_ball

theorem isOpen_Tk (k : ℕ) : IsOpen (Tk k) := by
  have : Tk k = {z : ℂ | cc k < z.re} ∩ ({z : ℂ | z.re < cc (k - 1)} ∩ {z : ℂ | |z.im| < hh k}) :=
    rfl
  rw [this]
  refine (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter ?_)
  exact isOpen_lt (Complex.continuous_im.abs) continuous_const

theorem isOpen_Sk (k : ℕ) : IsOpen (Sk k) := by
  have : Sk k = {z : ℂ | cc k < z.re} ∩ ({z : ℂ | z.re < 1} ∩ {z : ℂ | |z.im| < hh k}) := rfl
  rw [this]
  refine (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter ?_)
  exact isOpen_lt (Complex.continuous_im.abs) continuous_const

private theorem convex_abs_im_lt (h : ℝ) : Convex ℝ {z : ℂ | |z.im| < h} := by
  have : {z : ℂ | |z.im| < h} = {z : ℂ | z.im < h} ∩ {z : ℂ | -h < z.im} := by
    ext z
    simp [abs_lt, and_comm]
  rw [this]
  exact (convex_halfSpace_im_lt _).inter (convex_halfSpace_im_gt _)

theorem convex_Tk (k : ℕ) : Convex ℝ (Tk k) := by
  have : Tk k = {z : ℂ | cc k < z.re} ∩ ({z : ℂ | z.re < cc (k - 1)} ∩ {z : ℂ | |z.im| < hh k}) :=
    rfl
  rw [this]
  exact (convex_halfSpace_re_gt _).inter ((convex_halfSpace_re_lt _).inter (convex_abs_im_lt _))

theorem convex_Sk (k : ℕ) : Convex ℝ (Sk k) := by
  have : Sk k = {z : ℂ | cc k < z.re} ∩ ({z : ℂ | z.re < 1} ∩ {z : ℂ | |z.im| < hh k}) := rfl
  rw [this]
  exact (convex_halfSpace_re_gt _).inter ((convex_halfSpace_re_lt _).inter (convex_abs_im_lt _))

theorem convex_Dsc (k : ℕ) : Convex ℝ (Dsc k) := convex_ball _ _

theorem isOpen_regionT : IsOpen regionT :=
  isOpen_iUnion fun k => (isOpen_Dsc k).union (isOpen_Tk k)

theorem isOpen_regionS : IsOpen regionS :=
  isOpen_iUnion fun k => (isOpen_Dsc k).union (isOpen_Sk k)

theorem isOpen_regionStar : IsOpen regionStar :=
  (isOpen_Dsc 0).union (isOpen_iUnion isOpen_Sk)

theorem mem_Dsc_real {k : ℕ} {x : ℝ} (hx : |x - cc k| < cc k / 4) : (x : ℂ) ∈ Dsc k := by
  rw [Dsc, mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact hx

theorem one_mem_Dsc_zero : (1 : ℂ) ∈ Dsc 0 := by
  have := mem_Dsc_real (k := 0) (x := 1) (by rw [cc_zero]; norm_num)
  simpa using this

theorem Tk_zero : Tk 0 = ∅ := by
  ext z
  simp only [Tk, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
  intro h1 h2
  exact absurd h2 (not_lt.2 h1.le)

theorem Sk_zero : Sk 0 = ∅ := by
  ext z
  simp only [Sk, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, cc_zero]
  intro h1 h2
  exact absurd h2 (not_lt.2 h1.le)

theorem cc_le_one (k : ℕ) : cc k ≤ 1 := by
  rw [← cc_zero]
  exact cc_antitone (Nat.zero_le k)

theorem Tk_subset_Sk (k : ℕ) : Tk k ⊆ Sk k := fun _ hz =>
  ⟨hz.1, hz.2.1.trans_le ((cc_le_one _)), hz.2.2⟩

theorem regionT_subset_regionS : regionT ⊆ regionS :=
  iUnion_mono fun k => union_subset_union_right _ (Tk_subset_Sk k)

theorem regionStar_subset_regionS : regionStar ⊆ regionS := by
  intro z hz
  rcases hz with hz | hz
  · exact mem_iUnion.2 ⟨0, Or.inl hz⟩
  · obtain ⟨k, hk⟩ := mem_iUnion.1 hz
    exact mem_iUnion.2 ⟨k, Or.inr hk⟩

/-- A real point at a given fraction of the scale lies in a chamber. -/
private theorem real_mem_Dsc (k : ℕ) (t : ℝ) (ht : |t - 1| < 1 / 4) :
    ((t * cc k : ℝ) : ℂ) ∈ Dsc k := by
  refine mem_Dsc_real ?_
  have hc := cc_pos k
  have : t * cc k - cc k = (t - 1) * cc k := by ring
  rw [this, abs_mul, abs_of_pos hc]
  nlinarith

theorem Dsc_inter_Tk_succ (k : ℕ) : (Dsc k ∩ Tk (k + 1)).Nonempty := by
  refine ⟨(((7 / 8 : ℝ) * cc k : ℝ) : ℂ), real_mem_Dsc k _ (by norm_num), ?_⟩
  have h1 := cc_succ_le k
  have h2 := cc_pos k
  have h3 := hh_pos (k + 1)
  simp only [Tk, mem_ofPred_eq, Complex.ofReal_re, Complex.ofReal_im, abs_zero, Nat.add_sub_cancel]
  refine ⟨by nlinarith, by nlinarith, h3⟩

theorem Dsc_inter_Tk (k : ℕ) (hk : 1 ≤ k) : (Dsc k ∩ Tk k).Nonempty := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  refine ⟨(((9 / 8 : ℝ) * cc (j + 1) : ℝ) : ℂ), real_mem_Dsc _ _ (by norm_num), ?_⟩
  have h1 := cc_succ_le j
  have h2 := cc_pos (j + 1)
  have h3 := hh_pos (j + 1)
  have h4 := cc_pos j
  simp only [Tk, mem_ofPred_eq, Complex.ofReal_re, Complex.ofReal_im, abs_zero, Nat.add_sub_cancel]
  refine ⟨by nlinarith, by nlinarith, h3⟩

theorem isConnected_regionT : IsConnected regionT := by
  have hpre : ∀ n, IsPreconnected (Dsc n ∪ Tk n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Tk_zero, union_empty]
      exact (convex_Dsc 0).isPreconnected
    · exact (convex_Dsc n).isPreconnected.union _ (Dsc_inter_Tk n hn).some_mem.1
        (Dsc_inter_Tk n hn).some_mem.2 (convex_Tk n).isPreconnected
  refine ⟨⟨1, mem_iUnion.2 ⟨0, Or.inl one_mem_Dsc_zero⟩⟩, ?_⟩
  refine IsPreconnected.iUnion_of_chain hpre fun n => ?_
  obtain ⟨x, hx1, hx2⟩ := Dsc_inter_Tk_succ n
  exact ⟨x, Or.inl hx1, Or.inr hx2⟩


theorem one_mem_regionStar : (1 : ℂ) ∈ regionStar := Set.mem_union_left _ one_mem_Dsc_zero

theorem segment_subset_regionStar {z : ℂ} (hz : z ∈ regionStar) : segment ℝ 1 z ⊆ regionStar := by
  rcases hz with hz | hz
  · exact fun w hw => Or.inl ((convex_Dsc 0).segment_subset one_mem_Dsc_zero hz hw)
  · obtain ⟨k, hk⟩ := mem_iUnion.1 hz
    rintro w ⟨a, b, ha, hb, hab, rfl⟩
    rcases hb.eq_or_lt with hb0 | hbpos
    · have ha1 : a = 1 := by linarith
      subst ha1
      rw [← hb0]
      simpa using one_mem_regionStar
    · right
      refine mem_iUnion.2 ⟨k, ?_, ?_, ?_⟩
      · simp only [Complex.add_re, Complex.smul_re, Complex.one_re, smul_eq_mul]
        have := hk.1
        have := hk.2.1
        nlinarith
      · simp only [Complex.add_re, Complex.smul_re, Complex.one_re, smul_eq_mul]
        have := hk.2.1
        nlinarith
      · simp only [Complex.add_im, Complex.smul_im, Complex.one_im, smul_eq_mul, mul_zero,
          zero_add]
        rw [abs_mul, abs_of_nonneg hb]
        have := hk.2.2
        have hb1 : b ≤ 1 := by linarith
        nlinarith [abs_nonneg z.im]

theorem isStarlikeRegion_regionStar : IsStarlikeRegion regionStar := by
  have hsc : StarConvex ℝ (1 : ℂ) regionStar := fun z hz a b ha hb hab =>
    segment_subset_regionStar hz ⟨a, b, ha, hb, hab, rfl⟩
  exact ⟨⟨isOpen_regionStar, (hsc.isPathConnected one_mem_regionStar).isConnected⟩, 1,
    one_mem_regionStar, fun z hz => segment_subset_regionStar hz⟩

theorem isRegion_regionT : IsRegion regionT := ⟨isOpen_regionT, isConnected_regionT⟩

theorem one_mem_regionT : (1 : ℂ) ∈ regionT := mem_iUnion.2 ⟨0, Or.inl one_mem_Dsc_zero⟩


theorem isBounded_regionS : Bornology.IsBounded regionS := by
  refine (Metric.isBounded_ball (x := (0 : ℂ)) (r := 3)).subset ?_
  intro z hz
  obtain ⟨k, hk⟩ := mem_iUnion.1 hz
  rw [mem_ball, dist_zero_right]
  rcases hk with hk | hk
  · have h1 : ‖z - ((cc k : ℝ) : ℂ)‖ < cc k / 4 := by
      have := hk
      rwa [Dsc, mem_ball, dist_eq_norm] at this
    have h2 : ‖((cc k : ℝ) : ℂ)‖ = cc k := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (cc_pos k)]
    have := norm_le_norm_add_norm_sub' z ((cc k : ℝ) : ℂ)
    have := cc_le_one k
    linarith [norm_sub_rev z ((cc k : ℝ) : ℂ)]
  · have hre := hk.2.1
    have hre0 : 0 < z.re := (cc_pos k).trans hk.1
    have him : |z.im| < 1 := by
      refine hk.2.2.trans_le ?_
      unfold hh
      have : (1 : ℝ) ≤ (mm k : ℝ) ^ 10 := one_le_pow₀ (by exact_mod_cast one_le_mm k)
      rw [div_le_one (by linarith)]
      exact this
    have := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hre0] at this
    linarith

end DirichletPoincare
