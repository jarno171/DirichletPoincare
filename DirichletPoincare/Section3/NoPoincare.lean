import DirichletPoincare.Definitions
import DirichletPoincare.Section3.Mass

/-!
# Bounded region without the Poincaré (2,2) inequality (thesis Section 3.1)

The region `regionT` is a chain of discs `Dsc k` joined by thin rectangular necks `Tk k`
(`Section3/Region.lean`). The functions `g_m(z) = (1 - z²)^m` have Dirichlet energy
`O(m⁻⁵)` on it (`energy_regionS_le`) but `L²` distance at least `c · m⁻²` from every constant,
because they are close to `1` on the chamber `Dsc m` and close to `0` on the chamber `Dsc 0`
around the point `1`.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace DirichletPoincare

theorem volume_Dsc_le_zero (k : ℕ) : volume (Dsc k) ≤ volume (Dsc 0) := by
  have hc := cc_pos k
  have hc1 := cc_le_one k
  rw [Dsc, Dsc, volume_ball_eq _ (by positivity), volume_ball_eq _ (by rw [cc_zero]; norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [cc_zero]
  have : (cc k / 4) ^ 2 ≤ (1 / 4) ^ 2 := by gcongr
  nlinarith [Real.pi_pos]

theorem volume_Dsc_succ (n : ℕ) :
    volume (Dsc (n + 1)) = ENNReal.ofReal (Real.pi / (16 * (mm (n + 1) : ℝ) ^ 4)) := by
  have hc := cc_pos (n + 1)
  rw [Dsc, volume_ball_eq _ (by positivity)]
  congr 1
  have : cc (n + 1) = 1 / (mm (n + 1) : ℝ) ^ 2 := rfl
  have hm : (0 : ℝ) < mm (n + 1) := by exact_mod_cast one_le_mm (n + 1)
  rw [this]
  field_simp
  ring

theorem Dsc_subset_regionT (k : ℕ) : Dsc k ⊆ regionT := fun _ hz => mem_iUnion.2 ⟨k, Or.inl hz⟩

/-- The Dirichlet energy of `g_m - c` on a subregion of `regionS`. -/
theorem dirichletEnergy_gm_le {G : Set ℂ} (hG : G ⊆ regionS) (n : ℕ) (c : ℂ) :
    dirichletEnergy G (fun z => gm (mm (n + 1)) z - c) ≤
      ENNReal.ofReal (10 / (mm (n + 1) : ℝ) ^ 5) := by
  unfold dirichletEnergy
  simp only [deriv_sub_const]
  exact (lintegral_mono_set hG).trans (energy_regionS_le n)

/-- No basepoint admits the Poincaré inequality on `regionT`. -/
theorem not_poincare_regionT {z₀ : ℂ} : ¬ PoincareInequality regionT z₀ := by
  rintro ⟨K, hK, hP⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (10240 * K.toReal)
  obtain ⟨hN, h2M, h4, -, -⟩ := mm_spec n
  set m := mm (n + 1) with hm
  have hm4 : (4 : ℝ) ≤ m := by exact_mod_cast h4
  have hcn : cc (n + 1) = 1 / (m : ℝ) ^ 2 := rfl
  have hmpos : (0 : ℝ) < m := by linarith
  have hD : IsInDirichletSpace regionT z₀ (fun z => gm m z - gm m z₀) := by
    refine ⟨(gm_differentiable m).differentiableOn.sub_const _, sub_self _, ?_⟩
    exact (dirichletEnergy_gm_le regionT_subset_regionS n _).trans_lt ENNReal.ofReal_lt_top
  have hup := (hP _ hD).trans
    (mul_le_mul' le_rfl (dirichletEnergy_gm_le regionT_subset_regionS n _))
  -- the lower bound for the `L²` norm
  have hlow : ENNReal.ofReal (1 / 64) * volume (Dsc (n + 1)) ≤
      bergmanNormSq regionT (fun z => gm m z - gm m z₀) := by
    have hbig := big_diff_or (m := m) (A₀ := Dsc 0) (A₁ := Dsc (n + 1))
      (fun z hz => norm_gm_le_of_mem_Dsc_zero h4 hz)
      (fun z hz => norm_gm_ge_of_mem_Dsc h4 hcn hz) (gm m z₀)
    rcases hbig with h | h
    · calc ENNReal.ofReal (1 / 64) * volume (Dsc (n + 1))
          ≤ ENNReal.ofReal (1 / 64) * volume (Dsc 0) :=
            mul_le_mul' le_rfl (volume_Dsc_le_zero _)
        _ ≤ _ := lintegral_sq_ge (isOpen_Dsc 0).measurableSet (Dsc_subset_regionT 0)
            (f := fun z => gm m z - gm m z₀) h
    · exact lintegral_sq_ge (isOpen_Dsc _).measurableSet (Dsc_subset_regionT _)
        (f := fun z => gm m z - gm m z₀) h
  have hchain := hlow.trans hup
  rw [volume_Dsc_succ, ← ENNReal.ofReal_toReal hK.ne, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hchain
  simp only [← hm] at hchain
  have hk := ENNReal.toReal_nonneg (a := K)
  have hm5 : (0 : ℝ) < (m : ℝ) ^ 5 := by positivity
  have hm4' : (0 : ℝ) < (m : ℝ) ^ 4 := by positivity
  have e1 : 1 / 64 * (Real.pi / (16 * (m : ℝ) ^ 4)) * (1024 * (m : ℝ) ^ 5) = Real.pi * m := by
    field_simp
    ring
  have e2 : K.toReal * (10 / (m : ℝ) ^ 5) * (1024 * (m : ℝ) ^ 5) = 10240 * K.toReal := by
    field_simp
    ring
  have h3 := mul_le_mul_of_nonneg_right hchain (by positivity : (0 : ℝ) ≤ 1024 * (m : ℝ) ^ 5)
  rw [e1, e2] at h3
  have hmn : (n : ℝ) + 2 ≤ m := by exact_mod_cast hN
  nlinarith [Real.pi_gt_three]

end DirichletPoincare
