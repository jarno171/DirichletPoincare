import Mathlib

/-!
# Parameters of the counterexample region (thesis Section 3.1)

The region of Theorem 3.2 is built from a rapidly decreasing sequence `cₖ = 1/mₖ²`. The integers
`mₖ` are chosen recursively so that the estimates used in the proof hold.
-/

open Filter Topology

namespace DirichletPoincare

/-- For `r ∈ (0,1)`, polynomial factors times `r^(m-1)` are eventually at most `1`. -/
theorem eventually_pow_mul_le_one (r K : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∀ᶠ m : ℕ in atTop, K * (m : ℝ) ^ 8 * r ^ (m - 1) ≤ 1 := by
  have hr : |r| < 1 := by rwa [abs_of_pos hr0]
  have hT := (tendsto_pow_const_mul_const_pow_of_abs_lt_one 8 hr).const_mul (K / r)
  rw [mul_zero] at hT
  filter_upwards [hT.eventually_lt_const one_pos, eventually_ge_atTop 1] with m hm hm1
  have hpow : r ^ m = r ^ (m - 1) * r := by
    rw [← pow_succ]
    congr 1
    omega
  have : K / r * ((m : ℝ) ^ 8 * r ^ m) = K * (m : ℝ) ^ 8 * r ^ (m - 1) := by
    rw [hpow]
    field_simp
  rw [this] at hm
  exact hm.le

/-- Choice of the next index `m` in the recursive construction. -/
theorem exists_good_m (n M : ℕ) (hM : 1 ≤ M) :
    ∃ m : ℕ, n < m ∧ 2 * M < m ∧ 4 ≤ m ∧
      7 * (m : ℝ) ^ 8 * ((9 / 16 : ℝ) ^ 2) ^ (m - 1) ≤ 1 ∧
      16 * (n : ℝ) * (m : ℝ) ^ 8 * (1 - (3 / (4 * (M : ℝ) ^ 2)) ^ 2 / 2) ^ (m - 1) ≤ 1 := by
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hξ0 : 0 < (3 / (4 * (M : ℝ) ^ 2)) ^ 2 / 2 := by positivity
  have hξ1 : (3 / (4 * (M : ℝ) ^ 2)) ^ 2 / 2 < 1 := by
    have h1 : 4 * (M : ℝ) ^ 2 ≥ 4 := by nlinarith
    have h2 : 3 / (4 * (M : ℝ) ^ 2) ≤ 3 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h3 : 0 ≤ 3 / (4 * (M : ℝ) ^ 2) := by positivity
    nlinarith
  have hA := eventually_pow_mul_le_one ((9 / 16 : ℝ) ^ 2) 7 (by norm_num) (by norm_num)
  have hB := eventually_pow_mul_le_one (1 - (3 / (4 * (M : ℝ) ^ 2)) ^ 2 / 2) (16 * (n : ℝ))
    (by linarith) (by linarith)
  obtain ⟨m, h1, h2, h3, h4, h5⟩ := (hA.and (hB.and ((eventually_gt_atTop n).and
    ((eventually_gt_atTop (2 * M)).and (eventually_ge_atTop 4))))).exists
  exact ⟨m, h3, h4, h5, h1, h2⟩

/-- The recursive sequence of indices; `seq 0 = 1`. -/
noncomputable def seq : ℕ → {M : ℕ // 1 ≤ M}
  | 0 => ⟨1, le_rfl⟩
  | n + 1 =>
    ⟨Classical.choose (exists_good_m (n + 1) (seq n).1 (seq n).2),
      (Classical.choose_spec (exists_good_m (n + 1) (seq n).1 (seq n).2)).2.2.1.trans'
        (by norm_num)⟩

/-- The index `mₙ`. -/
noncomputable def mm (n : ℕ) : ℕ := (seq n).1

theorem mm_zero : mm 0 = 1 := rfl

theorem one_le_mm (n : ℕ) : 1 ≤ mm n := (seq n).2

theorem mm_spec (n : ℕ) :
    n + 1 < mm (n + 1) ∧ 2 * mm n < mm (n + 1) ∧ 4 ≤ mm (n + 1) ∧
      7 * (mm (n + 1) : ℝ) ^ 8 * ((9 / 16 : ℝ) ^ 2) ^ (mm (n + 1) - 1) ≤ 1 ∧
      16 * ((n + 1 : ℕ) : ℝ) * (mm (n + 1) : ℝ) ^ 8 *
        (1 - (3 / (4 * (mm n : ℝ) ^ 2)) ^ 2 / 2) ^ (mm (n + 1) - 1) ≤ 1 :=
  Classical.choose_spec (exists_good_m (n + 1) (seq n).1 (seq n).2)

/-- The scales `cₙ = 1/mₙ²` (`c₀ = 1`). -/
noncomputable def cc (n : ℕ) : ℝ := 1 / (mm n : ℝ) ^ 2

/-- The heights `hₙ = 1/mₙ^10` of the necks. -/
noncomputable def hh (n : ℕ) : ℝ := 1 / (mm n : ℝ) ^ 10

theorem cc_zero : cc 0 = 1 := by simp [cc, mm_zero]

theorem cc_pos (n : ℕ) : 0 < cc n := by
  have := one_le_mm n
  unfold cc
  positivity

theorem hh_pos (n : ℕ) : 0 < hh n := by
  have := one_le_mm n
  unfold hh
  positivity

theorem cc_succ_le (n : ℕ) : cc (n + 1) ≤ cc n / 4 := by
  have h := (mm_spec n).2.1
  have h1 : (2 : ℝ) * mm n ≤ mm (n + 1) := by exact_mod_cast h.le
  have hpos : (0 : ℝ) < mm n := by exact_mod_cast one_le_mm n
  have hpos1 : (0 : ℝ) < mm (n + 1) := by exact_mod_cast one_le_mm (n + 1)
  unfold cc
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem cc_antitone : Antitone cc :=
  antitone_nat_of_succ_le fun n => (cc_succ_le n).trans (by linarith [cc_pos n])

theorem cc_le_quarter (n : ℕ) (hn : 1 ≤ n) : cc n ≤ 1 / 4 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have := cc_succ_le k
  have h1 : cc k ≤ 1 := by rw [← cc_zero]; exact cc_antitone (Nat.zero_le k)
  linarith

theorem hh_le (n : ℕ) (hn : 1 ≤ n) : hh n ≤ cc n / 4 := by
  have h4 : (4 : ℝ) ≤ mm n := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact_mod_cast (mm_spec k).2.2.1
  have hpos : (0 : ℝ) < mm n := by linarith
  unfold hh cc
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have : (mm n : ℝ) ^ 10 = (mm n : ℝ) ^ 2 * (mm n : ℝ) ^ 8 := by ring
  rw [this]
  have h8 : (4 : ℝ) ≤ (mm n : ℝ) ^ 8 := by
    calc (4 : ℝ) ≤ 4 ^ 8 := by norm_num
      _ ≤ (mm n : ℝ) ^ 8 := pow_le_pow_left₀ (by norm_num) h4 8
  nlinarith [sq_nonneg ((mm n : ℝ))]

theorem hh_antitone : Antitone hh := by
  refine antitone_nat_of_succ_le fun n => ?_
  have h : mm n < mm (n + 1) := by
    have := (mm_spec n).2.1
    have := one_le_mm n
    omega
  have h1 : (mm n : ℝ) ^ 10 ≤ (mm (n + 1) : ℝ) ^ 10 :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast h.le) 10
  have h2 : (0 : ℝ) < (mm n : ℝ) ^ 10 := by
    have := one_le_mm n
    positivity
  unfold hh
  exact one_div_le_one_div_of_le h2 h1

end DirichletPoincare
