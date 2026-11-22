import Mathlib

/-!
# Auxiliary sequence estimates (thesis Lemma 3.1, Section 3.1)

Pure real-analysis lemma used in the construction of the counterexample region.
-/

open Filter Topology

namespace DirichletPoincare

/-- **Lemma 3.1** (thesis p. 21). For a decreasing sequence `0 < aₙ < 1` with `aₙ → 0` and every
`n ≥ 1`, there is `m > n` such that three estimates hold. The `0.8` in the first estimate is the
decimal `0,8` of the thesis. The index `2 * n - 1` in the second estimate is only meaningful for
`n ≥ 1`, since natural-number subtraction would otherwise truncate it to `0`. -/
theorem exists_good_index (a : ℕ → ℝ) (_hanti : Antitone a)
    (hpos : ∀ n, 0 < a n ∧ a n < 1) (_hlim : Tendsto a atTop (𝓝 0)) (n : ℕ) (_hn : 1 ≤ n) :
    ∃ m : ℕ, n < m ∧
      16 * (m : ℝ) ^ 2 * (0.8 : ℝ) ^ (2 * m - 2) < 1 / (m : ℝ) ^ 6 ∧
      (2 * (n : ℝ) - 2) * (m : ℝ) ^ 2 * (1 - (1 / 2) * a (2 * n - 1) ^ 2) ^ (2 * m - 2)
        < 1 / (m : ℝ) ^ 6 ∧
      (1 - 1 / (m : ℝ) ^ 4) ^ (2 * m + 1) > 1 / 2 := by
  -- For `0 < c < 1` and any `K`, the estimate `K m² c^(2m-2) < 1/m⁶` holds for large `m`:
  -- `m⁸ (c²)^m → 0`, and `c^(2m-2) · c² = (c²)^m`.
  have key : ∀ c K : ℝ, 0 < c → c < 1 →
      ∀ᶠ m : ℕ in atTop, K * (m : ℝ) ^ 2 * c ^ (2 * m - 2) < 1 / (m : ℝ) ^ 6 := by
    intro c K hc0 hc1
    have hc2 : c ^ 2 ≠ 0 := by positivity
    have hr : |c ^ 2| < 1 := by
      rw [abs_of_pos (by positivity)]
      nlinarith
    have hT := (tendsto_pow_const_mul_const_pow_of_abs_lt_one 8 hr).const_mul (K / c ^ 2)
    rw [mul_zero] at hT
    filter_upwards [hT.eventually_lt_const one_pos, eventually_ge_atTop 1] with m hm hm1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hpow : (c ^ 2) ^ m = c ^ (2 * m - 2) * c ^ 2 := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    have hprod : K / c ^ 2 * ((m : ℝ) ^ 8 * (c ^ 2) ^ m)
        = K * (m : ℝ) ^ 2 * c ^ (2 * m - 2) * (m : ℝ) ^ 6 := by
      rw [hpow]
      field_simp
    rw [hprod] at hm
    rw [lt_div_iff₀ (by positivity)]
    exact hm
  have h1 : ∀ᶠ m : ℕ in atTop, 16 * (m : ℝ) ^ 2 * (0.8 : ℝ) ^ (2 * m - 2) < 1 / (m : ℝ) ^ 6 :=
    key 0.8 16 (by norm_num) (by norm_num)
  have ha := hpos (2 * n - 1)
  have ha2 : a (2 * n - 1) ^ 2 < 1 := by nlinarith [ha.1, ha.2]
  have h2 := key (1 - (1 / 2) * a (2 * n - 1) ^ 2) (2 * (n : ℝ) - 2)
    (by nlinarith [ha.1, ha.2]) (by nlinarith [ha.1, ha.2])
  -- Bernoulli: `(1 - x)^k ≥ 1 - k x` with `x = m⁻⁴`, and `(2m+1)/m⁴ < 1/2` for `m ≥ 2`.
  have h3 : ∀ᶠ m : ℕ in atTop, (1 - 1 / (m : ℝ) ^ 4) ^ (2 * m + 1) > 1 / 2 := by
    filter_upwards [eventually_ge_atTop 2] with m hm
    have hx : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have hpos4 : (0 : ℝ) < (m : ℝ) ^ 4 := by positivity
    have hnonneg : 0 ≤ 1 / (m : ℝ) ^ 4 := by positivity
    have hle1 : 1 / (m : ℝ) ^ 4 ≤ 1 := by
      rw [div_le_one hpos4]
      exact one_le_pow₀ (by linarith)
    have hbern := one_add_mul_le_pow (a := -(1 / (m : ℝ) ^ 4)) (by linarith) (2 * m + 1)
    have hcast : ((2 * m + 1 : ℕ) : ℝ) = 2 * (m : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hbern
    have hfrac : (2 * (m : ℝ) + 1) * (1 / (m : ℝ) ^ 4) < 1 / 2 := by
      have e : (2 * (m : ℝ) + 1) * (1 / (m : ℝ) ^ 4) = (2 * m + 1) / (m : ℝ) ^ 4 := by ring
      rw [e, div_lt_iff₀ hpos4]
      have h8 : (2 : ℝ) ^ 3 ≤ (m : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hx 3
      nlinarith [mul_le_mul_of_nonneg_left h8 (by positivity : (0 : ℝ) ≤ m)]
    have hc : (1 - 1 / (m : ℝ) ^ 4) = 1 + -(1 / (m : ℝ) ^ 4) := by ring
    rw [hc]
    linarith
  obtain ⟨m, h1m, h2m, h3m, hnm⟩ := (h1.and (h2.and (h3.and (eventually_gt_atTop n)))).exists
  exact ⟨m, hnm, h1m, h2m, h3m⟩

end DirichletPoincare
