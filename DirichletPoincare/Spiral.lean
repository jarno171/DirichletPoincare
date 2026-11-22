import Mathlib

/-!
# The spiral counterexample (Varis (2013), Section 4, Theorem 4.1)

Construction: for `u > 1` take the strip between the curves `v = f₁(u)` and `v = f₂(u)`, where
`f₂(u) = 1/u²` and `f₁(u) = f₂(u + 2π)`. The strip `Δ` is mapped by `w ↦ exp(i w)` to a
spiralling domain `G`. This file formalizes the strip, the spiral domain, and the injectivity of
the map on the strip (the step that makes the inverse map well defined).
-/

open Complex

namespace DirichletPoincare

/-- Upper boundary curve of the strip: `f₂(u) = 1/u²` (thesis, Section 4). -/
noncomputable def f₂ (u : ℝ) : ℝ := 1 / u ^ 2

/-- Lower boundary curve of the strip: `f₁(u) = f₂(u + 2π)` (thesis, Section 4). -/
noncomputable def f₁ (u : ℝ) : ℝ := 1 / (u + 2 * Real.pi) ^ 2

/-- The strip `Δ = {u + iv : u > 1, f₁(u) < v < f₂(u)}` (thesis, Section 4). -/
def strip : Set ℂ := {w | 1 < w.re ∧ f₁ w.re < w.im ∧ w.im < f₂ w.re}

/-- The spiral domain `G = exp(iΔ)` (thesis, Section 4). -/
noncomputable def spiralDomain : Set ℂ := (fun w : ℂ => exp (I * w)) '' strip

/-- `f₂` is antitone on the positive reals. -/
lemma f₂_anti {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : f₂ b ≤ f₂ a := by
  unfold f₂
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_left₀ ha.le hab 2

/-- Two points of the strip whose real parts differ by a positive multiple of `2π` cannot have
equal imaginary parts: the strip windings are disjoint. -/
lemma strip_no_shift {w w' : ℂ} (hw : w ∈ strip) (hw' : w' ∈ strip) {n : ℤ} (hn : 1 ≤ n)
    (hre : w.re = w'.re + n * (2 * Real.pi)) (him : w.im = w'.im) : False := by
  simp only [strip, Set.mem_ofPred_eq] at hw hw'
  obtain ⟨-, -, hw_top⟩ := hw
  obtain ⟨hw'_gt, hw'_bot, -⟩ := hw'
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hshift : w'.re + 2 * Real.pi ≤ w.re := by nlinarith [Real.pi_pos]
  have hpos : 0 < w'.re + 2 * Real.pi := by linarith [Real.pi_pos]
  -- the upper boundary over `w` lies below the lower boundary over `w'`
  have hbound : f₂ w.re ≤ f₁ w'.re := f₂_anti hpos hshift
  linarith

/-- `exp (i w₁) = exp (i w₂)` forces `w₁ = w₂ + n·2π` for some integer `n`. -/
lemma exp_mul_I_eq_iff_shift {w₁ w₂ : ℂ} (h : exp (I * w₁) = exp (I * w₂)) :
    ∃ n : ℤ, w₁ = w₂ + n * (2 * Real.pi) := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  refine ⟨n, ?_⟩
  linear_combination (-I) * hn + (w₁ - w₂ - (n : ℂ) * (2 * Real.pi)) * Complex.I_sq

/-- The map `w ↦ exp (i w)` is injective on the strip `Δ`, so the inverse of `G = exp(iΔ)` is
well defined. -/
theorem exp_injOn_strip : Set.InjOn (fun w : ℂ => exp (I * w)) strip := by
  intro w₁ h₁ w₂ h₂ heq
  obtain ⟨n, hw⟩ := exp_mul_I_eq_iff_shift heq
  have hre : w₁.re = w₂.re + n * (2 * Real.pi) := by
    simpa using congrArg Complex.re hw
  have him : w₁.im = w₂.im := by
    simpa using congrArg Complex.im hw
  rcases lt_trichotomy n 0 with hneg | hzero | hpos
  · exact (strip_no_shift h₂ h₁ (n := -n) (by omega)
      (by push_cast; linarith) him.symm).elim
  · subst hzero
    simp only [Int.cast_zero, zero_mul, add_zero] at hre
    exact Complex.ext hre him
  · exact (strip_no_shift h₁ h₂ (n := n) (by omega) hre him).elim

end DirichletPoincare
