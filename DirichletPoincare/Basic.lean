import Mathlib

/-!
# Smoke test

A minimal check that the Lean/Mathlib setup builds.
-/

/-- Hello world: 2 divides 4. -/
theorem two_dvd_four : (2 : ℕ) ∣ 4 := ⟨2, by norm_num⟩
