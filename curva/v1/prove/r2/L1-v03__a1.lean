import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_293
  (x : NNReal) :
  Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = 36 * x * Real.sqrt (35 * x) := by
  have hx : (0:ℝ) ≤ (x:ℝ) := NNReal.coe_nonneg x
  have h1 : (0:ℝ) ≤ 60 * (x:ℝ) := mul_nonneg (by norm_num) hx
  have h2 : (0:ℝ) ≤ 12 * (x:ℝ) := mul_nonneg (by norm_num) hx
  have h4 : (0:ℝ) ≤ 36 * (x:ℝ) := mul_nonneg (by norm_num) hx
  have e : (60 * (x:ℝ)) * (12 * (x:ℝ)) * (63 * (x:ℝ)) = (36 * (x:ℝ))^2 * (35 * (x:ℝ)) := by
    ring
  rw [← Real.sqrt_mul h1, ← Real.sqrt_mul (mul_nonneg h1 h2), e,
    Real.sqrt_mul (sq_nonneg (36 * (x:ℝ))), Real.sqrt_sq h4]
