import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_293
  (x : NNReal) :
  Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = 36 * x * Real.sqrt (35 * x) := by
  have ht : (0:ℝ) ≤ (x:ℝ) := NNReal.coe_nonneg x
  have h60 : (0:ℝ) ≤ 60 * (x:ℝ) := mul_nonneg (by norm_num) ht
  have h720 : (0:ℝ) ≤ 60 * (x:ℝ) * (12 * (x:ℝ)) :=
    mul_nonneg h60 (mul_nonneg (by norm_num) ht)
  have h36 : (0:ℝ) ≤ 36 * (x:ℝ) := mul_nonneg (by norm_num) ht
  have h1 : Real.sqrt (60 * (x:ℝ)) * Real.sqrt (12 * (x:ℝ))
      = Real.sqrt (60 * (x:ℝ) * (12 * (x:ℝ))) :=
    (Real.sqrt_mul h60 _).symm
  have h2 : Real.sqrt (60 * (x:ℝ) * (12 * (x:ℝ))) * Real.sqrt (63 * (x:ℝ))
      = Real.sqrt (60 * (x:ℝ) * (12 * (x:ℝ)) * (63 * (x:ℝ))) :=
    (Real.sqrt_mul h720 _).symm
  have h3 : 36 * (x:ℝ) * Real.sqrt (35 * (x:ℝ))
      = Real.sqrt ((36 * (x:ℝ)) ^ 2 * (35 * (x:ℝ))) := by
    rw [Real.sqrt_mul (sq_nonneg (36 * (x:ℝ))), Real.sqrt_sq h36]
  rw [h1, h2, h3]
  congr 1
  ring
