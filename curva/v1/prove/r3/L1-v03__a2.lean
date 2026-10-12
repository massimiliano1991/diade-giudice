import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_293
  (x : NNReal) :
  Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = 36 * x * Real.sqrt (35 * x) := by
  have hy : (0:ℝ) ≤ (x:ℝ) := NNReal.coe_nonneg x
  have h60 : (0:ℝ) ≤ 60 * (x:ℝ) := by positivity
  have h12 : (0:ℝ) ≤ 12 * (x:ℝ) := by positivity
  have h1 : Real.sqrt (60 * (x:ℝ)) * Real.sqrt (12 * (x:ℝ))
      = Real.sqrt (60 * (x:ℝ) * (12 * (x:ℝ))) :=
    (Real.sqrt_mul h60 (12 * (x:ℝ))).symm
  have h60_12 : (0:ℝ) ≤ 60 * (x:ℝ) * (12 * (x:ℝ)) := by positivity
  have h2 : Real.sqrt (60 * (x:ℝ) * (12 * (x:ℝ))) * Real.sqrt (63 * (x:ℝ))
      = Real.sqrt (60 * (x:ℝ) * (12 * (x:ℝ)) * (63 * (x:ℝ))) :=
    (Real.sqrt_mul h60_12 (63 * (x:ℝ))).symm
  rw [h1, h2]
  have h3 : 60 * (x:ℝ) * (12 * (x:ℝ)) * (63 * (x:ℝ))
      = (36 * (x:ℝ))^2 * (35 * (x:ℝ)) := by ring
  have h36sq : (0:ℝ) ≤ (36 * (x:ℝ))^2 := by positivity
  have h36 : (0:ℝ) ≤ 36 * (x:ℝ) := by positivity
  rw [h3, Real.sqrt_mul h36sq (35 * (x:ℝ)), Real.sqrt_sq h36]
