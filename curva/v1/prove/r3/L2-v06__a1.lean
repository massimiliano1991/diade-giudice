import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem imo_1968_p5_1
  (a : ℝ)
  (f : ℝ → ℝ)
  (h₀ : 0 < a)
  (h₁ : ∀ x, f (x + a) = 1 / 2 + Real.sqrt (f x - (f x)^2)) :
  ∃ b > 0, ∀ x, f (x + b) = f x := by
  have hge : ∀ x, 1/2 ≤ f x := by
    intro x
    have h := h₁ (x - a)
    rw [sub_add_cancel] at h
    linarith [h, Real.sqrt_nonneg (f (x - a) - f (x - a) ^ 2)]
  have hle : ∀ x, f x ≤ 1 := by
    intro x
    have h := h₁ (x - a)
    rw [sub_add_cancel] at h
    have ht : f (x - a) - f (x - a) ^ 2 ≤ (1/2 : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (f (x - a) - 1/2)]
    have hs : Real.sqrt (f (x - a) - f (x - a) ^ 2) ≤ Real.sqrt ((1/2 : ℝ) ^ 2) :=
      Real.sqrt_le_sqrt ht
    rw [Real.sqrt_sq (by norm_num)] at hs
    linarith [h, hs]
  have K : ∀ x, f (x + 2 * a) = 1/2 + |f x - 1/2| := by
    intro x
    have hx := h₁ x
    have hy := h₁ (x + a)
    have e : x + a + a = x + 2 * a := by ring
    rw [e] at hy
    have hnn : 0 ≤ f x - f x ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.2 (hle x)) (by linarith [hge x] : (0:ℝ) ≤ f x)]
    have hs2 : Real.sqrt (f x - f x ^ 2) ^ 2 = f x - f x ^ 2 := Real.sq_sqrt hnn
    have key : f (x + a) - f (x + a) ^ 2 = (f x - 1/2) ^ 2 := by
      rw [hx]
      linear_combination (-1:ℝ) * hs2
    rw [hy, key, Real.sqrt_sq_eq_abs]
  refine ⟨2 * a, by linarith, fun z => ?_⟩
  rw [K z, abs_of_nonneg (by linarith [hge z])]
  ring
