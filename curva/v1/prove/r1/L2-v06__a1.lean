import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem imo_1968_p5_1
  (a : ℝ)
  (f : ℝ → ℝ)
  (h₀ : 0 < a)
  (h₁ : ∀ x, f (x + a) = 1 / 2 + Real.sqrt (f x - (f x)^2)) :
  ∃ b > 0, ∀ x, f (x + b) = f x := by
  have key : ∀ t : ℝ, Real.sqrt (t - t ^ 2) ≤ 1 / 2 := by
    intro t
    rcases le_total 0 (t - t ^ 2) with hc | hc
    · have hsq := Real.sq_sqrt hc
      nlinarith [sq_nonneg (t - 1 / 2), Real.sqrt_nonneg (t - t ^ 2)]
    · rw [Real.sqrt_eq_zero'.mpr hc]
      norm_num
  have hge : ∀ x, 1 / 2 ≤ f x := by
    intro x
    have h := h₁ (x - a)
    rw [sub_add_cancel] at h
    rw [h]
    linarith [Real.sqrt_nonneg (f (x - a) - f (x - a) ^ 2)]
  have hle : ∀ x, f x ≤ 1 := by
    intro x
    have h := h₁ (x - a)
    rw [sub_add_cancel] at h
    rw [h]
    linarith [key (f (x - a))]
  refine ⟨2 * a, by linarith, fun x => ?_⟩
  have e1 := h₁ x
  have e2 := h₁ (x + a)
  have hx : x + 2 * a = x + a + a := by ring
  rw [hx, e2, e1]
  have hc : 0 ≤ f x - f x ^ 2 := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ f x by linarith [hge x])
                          (show (0:ℝ) ≤ 1 - f x by linarith [hle x])]
  have hs2 := Real.sq_sqrt hc
  have inner : 1 / 2 + Real.sqrt (f x - f x ^ 2) - (1 / 2 + Real.sqrt (f x - f x ^ 2)) ^ 2
      = (f x - 1 / 2) ^ 2 := by
    linear_combination (-1 : ℝ) * hs2
  rw [inner, Real.sqrt_sq (by linarith [hge x])]
  ring
