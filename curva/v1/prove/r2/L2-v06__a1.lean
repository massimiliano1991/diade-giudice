import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem imo_1968_p5_1
  (a : ℝ)
  (f : ℝ → ℝ)
  (h₀ : 0 < a)
  (h₁ : ∀ x, f (x + a) = 1 / 2 + Real.sqrt (f x - (f x)^2)) :
  ∃ b > 0, ∀ x, f (x + b) = f x := by
  refine ⟨2 * a, by linarith, ?_⟩
  have hge : ∀ x, 1/2 ≤ f x := by
    intro x
    have h := h₁ (x - a)
    rw [sub_add_cancel] at h
    rw [h]
    have := Real.sqrt_nonneg (f (x - a) - f (x - a)^2)
    linarith
  have hle : ∀ x, f x ≤ 1 := by
    intro x
    have h := h₁ (x - a)
    rw [sub_add_cancel] at h
    rw [h]
    set q := f (x - a) - f (x - a)^2 with hq_def
    have hq4 : q ≤ 1/4 := by
      rw [hq_def]
      nlinarith [sq_nonneg (f (x - a) - 1/2)]
    have hs : Real.sqrt q ≤ 1/2 := by
      by_cases hq : 0 ≤ q
      · have := Real.sq_sqrt hq
        nlinarith [Real.sqrt_nonneg q]
      · have : Real.sqrt q = 0 := Real.sqrt_eq_zero'.mpr (by linarith)
        linarith
    linarith
  intro x
  have hu1 := hge x
  have hu2 := hle x
  set u := f x with hu
  have hq0 : 0 ≤ u - u^2 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ u) (by linarith : (0:ℝ) ≤ 1 - u)]
  have hs2 : Real.sqrt (u - u^2) ^ 2 = u - u^2 := Real.sq_sqrt hq0
  have hA : f (x + a) = 1/2 + Real.sqrt (u - u^2) := h₁ x
  have hB := h₁ (x + a)
  rw [hA] at hB
  have hC : (1/2 + Real.sqrt (u - u^2)) - (1/2 + Real.sqrt (u - u^2))^2 = (u - 1/2)^2 := by
    linear_combination (-1 : ℝ) * hs2
  rw [hC, Real.sqrt_sq (by linarith : (0:ℝ) ≤ u - 1/2)] at hB
  have hx : x + 2 * a = x + a + a := by ring
  rw [hx, hB]
  ring
