import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12a_2002_p13
  (a b : ℝ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : a ≠ b)
  (h₂ : abs (a - 1/a) = 1)
  (h₃ : abs (b - 1/b) = 1) :
  a + b = Real.sqrt 5 := by
  have hs : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have key : ∀ x : ℝ, 0 < x → abs (x - 1/x) = 1 →
      x = (1 + Real.sqrt 5)/2 ∨ x = (Real.sqrt 5 - 1)/2 := by
    intro x hx hab
    have hx0 : x ≠ 0 := ne_of_gt hx
    have e : x * (1/x) = 1 := mul_one_div_cancel hx0
    have quad : x*x - x - 1 = 0 ∨ x*x + x - 1 = 0 := by
      rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hab with h | h
      · left; linear_combination x * h + e
      · right; linear_combination x * h + e
    rcases quad with q | q
    · have hf : (x - (1 + Real.sqrt 5)/2) * (x - (1 - Real.sqrt 5)/2) = 0 := by
        linear_combination q - (1/4) * hs
      rcases mul_eq_zero.mp hf with h | h
      · left; linarith
      · exfalso
        have hlt : Real.sqrt 5 < 1 := by linarith
        nlinarith
    · have hf : (x - (Real.sqrt 5 - 1)/2) * (x + (Real.sqrt 5 + 1)/2) = 0 := by
        linear_combination q - (1/4) * hs
      rcases mul_eq_zero.mp hf with h | h
      · right; linarith
      · exfalso; linarith
  obtain ⟨ha0, hb0⟩ := h₀
  rcases key a ha0 h₂ with ha | ha <;> rcases key b hb0 h₃ with hb | hb <;>
    first
    | linarith
    | (exfalso; apply h₁; linarith)
