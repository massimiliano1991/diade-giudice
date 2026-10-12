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
  have key : ∀ x : ℝ, x ≠ 0 → |x - 1/x| = 1 → (x^2 - x - 1 = 0 ∨ x^2 + x - 1 = 0) := by
    intro x hx h
    have hinv : x * (1/x) = 1 := mul_one_div_cancel hx
    rcases (abs_eq (zero_le_one)).mp h with h' | h'
    · left
      linear_combination x * h' + hinv
    · right
      linear_combination x * h' + hinv
  have key2 : ∀ x y : ℝ, 0 < x → 0 < y → x^2 - x - 1 = 0 → y^2 + y - 1 = 0 →
      x + y = Real.sqrt 5 := by
    intro x y hx hy hx2 hy2
    have hfac : (y - (x - 1)) * (y + (x - 1) + 1) = 0 := by
      linear_combination hy2 - hx2
    rcases mul_eq_zero.mp hfac with h | h
    · have h5 : (x + y)^2 = 5 := by
        linear_combination 4 * hx2 + (y + 3 * x - 1) * h
      have hpos : 0 < x + y := by linarith
      rw [← h5]
      rw [Real.sqrt_sq hpos.le]
    · exfalso
      linarith
  have ha := key a h₀.1.ne' h₂
  have hb := key b h₀.2.ne' h₃
  rcases ha with ha | ha
  · rcases hb with hb | hb
    · exfalso
      have hf : (a - b) * (a + b - 1) = 0 := by
        linear_combination ha - hb
      rcases mul_eq_zero.mp hf with h | h
      · exact h₁ (by linarith)
      · nlinarith [mul_pos h₀.1 (show (0:ℝ) < 1 - a by linarith [h₀.2])]
    · exact key2 a b h₀.1 h₀.2 ha hb
  · rcases hb with hb | hb
    · rw [add_comm]
      exact key2 b a h₀.2 h₀.1 hb ha
    · exfalso
      have hf : (a - b) * (a + b + 1) = 0 := by
        linear_combination ha - hb
      rcases mul_eq_zero.mp hf with h | h
      · exact h₁ (by linarith)
      · linarith [h₀.1, h₀.2]
