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
  obtain ⟨ha, hb⟩ := h₀
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hs1 : 1 < Real.sqrt 5 := by nlinarith [hs, hs0]
  have key : ∀ x : ℝ, 0 < x → |x - 1/x| = 1 → (x^2 - x - 1 = 0 ∨ x^2 + x - 1 = 0) := by
    intro x hx h
    have hx' : x ≠ 0 := ne_of_gt hx
    have e : x * (1/x) = 1 := by field_simp
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp h with h' | h'
    · left
      linear_combination x * h' + e
    · right
      linear_combination x * h' + e
  have mixed : ∀ x y : ℝ, 0 < x → 0 < y → x^2 - x - 1 = 0 → y^2 + y - 1 = 0 →
      x + y = Real.sqrt 5 := by
    intro x y hx hy hx2 hy2
    have hA : (2*x - 1 - Real.sqrt 5) * (2*x - 1 + Real.sqrt 5) = 0 := by
      linear_combination 4*hx2 - hs
    have hB : (2*y + 1 - Real.sqrt 5) * (2*y + 1 + Real.sqrt 5) = 0 := by
      linear_combination 4*hy2 - hs
    rcases mul_eq_zero.mp hA with h1 | h1 <;> rcases mul_eq_zero.mp hB with h2 | h2 <;> linarith
  have ha2 := key a ha h₂
  have hb2 := key b hb h₃
  rcases ha2 with ha2 | ha2 <;> rcases hb2 with hb2 | hb2
  · exfalso
    have hf : (a - b) * (a + b - 1) = 0 := by
      linear_combination ha2 - hb2
    rcases mul_eq_zero.mp hf with h | h
    · exact h₁ (by linarith)
    · nlinarith [mul_pos ha hb]
  · exact mixed a b ha hb ha2 hb2
  · have := mixed b a hb ha hb2 ha2
    linarith
  · exfalso
    have hf : (a - b) * (a + b + 1) = 0 := by
      linear_combination ha2 - hb2
    rcases mul_eq_zero.mp hf with h | h
    · exact h₁ (by linarith)
    · linarith
