import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1988_p8
  (f : ℕ → ℕ → ℝ)
  (h₀ : ∀ x, 0 < x → f x x = x)
  (h₁ : ∀ x y, (0 < x ∧ 0 < y) → f x y = f y x)
  (h₂ : ∀ x y, (0 < x ∧ 0 < y) → (↑x + ↑y) * f x y = y * (f x (x + y))) :
  f 14 52 = 364 := by
  have k1 := h₀ 2 (by norm_num)
  have k2 := h₂ 2 2 (by norm_num)
  have k3 := h₁ 4 2 (by norm_num)
  have k4 := h₂ 4 2 (by norm_num)
  have k5 := h₂ 4 6 (by norm_num)
  have k6 := h₁ 4 10 (by norm_num)
  have k7 := h₂ 10 4 (by norm_num)
  have k8 := h₁ 14 10 (by norm_num)
  have k9 := h₂ 14 10 (by norm_num)
  have k10 := h₂ 14 24 (by norm_num)
  have k11 := h₂ 14 38 (by norm_num)
  norm_num at k1 k2 k4 k5 k7 k9 k10 k11
  linarith
