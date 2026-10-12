import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_341
  (a b c : ℕ)
  (h₀ : a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9)
  (h₁ : Nat.digits 10 ((5^100) % 1000) = [c,b,a]) :
  a + b + c = 13 := by
  have h2 : (5^100 : ℕ) % 1000 = 625 := by norm_num
  rw [h2] at h₁
  norm_num at h₁
  obtain ⟨h3, h4, h5⟩ := h₁
  omega
