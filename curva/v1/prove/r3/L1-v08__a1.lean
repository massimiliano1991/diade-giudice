import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_234
  (a b : ℕ)
  (h₀ : 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9)
  (h₁ : (10 * a + b)^3 = 912673) :
  a + b = 16 := by
  obtain ⟨ha1, ha9, hb9⟩ := h₀
  interval_cases a <;> interval_cases b <;> simp_all
