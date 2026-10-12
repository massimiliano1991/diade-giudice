import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_234
  (a b : ℕ)
  (h₀ : 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9)
  (h₁ : (10 * a + b)^3 = 912673) :
  a + b = 16 := by
  obtain ⟨ha1, ha9, hb9⟩ := h₀
  have hlt : 10 * a + b < 100 := by omega
  have key : 10 * a + b = 97 := by
    generalize hn : 10 * a + b = n at h₁ hlt ⊢
    interval_cases n <;> first | rfl | (exfalso; norm_num at h₁)
  omega
