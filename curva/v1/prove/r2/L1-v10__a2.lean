import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_711
  (m n : ℕ)
  (h₀ : 0 < m ∧ 0 < n)
  (h₁ : Nat.gcd m n = 8)
  (h₂ : Nat.lcm m n = 112) :
  72 ≤ m + n := by
  have hmn : m * n = 896 := by
    have h := Nat.gcd_mul_lcm m n
    rw [h₁, h₂] at h
    linarith
  by_contra h
  have hm : m < 72 := by omega
  have hn : n < 72 := by omega
  interval_cases m <;> (try omega) <;> interval_cases n <;> first | omega | (norm_num at h₁) | simp_all
