import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_711
  (m n : ℕ)
  (h₀ : 0 < m ∧ 0 < n)
  (h₁ : Nat.gcd m n = 8)
  (h₂ : Nat.lcm m n = 112) :
  72 ≤ m + n := by
  obtain ⟨hm0, hn0⟩ := h₀
  have hmn : m * n = 896 := by
    have := Nat.gcd_mul_lcm m n
    rw [h₁, h₂] at this
    omega
  have hdm : m ∣ 112 := by
    rw [← h₂]
    exact Nat.dvd_lcm_left m n
  have h8m : 8 ∣ m := by
    rw [← h₁]
    exact Nat.gcd_dvd_left m n
  have hm : m ≤ 112 := Nat.le_of_dvd (by norm_num) hdm
  clear h₁ h₂
  interval_cases m <;> omega
