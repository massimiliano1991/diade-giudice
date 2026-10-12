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
  have h8m : 8 ∣ m := by
    rw [← h₁]
    exact Nat.gcd_dvd_left m n
  have h8n : 8 ∣ n := by
    rw [← h₁]
    exact Nat.gcd_dvd_right m n
  obtain ⟨a, rfl⟩ := h8m
  obtain ⟨b, rfl⟩ := h8n
  have hab : a * b = 14 := by nlinarith [hmn]
  have ha0 : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at hab)
  have hb0 : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hab)
  have ha14 : a ≤ 14 := Nat.le_of_dvd (by norm_num) ⟨b, hab.symm⟩
  clear hmn h₁ h₂ h₀
  interval_cases a <;> omega
