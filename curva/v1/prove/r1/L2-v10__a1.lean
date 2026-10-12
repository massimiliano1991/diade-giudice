import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12a_2020_p7
  (a : ℕ → ℕ)
  (h₀ : (a 0)^3 = 1)
  (h₁ : (a 1)^3 = 8)
  (h₂ : (a 2)^3 = 27)
  (h₃ : (a 3)^3 = 64)
  (h₄ : (a 4)^3 = 125)
  (h₅ : (a 5)^3 = 216)
  (h₆ : (a 6)^3 = 343) :
  ∑ k ∈ Finset.range 7, (6 * (a k)^2) - ↑(2 * ∑ k ∈ Finset.range 6, (a k)^2) = 658 := by
  have e0 : a 0 = 1 :=
    Nat.pow_left_injective (n := 3) (by norm_num) (show a 0 ^ 3 = 1 ^ 3 by simp [h₀])
  have e1 : a 1 = 2 :=
    Nat.pow_left_injective (n := 3) (by norm_num) (show a 1 ^ 3 = 2 ^ 3 by simp [h₁])
  have e2 : a 2 = 3 :=
    Nat.pow_left_injective (n := 3) (by norm_num) (show a 2 ^ 3 = 3 ^ 3 by simp [h₂])
  have e3 : a 3 = 4 :=
    Nat.pow_left_injective (n := 3) (by norm_num) (show a 3 ^ 3 = 4 ^ 3 by simp [h₃])
  have e4 : a 4 = 5 :=
    Nat.pow_left_injective (n := 3) (by norm_num) (show a 4 ^ 3 = 5 ^ 3 by simp [h₄])
  have e5 : a 5 = 6 :=
    Nat.pow_left_injective (n := 3) (by norm_num) (show a 5 ^ 3 = 6 ^ 3 by simp [h₅])
  have e6 : a 6 = 7 :=
    Nat.pow_left_injective (n := 3) (by norm_num) (show a 6 ^ 3 = 7 ^ 3 by simp [h₆])
  norm_num [Finset.sum_range_succ, e0, e1, e2, e3, e4, e5, e6]
