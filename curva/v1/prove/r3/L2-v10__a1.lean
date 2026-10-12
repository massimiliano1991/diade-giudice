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
  have key : ∀ x y : ℕ, x^3 = y^3 → x = y := fun x y h => Nat.pow_left_injective (by norm_num) h
  have e0 : a 0 = 1 := key _ 1 (by rw [h₀]; norm_num)
  have e1 : a 1 = 2 := key _ 2 (by rw [h₁]; norm_num)
  have e2 : a 2 = 3 := key _ 3 (by rw [h₂]; norm_num)
  have e3 : a 3 = 4 := key _ 4 (by rw [h₃]; norm_num)
  have e4 : a 4 = 5 := key _ 5 (by rw [h₄]; norm_num)
  have e5 : a 5 = 6 := key _ 6 (by rw [h₅]; norm_num)
  have e6 : a 6 = 7 := key _ 7 (by rw [h₆]; norm_num)
  norm_num [Finset.sum_range_succ, e0, e1, e2, e3, e4, e5, e6]
