import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1988_p8
  (f : ℕ → ℕ → ℝ)
  (h₀ : ∀ x, 0 < x → f x x = x)
  (h₁ : ∀ x y, (0 < x ∧ 0 < y) → f x y = f y x)
  (h₂ : ∀ x y, (0 < x ∧ 0 < y) → (↑x + ↑y) * f x y = y * (f x (x + y))) :
  f 14 52 = 364 := by
  have key : ∀ n : ℕ, ∀ x y : ℕ, 0 < x → 0 < y → x + y ≤ n →
      f x y = ((x:ℝ) * (y:ℝ)) / (Nat.gcd x y : ℝ) := by
    intro n
    induction n with
    | zero =>
      intro x y hx hy h
      omega
    | succ n ih =>
      have lt_case : ∀ x y : ℕ, 0 < x → 0 < y → x < y → x + y ≤ n + 1 →
          f x y = ((x:ℝ) * (y:ℝ)) / (Nat.gcd x y : ℝ) := by
        intro x y hx hy hxy hs
        obtain ⟨z, rfl⟩ : ∃ z, y = x + z := ⟨y - x, by omega⟩
        have hz : 0 < z := by omega
        have hfz : f x z = ((x:ℝ) * (z:ℝ)) / (Nat.gcd x z : ℝ) :=
          ih x z hx hz (by omega)
        have e : ((x:ℝ) + (z:ℝ)) * f x z = (z:ℝ) * f x (x + z) :=
          h₂ x z ⟨hx, hz⟩
        have hgcd : Nat.gcd x (x + z) = Nat.gcd x z := Nat.gcd_self_add_right x z
        rw [hgcd]
        have hz' : (z:ℝ) ≠ 0 := by exact_mod_cast hz.ne'
        rw [hfz] at e
        refine mul_left_cancel₀ hz' ?_
        rw [← e]
        push_cast
        ring
      intro x y hx hy hs
      rcases lt_trichotomy x y with hlt | heq | hgt
      · exact lt_case x y hx hy hlt hs
      · rw [heq]
        have hy' : (y:ℝ) ≠ 0 := by exact_mod_cast hy.ne'
        rw [h₀ y hy, Nat.gcd_self, mul_div_assoc, div_self hy', mul_one]
      · rw [h₁ x y ⟨hx, hy⟩, lt_case y x hy hx hgt (by omega), Nat.gcd_comm]
        ring
  have hg : Nat.gcd 14 52 = 2 := by norm_num
  rw [key (14 + 52) 14 52 (by norm_num) (by norm_num) (by norm_num), hg]
  norm_num
