import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1988_p8
  (f : ℕ → ℕ → ℝ)
  (h₀ : ∀ x, 0 < x → f x x = x)
  (h₁ : ∀ x y, (0 < x ∧ 0 < y) → f x y = f y x)
  (h₂ : ∀ x y, (0 < x ∧ 0 < y) → (↑x + ↑y) * f x y = y * (f x (x + y))) :
  f 14 52 = 364 := by
  have key : ∀ n : ℕ, ∀ x y : ℕ, x + y = n → 0 < x → 0 < y →
      f x y * ((Nat.gcd x y : ℕ) : ℝ) = (x : ℝ) * (y : ℝ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      have step : ∀ x k : ℕ, x + (x + k) = n → 0 < x → 0 < k →
          f x (x + k) * ((Nat.gcd x (x + k) : ℕ) : ℝ) = (x : ℝ) * ((x + k : ℕ) : ℝ) := by
        intro x k hn hx hk
        have IH := ih (x + k) (by omega) x k rfl hx hk
        have h := h₂ x k ⟨hx, hk⟩
        have hg : Nat.gcd x (x + k) = Nat.gcd x k := by
          first
          | simp
          | exact Nat.gcd_self_add_right x k
        have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
        rw [hg]
        push_cast
        apply mul_left_cancel₀ hk'
        linear_combination (-((Nat.gcd x k : ℕ) : ℝ)) * h + ((x : ℝ) + (k : ℝ)) * IH
      intro x y hn hx hy
      rcases lt_trichotomy x y with hlt | heq | hgt
      · obtain ⟨k, rfl⟩ : ∃ k, y = x + k := ⟨y - x, by omega⟩
        exact step x k hn hx (by omega)
      · rw [heq, h₀ y hy, Nat.gcd_self]
      · obtain ⟨k, rfl⟩ : ∃ k, x = y + k := ⟨x - y, by omega⟩
        have hc : Nat.gcd (y + k) y = Nat.gcd y (y + k) := Nat.gcd_comm _ _
        have hs := step y k (by omega) hy (by omega)
        rw [h₁ (y + k) y ⟨by omega, hy⟩, hc]
        push_cast at hs ⊢
        linear_combination hs
  have h := key (14 + 52) 14 52 rfl (by norm_num) (by norm_num)
  have hg : Nat.gcd 14 52 = 2 := by norm_num
  rw [hg] at h
  norm_num at h
  linarith
