import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_451
  (S : Finset ℕ)
  (h₀ : ∀ (n : ℕ), n ∈ S ↔ 2010 ≤ n ∧ n ≤ 2019 ∧ ∃ m, ((Nat.divisors m).card = 4 ∧ ∑ p ∈ (Nat.divisors m), p = n)) :
  ∑ k ∈ S, k = 2016 := by
  have check : ∀ m, m < 2020 → (Nat.divisors m).card = 4 →
      (∑ p ∈ Nat.divisors m, p) < 2010 ∨ 2019 < (∑ p ∈ Nat.divisors m, p) ∨
        (∑ p ∈ Nat.divisors m, p) = 2016 := by
    intro m hm
    interval_cases m <;> decide +kernel
  have key : S = {2016} := by
    ext n
    rw [h₀ n, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2, m, hc, hs⟩
      have hm0 : m ≠ 0 := by
        rintro rfl
        simp at hc
      have hmem : m ∈ Nat.divisors m := Nat.mem_divisors_self m hm0
      have hle : m ≤ ∑ p ∈ Nat.divisors m, p :=
        Finset.single_le_sum (f := fun p : ℕ => p) (fun _ _ => Nat.zero_le _) hmem
      have hm : m < 2020 := by omega
      rcases check m hm hc with h | h | h <;> omega
    · rintro rfl
      refine ⟨by norm_num, by norm_num, 1909, ?_, ?_⟩
      · decide +kernel
      · decide +kernel
  rw [key]
  simp
