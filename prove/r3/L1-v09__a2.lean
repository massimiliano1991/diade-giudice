import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_numbertheory_451
  (S : Finset ℕ)
  (h₀ : ∀ (n : ℕ), n ∈ S ↔ 2010 ≤ n ∧ n ≤ 2019 ∧ ∃ m, ((Nat.divisors m).card = 4 ∧ ∑ p ∈ (Nat.divisors m), p = n)) :
  ∑ k ∈ S, k = 2016 := by
  have key : ∀ m < 2020, (Nat.divisors m).card = 4 →
      2010 ≤ ∑ p ∈ Nat.divisors m, p → ∑ p ∈ Nat.divisors m, p ≤ 2019 →
      ∑ p ∈ Nat.divisors m, p = 2016 := by
    set_option maxRecDepth 100000 in
    decide
  have hS : S = {2016} := by
    ext n
    rw [h₀ n, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2, m, hc, hs⟩
      have hm0 : m ≠ 0 := by
        rintro rfl
        simp at hc
      have hmle : m ≤ ∑ p ∈ Nat.divisors m, p :=
        Finset.single_le_sum (f := fun p => p) (fun i _ => Nat.zero_le i)
          (Nat.mem_divisors_self m hm0)
      have hm : m < 2020 := by omega
      have hsum := key m hm hc (by omega) (by omega)
      omega
    · rintro rfl
      refine ⟨by norm_num, by norm_num, 1909, ?_, ?_⟩
      · set_option maxRecDepth 100000 in
        decide
      · set_option maxRecDepth 100000 in
        decide
  rw [hS, Finset.sum_singleton]
