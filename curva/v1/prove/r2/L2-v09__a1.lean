import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem imo_1969_p2
  (m n : ℝ)
  (k : ℕ)
  (a : ℕ → ℝ)
  (y : ℝ → ℝ)
  (h₀ : 0 < k)
  (h₁ : ∀ x, y x = ∑ i ∈ Finset.range k, ((Real.cos (a i + x)) / (2^i)))
  (h₂ : y m = 0)
  (h₃ : y n = 0) :
  ∃ t : ℤ, m - n = t * π := by
  have geom : ∀ N : ℕ, ∑ i ∈ Finset.range N, (1:ℝ) / 2^i = 2 - 2 / 2^N := by
    intro N
    induction N with
    | zero => norm_num
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  have hpos : 0 < y (-a 0) := by
    rw [h₁]
    have key : ∀ i ∈ Finset.range k,
        (0:ℝ) ≤ Real.cos (a i + -a 0) / 2^i + 1 / 2^i := by
      intro i _
      have hc := Real.neg_one_le_cos (a i + -a 0)
      have hp : (0:ℝ) < 2^i := by positivity
      have e : Real.cos (a i + -a 0) / 2^i + 1 / 2^i
          = (Real.cos (a i + -a 0) + 1) / 2^i := by ring
      rw [e]
      exact div_nonneg (by linarith) hp.le
    have h0 : Real.cos (a 0 + -a 0) / 2^0 + (1:ℝ) / 2^0
        ≤ ∑ i ∈ Finset.range k, (Real.cos (a i + -a 0) / 2^i + 1 / 2^i) :=
      Finset.single_le_sum key (Finset.mem_range.mpr h₀)
    have hsplit : ∑ i ∈ Finset.range k, (Real.cos (a i + -a 0) / 2^i + 1 / 2^i)
        = ∑ i ∈ Finset.range k, Real.cos (a i + -a 0) / 2^i
          + ∑ i ∈ Finset.range k, (1:ℝ) / 2^i :=
      Finset.sum_add_distrib
    have hcos0 : Real.cos (a 0 + -a 0) / 2^0 + (1:ℝ) / 2^0 = 2 := by
      norm_num
    have hgeom := geom k
    have hk2 : (0:ℝ) < 2 / 2^k := by positivity
    linarith [h0, hsplit, hgeom, hcos0, hk2]
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = ∑ i ∈ Finset.range k, Real.cos (a i) / 2^i := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = ∑ i ∈ Finset.range k, Real.sin (a i) / 2^i := ⟨_, rfl⟩
  have hy : ∀ x, y x = A * Real.cos x - B * Real.sin x := by
    intro x
    rw [h₁, hAdef, hBdef, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.cos_add]
    ring
  have hAB : A ≠ 0 ∨ B ≠ 0 := by
    by_contra hc
    push_neg at hc
    obtain ⟨hA0, hB0⟩ := hc
    have h00 : y (-a 0) = 0 := by
      rw [hy, hA0, hB0]
      ring
    linarith [hpos, h00]
  have hm : A * Real.cos m - B * Real.sin m = 0 := by
    have := hy m
    linarith
  have hn : A * Real.cos n - B * Real.sin n = 0 := by
    have := hy n
    linarith
  have e1 : A * (Real.sin m * Real.cos n - Real.cos m * Real.sin n) = 0 := by
    linear_combination (Real.sin m) * hn - (Real.sin n) * hm
  have e2 : B * (Real.sin m * Real.cos n - Real.cos m * Real.sin n) = 0 := by
    linear_combination (Real.cos m) * hn - (Real.cos n) * hm
  have hD : Real.sin m * Real.cos n - Real.cos m * Real.sin n = 0 := by
    rcases hAB with h | h
    · exact (mul_eq_zero.mp e1).resolve_left h
    · exact (mul_eq_zero.mp e2).resolve_left h
  have hs : Real.sin (m - n) = 0 := by
    rw [Real.sin_sub]
    exact hD
  obtain ⟨t, ht⟩ := Real.sin_eq_zero_iff.mp hs
  exact ⟨t, ht.symm⟩
