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
  obtain ⟨N, rfl⟩ : ∃ N, k = N + 1 := ⟨k - 1, by omega⟩
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = ∑ i ∈ Finset.range (N + 1),
      Complex.exp (((a i : ℝ) : ℂ) * Complex.I) * (((1 / 2 : ℝ) ^ i : ℝ) : ℂ) := ⟨_, rfl⟩
  have key : ∀ x : ℝ, y x = (z * Complex.exp ((x : ℂ) * Complex.I)).re := by
    intro x
    rw [h₁ x, hz, Finset.sum_mul, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    have e : Complex.exp (((a i : ℝ) : ℂ) * Complex.I) * Complex.exp ((x : ℂ) * Complex.I)
        = Complex.exp (((a i + x : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hcomm : Complex.exp (((a i : ℝ) : ℂ) * Complex.I) * (((1 / 2 : ℝ) ^ i : ℝ) : ℂ)
        * Complex.exp ((x : ℂ) * Complex.I)
        = Complex.exp (((a i + x : ℝ) : ℂ) * Complex.I) * (((1 / 2 : ℝ) ^ i : ℝ) : ℂ) := by
      rw [_root_.mul_right_comm, e]
    rw [hcomm, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im, one_div_pow]
    ring
  have hA : ‖Complex.exp (((a 0 : ℝ) : ℂ) * Complex.I) * (((1 / 2 : ℝ) ^ 0 : ℝ) : ℂ)‖ = 1 := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real]
    norm_num
  have hterm : ∀ i : ℕ, ‖Complex.exp (((a (i + 1) : ℝ) : ℂ) * Complex.I)
      * (((1 / 2 : ℝ) ^ (i + 1) : ℝ) : ℂ)‖ = (1 / 2 : ℝ) ^ (i + 1) := by
    intro i
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, _root_.one_mul,
      Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (i + 1))]
  have geom_bound : ∀ j : ℕ, ∑ i ∈ Finset.range j, (1 / 2 : ℝ) ^ (i + 1) ≤ 1 - (1 / 2 : ℝ) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Finset.sum_range_succ]
      have h := _root_.pow_succ (1 / 2 : ℝ) j
      linarith
  have htail : ‖∑ i ∈ Finset.range N, Complex.exp (((a (i + 1) : ℝ) : ℂ) * Complex.I)
      * (((1 / 2 : ℝ) ^ (i + 1) : ℝ) : ℂ)‖ ≤ 1 - (1 / 2 : ℝ) ^ N := by
    calc _ ≤ ∑ i ∈ Finset.range N, ‖Complex.exp (((a (i + 1) : ℝ) : ℂ) * Complex.I)
          * (((1 / 2 : ℝ) ^ (i + 1) : ℝ) : ℂ)‖ := norm_sum_le _ _
      _ = ∑ i ∈ Finset.range N, (1 / 2 : ℝ) ^ (i + 1) :=
          Finset.sum_congr rfl (fun i _ => hterm i)
      _ ≤ 1 - (1 / 2 : ℝ) ^ N := geom_bound N
  have hsplit : z = Complex.exp (((a 0 : ℝ) : ℂ) * Complex.I) * (((1 / 2 : ℝ) ^ 0 : ℝ) : ℂ)
      + ∑ i ∈ Finset.range N, Complex.exp (((a (i + 1) : ℝ) : ℂ) * Complex.I)
          * (((1 / 2 : ℝ) ^ (i + 1) : ℝ) : ℂ) := by
    rw [hz, Finset.sum_range_succ']
    exact _root_.add_comm _ _
  have hz0 : z ≠ 0 := by
    intro h0
    have hs := hsplit.symm.trans h0
    have hAB := eq_neg_of_add_eq_zero_left hs
    have h1 := congrArg norm hAB
    rw [norm_neg, hA] at h1
    have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ N := by positivity
    linarith [htail]
  have hpq : z.re ≠ 0 ∨ z.im ≠ 0 := by
    by_contra hcon
    simp only [ne_eq, not_or, not_not] at hcon
    exact hz0 (Complex.ext (by simpa using hcon.1) (by simpa using hcon.2))
  have hy : ∀ x : ℝ, y x = z.re * Real.cos x - z.im * Real.sin x := by
    intro x
    rw [key x, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have e1 : z.re * Real.cos m - z.im * Real.sin m = 0 := by
    rw [← hy m]
    exact h₂
  have e2 : z.re * Real.cos n - z.im * Real.sin n = 0 := by
    rw [← hy n]
    exact h₃
  have hD : Real.sin (n - m) = 0 := by
    rw [Real.sin_sub]
    have hp : z.re * (Real.cos m * Real.sin n - Real.sin m * Real.cos n) = 0 := by
      linear_combination Real.sin n * e1 - Real.sin m * e2
    have hq : z.im * (Real.cos m * Real.sin n - Real.sin m * Real.cos n) = 0 := by
      linear_combination Real.cos n * e1 - Real.cos m * e2
    have hD0 : Real.cos m * Real.sin n - Real.sin m * Real.cos n = 0 := by
      rcases hpq with hp0 | hq0
      · exact (_root_.mul_eq_zero.mp hp).resolve_left hp0
      · exact (_root_.mul_eq_zero.mp hq).resolve_left hq0
    linear_combination hD0
  obtain ⟨t, ht⟩ := Real.sin_eq_zero_iff.mp hD
  exact ⟨-t, by push_cast; linear_combination ht⟩
