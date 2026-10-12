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
  obtain ⟨P, Q, hy, hPQ⟩ : ∃ P Q : ℝ, (∀ x, y x = P * Real.cos x - Q * Real.sin x) ∧
      (P ≠ 0 ∨ Q ≠ 0) := by
    refine ⟨∑ i ∈ Finset.range k, Real.cos (a i) / (2^i),
      ∑ i ∈ Finset.range k, Real.sin (a i) / (2^i), ?_, ?_⟩
    · intro x
      rw [h₁ x, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Real.cos_add]
      ring
    · by_contra hcon
      push_neg at hcon
      obtain ⟨hP, hQ⟩ := hcon
      set g : ℕ → ℂ := fun i => (((1:ℝ) / 2^i : ℝ) : ℂ) * Complex.exp ((a i : ℂ) * Complex.I) with hg
      have e1 : ∑ i ∈ Finset.range k, (g i).re = ∑ i ∈ Finset.range k, Real.cos (a i) / (2^i) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp only [hg]
        rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
        ring
      have e2 : ∑ i ∈ Finset.range k, (g i).im = ∑ i ∈ Finset.range k, Real.sin (a i) / (2^i) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp only [hg]
        rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
        ring
      have hc : ∑ i ∈ Finset.range k, g i = 0 := by
        apply Complex.ext
        · rw [Complex.re_sum, Complex.zero_re, e1, hP]
        · rw [Complex.im_sum, Complex.zero_im, e2, hQ]
      have hn : ∀ i, ‖g i‖ = 1 / 2^i := by
        intro i
        simp only [hg]
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 1 / 2^i)]
      have hgeo : ∀ j : ℕ, ∑ i ∈ Finset.range j, (1:ℝ) / 2^(i+1) = 1 - 1 / 2^j := by
        intro j
        induction j with
        | zero => simp
        | succ j ih => rw [Finset.sum_range_succ, ih]; ring
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [Finset.sum_range_succ'] at hc
      have hg0 : g 0 = -∑ i ∈ Finset.range j, g (i+1) := by
        linear_combination hc
      have hbound : ‖∑ i ∈ Finset.range j, g (i+1)‖ ≤ ∑ i ∈ Finset.range j, (1:ℝ) / 2^(i+1) :=
        (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl (fun i _ => hn (i+1))))
      have h1 : ‖g 0‖ = 1 := by
        rw [hn 0]
        norm_num
      have h2 : ‖g 0‖ = ‖∑ i ∈ Finset.range j, g (i+1)‖ := by
        rw [hg0, norm_neg]
      rw [hgeo] at hbound
      have hpos : (0:ℝ) < 1 / 2^j := by positivity
      linarith
  have hm : P * Real.cos m - Q * Real.sin m = 0 := by
    rw [← hy m]
    exact h₂
  have hn' : P * Real.cos n - Q * Real.sin n = 0 := by
    rw [← hy n]
    exact h₃
  have hA : P * (Real.cos m * Real.sin n - Real.cos n * Real.sin m) = 0 := by
    linear_combination (Real.sin n) * hm - (Real.sin m) * hn'
  have hB : Q * (Real.sin m * Real.cos n - Real.sin n * Real.cos m) = 0 := by
    linear_combination (-(Real.cos n)) * hm + (Real.cos m) * hn'
  have hsin : Real.sin (m - n) = 0 := by
    rw [Real.sin_sub]
    rcases hPQ with hP | hQ
    · have h := (mul_eq_zero.mp hA).resolve_left hP
      linear_combination -h
    · have h := (mul_eq_zero.mp hB).resolve_left hQ
      linear_combination h
  obtain ⟨t, ht⟩ := Real.sin_eq_zero_iff.mp hsin
  exact ⟨t, ht.symm⟩
