import Mathlib
set_option autoImplicit false

open MeasureTheory

/--
Prove that for every integer $n$ greater than 1: \[ \frac{3n+1}{2n+2} < \left( \frac{1}{n} \right)^n + \left(\frac{2}{n} \right)^n + \cdots + \left(\frac{n}{n} \right)^n < 2. \]
-/
theorem putnam_1962_b5
(n : ℤ)
(ng1 : n > 1)
: (3 * (n : ℝ) + 1) / (2 * n + 2) < ∑ i : Finset.Icc 1 n, ((i : ℝ) / n) ^ (n : ℝ) ∧ ∑ i : Finset.Icc 1 n, ((i : ℝ) / n) ^ (n : ℝ) < 2 := by
  -- (b+1)^(m+1) - b^(m+1) = ∑_{i ≤ m} (b+1)^i b^(m-i)
  have G1 : ∀ (m : ℕ) (b : ℝ),
      (b+1)^(m+1) - b^(m+1) = ∑ i ∈ Finset.range (m+1), (b+1)^i * b^(m-i) := by
    intro m b
    have h := geom_sum₂_mul (b+1) b (m+1)
    simp only [Nat.add_sub_cancel] at h
    rw [show (b+1) - b = (1:ℝ) by ring, mul_one] at h
    exact h.symm
  -- trapezoid-type inequality
  have L1 : ∀ (m : ℕ) (b : ℝ), 0 ≤ b →
      2 * ((b+1)^(m+1) - b^(m+1)) ≤ ((m:ℝ)+1) * ((b+1)^m + b^m) := by
    intro m b hb
    have hG := G1 m b
    have hrefl : (∑ i ∈ Finset.range (m+1), (b+1)^(m-i) * b^(m-(m-i)))
        = ∑ i ∈ Finset.range (m+1), (b+1)^i * b^(m-i) := by
      have h := Finset.sum_range_reflect (fun i => (b+1)^i * b^(m-i)) (m+1)
      simp only [Nat.add_sub_cancel] at h
      exact h
    have hrefl2 : (∑ i ∈ Finset.range (m+1), (b+1)^(m-i) * b^(m-(m-i)))
        = ∑ i ∈ Finset.range (m+1), (b+1)^(m-i) * b^i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [Nat.sub_sub_self (by omega : i ≤ m)]
    have hGS : (∑ i ∈ Finset.range (m+1), (b+1)^(m-i) * b^i)
        = ∑ i ∈ Finset.range (m+1), (b+1)^i * b^(m-i) :=
      hrefl2.symm.trans hrefl
    have hterm : ∀ j ∈ Finset.range (m+1),
        (b+1)^j * b^(m-j) + (b+1)^(m-j) * b^j ≤ (b+1)^m + b^m := by
      intro j hj
      rw [Finset.mem_range] at hj
      have e1 : (b+1)^m = (b+1)^j * (b+1)^(m-j) := by
        rw [← pow_add]; congr 1; omega
      have e2 : b^m = b^j * b^(m-j) := by
        rw [← pow_add]; congr 1; omega
      have p1 : b^j ≤ (b+1)^j := by gcongr <;> linarith
      have p2 : b^(m-j) ≤ (b+1)^(m-j) := by gcongr <;> linarith
      rw [e1, e2]
      nlinarith [mul_nonneg (sub_nonneg.2 p1) (sub_nonneg.2 p2)]
    have hsplit : (∑ j ∈ Finset.range (m+1), ((b+1)^j * b^(m-j) + (b+1)^(m-j) * b^j))
        = (∑ i ∈ Finset.range (m+1), (b+1)^i * b^(m-i))
          + (∑ i ∈ Finset.range (m+1), (b+1)^i * b^(m-i)) := by
      rw [Finset.sum_add_distrib, hGS]
    have hfin := Finset.sum_le_sum hterm
    rw [hsplit, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← hG] at hfin
    push_cast at hfin
    linarith
  -- upper partial-sum bound
  have U1 : ∀ (m N : ℕ), ((m:ℝ)+1) * (∑ k ∈ Finset.range N, (k:ℝ)^m) ≤ (N:ℝ)^(m+1) := by
    intro m N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      push_cast
      have hb : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
      have hG := G1 m (N:ℝ)
      have hterm : ∀ i ∈ Finset.range (m+1),
          (N:ℝ)^m ≤ ((N:ℝ)+1)^i * (N:ℝ)^(m-i) := by
        intro i hi
        rw [Finset.mem_range] at hi
        have e : (N:ℝ)^m = (N:ℝ)^i * (N:ℝ)^(m-i) := by
          rw [← pow_add]; congr 1; omega
        have p : (N:ℝ)^i ≤ ((N:ℝ)+1)^i := by gcongr <;> linarith
        rw [e]
        exact mul_le_mul_of_nonneg_right p (by positivity)
      have hsum := Finset.sum_le_sum hterm
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
      push_cast at hsum
      linarith
  -- lower bound by trapezoid telescoping, with strictness
  have L3 : ∀ (m N : ℕ), 2 * ((m:ℝ)+1) * (∑ k ∈ Finset.range (N+1), ((k:ℝ)+1)^m)
      ≥ 2 * ((N:ℝ)+1)^(m+1) + ((m:ℝ)+1) * ((N:ℝ)+1)^m + ((m:ℝ)-1) := by
    intro m N
    induction N with
    | zero => norm_num <;> linarith
    | succ N ih =>
      rw [Finset.sum_range_succ]
      push_cast
      have h1 := L1 m ((N:ℝ)+1) (by positivity)
      linarith
  -- reduce to a natural number m
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m:ℤ) := ⟨n.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hm : 2 ≤ m := by omega
  have hm0 : m ≠ 0 := by omega
  have hIcc : Finset.Icc (1:ℤ) (m:ℤ) = (Finset.range m).image (fun k : ℕ => (k:ℤ)+1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : (((x-1).toNat : ℕ) : ℤ) = x - 1 := Int.toNat_of_nonneg (by omega)
      exact ⟨(x-1).toNat, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      omega
  have hsum : ∑ i : Finset.Icc 1 (m:ℤ), ((i:ℝ) / ((m:ℤ):ℝ)) ^ (((m:ℤ)):ℝ)
      = (∑ k ∈ Finset.range m, ((k:ℝ)+1)^m) / (m:ℝ)^m := by
    refine (Finset.sum_coe_sort (Finset.Icc (1:ℤ) (m:ℤ))
      (fun i : ℤ => ((i:ℝ) / ((m:ℤ):ℝ)) ^ (((m:ℤ)):ℝ))).trans ?_
    rw [hIcc, Finset.sum_image]
    · rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      simp [div_pow, Real.rpow_natCast]
    · intro a _ b _ h
      simpa using h
  rw [hsum]
  push_cast
  have hMpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hM1 : (1:ℝ) < (m:ℝ) := by exact_mod_cast (show 1 < m by omega)
  have hpow : (0:ℝ) < (m:ℝ)^m := pow_pos hMpos m
  have hpow_succ : (m:ℝ)^(m+1) = (m:ℝ)^m * (m:ℝ) := pow_succ _ _
  have hQ : (∑ k ∈ Finset.range m, ((k:ℝ)+1)^m)
      = (∑ k ∈ Finset.range m, (k:ℝ)^m) + (m:ℝ)^m := by
    have h1 := Finset.sum_range_succ (fun k : ℕ => (k:ℝ)^m) m
    have h2 := Finset.sum_range_succ' (fun k : ℕ => (k:ℝ)^m) m
    push_cast at h1 h2
    have h0 : (0:ℝ)^m = 0 := zero_pow hm0
    linarith
  have hup : ((m:ℝ)+1) * (∑ k ∈ Finset.range m, ((k:ℝ)+1)^m)
      ≤ (m:ℝ) * (m:ℝ)^m + ((m:ℝ)+1) * (m:ℝ)^m := by
    rw [hQ]
    have h := U1 m m
    rw [hpow_succ] at h
    linarith
  have key := L3 m (m-1)
  have hm1 : m - 1 + 1 = m := by omega
  have hc : ((m-1 : ℕ) : ℝ) + 1 = (m:ℝ) := by exact_mod_cast hm1
  rw [hm1, hc, hpow_succ] at key
  have ht : (∑ k ∈ Finset.range m, ((k:ℝ)+1)^m) / (m:ℝ)^m * (m:ℝ)^m
      = ∑ k ∈ Finset.range m, ((k:ℝ)+1)^m := by
    have hne : (m:ℝ)^m ≠ 0 := hpow.ne'
    field_simp
  set t := (∑ k ∈ Finset.range m, ((k:ℝ)+1)^m) / (m:ℝ)^m with htdef
  rw [← ht] at key hup
  constructor
  · have h2 : (m:ℝ)^m * (3*(m:ℝ)+1) < (m:ℝ)^m * (2*((m:ℝ)+1)*t) := by
      nlinarith [key, hM1]
    have h3 := lt_of_mul_lt_mul_left h2 hpow.le
    rw [div_lt_iff₀ (by positivity)]
    linarith
  · have h2 : (m:ℝ)^m * (((m:ℝ)+1)*t) < (m:ℝ)^m * (((m:ℝ)+1)*2) := by
      nlinarith [hup, hpow]
    have h3 := lt_of_mul_lt_mul_left h2 hpow.le
    have h4 := lt_of_mul_lt_mul_left h3 (by positivity)
    linarith
