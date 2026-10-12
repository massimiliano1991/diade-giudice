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
  -- Not compiled in this session. Outline: trapezoid rule for x^k on [0,1]
  -- (lower bound) and comparison with a geometric series (upper bound).
  have key_ineq : ∀ (a b : ℝ) (k : ℕ), 2 ≤ k → 0 ≤ a → a < b →
      2 * (b^(k+1) - a^(k+1)) < (b - a) * ((k:ℝ)+1) * (a^k + b^k) := by
    intro a b k hk ha hab
    have hab' : a ≤ b := hab.le
    have hba : 0 < b - a := sub_pos.2 hab
    have hgeom : (∑ i ∈ Finset.range (k+1), b^i * a^(k-i)) * (b - a) = b^(k+1) - a^(k+1) := by
      have h := geom_sum₂_mul b a (k+1)
      rw [Nat.add_sub_cancel] at h
      exact h
    have hAB : ∑ i ∈ Finset.range (k+1), a^i * b^(k-i)
        = ∑ i ∈ Finset.range (k+1), b^i * a^(k-i) := by
      rw [← Finset.sum_range_reflect (fun i => b^i * a^(k-i)) (k+1)]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < k+1 := Finset.mem_range.1 hi
      simp only [Nat.add_sub_cancel]
      rw [Nat.sub_sub_self (show i ≤ k by omega)]
      ring
    have hpt : ∀ i ∈ Finset.range (k+1), (b^i - a^i) * (b^(k-i) - a^(k-i))
        = b^k + a^k - (b^i * a^(k-i) + a^i * b^(k-i)) := by
      intro i hi
      have hik : i ≤ k := by have := Finset.mem_range.1 hi; omega
      have h1 : b^i * b^(k-i) = b^k := by rw [← pow_add, Nat.add_sub_of_le hik]
      have h2 : a^i * a^(k-i) = a^k := by rw [← pow_add, Nat.add_sub_of_le hik]
      linear_combination h1 + h2
    have hsum : ∑ i ∈ Finset.range (k+1), (b^i - a^i) * (b^(k-i) - a^(k-i))
        = ((k:ℝ)+1) * (a^k + b^k) - 2 * ∑ i ∈ Finset.range (k+1), b^i * a^(k-i) := by
      rw [Finset.sum_congr rfl hpt]
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      rw [hAB]
      push_cast
      ring
    have hpos : 0 < ∑ i ∈ Finset.range (k+1), (b^i - a^i) * (b^(k-i) - a^(k-i)) := by
      have hnn : ∀ i ∈ Finset.range (k+1), 0 ≤ (b^i - a^i) * (b^(k-i) - a^(k-i)) := by
        intro i _
        apply mul_nonneg
        · have h : a^i ≤ b^i := by
            gcongr <;> first | exact ha | exact hab' | omega
          linarith
        · have h : a^(k-i) ≤ b^(k-i) := by
            gcongr <;> first | exact ha | exact hab' | omega
          linarith
      have h1 : (1:ℕ) ∈ Finset.range (k+1) := Finset.mem_range.2 (by omega)
      have hterm1 : 0 < (b^1 - a^1) * (b^(k-1) - a^(k-1)) := by
        apply mul_pos
        · simp only [pow_one]; linarith
        · have h : a^(k-1) < b^(k-1) := by
            gcongr <;> first | exact ha | exact hab | omega
          linarith
      exact lt_of_lt_of_le hterm1 (Finset.single_le_sum hnn h1)
    have hbr : 0 < ((k:ℝ)+1) * (a^k + b^k) - 2 * ∑ i ∈ Finset.range (k+1), b^i * a^(k-i) := by
      rw [← hsum]; exact hpos
    nlinarith [mul_pos hba hbr, hgeom]
  have up_term : ∀ k i : ℕ, i ≤ k → 0 < k → ((i:ℝ)/k)^k ≤ (1/2:ℝ)^(k-i) := by
    intro k i hi hk
    have hkR : (0:ℝ) < k := by exact_mod_cast hk
    have hkR0 : (k:ℝ) ≠ 0 := hkR.ne'
    have hkk : (k:ℝ) * (1/(k:ℝ)) = 1 := mul_one_div_cancel hkR0
    have hmR : ((k-i:ℕ):ℝ) = (k:ℝ) - i := by rw [Nat.cast_sub hi]
    have hy1 : (i:ℝ)/k ≤ Real.exp (-((k-i:ℕ):ℝ)/k) := by
      have h := Real.add_one_le_exp (-((k-i:ℕ):ℝ)/k)
      have hyy : -((k-i:ℕ):ℝ)/k + 1 = (i:ℝ)/k := by
        rw [hmR]; linear_combination (-1:ℝ) * hkk
      linarith
    have hy2 : ((i:ℝ)/k)^k ≤ (Real.exp (-((k-i:ℕ):ℝ)/k))^k := by
      gcongr <;> first | exact hy1 | positivity
    have hy3 : (Real.exp (-((k-i:ℕ):ℝ)/k))^k = Real.exp (-((k-i:ℕ):ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      linear_combination (-((k-i:ℕ):ℝ)) * hkk
    have hy4 : Real.exp (-((k-i:ℕ):ℝ)) = (Real.exp (-1))^(k-i) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have he : (2:ℝ) < Real.exp 1 := by
      have := Real.exp_one_gt_d9
      norm_num at this
      linarith
    have hprod : Real.exp (-1) * Real.exp 1 = 1 := by
      rw [← Real.exp_add]; norm_num
    have hy5 : Real.exp (-1) ≤ 1/2 := by
      nlinarith [Real.exp_pos (-1), he, hprod]
    have hy6 : (Real.exp (-1))^(k-i) ≤ (1/2:ℝ)^(k-i) := by
      gcongr <;> first | exact hy5 | positivity
    rw [hy3, hy4] at hy2
    exact hy2.trans hy6
  have hgeo : ∀ t : ℕ, ∑ j ∈ Finset.range t, (1/2:ℝ)^j = 2 - 2*(1/2:ℝ)^t := by
    intro t
    induction t with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; ring
  have main_aux : ∀ k : ℕ, 2 ≤ k →
      (3*(k:ℝ)+1)/(2*(k:ℝ)+2) < ∑ j ∈ Finset.range k, (((j+1:ℕ):ℝ)/k)^k ∧
      ∑ j ∈ Finset.range k, (((j+1:ℕ):ℝ)/k)^k < 2 := by
    intro k hk
    have hk0 : 0 < k := by omega
    have hkR : (0:ℝ) < k := by exact_mod_cast hk0
    have hkR0 : (k:ℝ) ≠ 0 := hkR.ne'
    have hkk : (k:ℝ) * (1/(k:ℝ)) = 1 := mul_one_div_cancel hkR0
    constructor
    · have hterm : ∀ i ∈ Finset.range k,
          2 * ((((i+1:ℕ):ℝ)/k)^(k+1) - ((i:ℝ)/k)^(k+1))
            < (1/(k:ℝ)*((k:ℝ)+1)) * ((((i:ℝ)/k))^k + (((i+1:ℕ):ℝ)/k)^k) := by
        intro i _
        have hd : ((i+1:ℕ):ℝ)/k - (i:ℝ)/k = 1/k := by push_cast; ring
        have hab : (i:ℝ)/k < ((i+1:ℕ):ℝ)/k := by
          have h2 : (0:ℝ) < 1/k := one_div_pos.2 hkR
          linarith
        have hkey := key_ineq ((i:ℝ)/k) (((i+1:ℕ):ℝ)/k) k hk (by positivity) hab
        rw [hd] at hkey
        exact hkey
      have hL : ∑ i ∈ Finset.range k, 2 * ((((i+1:ℕ):ℝ)/k)^(k+1) - ((i:ℝ)/k)^(k+1)) = 2 := by
        rw [← Finset.mul_sum, Finset.sum_range_sub (fun i : ℕ => ((i:ℝ)/k)^(k+1))]
        simp [div_self hkR0, zero_pow (show k+1 ≠ 0 by omega)]
      have hS := Finset.sum_lt_sum_of_nonempty
        (Finset.nonempty_range_iff.2 (show k ≠ 0 by omega)) hterm
      rw [hL, ← Finset.mul_sum, Finset.sum_add_distrib] at hS
      have h1 : ∑ i ∈ Finset.range (k+1), ((i:ℝ)/k)^k
          = ∑ i ∈ Finset.range k, (((i+1:ℕ):ℝ)/k)^k + ((((0:ℕ)):ℝ)/k)^k :=
        Finset.sum_range_succ' (fun i : ℕ => ((i:ℝ)/k)^k) k
      have h2 : ∑ i ∈ Finset.range (k+1), ((i:ℝ)/k)^k
          = ∑ i ∈ Finset.range k, ((i:ℝ)/k)^k + ((k:ℝ)/k)^k :=
        Finset.sum_range_succ (fun i : ℕ => ((i:ℝ)/k)^k) k
      have h0 : ((((0:ℕ)):ℝ)/k)^k = 0 := by
        rw [Nat.cast_zero, zero_div, zero_pow (by omega : k ≠ 0)]
      have hkone : ((k:ℝ)/k)^k = 1 := by rw [div_self hkR0, one_pow]
      have hPQ : ∑ i ∈ Finset.range k, ((i:ℝ)/k)^k + 1
          = ∑ i ∈ Finset.range k, (((i+1:ℕ):ℝ)/k)^k := by
        linarith
      have h5 : 2 * (k:ℝ) < ((k:ℝ)+1) * (∑ i ∈ Finset.range k, ((i:ℝ)/k)^k
          + ∑ i ∈ Finset.range k, (((i+1:ℕ):ℝ)/k)^k) := by
        have h3 := mul_lt_mul_of_pos_left hS hkR
        have h4 : (k:ℝ) * ((1/(k:ℝ)*((k:ℝ)+1)) * (∑ i ∈ Finset.range k, ((i:ℝ)/k)^k
            + ∑ i ∈ Finset.range k, (((i+1:ℕ):ℝ)/k)^k))
            = ((k:ℝ)+1) * (∑ i ∈ Finset.range k, ((i:ℝ)/k)^k
            + ∑ i ∈ Finset.range k, (((i+1:ℕ):ℝ)/k)^k) := by
          linear_combination ((k:ℝ)+1) * (∑ i ∈ Finset.range k, ((i:ℝ)/k)^k
            + ∑ i ∈ Finset.range k, (((i+1:ℕ):ℝ)/k)^k) * hkk
        linarith
      rw [div_lt_iff₀ (by positivity)]
      have hP' : ∑ i ∈ Finset.range k, ((i:ℝ)/k)^k
          = ∑ i ∈ Finset.range k, (((i+1:ℕ):ℝ)/k)^k - 1 := by linarith
      rw [hP'] at h5
      nlinarith [h5]
    · have hup : ∑ j ∈ Finset.range k, (((j+1:ℕ):ℝ)/k)^k
          ≤ ∑ j ∈ Finset.range k, (1/2:ℝ)^(k-1-j) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' : j < k := Finset.mem_range.1 hj
        have h := up_term k (j+1) (by omega) hk0
        have e : k - (j+1) = k-1-j := by omega
        rw [e] at h
        exact h
      have hr : ∑ j ∈ Finset.range k, (1/2:ℝ)^(k-1-j) = ∑ j ∈ Finset.range k, (1/2:ℝ)^j :=
        Finset.sum_range_reflect (fun j => (1/2:ℝ)^j) k
      have hg := hgeo k
      have hpos : (0:ℝ) < (1/2:ℝ)^k := by positivity
      linarith
  lift n to ℕ using (by omega)
  have hn : 2 ≤ n := by omega
  have hI : Finset.Icc (1:ℤ) (n:ℤ) = (Finset.range n).image (fun j : ℕ => (j:ℤ) + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro h
      obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (show (0:ℤ) ≤ x - 1 by omega)
      exact ⟨j, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      omega
  have hinj : Set.InjOn (fun j : ℕ => (j:ℤ) + 1) (Finset.range n : Set ℕ) := by
    intro a _ b _ h
    simpa using h
  simp only [Int.cast_natCast, Real.rpow_natCast]
  rw [Finset.sum_coe_sort (Finset.Icc (1:ℤ) (n:ℤ)) (fun i : ℤ => ((i:ℝ)/(n:ℝ))^n)]
  rw [hI, Finset.sum_image hinj]
  have key := main_aux n hn
  push_cast at key ⊢
  exact key
