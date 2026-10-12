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
  -- Not compiled in this environment; if a step fails, check the lemma names first.
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = (N : ℤ) :=
    ⟨n.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hN2 : 2 ≤ N := by omega
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
  have hp : (0 : ℝ) < (N : ℝ) ^ N := pow_pos hNpos N
  have hpos2 : (0 : ℝ) < 2 * (N : ℝ) + 2 := by linarith
  -- reindex the sum over Icc 1 N as a sum over range N
  have hconv : ∀ f : ℤ → ℝ,
      ∑ i : Finset.Icc (1 : ℤ) (N : ℤ), f (i : ℤ)
        = ∑ j ∈ Finset.range N, f ((j : ℤ) + 1) := by
    intro f
    rw [Finset.sum_coe_sort (Finset.Icc (1 : ℤ) (N : ℤ)) f]
    refine Finset.sum_nbij' (fun i : ℤ => (i - 1).toNat) (fun j : ℕ => (j : ℤ) + 1)
      ?_ ?_ ?_ ?_ ?_
    · intro a ha
      rw [Finset.mem_Icc] at ha
      rw [Finset.mem_range]
      show (a - 1).toNat < N
      have h := Int.toNat_of_nonneg (show (0 : ℤ) ≤ a - 1 by omega)
      omega
    · intro b hb
      rw [Finset.mem_range] at hb
      rw [Finset.mem_Icc]
      show 1 ≤ (b : ℤ) + 1 ∧ (b : ℤ) + 1 ≤ (N : ℤ)
      omega
    · intro a ha
      rw [Finset.mem_Icc] at ha
      have h := Int.toNat_of_nonneg (show (0 : ℤ) ≤ a - 1 by omega)
      show (((a - 1).toNat : ℕ) : ℤ) + 1 = a
      omega
    · intro b _
      show (((b : ℤ) + 1) - 1).toNat = b
      simp
    · intro a ha
      rw [Finset.mem_Icc] at ha
      have h := Int.toNat_of_nonneg (show (0 : ℤ) ≤ a - 1 by omega)
      show f a = f ((((a - 1).toNat : ℕ) : ℤ) + 1)
      congr 1
      omega
  have hS : ∑ i : Finset.Icc (1 : ℤ) (N : ℤ), (((i : ℤ) : ℝ) / ((N : ℤ) : ℝ)) ^ (((N : ℤ) : ℝ))
      = ∑ j ∈ Finset.range N, (((j : ℝ) + 1) / (N : ℝ)) ^ N := by
    refine (hconv (fun i : ℤ => ((i : ℝ) / ((N : ℤ) : ℝ)) ^ (((N : ℤ) : ℝ)))).trans ?_
    apply Finset.sum_congr rfl
    intro j _
    simp [Real.rpow_natCast]
  -- Upper bound
  have hr2 : Real.exp (-1) < 1 / 2 := by
    have h1 : Real.exp (-1) * Real.exp 1 = 1 := by
      rw [← Real.exp_add]; norm_num
    have h2 : (2 : ℝ) < Real.exp 1 := by
      have := Real.exp_one_gt_d9
      norm_num at this
      linarith
    nlinarith [Real.exp_pos (-1), Real.exp_pos 1]
  have hW : ∀ M : ℕ, ∑ j ∈ Finset.range M, Real.exp (((j : ℝ) + 1) - (M : ℝ)) < 2 := by
    intro M
    induction M with
    | zero => simp
    | succ k ih =>
      have hr : ∀ j : ℕ, Real.exp (((j : ℝ) + 1) - ((k + 1 : ℕ) : ℝ))
          = Real.exp (-1) * Real.exp (((j : ℝ) + 1) - (k : ℝ)) := by
        intro j
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring
      have e1 : ∑ j ∈ Finset.range k, Real.exp (((j : ℝ) + 1) - ((k + 1 : ℕ) : ℝ))
          = Real.exp (-1) * ∑ j ∈ Finset.range k, Real.exp (((j : ℝ) + 1) - (k : ℝ)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => hr j)
      have e2 : Real.exp (((k : ℝ) + 1) - ((k + 1 : ℕ) : ℝ)) = 1 := by
        simp
      rw [Finset.sum_range_succ, e1, e2]
      nlinarith [mul_pos (Real.exp_pos (-1)) (sub_pos.mpr ih), hr2]
  have hterm : ∀ x : ℝ, 0 ≤ x → x ^ N ≤ Real.exp ((N : ℝ) * (x - 1)) := by
    intro x hx
    have h1 : x ≤ Real.exp (x - 1) := by linarith [Real.add_one_le_exp (x - 1)]
    have h2 : x ^ N ≤ (Real.exp (x - 1)) ^ N := by gcongr
    rw [Real.exp_nat_mul]
    exact h2
  have hup : ∀ j : ℕ, (((j : ℝ) + 1) / (N : ℝ)) ^ N ≤ Real.exp (((j : ℝ) + 1) - (N : ℝ)) := by
    intro j
    have hx : (0 : ℝ) ≤ ((j : ℝ) + 1) / (N : ℝ) := by positivity
    have h := hterm (((j : ℝ) + 1) / (N : ℝ)) hx
    have hexp : (N : ℝ) * (((j : ℝ) + 1) / (N : ℝ) - 1) = ((j : ℝ) + 1) - (N : ℝ) := by
      field_simp <;> ring
    rw [hexp] at h
    exact h
  have hU : ∑ j ∈ Finset.range N, (((j : ℝ) + 1) / (N : ℝ)) ^ N < 2 :=
    lt_of_le_of_lt (Finset.sum_le_sum (fun j _ => hup j)) (hW N)
  -- Lower bound (discrete trapezoid inequality for x ↦ x^N)
  have T : ∀ x : ℝ, 0 ≤ x →
      2 * ((x + 1) ^ (N + 1) - x ^ (N + 1)) ≤ ((N : ℝ) + 1) * ((x + 1) ^ N + x ^ N) := by
    intro x hx
    have hab : x ≤ x + 1 := by linarith
    have hG : (∑ i ∈ Finset.range (N + 1), (x + 1) ^ i * x ^ (N + 1 - 1 - i))
        * ((x + 1) - x) = (x + 1) ^ (N + 1) - x ^ (N + 1) :=
      geom_sum₂_mul (x + 1) x (N + 1)
    have h1 : (x + 1) - x = 1 := by ring
    rw [h1, mul_one] at hG
    simp only [Nat.add_sub_cancel] at hG
    have hR : ∑ i ∈ Finset.range (N + 1), (x + 1) ^ (N - i) * x ^ i
        = ∑ i ∈ Finset.range (N + 1), (x + 1) ^ i * x ^ (N - i) := by
      refine Finset.sum_nbij' (fun i : ℕ => N - i) (fun i : ℕ => N - i) ?_ ?_ ?_ ?_ ?_
      · intro a ha
        rw [Finset.mem_range] at ha ⊢
        show N - a < N + 1
        omega
      · intro a ha
        rw [Finset.mem_range] at ha ⊢
        show N - a < N + 1
        omega
      · intro a ha
        rw [Finset.mem_range] at ha
        show N - (N - a) = a
        omega
      · intro a ha
        rw [Finset.mem_range] at ha
        show N - (N - a) = a
        omega
      · intro a ha
        rw [Finset.mem_range] at ha
        show (x + 1) ^ (N - a) * x ^ a = (x + 1) ^ (N - a) * x ^ (N - (N - a))
        rw [show N - (N - a) = a by omega]
    have hpt : ∀ i ∈ Finset.range (N + 1),
        (x + 1) ^ i * x ^ (N - i) + (x + 1) ^ (N - i) * x ^ i ≤ x ^ N + (x + 1) ^ N := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hi' : i ≤ N := by omega
      have e1 : x ^ N = x ^ i * x ^ (N - i) := by
        rw [← pow_add, Nat.add_sub_of_le hi']
      have e2 : (x + 1) ^ N = (x + 1) ^ i * (x + 1) ^ (N - i) := by
        rw [← pow_add, Nat.add_sub_of_le hi']
      have h1 : x ^ i ≤ (x + 1) ^ i := by gcongr <;> linarith
      have h2 : x ^ (N - i) ≤ (x + 1) ^ (N - i) := by gcongr <;> linarith
      rw [e1, e2]
      nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]
    have hbound : ∑ i ∈ Finset.range (N + 1),
        ((x + 1) ^ i * x ^ (N - i) + (x + 1) ^ (N - i) * x ^ i)
        ≤ ∑ i ∈ Finset.range (N + 1), (x ^ N + (x + 1) ^ N) :=
      Finset.sum_le_sum hpt
    have hsum2 : 2 * (∑ i ∈ Finset.range (N + 1), (x + 1) ^ i * x ^ (N - i))
        = ∑ i ∈ Finset.range (N + 1),
          ((x + 1) ^ i * x ^ (N - i) + (x + 1) ^ (N - i) * x ^ i) := by
      rw [Finset.sum_add_distrib, hR]
      ring
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hbound
    push_cast at hbound
    rw [← hG]
    nlinarith [hsum2, hbound]
  have hC : ∀ M : ℕ, 2 * ((N : ℝ) + 1) * (∑ j ∈ Finset.range (M + 1), ((j : ℝ) + 1) ^ N)
      ≥ 2 * ((M : ℝ) + 1) ^ (N + 1) + ((N : ℝ) + 1) * ((M : ℝ) + 1) ^ N + ((N : ℝ) - 1) := by
    intro M
    induction M with
    | zero => norm_num <;> linarith
    | succ k ih =>
      rw [Finset.sum_range_succ]
      simp only [Nat.cast_add, Nat.cast_one]
      have hT := T ((k : ℝ) + 1) (by positivity)
      nlinarith [ih, hT]
  have hC' := hC (N - 1)
  have e1 : N - 1 + 1 = N := by omega
  have e2 : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
    have h : N - 1 + 1 = N := by omega
    exact_mod_cast h
  rw [e1, e2, pow_succ] at hC'
  have hQ : ∑ j ∈ Finset.range N, (((j : ℝ) + 1) / (N : ℝ)) ^ N
      = (∑ j ∈ Finset.range N, ((j : ℝ) + 1) ^ N) / (N : ℝ) ^ N := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    rw [div_pow]
  have hL : (3 * (N : ℝ) + 1) / (2 * (N : ℝ) + 2)
      < ∑ j ∈ Finset.range N, (((j : ℝ) + 1) / (N : ℝ)) ^ N := by
    rw [hQ, lt_div_iff₀ hp, div_mul_eq_mul_div, div_lt_iff₀ hpos2]
    nlinarith [hC', hNr]
  rw [hS]
  push_cast
  exact ⟨hL, hU⟩
