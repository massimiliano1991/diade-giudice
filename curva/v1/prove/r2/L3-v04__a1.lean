import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Bounds on fractional parts $n r^2 - a(n)$ for $r = (2+\sqrt{5})/2$

$a(n) = \lfloor r \cdot \lfloor r \cdot n \rfloor \rfloor$, where $r = (2+\sqrt{5})/2$.

*References:*
- [A341254](https://oeis.org/A341254)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA341254

open Real

/-- The constant $r = (2 + \sqrt{5})/2$. -/
noncomputable def rConst : ℝ := (2 + sqrt 5) / 2

/-- The constant $r^2$. -/
noncomputable def rSq : ℝ := rConst * rConst

/--
$a(n) = \lfloor r \cdot \lfloor r \cdot n \rfloor \rfloor$, where $r = (2 + \sqrt{5})/2$.
Note: The original OEIS definition has $n$ starting at 1. We define $a(n)$ for all $\mathbb{N}$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let r := rConst
  let inner_floor : ℤ := Int.floor (r * n)
  (Int.floor (r * inner_floor.cast)).toNat

/--
Conjecture: $1/4 < n r^2 - a(n) < 3$ for $n \ge 1$, where $r = (2 + \sqrt{5})/2$.

A formal proof has been found with the methods described in
[arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
theorem a_bounds (n : ℕ) (hn : 1 ≤ n) : (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3 := by
  have hs2 : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hslo : 2 < Real.sqrt 5 := by nlinarith
  have hshi : Real.sqrt 5 < 5 / 2 := by nlinarith
  have hirr : Irrational (Real.sqrt 5) := by
    first
      | simpa using (Nat.Prime.irrational_sqrt (p := 5) (by norm_num))
      | simpa using (irrational_sqrt_natCast_iff.mpr (by decide : ¬ IsSquare (5 : ℕ)))
  have hrc : rConst = (2 + Real.sqrt 5) / 2 := rfl
  have hr2 : rConst * rConst = 2 * rConst + 1 / 4 := by
    rw [hrc]; linear_combination (1 / 4 : ℝ) * hs2
  have hr0 : 0 < rConst := by rw [hrc]; linarith
  have hrlo : 2 < rConst := by rw [hrc]; linarith
  have hrhi : rConst < 9 / 4 := by rw [hrc]; linarith
  have hrd : rConst * (rConst - 2) = 1 / 4 := by linear_combination hr2
  have hkey : rConst * rConst * (n : ℝ) = 2 * rConst * (n : ℝ) + (n : ℝ) / 4 := by
    linear_combination (n : ℝ) * hr2
  have hrd1 : 0 < rConst - 2 := by linarith
  have hrd2 : rConst - 2 < 1 / 4 := by linarith
  obtain ⟨m, hm⟩ : ∃ m : ℤ, m = ⌊rConst * (n : ℝ)⌋ := ⟨_, rfl⟩
  have hm1 : (m : ℝ) ≤ rConst * n := by rw [hm]; exact Int.floor_le _
  have hm2 : rConst * n < (m : ℝ) + 1 := by rw [hm]; exact Int.lt_floor_add_one _
  have hm0 : (0 : ℤ) ≤ m := by
    rw [hm]; exact Int.floor_nonneg.mpr (mul_nonneg hr0.le (Nat.cast_nonneg n))
  have hmR : (0 : ℝ) ≤ m := by exact_mod_cast hm0
  obtain ⟨A, hA⟩ : ∃ A : ℤ, A = ⌊rConst * (m : ℝ)⌋ := ⟨_, rfl⟩
  have hA1 : (A : ℝ) ≤ rConst * m := by rw [hA]; exact Int.floor_le _
  have hA2 : rConst * m < (A : ℝ) + 1 := by rw [hA]; exact Int.lt_floor_add_one _
  have hA0 : (0 : ℤ) ≤ A := by
    rw [hA]; exact Int.floor_nonneg.mpr (mul_nonneg hr0.le hmR)
  have haA : (a n : ℝ) = (A : ℝ) := by
    have h1 : a n = A.toNat := by
      subst hA; subst hm; rfl
    have h2 : ((a n : ℕ) : ℤ) = A := by
      rw [h1]; exact Int.toNat_of_nonneg hA0
    exact_mod_cast h2
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hnne : (n : ℝ) ≠ 0 := hnpos.ne'
  have hfpos : (0 : ℝ) < rConst * n - m := by
    have h0 : (0 : ℝ) ≤ rConst * n - m := by linarith
    rcases h0.lt_or_eq with h | h
    · exact h
    · exfalso
      have h' : Real.sqrt 5 * n = 2 * m - 2 * n := by
        rw [hrc] at h; linear_combination (-2 : ℝ) * h
      have hq : ((((2 * m - 2 * n : ℤ) : ℚ) / (n : ℚ) : ℚ) : ℝ) = Real.sqrt 5 := by
        push_cast
        rw [div_eq_iff hnne]
        linarith
      exact hirr ⟨((2 * m - 2 * n : ℤ) : ℚ) / (n : ℚ), hq⟩
  have hf1 : rConst * n - m < 1 := by linarith
  have hF0 : 0 < (rConst * n - m) * (rConst - 2) := mul_pos hfpos hrd1
  have hF1 : (rConst * n - m) * (rConst - 2) < 1 / 4 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hf1.le) hrd1.le]
  obtain ⟨T, hT⟩ : ∃ T : ℤ, T = (n : ℤ) - 4 * (A - 2 * m) := ⟨_, rfl⟩
  have hTR : (T : ℝ) = (n : ℝ) - 4 * ((A : ℝ) - 2 * (m : ℝ)) := by
    rw [hT]; push_cast; try ring
  have hTlo : 4 * ((rConst * n - m) * (rConst - 2)) ≤ (T : ℝ) := by
    rw [hTR]; nlinarith [hA1, hkey]
  have hThi : (T : ℝ) < 4 + 4 * ((rConst * n - m) * (rConst - 2)) := by
    rw [hTR]; nlinarith [hA2, hkey]
  have hTpos : (0 : ℤ) < T := by
    have : (0 : ℝ) < T := by linarith
    exact_mod_cast this
  have hT1 : (1 : ℤ) ≤ T := by omega
  have hT1R : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT1
  have hT5 : (T : ℝ) < 5 := by linarith
  have hT5' : T < 5 := by exact_mod_cast hT5
  have hcases : T = 4 ∨ T ≤ 3 := by omega
  have hQ : (n : ℝ) * (rConst * rConst) - (A : ℝ) = (T : ℝ) / 4 + 2 * (rConst * n - m) := by
    rw [hTR]; linear_combination (n : ℝ) * hr2
  show (1 / 4 : ℝ) < (n : ℝ) * (rConst * rConst) - (a n : ℝ) ∧
    (n : ℝ) * (rConst * rConst) - (a n : ℝ) < 3
  rw [haA]
  rw [hQ]
  constructor
  · linarith
  · rcases hcases with h4 | h3
    · have h4R : (T : ℝ) = 4 := by exact_mod_cast h4
      linarith
    · have h3R : (T : ℝ) ≤ 3 := by exact_mod_cast h3
      linarith

end OeisA341254
