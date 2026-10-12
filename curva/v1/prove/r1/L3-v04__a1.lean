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
  have hs5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hR2 : rConst * rConst = 2 * rConst + 1 / 4 := by
    unfold rConst
    linear_combination (1 / 4 : ℝ) * hs5
  have hRlo : 2 < rConst := by
    unfold rConst
    nlinarith [hs5, hs0]
  have hRhi : rConst < 9 / 4 := by
    unfold rConst
    nlinarith [hs5, hs0]
  have hirr : Irrational (Real.sqrt 5) := by
    have h := Nat.Prime.irrational_sqrt (p := 5) (by norm_num)
    simpa using h
  have hnpos : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  obtain ⟨m, hm⟩ : ∃ m : ℤ, m = ⌊rConst * (n : ℝ)⌋ := ⟨_, rfl⟩
  have hm1 : (m : ℝ) ≤ rConst * n := by
    rw [hm]; exact Int.floor_le _
  have hm2 : rConst * n < (m : ℝ) + 1 := by
    rw [hm]; exact Int.lt_floor_add_one _
  have hm0 : (0 : ℤ) ≤ m := by
    rw [hm]
    exact Int.floor_nonneg.mpr (mul_nonneg (by linarith) hnpos.le)
  obtain ⟨f, hf⟩ : ∃ f : ℝ, f = rConst * n - m := ⟨_, rfl⟩
  have hf0 : 0 ≤ f := by rw [hf]; linarith
  have hf1 : f < 1 := by rw [hf]; linarith
  have hfpos : 0 < f := by
    refine lt_of_le_of_ne hf0 ?_
    intro h0
    refine hirr ⟨((2 * (m : ℚ) - 2 * (n : ℚ)) / (n : ℚ)), ?_⟩
    unfold rConst at hf
    push_cast
    rw [div_eq_iff hnpos.ne']
    linear_combination 2 * h0 + 2 * hf
  obtain ⟨P, hP⟩ : ∃ P : ℤ, P = ⌊rConst * (m : ℝ)⌋ := ⟨_, rfl⟩
  have hP1 : (P : ℝ) ≤ rConst * m := by
    rw [hP]; exact Int.floor_le _
  have hP2 : rConst * m < (P : ℝ) + 1 := by
    rw [hP]; exact Int.lt_floor_add_one _
  have hP0 : (0 : ℤ) ≤ P := by
    rw [hP]
    exact Int.floor_nonneg.mpr (mul_nonneg (by linarith) (by exact_mod_cast hm0))
  have ha : a n = P.toNat := by
    subst hP
    subst hm
    rfl
  have hcastP : ((P.toNat : ℕ) : ℝ) = (P : ℝ) := by
    have h : ((P.toNat : ℕ) : ℤ) = P := Int.toNat_of_nonneg hP0
    exact_mod_cast h
  have hid : rConst * (m : ℝ) = 2 * (m : ℝ) + (n : ℝ) / 4 - (rConst - 2) * f := by
    rw [hf]
    linear_combination (n : ℝ) * hR2
  have hE : (rConst - 2) * f < 1 / 4 := by
    nlinarith [mul_pos (show (0 : ℝ) < 1 / 4 - (rConst - 2) by linarith) hfpos]
  have hEpos : 0 < (rConst - 2) * f := mul_pos (by linarith) hfpos
  obtain ⟨s, hs⟩ : ∃ s : ℤ, s = (n : ℤ) - 4 * (P - 2 * m) := ⟨_, rfl⟩
  have hsR : (s : ℝ) = (n : ℝ) - 4 * ((P : ℝ) - 2 * (m : ℝ)) := by
    rw [hs]; push_cast <;> ring
  have hslo : (0 : ℝ) < s := by
    rw [hsR]; linarith
  have hshi : (s : ℝ) < 5 := by
    rw [hsR]; linarith
  have hs1 : (1 : ℝ) ≤ s := by
    have h : (0 : ℤ) < s := by exact_mod_cast hslo
    have h' : (1 : ℤ) ≤ s := by omega
    exact_mod_cast h'
  have hs4 : (s : ℝ) ≤ 4 := by
    have h : s < 5 := by exact_mod_cast hshi
    have h' : s ≤ 4 := by omega
    exact_mod_cast h'
  have hx : (n : ℝ) * (rConst * rConst) - (P : ℝ) = 2 * f + (s : ℝ) / 4 := by
    linear_combination (n : ℝ) * hR2 + (-2 : ℝ) * hf - (1 / 4 : ℝ) * hsR
  have ha' : (a n : ℝ) = (P : ℝ) := by
    rw [ha, hcastP]
  rw [ha']
  unfold rSq
  constructor
  · rw [hx]; linarith
  · rw [hx]; linarith

end OeisA341254
