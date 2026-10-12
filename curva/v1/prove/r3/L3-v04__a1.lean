import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Bounds on fractional parts $n r^2 - a(n)$ for $r = (2+\sqrt{5})/2$

$a(n) = \lfloor r \cdot \lfloor r \cdot n \rfloor \rfloor$, where $r = (2 + \sqrt{5})/2$.

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
  have hs0 : (0:ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hss : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  have hs_lo : (2:ℝ) < Real.sqrt 5 := by nlinarith
  have hs_hi : Real.sqrt 5 < 5 / 2 := by nlinarith
  have h5irr : Irrational (Real.sqrt 5) := by
    have h := (by norm_num : Nat.Prime 5).irrational_sqrt
    simpa using h
  have hrc : rConst = (2 + Real.sqrt 5) / 2 := rfl
  have hrr : rConst * rConst = 2 * rConst + 1 / 4 := by
    rw [hrc]
    linear_combination (1 / 4 : ℝ) * hss
  have hr2 : rSq = 2 * rConst + 1 / 4 := by
    unfold rSq
    exact hrr
  have hr_gt2 : (2:ℝ) < rConst := by rw [hrc]; linarith
  have hr_lt : rConst < 9 / 4 := by rw [hrc]; linarith
  have hr_pos : (0:ℝ) < rConst := by linarith
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hn0 : (0:ℝ) < (n:ℝ) := by linarith
  have hn0ne : (n:ℝ) ≠ 0 := hn0.ne'
  have ha_eq : a n = (Int.floor (rConst * ((Int.floor (rConst * (n:ℝ)) : ℤ) : ℝ))).toNat := rfl
  obtain ⟨m, hm⟩ : ∃ m : ℤ, m = Int.floor (rConst * (n:ℝ)) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ, b = Int.floor (rConst * (m:ℝ)) := ⟨_, rfl⟩
  have ha_eq' : a n = b.toNat := by rw [ha_eq, ← hm, ← hb]
  have hm_nonneg : 0 ≤ m := by
    rw [hm]
    exact Int.floor_nonneg.mpr (mul_nonneg hr_pos.le hn0.le)
  have hmR : (0:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm_nonneg
  have hb_nonneg : 0 ≤ b := by
    rw [hb]
    exact Int.floor_nonneg.mpr (mul_nonneg hr_pos.le hmR)
  have hbcast : ((a n : ℕ) : ℝ) = (b : ℝ) := by
    rw [ha_eq']
    have h := Int.toNat_of_nonneg hb_nonneg
    exact_mod_cast h
  have hfl1 : (m:ℝ) ≤ rConst * (n:ℝ) := by
    have h := Int.floor_le (rConst * (n:ℝ))
    rw [← hm] at h
    exact h
  have hfl2 : rConst * (n:ℝ) < (m:ℝ) + 1 := by
    have h := Int.lt_floor_add_one (rConst * (n:ℝ))
    rw [← hm] at h
    exact h
  have hfl3 : (b:ℝ) ≤ rConst * (m:ℝ) := by
    have h := Int.floor_le (rConst * (m:ℝ))
    rw [← hb] at h
    exact h
  have hfl4 : rConst * (m:ℝ) < (b:ℝ) + 1 := by
    have h := Int.lt_floor_add_one (rConst * (m:ℝ))
    rw [← hb] at h
    exact h
  obtain ⟨k, hk⟩ : ∃ k : ℤ, k = 8 * m + (n:ℤ) - 4 * b := ⟨_, rfl⟩
  have hkR : (k:ℝ) = 8 * (m:ℝ) + (n:ℝ) - 4 * (b:ℝ) := by
    rw [hk]
    push_cast <;> ring
  have hkey : (k:ℝ) = 4 * (rConst * (m:ℝ) - b) + (4 * rConst - 8) * (rConst * (n:ℝ) - m) := by
    linear_combination hkR + (-4 * (n:ℝ)) * hrr
  have hE4 : 4 * ((n:ℝ) * rSq - b) = 8 * (rConst * (n:ℝ) - m) + k := by
    linear_combination (4 * (n:ℝ)) * hr2 - hkR
  have hT0 : (0:ℝ) ≤ rConst * (n:ℝ) - m := by linarith
  have hT1 : rConst * (n:ℝ) - m < 1 := by linarith
  have hF0 : (0:ℝ) ≤ rConst * (m:ℝ) - b := by linarith
  have hF1 : rConst * (m:ℝ) - b < 1 := by linarith
  have hT_pos : (0:ℝ) < rConst * (n:ℝ) - m := by
    refine lt_of_le_of_ne hT0 (fun h => ?_)
    rw [hrc] at h
    exact h5irr ⟨((2 * m - 2 * (n:ℤ) : ℤ) : ℚ) / ((n:ℤ) : ℚ), by
      push_cast
      rw [div_eq_iff hn0ne]
      linear_combination 2 * h⟩
  have h4r : (0:ℝ) < 4 * rConst - 8 := by linarith
  have hk_pos : (0:ℝ) < (k:ℝ) := by
    rw [hkey]
    nlinarith [mul_pos h4r hT_pos, mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hF0]
  have hk1 : (1:ℤ) ≤ k := by
    have : (0:ℤ) < k := by exact_mod_cast hk_pos
    omega
  have hk5 : (k:ℝ) < 5 := by
    rw [hkey]
    nlinarith [mul_nonneg h4r.le (by linarith : (0:ℝ) ≤ 1 - (rConst * (n:ℝ) - m)), hF1]
  have hk4 : k ≤ 4 := by
    have : k < 5 := by exact_mod_cast hk5
    omega
  have hk1R : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
  have hk4R : (k:ℝ) ≤ 4 := by exact_mod_cast hk4
  rw [hbcast]
  constructor
  · linarith
  · linarith

end OeisA341254
