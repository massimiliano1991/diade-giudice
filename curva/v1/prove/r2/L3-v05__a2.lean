import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Integer values of $\tan(\arctan 1 + \arctan 2 + \cdots + \arctan n)$

*References:*
- [arxiv/2607.05739](https://arxiv.org/abs/2607.05739)
  **Integer values of $\tan(\arctan 1+\arctan 2+\cdots+\arctan n)$ are rare** by *Ken Ono*
- [AMM08] T. Amdeberhan, L. A. Medina, and V. H. Moll, *Arithmetical properties of a sequence
  arising from an arctangent sum*, J. Number Theory 128 (2008), no. 6, 1807-1846.
- [TanArctan](https://github.com/AxiomMath/TanArctan), a Lean formalisation of the three
  results of [Ono26], MIT licensed. Its `P`, `A`, `B` and `x` are the definitions used
  here.
-/

open Finset

namespace Arxiv.«2607.05739»

/-- $Z_n = \prod_{k=1}^n (1 + ik)$, in the Gaussian integers. -/
def gaussProd (n : ℕ) : GaussianInt := ∏ k ∈ Finset.Icc 1 n, (⟨1, (k : ℤ)⟩ : GaussianInt)

/-- $A_n = \operatorname{Re} Z_n$. -/
def A (n : ℕ) : ℤ := (gaussProd n).re

/-- $B_n = \operatorname{Im} Z_n$. -/
def B (n : ℕ) : ℤ := (gaussProd n).im

/-- $x_n = \tan\left(\sum_{k=1}^n \arctan k\right) = B_n / A_n$. -/
noncomputable def x (n : ℕ) : ℚ := (B n : ℚ) / (A n : ℚ)

/-- $x_n$ takes an integer value.

Stated as $A_n \mid B_n$ rather than as `∃ m : ℤ, x n = m`, so that it still says the right
thing if $A_n$ were ever $0$. There $x_n$ is a pole of the tangent rather than an integer, but
`(B n : ℚ) / 0` is `0` in Lean and would count as one. The two agree whenever $A_n \neq 0$,
which holds for every $n \leq 3000$. -/
def IsIntegerValue (n : ℕ) : Prop := A n ∣ B n

instance (n : ℕ) : Decidable (IsIntegerValue n) := by unfold IsIntegerValue; infer_instance

/-- $x_n$ is the tangent of the partial sum of arctangents it is named for. -/
theorem x_eq_tan_sum_arctan (n : ℕ) (hn : 1 ≤ n) :
    (x n : ℝ) = Real.tan (∑ k ∈ Finset.Icc 1 n, Real.arctan k) := by
  have key : ∀ m : ℕ, ∃ r : ℝ, 0 < r ∧
      ((A m : ℤ) : ℝ) = r * Real.cos (∑ k ∈ Finset.Icc 1 m, Real.arctan k) ∧
      ((B m : ℤ) : ℝ) = r * Real.sin (∑ k ∈ Finset.Icc 1 m, Real.arctan k) := by
    intro m
    induction m with
    | zero =>
      have h0 : Finset.Icc 1 0 = (∅ : Finset ℕ) := by simp
      refine ⟨1, one_pos, ?_, ?_⟩
      · simp [A, gaussProd, h0]
      · simp [B, gaussProd, h0]
    | succ m ih =>
      obtain ⟨r, hr, hA, hB⟩ := ih
      have hG : gaussProd (m + 1) = gaussProd m * ⟨1, ((m + 1 : ℕ) : ℤ)⟩ := by
        unfold gaussProd
        rw [Finset.prod_Icc_succ_top (show 1 ≤ m + 1 by omega)]
      have hAm : A (m + 1) = A m - B m * ((m + 1 : ℕ) : ℤ) := by
        unfold A B
        rw [hG]
        simp <;> ring
      have hBm : B (m + 1) = A m * ((m + 1 : ℕ) : ℤ) + B m := by
        unfold A B
        rw [hG]
        simp <;> ring
      rw [Finset.sum_Icc_succ_top (show 1 ≤ m + 1 by omega)]
      refine ⟨r * Real.sqrt (1 + ((m + 1 : ℕ) : ℝ) ^ 2),
        mul_pos hr (Real.sqrt_pos.mpr (by positivity)), ?_, ?_⟩
      · rw [hAm]
        push_cast
        rw [Real.cos_add, Real.cos_arctan, Real.sin_arctan, hA, hB]
        have hs : Real.sqrt (1 + ((m : ℝ) + 1) ^ 2) ≠ 0 := by positivity
        field_simp <;> ring
      · rw [hBm]
        push_cast
        rw [Real.sin_add, Real.cos_arctan, Real.sin_arctan, hA, hB]
        have hs : Real.sqrt (1 + ((m : ℝ) + 1) ^ 2) ≠ 0 := by positivity
        field_simp <;> ring
  obtain ⟨r, hr, hA, hB⟩ := key n
  unfold x
  rw [Real.tan_eq_sin_div_cos]
  push_cast
  rw [hA, hB]
  exact mul_div_mul_left _ _ hr.ne'

end Arxiv.«2607.05739»
