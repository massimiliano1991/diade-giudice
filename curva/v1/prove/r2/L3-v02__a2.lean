import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Erdős Problem 780

*References:*
- [erdosproblems.com/780](https://www.erdosproblems.com/780)
- [Er76] Erdős, Paul, _Problems and results in combinatorial analysis_. Colloquio Internazionale
  sulle Teorie Combinatorie (Roma, 1973), Tomo II (1976), 3-17.
- [Lo78] Lovász, L., _Kneser's conjecture, chromatic number, and homotopy_. J. Combin. Theory
  Ser. A (1978), 319-324.
- [AFL86] Alon, N. and Frankl, P. and Lovász, L., _The chromatic number of Kneser hypergraphs_.
  Trans. Amer. Math. Soc. (1986), 359-370.
-/

namespace Erdos780

/--
This would be best possible: if $n=kr-1+(t-1)(k-1)$ then decomposing $[n]$ as one set $X_1$ of
size $kr-1$ and $t-1$ sets $X_2,\ldots,X_{t}$ of size $k-1$, a colouring without $k$ pairwise
disjoint edges is given colouring all subsets of $X_1$ in colour $1$ and assigning an edge with
colour $2\leq i\leq t$ if $i$ is minimal such that $X_i$ intersects the edge.
-/
theorem erdos_780.variants.sharp (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1 := by
  generalize hn : k * r - 1 + (t - 1) * (k - 1) = n
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℕ, ∀ v, f v =
      if v < k * r - 1 then 0 else 1 + (v - (k * r - 1)) / (k - 1) :=
    ⟨fun v => if v < k * r - 1 then 0 else 1 + (v - (k * r - 1)) / (k - 1), fun v => rfl⟩
  have hf0 : ∀ v, v < k * r - 1 → f v = 0 := by
    intro v hv
    rw [hf v, if_pos hv]
  have hf1 : ∀ v, k * r - 1 ≤ v → f v = 1 + (v - (k * r - 1)) / (k - 1) := by
    intro v hv
    rw [hf v, if_neg (not_lt.mpr hv)]
  have hfN : ∀ v, v < n → f v < t := by
    intro v hv
    by_cases hvM : v < k * r - 1
    · rw [hf0 v hvM]
      omega
    · rw [hf1 v (not_lt.mp hvM)]
      have hK : 0 < k - 1 := by
        rcases Nat.eq_zero_or_pos (k - 1) with h0 | h0
        · rw [h0, Nat.mul_zero] at hn
          omega
        · exact h0
      have h2 : (v - (k * r - 1)) / (k - 1) < t - 1 := by
        apply Nat.div_lt_of_lt_mul
        have hm : (t - 1) * (k - 1) = (k - 1) * (t - 1) := Nat.mul_comm _ _
        omega
      generalize (v - (k * r - 1)) / (k - 1) = q at h2 ⊢
      omega
  obtain ⟨c, hc⟩ : ∃ c : {e : Finset (Fin n) // e.card = r} → Fin t,
      ∀ e, (c e).val = f (e.1.sup Fin.val) % t :=
    ⟨fun e => ⟨f (e.1.sup Fin.val) % t, Nat.mod_lt _ (by omega)⟩, fun e => rfl⟩
  refine ⟨c, ?_⟩
  rintro ⟨i, e, hcol, hdisj⟩
  have hcardj : ∀ j, (e j).1.card = r := fun j => (e j).2
  have hsup : ∀ j, ∃ p ∈ (e j).1, (e j).1.sup Fin.val = p.val := by
    intro j
    have hne : (e j).1.Nonempty := by
      apply Finset.card_pos.mp
      rw [hcardj j]
      omega
    obtain ⟨p, hp, hpeq⟩ := Finset.exists_mem_eq_sup (e j).1 hne Fin.val
    exact ⟨p, hp, hpeq⟩
  have hlt : ∀ j, (e j).1.sup Fin.val < n := by
    intro j
    obtain ⟨p, _, hpeq⟩ := hsup j
    rw [hpeq]
    exact p.isLt
  have hA : ∀ j, (e j).1.sup Fin.val < k * r - 1 → ∀ b ∈ (e j).1, (b : ℕ) < k * r - 1 := by
    intro j hj b hb
    have hle : (b : ℕ) ≤ (e j).1.sup Fin.val := Finset.le_sup (f := Fin.val) hb
    omega
  have hval : ∀ j, f ((e j).1.sup Fin.val) = i.val := by
    intro j
    have h1 := hc (e j)
    rw [hcol j] at h1
    have h2 := hfN _ (hlt j)
    rw [Nat.mod_eq_of_lt h2] at h1
    omega
  have hcount : (∀ j, ∀ b ∈ (e j).1, (b : ℕ) < k * r - 1) → False := by
    intro hbound
    have hpd : ∀ x y : Fin k, x ≠ y →
        Disjoint ((e x).1.image Fin.val) ((e y).1.image Fin.val) := by
      intro x y hxy
      have hdxy : Disjoint (e x).1 (e y).1 := hdisj hxy
      refine Finset.disjoint_left.mpr ?_
      intro a ha hb
      simp only [Finset.mem_image] at ha hb
      obtain ⟨p, hp, rfl⟩ := ha
      obtain ⟨q, hq, hqp⟩ := hb
      have hqp' : q = p := Fin.ext hqp
      subst hqp'
      exact Finset.disjoint_left.mp hdxy hp hq
    have hcard : (Finset.univ.biUnion (fun j : Fin k => (e j).1.image Fin.val)).card
        = k * r := by
      rw [Finset.card_biUnion]
      · simp [Finset.card_image_of_injective _ Fin.val_injective, hcardj]
      · intro x _ y _ hxy
        exact hpd x y hxy
    have hsub : Finset.univ.biUnion (fun j : Fin k => (e j).1.image Fin.val)
        ⊆ Finset.range (k * r - 1) := by
      intro x hx
      rw [Finset.mem_biUnion] at hx
      obtain ⟨j, _, hj⟩ := hx
      rw [Finset.mem_image] at hj
      obtain ⟨p, hp, rfl⟩ := hj
      exact Finset.mem_range.mpr (hbound j p hp)
    have hle := Finset.card_le_card hsub
    rw [Finset.card_range] at hle
    have hkr : 0 < k * r := Nat.mul_pos (by omega) (by omega)
    omega
  by_cases hsmall : ∀ j, (e j).1.sup Fin.val < k * r - 1
  · exact hcount (fun j b hb => hA j (hsmall j) b hb)
  · obtain ⟨j0, hj0⟩ : ∃ j0 : Fin k, k * r - 1 ≤ (e j0).1.sup Fin.val := by
      by_contra hcon
      exact hsmall (fun j => not_le.mp (fun h => hcon ⟨j, h⟩))
    have hK : 0 < k - 1 := by
      rcases Nat.eq_zero_or_pos (k - 1) with h0 | h0
      · rw [h0, Nat.mul_zero] at hn
        have := hlt j0
        omega
      · exact h0
    have hq : ∀ j, k * r - 1 ≤ (e j).1.sup Fin.val := by
      intro j
      by_contra hcon
      have hlt' : (e j).1.sup Fin.val < k * r - 1 := not_le.mp hcon
      have e1 := hf0 _ hlt'
      have e5 : 1 ≤ f ((e j0).1.sup Fin.val) := by
        rw [hf1 _ hj0]
        exact Nat.le_add_right _ _
      have e3 := hval j
      have e4 := hval j0
      omega
    have hinj : Function.Injective (fun j : Fin k =>
        (⟨((e j).1.sup Fin.val - (k * r - 1)) % (k - 1), Nat.mod_lt _ hK⟩ : Fin (k - 1))) := by
      intro a b hab
      have hab' : ((e a).1.sup Fin.val - (k * r - 1)) % (k - 1)
          = ((e b).1.sup Fin.val - (k * r - 1)) % (k - 1) := congrArg Fin.val hab
      have hfa := hf1 _ (hq a)
      have hfb := hf1 _ (hq b)
      have hva := hval a
      have hvb := hval b
      have hXeq : ((e a).1.sup Fin.val - (k * r - 1)) / (k - 1)
          = ((e b).1.sup Fin.val - (k * r - 1)) / (k - 1) := by
        omega
      have hsup_eq : (e a).1.sup Fin.val = (e b).1.sup Fin.val := by
        have h1 := Nat.div_add_mod ((e a).1.sup Fin.val - (k * r - 1)) (k - 1)
        have h2 := Nat.div_add_mod ((e b).1.sup Fin.val - (k * r - 1)) (k - 1)
        rw [hXeq, hab'] at h1
        have hsa := hq a
        have hsb := hq b
        omega
      by_contra hne
      have hdab : Disjoint (e a).1 (e b).1 := hdisj hne
      obtain ⟨pa, hpa, hpa'⟩ := hsup a
      obtain ⟨pb, hpb, hpb'⟩ := hsup b
      have hpp : pa = pb := Fin.ext (hpa'.symm.trans (hsup_eq.trans hpb'))
      exact Finset.disjoint_left.mp hdab hpa (by rw [hpp]; exact hpb)
    have hcardle := Fintype.card_le_of_injective _ hinj
    simp only [Fintype.card_fin] at hcardle
    omega

end Erdos780
