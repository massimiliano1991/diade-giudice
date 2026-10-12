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
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = k * r - 1 := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = k - 1 := ⟨_, rfl⟩
  rw [← hL, ← hd]
  have hk0 : 0 < k := by omega
  have hkr : 0 < k * r := Nat.mul_pos hk0 (by omega)
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℕ, ∀ x, b x = if x < L then 0 else (x - L) / d + 1 :=
    ⟨fun x => if x < L then 0 else (x - L) / d + 1, fun x => rfl⟩
  refine ⟨fun e => ⟨min (b (e.1.sup fun y : Fin (L + (t - 1) * d) => (y : ℕ))) (t - 1),
    lt_of_le_of_lt (min_le_right _ _) (by omega)⟩, ?_⟩
  rintro ⟨i, e, hc, hdisj⟩
  obtain ⟨S, hS⟩ : ∃ S : Fin k → ℕ,
      ∀ j, S j = (e j).1.sup fun y : Fin (L + (t - 1) * d) => (y : ℕ) :=
    ⟨fun j => (e j).1.sup fun y : Fin (L + (t - 1) * d) => (y : ℕ), fun j => rfl⟩
  have hmax : ∀ j, ∃ m ∈ (e j).1, (m : ℕ) = S j := by
    intro j
    have hne : (e j).1.Nonempty := by
      apply Finset.card_pos.mp
      rw [(e j).2]
      omega
    obtain ⟨m, hm, hmeq⟩ := Finset.exists_mem_eq_sup (e j).1 hne
      (fun y : Fin (L + (t - 1) * d) => (y : ℕ))
    exact ⟨m, hm, by rw [hS j]; exact hmeq.symm⟩
  have hSlt : ∀ j, S j < L + (t - 1) * d := by
    intro j
    obtain ⟨m0, _, hmv0⟩ := hmax j
    rw [← hmv0]
    exact m0.isLt
  have hval : ∀ j, min (b (S j)) (t - 1) = (i : ℕ) := by
    intro j
    rw [hS j]
    exact congrArg Fin.val (hc j)
  have hbd : ∀ j, b (S j) ≤ t - 1 := by
    intro j
    have hSN := hSlt j
    rw [hb]
    split_ifs with h
    · omega
    · rcases Nat.eq_zero_or_pos d with h0 | h0
      · rw [h0, Nat.mul_zero, Nat.add_zero] at hSN
        omega
      · have hq : (S j - L) / d < t - 1 := by
          apply Nat.div_lt_of_lt_mul
          have hc' := Nat.mul_comm d (t - 1)
          omega
        omega
  have hbv : ∀ j, b (S j) = (i : ℕ) := by
    intro j
    have h1 := hval j
    rw [min_eq_left (hbd j)] at h1
    exact h1
  by_cases hi0 : (i : ℕ) = 0
  · -- colour 0: every edge lies in the first k*r-1 points, impossible by counting
    have hlow : ∀ j, S j < L := by
      intro j
      by_contra h1
      have h := hbv j
      rw [hb, if_neg h1] at h
      have h2 : (S j - L) / d + 1 = 0 := h.trans hi0
      exact Nat.succ_ne_zero _ h2
    have hsub : Finset.univ.biUnion (fun j => (e j).1) ⊆
        Finset.univ.filter (fun y : Fin (L + (t - 1) * d) => (y : ℕ) < L) := by
      intro y hy
      rw [Finset.mem_biUnion] at hy
      obtain ⟨j, _, hyj⟩ := hy
      have hle : (y : ℕ) ≤ S j := by
        rw [hS j]
        exact Finset.le_sup (f := fun y : Fin (L + (t - 1) * d) => (y : ℕ)) hyj
      have hlt : S j < L := hlow j
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      show (y : ℕ) < L
      omega
    have hc0 : ∀ j, (e j).1.card = r := fun j => (e j).2
    have hpd : ∀ x ∈ (Finset.univ : Finset (Fin k)), ∀ y ∈ (Finset.univ : Finset (Fin k)),
        x ≠ y → Disjoint (e x).1 (e y).1 := by
      intro x _ y _ hxy
      exact hdisj hxy
    have hcardU : (Finset.univ.biUnion (fun j => (e j).1)).card = k * r := by
      first
      | (rw [Finset.card_biUnion hpd]; simp [hc0])
      | (rw [Finset.card_biUnion (fun x _ y _ hxy => hdisj hxy)]; simp [hc0])
    have hT : (Finset.univ.filter (fun y : Fin (L + (t - 1) * d) => (y : ℕ) < L)).card ≤ L := by
      have hmap : (Finset.univ.filter
          (fun y : Fin (L + (t - 1) * d) => (y : ℕ) < L)).map Fin.valEmbedding
            ⊆ Finset.range L := by
        intro a ha
        rw [Finset.mem_map] at ha
        obtain ⟨y, hy, rfl⟩ := ha
        rw [Finset.mem_filter] at hy
        rw [Finset.mem_range]
        exact hy.2
      have := Finset.card_le_card hmap
      rw [Finset.card_map, Finset.card_range] at this
      exact this
    have h1 := Finset.card_le_card hsub
    omega
  · -- colour i ≥ 1: the maxima are k distinct naturals in an interval of length k-1
    choose m hm hmv using hmax
    obtain ⟨q, hq'⟩ : ∃ q : ℕ, q = (i : ℕ) - 1 := ⟨_, rfl⟩
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · exfalso
        have hj := hbv ⟨0, hk0⟩
        rw [hb] at hj
        by_cases hs' : S ⟨0, hk0⟩ < L
        · rw [if_pos hs'] at hj
          omega
        · have hL0 : L + (t - 1) * d = L := by simp [h0]
          have hs := hSlt ⟨0, hk0⟩
          omega
      · exact h0
    have hbox : ∀ j, L + d * q ≤ S j ∧ S j < L + d * q + d := by
      intro j
      have hb1 := hbv j
      rw [hb] at hb1
      by_cases hs : S j < L
      · rw [if_pos hs] at hb1
        exact absurd hb1.symm hi0
      · rw [if_neg hs] at hb1
        have hqj : (S j - L) / d = q := by omega
        have e1 := Nat.div_add_mod (S j - L) d
        have e2 := Nat.mod_lt (S j - L) hd0
        rw [hqj] at e1
        constructor <;> omega
    have hinj : ∀ p s : Fin k, p ≠ s → (m p : ℕ) ≠ (m s : ℕ) := by
      intro p s hne hab
      have hmem : m p ∈ (e s).1 := by
        rw [Fin.ext hab]
        exact hm s
      have hdp : Disjoint (e p).1 (e s).1 := hdisj hne
      exact Finset.disjoint_left.mp hdp (hm p) hmem
    have hSinj : Function.Injective S := by
      intro a c hac
      by_contra hne
      apply hinj a c hne
      rw [hmv a, hmv c, hac]
    have hI : Finset.univ.image S ⊆ Finset.Ico (L + d * q) (L + d * q + d) := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨j, _, rfl⟩ := hx
      exact Finset.mem_Ico.mpr (hbox j)
    have hcardI : (Finset.univ.image S).card = k := by
      rw [Finset.card_image_of_injective _ hSinj]
      simp
    have h1 := Finset.card_le_card hI
    rw [Nat.card_Ico, hcardI] at h1
    omega

end Erdos780
