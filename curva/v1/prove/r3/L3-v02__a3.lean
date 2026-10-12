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
  classical
  obtain ⟨M, hM⟩ : ∃ M, M = k * r - 1 := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = (t - 1) * (k - 1) := ⟨_, rfl⟩
  rw [← hM, ← hq]
  have ht0 : 0 < t := by omega
  have hq' : q = (k - 1) * (t - 1) := by
    rw [hq]
    exact Nat.mul_comm _ _
  obtain ⟨f, hf_def⟩ : ∃ f : Fin (M + q) → ℕ,
      ∀ x, f x = if x.val < M then 0 else (x.val - M) / (k - 1) + 1 :=
    ⟨fun x => if x.val < M then 0 else (x.val - M) / (k - 1) + 1, fun x => rfl⟩
  have hfb : ∀ x : Fin (M + q), f x < t := by
    intro x
    have hxq := x.isLt
    rw [hf_def]
    split_ifs with hlt
    · omega
    · have hlt2 : x.val - M < (k - 1) * (t - 1) := by omega
      have hd := Nat.div_lt_of_lt_mul hlt2
      omega
  obtain ⟨c, hc⟩ : ∃ c : {e : Finset (Fin (M + q)) // e.card = r} → Fin t,
      ∀ (A : {e : Finset (Fin (M + q)) // e.card = r}) (h : A.1.Nonempty),
        (c A).val = f (A.1.max' h) :=
    ⟨fun A => if h : A.1.Nonempty then ⟨f (A.1.max' h), hfb _⟩ else ⟨0, ht0⟩,
      fun A h => by simp [h]⟩
  refine ⟨c, ?_⟩
  rintro ⟨i, e, hcol, hdisj⟩
  have hne : ∀ j, (e j).1.Nonempty :=
    fun j => Finset.card_pos.mp (by have := (e j).2; omega)
  obtain ⟨m, hm⟩ : ∃ m : Fin k → Fin (M + q), ∀ j, m j = (e j).1.max' (hne j) :=
    ⟨fun j => (e j).1.max' (hne j), fun j => rfl⟩
  have hf_j : ∀ j, f (m j) = i.val := by
    intro j
    rw [hm j, ← hc (e j) (hne j)]
    exact congrArg Fin.val (hcol j)
  by_cases hi : i.val = 0
  · have hall : ∀ j, ∀ x ∈ (e j).1, x.val < M := by
      intro j x hx
      have h1 : x ≤ m j := by
        rw [hm j]
        exact Finset.le_max' _ _ hx
      have h2 : (m j).val < M := by
        have h := hf_j j
        rw [hf_def] at h
        split_ifs at h with hlt
        · exact hlt
        · rw [hi] at h
          simp at h
      have h3 : x.val ≤ (m j).val := Fin.le_iff_val_le_val.mp h1
      omega
    have hce : ∀ j, (e j).1.card = r := fun j => (e j).2
    have hcardS : (Finset.univ.biUnion fun j => (e j).1).card = k * r := by
      rw [Finset.card_biUnion]
      · simp [hce]
      · intro x _ y _ hxy
        exact hdisj hxy
    have hsub : (Finset.univ.biUnion fun j => (e j).1).image Fin.val ⊆ Finset.range M := by
      intro n hn
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
      obtain ⟨j, _, hxj⟩ := Finset.mem_biUnion.mp hx
      exact Finset.mem_range.mpr (hall j x hxj)
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ Fin.val_injective, Finset.card_range, hcardS] at h2
    have hR1 : 0 < k * r := Nat.mul_pos (by omega) (by omega)
    omega
  · have hk2 : 2 ≤ k := by
      by_contra hk1
      have hk1' : k = 1 := by omega
      have hq0 : q = 0 := by
        rw [hq, hk1']
        simp
      have j0 : Fin k := ⟨0, by omega⟩
      have hb := (m j0).isLt
      have hlt3 : (m j0).val < M := by omega
      have h := hf_j j0
      rw [hf_def, if_pos hlt3] at h
      omega
    obtain ⟨a, ha⟩ : ∃ a, a = M + (k - 1) * (i.val - 1) := ⟨_, rfl⟩
    have hbig : ∀ j, M ≤ (m j).val := by
      intro j
      by_contra hcon
      have h := hf_j j
      rw [hf_def, if_pos (show (m j).val < M by omega)] at h
      omega
    have hbounds : ∀ j, a ≤ (m j).val ∧ (m j).val < a + (k - 1) := by
      intro j
      have hb := hbig j
      have h := hf_j j
      rw [hf_def, if_neg (show ¬ (m j).val < M by omega)] at h
      have hQ : ((m j).val - M) / (k - 1) = i.val - 1 := by omega
      have hdiv := Nat.div_add_mod ((m j).val - M) (k - 1)
      have hmod := Nat.mod_lt ((m j).val - M) (show k - 1 > 0 by omega)
      rw [hQ] at hdiv
      constructor <;> omega
    have hinj : ∀ j j' : Fin k, (m j).val = (m j').val → j = j' := by
      intro j j' hjj
      by_contra hne'
      have hmm : m j = m j' := Fin.ext hjj
      have hd := hdisj hne'
      have h1 : m j ∈ (e j).1 := by
        rw [hm j]
        exact Finset.max'_mem _ _
      have h2 : m j ∈ (e j').1 := by
        rw [hmm, hm j']
        exact Finset.max'_mem _ _
      exact Finset.disjoint_left.mp hd h1 h2
    have hcard : (Finset.univ : Finset (Fin k)).card ≤ (Finset.Ico a (a + (k - 1))).card :=
      Finset.card_le_card_of_injOn (fun j : Fin k => (m j).val)
        (fun j _ => Finset.mem_coe.mpr (Finset.mem_Ico.mpr (hbounds j)))
        (fun j _ j' _ hjj => hinj j j' hjj)
    rw [Finset.card_univ, Fintype.card_fin, Nat.card_Ico] at hcard
    omega

end Erdos780
