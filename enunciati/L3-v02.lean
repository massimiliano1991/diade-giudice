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
  sorry
