import Mathlib
set_option autoImplicit false

open Set Nat Polynomial Filter Topology

/--
Let $y(x)$ be a continuously differentiable real-valued function of a real vairable $x$. Show that if $(y')^2 + y^3 \to 0$ as $x \to +\infty$, then $y(x)$ and $y'(x) \to 0$ as $x \to +\infty$.
-/
theorem putnam_1974_b2
(y : ℝ → ℝ)
(ycontdiff : ContDiff ℝ 1 y)
(limy : Tendsto (fun x : ℝ => (deriv y x)^2 + (y x)^3) atTop (𝓝 0))
: Tendsto y atTop (𝓝 0) ∧ Tendsto (deriv y) atTop (𝓝 0) := by
  have hdiff : Differentiable ℝ y := ycontdiff.differentiable (by norm_num)
  have hcont' : Continuous (deriv y) := ycontdiff.continuous_deriv le_rfl
  have hycont : Continuous y := hdiff.continuous
  have hg : ∀ ε > 0, ∃ X : ℝ, ∀ x ≥ X, |(deriv y x)^2 + (y x)^3| < ε := by
    intro ε hε
    obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp ((Metric.tendsto_nhds.mp limy) ε hε)
    refine ⟨X, fun x hx => ?_⟩
    have h := hX x hx
    simp only [Real.dist_eq, sub_zero] at h
    exact h
  have hup : ∀ δ > 0, ∃ X : ℝ, ∀ x ≥ X, y x < δ := by
    intro δ hδ
    obtain ⟨X, hX⟩ := hg (δ^3) (pow_pos hδ 3)
    refine ⟨X, fun x hx => ?_⟩
    by_contra h
    push_neg at h
    have h1 := abs_lt.mp (hX x hx)
    have h2 : δ^3 ≤ (y x)^3 := pow_le_pow_left₀ hδ.le h 3
    have h3 := sq_nonneg (deriv y x)
    linarith [h1.2]
  have hlow : ∀ β : ℝ, 0 < β → ∃ X : ℝ, ∀ x ≥ X, -β ≤ y x := by
    intro β hβ
    obtain ⟨X, hX⟩ := hg (β^3/2) (by have := pow_pos hβ 3; linarith)
    have hM0 : 0 ≤ (min 1 β)⁻¹ := inv_nonneg.2 (lt_min one_pos hβ).le
    have F1 : ∀ x, X ≤ x → y x < -β → (-(y x))^3 ≤ 2 * (deriv y x)^2 := by
      intro x hx hyx
      have h1 := abs_lt.mp (hX x hx)
      have hb : β ≤ -(y x) := by linarith
      have hb3 : β^3 ≤ (-(y x))^3 := pow_le_pow_left₀ hβ.le hb 3
      have e : (-(y x))^3 = -((y x)^3) := by ring
      linarith [h1.1, h1.2]
    have hnz : ∀ t, X ≤ t → y t < -β → deriv y t ≠ 0 := by
      intro t ht hyt h0
      have h2 : (deriv y t)^2 = 0 := by rw [h0]; ring
      have hF := F1 t ht hyt
      have hp := pow_pos (show (0:ℝ) < -(y t) by linarith) 3
      linarith
    have hsame : ∀ u w : ℝ, X ≤ u → u ≤ w → (∀ t ∈ Icc u w, y t < -β) →
        (0 < deriv y u ↔ 0 < deriv y w) := by
      intro u w hu huw hreg
      have hcz : ∀ z ∈ Icc u w, deriv y z ≠ 0 :=
        fun z hz => hnz z (le_trans hu hz.1) (hreg z hz)
      have hzero : ∀ a b : ℝ, a ∈ Icc u w → b ∈ Icc u w →
          deriv y a < 0 → 0 < deriv y b → False := by
        intro a b ha hb hna hpb
        have h0 : (0:ℝ) ∈ uIcc (deriv y a) (deriv y b) := by
          rw [Set.mem_uIcc]
          exact Or.inl ⟨hna.le, hpb.le⟩
        have hcu : ContinuousOn (deriv y) (uIcc a b) := hcont'.continuousOn
        obtain ⟨z, hz, hz0⟩ := intermediate_value_uIcc hcu h0
        exact hcz z (Set.uIcc_subset_Icc ha hb hz) hz0
      constructor
      · intro hu0
        by_contra hw
        push_neg at hw
        have hw' : deriv y w < 0 := lt_of_le_of_ne hw (hcz w ⟨huw, le_refl w⟩)
        exact hzero w u ⟨huw, le_refl w⟩ ⟨le_refl u, huw⟩ hw' hu0
      · intro hw0
        by_contra hu'
        push_neg at hu'
        have hu'' : deriv y u < 0 := lt_of_le_of_ne hu' (hcz u ⟨le_refl u, huw⟩)
        exact hzero u w ⟨le_refl u, huw⟩ ⟨huw, le_refl w⟩ hu'' hw0
    have hlen : ∀ p q : ℝ, X ≤ p → p < q → (∀ t ∈ Icc p q, y t < -β) →
        q - p ≤ 3 * (min 1 β)⁻¹ := by
      intro p q hp hpq hreg
      have hm : 0 < min 1 β := lt_min one_pos hβ
      have hmr : ∀ r : ℝ, 0 < r → β ≤ r^2 → min 1 β ≤ r := by
        intro r hr hr2
        rcases le_total 1 r with h | h
        · exact le_trans (min_le_left _ _) h
        · have hβr : β ≤ r := by nlinarith [mul_nonneg hr.le (sub_nonneg.2 h)]
          exact le_trans (min_le_right _ _) hβr
      have hWbd : ∀ t ∈ Icc p q,
          0 ≤ (Real.sqrt (-(y t)))⁻¹ ∧ (Real.sqrt (-(y t)))⁻¹ ≤ (min 1 β)⁻¹ := by
        intro t ht
        have hyt := hreg t ht
        have hpos : 0 < -(y t) := by linarith
        have hr : 0 < Real.sqrt (-(y t)) := Real.sqrt_pos.2 hpos
        have hr2 : (Real.sqrt (-(y t)))^2 = -(y t) := Real.sq_sqrt hpos.le
        refine ⟨inv_nonneg.2 hr.le, ?_⟩
        exact inv_anti₀ hm (hmr _ hr (by rw [hr2]; linarith))
      have hWd : ∀ t, y t < -β → HasDerivAt (fun s => (Real.sqrt (-(y s)))⁻¹)
          (-(-(deriv y t) / (2 * Real.sqrt (-(y t)))) / (Real.sqrt (-(y t)))^2) t := by
        intro t ht
        have hpos : 0 < -(y t) := by linarith
        exact (((hdiff t).hasDerivAt.neg).sqrt hpos.ne').inv (Real.sqrt_pos.2 hpos).ne'
      have hcont : ContinuousOn (fun s => (Real.sqrt (-(y s)))⁻¹) (Icc p q) := by
        intro t ht
        exact (hWd t (hreg t ht)).continuousAt.continuousWithinAt
      obtain ⟨c, hc, hEc⟩ := exists_hasDerivAt_eq_slope
        (fun s => (Real.sqrt (-(y s)))⁻¹)
        (fun t => -(-(deriv y t) / (2 * Real.sqrt (-(y t)))) / (Real.sqrt (-(y t)))^2)
        hpq hcont (fun t ht => hWd t (hreg t ⟨ht.1.le, ht.2.le⟩))
      have hEc' : -(-(deriv y c) / (2 * Real.sqrt (-(y c)))) / (Real.sqrt (-(y c)))^2
          = ((Real.sqrt (-(y q)))⁻¹ - (Real.sqrt (-(y p)))⁻¹) / (q - p) := hEc
      have hcpos : c ∈ Icc p q := ⟨hc.1.le, hc.2.le⟩
      have hyc : y c < -β := hreg c hcpos
      have hFc := F1 c (le_trans hp hc.1.le) hyc
      have hpos : 0 < -(y c) := by linarith
      have hr : 0 < Real.sqrt (-(y c)) := Real.sqrt_pos.2 hpos
      have hr0 : Real.sqrt (-(y c)) ≠ 0 := hr.ne'
      have hr2 : (Real.sqrt (-(y c)))^2 = -(y c) := Real.sq_sqrt hpos.le
      have hEq : -(-(deriv y c) / (2 * Real.sqrt (-(y c)))) / (Real.sqrt (-(y c)))^2
          = deriv y c / (2 * (Real.sqrt (-(y c)))^3) := by
        field_simp <;> ring
      have hsq : (1:ℝ)/9 ≤ (deriv y c / (2 * (Real.sqrt (-(y c)))^3))^2 := by
        rw [div_pow, le_div_iff₀ (pow_pos (mul_pos two_pos (pow_pos hr 3)) 2)]
        rw [show (2 * (Real.sqrt (-(y c)))^3)^2 = 4 * ((Real.sqrt (-(y c)))^2)^3 by ring, hr2]
        linarith [sq_nonneg (deriv y c)]
      have hsqE : (1:ℝ)/9 ≤ (-(-(deriv y c) / (2 * Real.sqrt (-(y c)))) / (Real.sqrt (-(y c)))^2)^2 := by
        rw [hEq]; exact hsq
      have hqp : 0 < q - p := by linarith
      have hqp0 : q - p ≠ 0 := hqp.ne'
      have hmul : (q - p) * (-(-(deriv y c) / (2 * Real.sqrt (-(y c)))) / (Real.sqrt (-(y c)))^2)
          = (Real.sqrt (-(y q)))⁻¹ - (Real.sqrt (-(y p)))⁻¹ := by
        rw [hEc']
        field_simp
      have hkey : (q - p)^2 / 9 ≤ ((Real.sqrt (-(y q)))⁻¹ - (Real.sqrt (-(y p)))⁻¹)^2 := by
        rw [← hmul]
        nlinarith [mul_nonneg (sq_nonneg (q - p)) (sub_nonneg.2 hsqE)]
      obtain ⟨hq0, hq1⟩ := hWbd q ⟨hpq.le, le_refl q⟩
      obtain ⟨hp0, hp1⟩ := hWbd p ⟨le_refl p, hpq.le⟩
      have hdiffsq : ((Real.sqrt (-(y q)))⁻¹ - (Real.sqrt (-(y p)))⁻¹)^2 ≤ ((min 1 β)⁻¹)^2 := by
        nlinarith [mul_nonneg
          (by linarith : (0:ℝ) ≤ (min 1 β)⁻¹ - ((Real.sqrt (-(y q)))⁻¹ - (Real.sqrt (-(y p)))⁻¹))
          (by linarith : (0:ℝ) ≤ (min 1 β)⁻¹ + ((Real.sqrt (-(y q)))⁻¹ - (Real.sqrt (-(y p)))⁻¹))]
      nlinarith [hkey, hdiffsq, hM0]
    refine ⟨X + 3 * (min 1 β)⁻¹ + 1, fun x1 hx1 => ?_⟩
    by_contra hneg
    push_neg at hneg
    have hXx1 : X ≤ x1 := by linarith
    have hF1x : deriv y x1 ≠ 0 := hnz x1 hXx1 hneg
    rcases lt_or_gt_of_ne hF1x with hd | hd
    · -- forward case
      have hd' : deriv y x1 < 0 := hd
      obtain ⟨D, hD⟩ : ∃ D : Set ℝ,
          D = {t | t ∈ Icc x1 (x1 + 3 * (min 1 β)⁻¹ + 1) ∧ -β ≤ y t} := ⟨_, rfl⟩
      have memD : ∀ t, t ∈ D ↔ (x1 ≤ t ∧ t ≤ x1 + 3 * (min 1 β)⁻¹ + 1) ∧ -β ≤ y t := by
        intro t
        rw [hD]
        exact Iff.rfl
      have hDne : D.Nonempty := by
        by_contra hemp
        rw [Set.not_nonempty_iff_eq_empty] at hemp
        have hreg : ∀ t ∈ Icc x1 (x1 + 3 * (min 1 β)⁻¹ + 1), y t < -β := by
          intro t ht
          by_contra hh
          push_neg at hh
          have htD : t ∈ D := (memD t).2 ⟨ht, hh⟩
          simp [hemp] at htD
        have := hlen x1 (x1 + 3 * (min 1 β)⁻¹ + 1) hXx1 (by linarith) hreg
        linarith
      have hclosed1 : IsClosed (Icc x1 (x1 + 3 * (min 1 β)⁻¹ + 1)) := isClosed_Icc
      have hclosed2 : IsClosed {t : ℝ | -β ≤ y t} := isClosed_le continuous_const hycont
      have hDclosed : IsClosed D := by
        rw [hD]
        exact hclosed1.inter hclosed2
      have hDbdd : BddBelow D := ⟨x1, fun t ht => ((memD t).1 ht).1.1⟩
      obtain ⟨b, hb⟩ : ∃ b : ℝ, b = sInf D := ⟨_, rfl⟩
      have hbD : b ∈ D := by
        rw [hb]
        exact hDclosed.csInf_mem hDne hDbdd
      have hbmin : ∀ t ∈ D, b ≤ t := fun t ht => by
        rw [hb]
        exact csInf_le hDbdd ht
      obtain ⟨⟨hxb, hbx2⟩, hyb⟩ := (memD b).1 hbD
      have hx1b : x1 < b := by
        rcases lt_or_eq_of_le hxb with h | h
        · exact h
        · exfalso
          rw [← h] at hyb
          linarith
      have hregB : ∀ t, x1 ≤ t → t < b → y t < -β := by
        intro t ht1 htb
        by_contra hh
        push_neg at hh
        have htD : t ∈ D := (memD t).2 ⟨⟨ht1, by linarith⟩, hh⟩
        have := hbmin t htD
        linarith
      obtain ⟨ξ, hξ, hξeq⟩ := exists_deriv_eq_slope y hx1b hycont.continuousOn
        hdiff.differentiableOn
      have hξneg : deriv y ξ < 0 := by
        have hiff := hsame x1 ξ hXx1 hξ.1.le
          (fun t ht => hregB t ht.1 (lt_of_le_of_lt ht.2 hξ.2))
        have hnot : ¬ (0 < deriv y ξ) := by
          intro h
          have := hiff.2 h
          linarith
        exact lt_of_le_of_ne (not_lt.1 hnot)
          (hnz ξ (le_trans hXx1 hξ.1.le) (hregB ξ hξ.1.le hξ.2))
      have hne : b - x1 ≠ 0 := (sub_pos.2 hx1b).ne'
      have hsl : y b - y x1 = deriv y ξ * (b - x1) := by
        rw [hξeq]
        field_simp
      have hneg2 : deriv y ξ * (b - x1) < 0 := mul_neg_of_neg_of_pos hξneg (sub_pos.2 hx1b)
      linarith
    · -- backward case
      have hd' : 0 < deriv y x1 := hd
      obtain ⟨c0, hc0⟩ : ∃ c0 : ℝ, c0 = x1 - 3 * (min 1 β)⁻¹ - 1 := ⟨_, rfl⟩
      have hc0X : X ≤ c0 := by linarith
      have hc0x : c0 < x1 := by linarith
      obtain ⟨D, hD⟩ : ∃ D : Set ℝ, D = {t | t ∈ Icc c0 x1 ∧ -β ≤ y t} := ⟨_, rfl⟩
      have memD : ∀ t, t ∈ D ↔ (c0 ≤ t ∧ t ≤ x1) ∧ -β ≤ y t := by
        intro t
        rw [hD]
        exact Iff.rfl
      have hDne : D.Nonempty := by
        by_contra hemp
        rw [Set.not_nonempty_iff_eq_empty] at hemp
        have hreg : ∀ t ∈ Icc c0 x1, y t < -β := by
          intro t ht
          by_contra hh
          push_neg at hh
          have htD : t ∈ D := (memD t).2 ⟨ht, hh⟩
          simp [hemp] at htD
        have := hlen c0 x1 hc0X hc0x hreg
        linarith
      have hclosed1 : IsClosed (Icc c0 x1) := isClosed_Icc
      have hclosed2 : IsClosed {t : ℝ | -β ≤ y t} := isClosed_le continuous_const hycont
      have hDclosed : IsClosed D := by
        rw [hD]
        exact hclosed1.inter hclosed2
      have hDbdd : BddAbove D := ⟨x1, fun t ht => ((memD t).1 ht).1.2⟩
      obtain ⟨a, ha⟩ : ∃ a : ℝ, a = sSup D := ⟨_, rfl⟩
      have haD : a ∈ D := by
        rw [ha]
        exact hDclosed.csSup_mem hDne hDbdd
      have hleA : ∀ t ∈ D, t ≤ a := fun t ht => by
        rw [ha]
        exact le_csSup hDbdd ht
      obtain ⟨⟨hca, hax⟩, hya⟩ := (memD a).1 haD
      have hax1 : a < x1 := by
        rcases lt_or_eq_of_le hax with h | h
        · exact h
        · exfalso
          rw [h] at hya
          linarith
      have hregA : ∀ t, a < t → t ≤ x1 → y t < -β := by
        intro t hat htx
        by_contra hh
        push_neg at hh
        have htD : t ∈ D := (memD t).2 ⟨⟨by linarith, htx⟩, hh⟩
        have := hleA t htD
        linarith
      have hpos : ∀ ξ, a < ξ → ξ ≤ x1 → 0 < deriv y ξ := by
        intro ξ hξa hξx
        have hiff := hsame ξ x1 (by linarith) hξx
          (fun t ht => hregA t (lt_of_lt_of_le hξa ht.1) ht.2)
        exact hiff.2 hd'
      obtain ⟨ξ, hξ, hξeq⟩ := exists_deriv_eq_slope y hax1 hycont.continuousOn
        hdiff.differentiableOn
      have hξpos : 0 < deriv y ξ := hpos ξ hξ.1 hξ.2.le
      have hne : x1 - a ≠ 0 := (sub_pos.2 hax1).ne'
      have hsl : y x1 - y a = deriv y ξ * (x1 - a) := by
        rw [hξeq]
        field_simp
      have hpos2 : 0 < deriv y ξ * (x1 - a) := mul_pos hξpos (sub_pos.2 hax1)
      linarith
  have hy0 : Tendsto y atTop (𝓝 0) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      obtain ⟨X', hX'⟩ := hlow (-a/2) (by linarith)
      exact Filter.eventually_atTop.2 ⟨X', fun x hx => by
        have := hX' x hx
        linarith⟩
    · intro b hb
      obtain ⟨X', hX'⟩ := hup b hb
      exact Filter.eventually_atTop.2 ⟨X', fun x hx => hX' x hx⟩
  have hsq : Tendsto (fun x => (deriv y x)^2) atTop (𝓝 0) := by
    have h3 : Tendsto (fun x => (y x)^3) atTop (𝓝 0) := by
      have h := hy0.pow 3
      simpa using h
    have h4 := limy.sub h3
    simpa using h4
  have hd : Tendsto (deriv y) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x => Real.sqrt ((deriv y x)^2)) atTop (𝓝 (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).comp hsq
    rw [Real.sqrt_zero] at h1
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa [Real.sqrt_sq_eq_abs, Real.norm_eq_abs] using h1
  exact ⟨hy0, hd⟩
