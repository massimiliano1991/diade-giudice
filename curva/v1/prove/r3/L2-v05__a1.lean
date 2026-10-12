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
  have hcont' : Continuous (deriv y) := ycontdiff.continuous_deriv (by norm_num)
  have hy_cont : Continuous y := ycontdiff.continuous
  have hyd : ∀ t, HasDerivAt y (deriv y t) t := fun t => (hdiff t).hasDerivAt
  have cube_mono : ∀ p q : ℝ, 0 ≤ p → p ≤ q → p ^ 3 ≤ q ^ 3 := by
    intro p q hp hpq
    have h2 : 0 ≤ q ^ 2 + q * p + p ^ 2 := by
      nlinarith [sq_nonneg (q + p), sq_nonneg q, sq_nonneg p]
    nlinarith [mul_nonneg (sub_nonneg.2 hpq) h2]
  have hlow : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ s : ℝ, T ≤ s → -ε ≤ y s := by
    intro ε hε
    have hε3 : 0 < ε ^ 3 := pow_pos hε 3
    have hη : ∀ᶠ x in atTop, -(ε ^ 3 / 2) < (deriv y x) ^ 2 + (y x) ^ 3 ∧
        (deriv y x) ^ 2 + (y x) ^ 3 < ε ^ 3 / 2 := by
      have h1 := (tendsto_order.1 limy).1 (-(ε ^ 3 / 2)) (by linarith)
      have h2 := (tendsto_order.1 limy).2 (ε ^ 3 / 2) (by linarith)
      filter_upwards [h1, h2] with x h1x h2x
      exact ⟨h1x, h2x⟩
    obtain ⟨X, hX⟩ := eventually_atTop.1 hη
    have K1 : ∀ x : ℝ, X ≤ x → y x ≤ -ε → (-y x) ^ 3 / 2 ≤ (deriv y x) ^ 2 := by
      intro x hxX hyx
      have h1 := (hX x hxX).1
      have hc := cube_mono ε (-y x) hε.le (by linarith)
      nlinarith [hc, h1]
    have K2 : ∀ x : ℝ, X ≤ x → y x ≤ -ε → deriv y x ≠ 0 := by
      intro x hxX hyx h0
      have h3 := K1 x hxX hyx
      rw [h0] at h3
      have hp : 0 < (-y x) ^ 3 := pow_pos (by linarith) 3
      nlinarith [h3, hp]
    have hkey' : ∀ d s : ℝ, 0 ≤ d → 0 < s → s ^ 6 / 2 ≤ d ^ 2 → s ^ 3 / 2 ≤ d := by
      intro d s hd hs h
      by_contra hcon
      push_neg at hcon
      have h3 : 0 < s ^ 3 := pow_pos hs 3
      have h6 : 0 < s ^ 6 := pow_pos hs 6
      nlinarith [mul_pos (sub_pos.2 hcon) (add_pos_of_pos_of_nonneg (half_pos h3) hd)]
    -- once y ≤ -ε and y' ≤ 0 at some point, this persists forever
    have K3 : ∀ a : ℝ, X ≤ a → y a ≤ -ε → deriv y a ≤ 0 →
        ∀ t : ℝ, a ≤ t → y t ≤ -ε ∧ deriv y t ≤ 0 := by
      intro a ha hya hda t hat
      have hcl1 : IsClosed {u : ℝ | y u ≤ -ε} := isClosed_le hy_cont continuous_const
      have hcl2 : IsClosed {u : ℝ | deriv y u ≤ 0} := isClosed_le hcont' continuous_const
      have hcl : IsClosed {u : ℝ | y u ≤ -ε ∧ deriv y u ≤ 0} := hcl1.inter hcl2
      have hmain : Set.Icc a t ⊆ {u : ℝ | y u ≤ -ε ∧ deriv y u ≤ 0} := by
        refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin (hcl.inter isClosed_Icc) ?_ ?_
        · exact ⟨hya, hda⟩
        · rintro x ⟨⟨hyx, hdx⟩, hxI⟩
          have hxX : X ≤ x := le_trans ha hxI.1
          have hdneg : deriv y x < 0 := lt_of_le_of_ne hdx (K2 x hxX hyx)
          have hev : ∀ᶠ u in 𝓝[≠] x, slope y x u < 0 :=
            (hasDerivAt_iff_tendsto_slope.1 (hyd x)).eventually (gt_mem_nhds hdneg)
          have hev2 : ∀ᶠ u in 𝓝[>] x, slope y x u < 0 :=
            nhdsWithin_mono x (fun u (hu : x < u) => hu.ne') hev
          have hlt : ∀ᶠ u in 𝓝[>] x, y u < y x := by
            filter_upwards [hev2, self_mem_nhdsWithin] with u h1 h2
            have hxu : x < u := h2
            rw [slope_def_field] at h1
            have := (div_lt_iff₀ (sub_pos.2 hxu)).1 h1
            linarith
          have hdlt : ∀ᶠ u in 𝓝 x, deriv y u < 0 :=
            (hcont'.tendsto x).eventually (gt_mem_nhds hdneg)
          have hdlt' : ∀ᶠ u in 𝓝[>] x, deriv y u < 0 :=
            eventually_nhdsWithin_of_eventually_nhds hdlt
          filter_upwards [hlt, hdlt'] with u h1 h2
          show y u ≤ -ε ∧ deriv y u ≤ 0
          exact ⟨by linarith, h2.le⟩
      exact hmain ⟨hat, le_refl t⟩
    -- blow-up contradiction
    have K4 : ∀ a : ℝ, X ≤ a → y a ≤ -ε → deriv y a ≤ 0 → False := by
      intro a ha hya hda
      have hst := K3 a ha hya hda
      have hpos : ∀ t, a ≤ t → 0 < -y t := fun t ht => by linarith [(hst t ht).1]
      have hsq : ∀ t, a ≤ t → HasDerivAt (fun u => (Real.sqrt (-y u))⁻¹)
          (-((-deriv y t) / (2 * Real.sqrt (-y t))) / Real.sqrt (-y t) ^ 2) t := by
        intro t ht
        have hv : HasDerivAt (fun u => -y u) (-deriv y t) t := (hyd t).neg
        have hs : HasDerivAt (fun u => Real.sqrt (-y u))
            ((-deriv y t) / (2 * Real.sqrt (-y t))) t := hv.sqrt (hpos t ht).ne'
        exact hs.inv (Real.sqrt_pos.2 (hpos t ht)).ne'
      have hΦ : ∀ t, a ≤ t → HasDerivAt (fun u => (Real.sqrt (-y u))⁻¹ + u / 4)
          (-((-deriv y t) / (2 * Real.sqrt (-y t))) / Real.sqrt (-y t) ^ 2 + 1 / 4) t := by
        intro t ht
        exact (hsq t ht).add ((hasDerivAt_id' t).div_const 4)
      have key : ∀ t, a ≤ t →
          -((-deriv y t) / (2 * Real.sqrt (-y t))) / Real.sqrt (-y t) ^ 2 + 1 / 4 ≤ 0 := by
        intro t ht
        obtain ⟨hyt, hdt⟩ := hst t ht
        have hXt : X ≤ t := le_trans ha ht
        have hK := K1 t hXt hyt
        obtain ⟨s, hs_def⟩ : ∃ s, s = Real.sqrt (-y t) := ⟨_, rfl⟩
        have hs : 0 < s := by rw [hs_def]; exact Real.sqrt_pos.2 (hpos t ht)
        have hsq2 : s ^ 2 = -y t := by rw [hs_def]; exact Real.sq_sqrt (hpos t ht).le
        rw [← hs_def]
        have hd : 0 ≤ -deriv y t := by linarith
        have hdd : s ^ 6 / 2 ≤ (-deriv y t) ^ 2 := by
          have e1 : (-y t) = s ^ 2 := hsq2.symm
          rw [e1] at hK
          nlinarith [hK]
        have hk2 := hkey' (-deriv y t) s hd hs hdd
        have hpos2 : 0 < 2 * s * s ^ 2 := mul_pos (mul_pos two_pos hs) (pow_pos hs 2)
        have h1 : 1 / 4 ≤ (-deriv y t) / (2 * s) / s ^ 2 := by
          rw [div_div, le_div_iff₀ hpos2]
          nlinarith [hk2]
        have h2 : -((-deriv y t) / (2 * s)) / s ^ 2 = -((-deriv y t) / (2 * s) / s ^ 2) := by
          ring
        rw [h2]
        linarith
      have hanti : AntitoneOn (fun u => (Real.sqrt (-y u))⁻¹ + u / 4) (Set.Ici a) := by
        refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici a)
          (f' := fun t => -((-deriv y t) / (2 * Real.sqrt (-y t))) / Real.sqrt (-y t) ^ 2 + 1 / 4)
          ?_ ?_ ?_
        · intro t ht
          exact (hΦ t (Set.mem_Ici.1 ht)).continuousAt.continuousWithinAt
        · intro t ht
          rw [interior_Ici] at ht ⊢
          exact (hΦ t (le_of_lt (Set.mem_Ioi.1 ht))).hasDerivWithinAt
        · intro t ht
          rw [interior_Ici] at ht
          exact key t (le_of_lt (Set.mem_Ioi.1 ht))
      have hG0 : 0 < (Real.sqrt (-y a))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 (hpos a le_rfl))
      obtain ⟨t, ht⟩ : ∃ t : ℝ, t = a + 4 * (Real.sqrt (-y a))⁻¹ + 4 := ⟨_, rfl⟩
      have hat : a ≤ t := by rw [ht]; linarith
      have hle := hanti (Set.mem_Ici.2 (le_refl a)) (Set.mem_Ici.2 hat) hat
      have hle' : (Real.sqrt (-y t))⁻¹ + t / 4 ≤ (Real.sqrt (-y a))⁻¹ + a / 4 := hle
      have hGt : 0 < (Real.sqrt (-y t))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 (hpos t hat))
      linarith [hle', hGt, ht]
    -- once above -ε (past X), stays above -ε
    have K5 : ∀ t : ℝ, X ≤ t → -ε < y t → ∀ s : ℝ, t ≤ s → -ε ≤ y s := by
      intro t ht hyt s hts
      have hcl : IsClosed {u : ℝ | -ε ≤ y u} := isClosed_le continuous_const hy_cont
      have hmain : Set.Icc t s ⊆ {u : ℝ | -ε ≤ y u} := by
        refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin (hcl.inter isClosed_Icc) ?_ ?_
        · exact le_of_lt hyt
        · rintro x ⟨hxS, hxI⟩
          have hxX : X ≤ x := le_trans ht hxI.1
          have hxS' : -ε ≤ y x := hxS
          rcases lt_or_eq_of_le hxS' with hlt | heq
          · have hev : ∀ᶠ u in 𝓝 x, -ε < y u :=
              (hy_cont.tendsto x).eventually (lt_mem_nhds hlt)
            have hev' : ∀ᶠ u in 𝓝[>] x, -ε < y u :=
              eventually_nhdsWithin_of_eventually_nhds hev
            filter_upwards [hev'] with u hu
            show -ε ≤ y u
            exact hu.le
          · have hyx : y x ≤ -ε := le_of_eq heq.symm
            have hdpos : 0 < deriv y x := by
              by_contra hcon
              push_neg at hcon
              exact K4 x hxX hyx hcon
            have hslope := hasDerivAt_iff_tendsto_slope.1 (hyd x)
            have hev : ∀ᶠ u in 𝓝[≠] x, 0 < slope y x u :=
              hslope.eventually (lt_mem_nhds hdpos)
            have hev2 : ∀ᶠ u in 𝓝[>] x, 0 < slope y x u :=
              nhdsWithin_mono x (fun u (hu : x < u) => hu.ne') hev
            have hlt : ∀ᶠ u in 𝓝[>] x, y x < y u := by
              filter_upwards [hev2, self_mem_nhdsWithin] with u h1 h2
              have hxu : x < u := h2
              rw [slope_def_field] at h1
              have := (lt_div_iff₀ (sub_pos.2 hxu)).1 h1
              linarith
            filter_upwards [hlt] with u hu
            show -ε ≤ y u
            linarith
      exact hmain ⟨hts, le_refl s⟩
    by_cases hex : ∃ t : ℝ, X ≤ t ∧ -ε < y t
    · obtain ⟨t, htX, hyt⟩ := hex
      exact ⟨t, fun s hs => K5 t htX hyt s hs⟩
    · exfalso
      push_neg at hex
      have hpos_d : ∀ t, X ≤ t → 0 < deriv y t := by
        intro t ht
        by_contra hcon
        push_neg at hcon
        exact K4 t ht (hex t ht) hcon
      obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = Real.sqrt (ε ^ 3 / 2) := ⟨_, rfl⟩
      have hc_pos : 0 < c := by rw [hc_def]; exact Real.sqrt_pos.2 (half_pos hε3)
      have hc_sq : c ^ 2 = ε ^ 3 / 2 := by
        rw [hc_def]; exact Real.sq_sqrt (half_pos hε3).le
      have hgrow : ∀ t, X ≤ t → c ≤ deriv y t := by
        intro t ht
        have hK := K1 t ht (hex t ht)
        have hd := hpos_d t ht
        have hcube : ε ^ 3 ≤ (-y t) ^ 3 := cube_mono ε (-y t) hε.le (by linarith [hex t ht])
        by_contra hcon
        push_neg at hcon
        nlinarith [hK, hcube, hc_sq, mul_pos (sub_pos.2 hcon) (add_pos hc_pos hd)]
      have hfd : Differentiable ℝ (fun t => y t - c * t) :=
        fun t => (hdiff t).sub ((hasDerivAt_id' t).const_mul c).differentiableAt
      have hmono : MonotoneOn (fun t => y t - c * t) (Set.Ici X) := by
        refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici X)
          (f' := fun t => deriv y t - c * 1) ?_ ?_ ?_
        · exact hfd.continuous.continuousOn
        · intro t ht
          rw [interior_Ici] at ht ⊢
          exact ((hyd t).sub ((hasDerivAt_id' t).const_mul c)).hasDerivWithinAt
        · intro t ht
          rw [interior_Ici] at ht
          show 0 ≤ deriv y t - c * 1
          have := hgrow t (le_of_lt (Set.mem_Ioi.1 ht))
          linarith
      obtain ⟨T, hT⟩ : ∃ T : ℝ, T = X + (-(y X) + ε + 1) / c := ⟨_, rfl⟩
      have hcne : c ≠ 0 := hc_pos.ne'
      have hq : c * ((-(y X) + ε + 1) / c) = -(y X) + ε + 1 := by
        field_simp
      have hcT : c * T - c * X = -(y X) + ε + 1 := by
        rw [hT]
        linear_combination hq
      have hyX : y X ≤ -ε := hex X le_rfl
      have hq0 : 0 ≤ -(y X) + ε + 1 := by linarith
      have hTX : X ≤ T := by
        rw [hT]
        have := div_nonneg hq0 hc_pos.le
        linarith
      have hm' : y X - c * X ≤ y T - c * T :=
        hmono (Set.mem_Ici.2 (le_refl X)) (Set.mem_Ici.2 hTX) hTX
      have hyT : y T ≤ -ε := hex T hTX
      linarith
  have hyT : Tendsto y atTop (𝓝 0) := by
    rw [tendsto_order]
    constructor
    · intro c hc
      obtain ⟨T, hT⟩ := hlow (-c / 2) (by linarith)
      filter_upwards [eventually_ge_atTop T] with s hs
      have := hT s hs
      linarith
    · intro b hb
      have hfb : ∀ᶠ x in atTop, (deriv y x) ^ 2 + (y x) ^ 3 < b ^ 3 :=
        (tendsto_order.1 limy).2 (b ^ 3) (pow_pos hb 3)
      filter_upwards [hfb] with x hx
      by_contra hcon
      push_neg at hcon
      have hc3 := cube_mono b (y x) hb.le hcon
      nlinarith [sq_nonneg (deriv y x)]
  refine ⟨hyT, ?_⟩
  have h3 : Tendsto (fun x => (y x) ^ 3) atTop (𝓝 0) := by
    have := hyT.pow 3
    simpa using this
  have h4 : Tendsto (fun x => (deriv y x) ^ 2 + (y x) ^ 3 - (y x) ^ 3) atTop (𝓝 (0 - 0)) :=
    limy.sub h3
  have h2 : Tendsto (fun x => (deriv y x) ^ 2) atTop (𝓝 0) := by
    simpa using h4
  have h5 : Tendsto (fun x => Real.sqrt ((deriv y x) ^ 2)) atTop (𝓝 (Real.sqrt 0)) :=
    (Real.continuous_sqrt.tendsto 0).comp h2
  simp only [Real.sqrt_zero, Real.sqrt_sq_eq_abs] at h5
  exact tendsto_zero_iff_norm_tendsto_zero.2 (by simpa only [Real.norm_eq_abs] using h5)
