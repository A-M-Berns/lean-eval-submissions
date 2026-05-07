import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

open Set
open scoped Topology

noncomputable def wronskian (y₁ y₂ : ℝ → ℝ) : ℝ → ℝ :=
  fun x => y₁ x * deriv y₂ x - y₂ x * deriv y₁ x

lemma hasDerivAt_wronskian
    {y₁ y₂ : ℝ → ℝ} {x y₁'' y₂'' : ℝ}
    (hy₁ : HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : HasDerivAt (deriv y₁) y₁'' x)
    (hy₂ : HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : HasDerivAt (deriv y₂) y₂'' x) :
    HasDerivAt (wronskian y₁ y₂)
      (y₁ x * y₂'' - y₂ x * y₁'') x := by
  unfold wronskian
  convert (hy₁.mul hy₂').sub (hy₂.mul hy₁') using 1
  ring

lemma hasDerivAt_wronskian_of_ode
    {p q y₁ y₂ : ℝ → ℝ} {x : ℝ}
    (hy₁ : HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' :
      HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' :
    HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x) :
    HasDerivAt (wronskian y₁ y₂) (-(p x) * wronskian y₁ y₂ x) x := by
  convert hasDerivAt_wronskian hy₁ hy₁' hy₂ hy₂' using 1
  simp [wronskian]
  ring

lemma deriv_wronskian_of_ode
    {p q y₁ y₂ : ℝ → ℝ} {x : ℝ}
    (hy₁ : HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' :
      HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' :
      HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x) :
    deriv (wronskian y₁ y₂) x = -(p x) * wronskian y₁ y₂ x :=
  (hasDerivAt_wronskian_of_ode hy₁ hy₁' hy₂ hy₂').deriv

lemma hasDerivAt_ratio
    {y₁ y₂ : ℝ → ℝ} {x : ℝ}
    (hy₁ : HasDerivAt y₁ (deriv y₁ x) x)
    (hy₂ : HasDerivAt y₂ (deriv y₂ x) x)
    (hy₁_ne : y₁ x ≠ 0) :
    HasDerivAt (fun t => y₂ t / y₁ t)
      (wronskian y₁ y₂ x / (y₁ x) ^ 2) x := by
  convert hy₂.div hy₁ hy₁_ne using 1
  simp [wronskian, pow_two]
  ring

lemma deriv_ratio
    {y₁ y₂ : ℝ → ℝ} {x : ℝ}
    (hy₁ : HasDerivAt y₁ (deriv y₁ x) x)
    (hy₂ : HasDerivAt y₂ (deriv y₂ x) x)
    (hy₁_ne : y₁ x ≠ 0) :
    deriv (fun t => y₂ t / y₁ t) x =
      wronskian y₁ y₂ x / (y₁ x) ^ 2 :=
  (hasDerivAt_ratio hy₁ hy₂ hy₁_ne).deriv

lemma wronskian_swap (y₁ y₂ : ℝ → ℝ) (x : ℝ) :
    wronskian y₂ y₁ x = -wronskian y₁ y₂ x := by
  simp [wronskian]

lemma continuousOn_Icc_of_hasDerivAt_on_superset
    {J : Set ℝ} {a b : ℝ} {f f' : ℝ → ℝ}
    (hJ_sub : Set.Icc a b ⊆ J)
    (hf : ∀ x ∈ J, HasDerivAt f (f' x) x) :
    ContinuousOn f (Set.Icc a b) := by
  intro x hx
  exact (hf x (hJ_sub hx)).continuousAt.continuousWithinAt

lemma exists_y₂_zero_of_wronskian_ne_on_Icc
    {y₁ y₂ : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hy₁ : ∀ x ∈ Set.Icc a b, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₂ : ∀ x ∈ Set.Icc a b, HasDerivAt y₂ (deriv y₂ x) x)
    (hW_ne : ∀ x ∈ Set.Icc a b, wronskian y₁ y₂ x ≠ 0)
    (hza : y₁ a = 0) (hzb : y₁ b = 0) :
    ∃ c ∈ Set.Ioo a b, y₂ c = 0 := by
  classical
  by_contra hno
  have hy₂a_ne : y₂ a ≠ 0 := by
    intro hy₂a
    have hW := hW_ne a (by exact ⟨le_rfl, le_of_lt hab⟩)
    rw [wronskian, hza, hy₂a] at hW
    simp at hW
  have hy₂b_ne : y₂ b ≠ 0 := by
    intro hy₂b
    have hW := hW_ne b (by exact ⟨le_of_lt hab, le_rfl⟩)
    rw [wronskian, hzb, hy₂b] at hW
    simp at hW
  have hy₂_ne_Icc : ∀ x ∈ Set.Icc a b, y₂ x ≠ 0 := by
    intro x hx
    by_cases hxa : x = a
    · simpa [hxa] using hy₂a_ne
    by_cases hxb : x = b
    · simpa [hxb] using hy₂b_ne
    have hxIoo : x ∈ Set.Ioo a b := by
      exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
    intro hy₂x
    exact hno ⟨x, hxIoo, hy₂x⟩
  have hcont_y₁ : ContinuousOn y₁ (Set.Icc a b) := by
    intro x hx
    exact (hy₁ x hx).continuousAt.continuousWithinAt
  have hcont_y₂ : ContinuousOn y₂ (Set.Icc a b) := by
    intro x hx
    exact (hy₂ x hx).continuousAt.continuousWithinAt
  have hcont_ratio : ContinuousOn (fun x => y₁ x / y₂ x) (Set.Icc a b) :=
    hcont_y₁.div hcont_y₂ hy₂_ne_Icc
  have hsame : y₁ a / y₂ a = y₁ b / y₂ b := by
    simp [hza, hzb]
  obtain ⟨c, hcIoo, hcderiv⟩ :=
    exists_hasDerivAt_eq_zero (f := fun x => y₁ x / y₂ x)
      (f' := fun x => wronskian y₂ y₁ x / (y₂ x) ^ 2)
      hab hcont_ratio hsame
      (by
        intro x hx
        exact hasDerivAt_ratio (hy₂ x ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
          (hy₁ x ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
          (hy₂_ne_Icc x ⟨le_of_lt hx.1, le_of_lt hx.2⟩))
  have hWc_ne : wronskian y₁ y₂ c ≠ 0 :=
    hW_ne c ⟨le_of_lt hcIoo.1, le_of_lt hcIoo.2⟩
  have hy₂c_ne : y₂ c ≠ 0 :=
    hy₂_ne_Icc c ⟨le_of_lt hcIoo.1, le_of_lt hcIoo.2⟩
  rw [wronskian_swap] at hcderiv
  have hden_ne : (y₂ c) ^ 2 ≠ 0 := pow_ne_zero 2 hy₂c_ne
  have hnegW_zero : -wronskian y₁ y₂ c = 0 := by
    rcases div_eq_zero_iff.mp hcderiv with h | h
    · exact h
    · exact False.elim (hden_ne h)
  exact hWc_ne (neg_eq_zero.mp hnegW_zero)

lemma unique_y₂_zero_of_wronskian_ne_on_Icc
    {y₁ y₂ : ℝ → ℝ} {a b : ℝ}
    (hy₁ : ∀ x ∈ Set.Icc a b, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₂ : ∀ x ∈ Set.Icc a b, HasDerivAt y₂ (deriv y₂ x) x)
    (hW_ne : ∀ x ∈ Set.Icc a b, wronskian y₁ y₂ x ≠ 0)
    (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0) :
    ∀ c d, c ∈ Set.Ioo a b → y₂ c = 0 →
      d ∈ Set.Ioo a b → y₂ d = 0 → c = d := by
  classical
  have no_two_ordered :
      ∀ {c d : ℝ}, c ∈ Set.Ioo a b → d ∈ Set.Ioo a b → c < d →
        y₂ c = 0 → y₂ d = 0 → False := by
    intro c d hc hd hcd hy₂c hy₂d
    have hIcc_sub : Set.Icc c d ⊆ Set.Icc a b := by
      intro x hx
      exact ⟨le_trans (le_of_lt hc.1) hx.1, le_trans hx.2 (le_of_lt hd.2)⟩
    have hIcc_sub_Ioo : Set.Icc c d ⊆ Set.Ioo a b := by
      intro x hx
      exact ⟨lt_of_lt_of_le hc.1 hx.1, lt_of_le_of_lt hx.2 hd.2⟩
    have hy₁_ne_Icc : ∀ x ∈ Set.Icc c d, y₁ x ≠ 0 := by
      intro x hx
      exact hne x (hIcc_sub_Ioo hx)
    have hcont_y₁ : ContinuousOn y₁ (Set.Icc c d) := by
      intro x hx
      exact (hy₁ x (hIcc_sub hx)).continuousAt.continuousWithinAt
    have hcont_y₂ : ContinuousOn y₂ (Set.Icc c d) := by
      intro x hx
      exact (hy₂ x (hIcc_sub hx)).continuousAt.continuousWithinAt
    have hcont_ratio : ContinuousOn (fun x => y₂ x / y₁ x) (Set.Icc c d) :=
      hcont_y₂.div hcont_y₁ hy₁_ne_Icc
    have hsame : y₂ c / y₁ c = y₂ d / y₁ d := by
      simp [hy₂c, hy₂d]
    obtain ⟨e, heIoo, hederiv⟩ :=
      exists_hasDerivAt_eq_zero (f := fun x => y₂ x / y₁ x)
        (f' := fun x => wronskian y₁ y₂ x / (y₁ x) ^ 2)
        hcd hcont_ratio hsame
        (by
          intro x hx
          have hxIcc_cd : x ∈ Set.Icc c d := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
          have hxIcc_ab : x ∈ Set.Icc a b := hIcc_sub hxIcc_cd
          exact hasDerivAt_ratio (hy₁ x hxIcc_ab) (hy₂ x hxIcc_ab)
            (hy₁_ne_Icc x hxIcc_cd))
    have heIcc_cd : e ∈ Set.Icc c d := ⟨le_of_lt heIoo.1, le_of_lt heIoo.2⟩
    have heIcc_ab : e ∈ Set.Icc a b := hIcc_sub heIcc_cd
    have hW_e_ne : wronskian y₁ y₂ e ≠ 0 := hW_ne e heIcc_ab
    have hy₁e_ne : y₁ e ≠ 0 := hy₁_ne_Icc e heIcc_cd
    have hden_ne : (y₁ e) ^ 2 ≠ 0 := pow_ne_zero 2 hy₁e_ne
    have hW_e_zero : wronskian y₁ y₂ e = 0 := by
      rcases div_eq_zero_iff.mp hederiv with h | h
      · exact h
      · exact False.elim (hden_ne h)
    exact hW_e_ne hW_e_zero
  intro c d hc hy₂c hd hy₂d
  by_cases hcd : c = d
  · exact hcd
  rcases lt_or_gt_of_ne hcd with hlt | hgt
  · exact False.elim (no_two_ordered hc hd hlt hy₂c hy₂d)
  · exact False.elim (no_two_ordered hd hc hgt hy₂d hy₂c)

lemma existsUnique_y₂_zero_of_wronskian_ne_on_Icc
    {y₁ y₂ : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hy₁ : ∀ x ∈ Set.Icc a b, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₂ : ∀ x ∈ Set.Icc a b, HasDerivAt y₂ (deriv y₂ x) x)
    (hW_ne : ∀ x ∈ Set.Icc a b, wronskian y₁ y₂ x ≠ 0)
    (hza : y₁ a = 0) (hzb : y₁ b = 0)
    (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0) :
    ∃! c, c ∈ Set.Ioo a b ∧ y₂ c = 0 := by
  obtain ⟨c, hc, hy₂c⟩ :=
    exists_y₂_zero_of_wronskian_ne_on_Icc hab hy₁ hy₂ hW_ne hza hzb
  refine ⟨c, ⟨hc, hy₂c⟩, ?_⟩
  intro d hd
  exact unique_y₂_zero_of_wronskian_ne_on_Icc hy₁ hy₂ hW_ne hne
    d c hd.1 hd.2 hc hy₂c

lemma lipschitzWith_linear_wronskian_rhs
    {p : ℝ → ℝ} {K : NNReal} {t : ℝ}
    (hp_bound : ‖p t‖ ≤ (K : ℝ)) :
    LipschitzWith K (fun z : ℝ => -(p t) * z) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  calc
    dist (-(p t) * x) (-(p t) * y)
        = ‖p t‖ * dist x y := by
          rw [Real.dist_eq, Real.dist_eq]
          rw [Real.norm_eq_abs]
          calc
            |-(p t) * x - -(p t) * y| = |p t * (y - x)| := by
              congr 1
              ring
            _ = |p t| * |y - x| := abs_mul _ _
            _ = |p t| * |x - y| := by rw [abs_sub_comm]
    _ ≤ (K : ℝ) * dist x y := by
      gcongr
    _ = K * dist x y := rfl

lemma wronskian_eq_zero_on_Icc_right_of_eq_zero
    {p q y₁ y₂ : ℝ → ℝ} {a b : ℝ}
    (hp : ContinuousOn p (Set.Icc a b))
    (hy₁ : ∀ x ∈ Set.Icc a b, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ Set.Icc a b,
      HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ Set.Icc a b, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ Set.Icc a b,
      HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (hWa : wronskian y₁ y₂ a = 0) :
    ∀ x ∈ Set.Icc a b, wronskian y₁ y₂ x = 0 := by
  classical
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hp
  let K : NNReal := Real.toNNReal C
  have hv :
      ∀ t ∈ Set.Ico a b,
        LipschitzOnWith K (fun z : ℝ => -(p t) * z) Set.univ := by
    intro t ht
    exact (lipschitzWith_linear_wronskian_rhs
      (p := p) (K := K) (t := t)
      ((hC t ⟨ht.1, le_of_lt ht.2⟩).trans (Real.le_coe_toNNReal C))).lipschitzOnWith
  have hW_cont : ContinuousOn (wronskian y₁ y₂) (Set.Icc a b) := by
    intro x hx
    exact (hasDerivAt_wronskian_of_ode
      (hy₁ x hx) (hy₁' x hx) (hy₂ x hx) (hy₂' x hx)).continuousAt.continuousWithinAt
  have hW_deriv :
      ∀ t ∈ Set.Ico a b,
        HasDerivWithinAt (wronskian y₁ y₂)
          ((fun z : ℝ => -(p t) * z) (wronskian y₁ y₂ t)) (Set.Ici t) t := by
    intro t ht
    have htIcc : t ∈ Set.Icc a b := ⟨ht.1, le_of_lt ht.2⟩
    simpa using
      (hasDerivAt_wronskian_of_ode
        (hy₁ t htIcc) (hy₁' t htIcc) (hy₂ t htIcc) (hy₂' t htIcc)).hasDerivWithinAt
  have hzero_cont : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Set.Icc a b) := continuous_const.continuousOn
  have hzero_deriv :
      ∀ t ∈ Set.Ico a b,
        HasDerivWithinAt (fun _ : ℝ => (0 : ℝ))
          ((fun z : ℝ => -(p t) * z) ((fun _ : ℝ => (0 : ℝ)) t)) (Set.Ici t) t := by
    intro t ht
    simpa using (hasDerivAt_const (x := t) (c := (0 : ℝ))).hasDerivWithinAt
  have hEq :=
    ODE_solution_unique_of_mem_Icc_right (v := fun t z : ℝ => -(p t) * z)
      (s := fun _ : ℝ => Set.univ)
      (K := K) (f := wronskian y₁ y₂) (g := fun _ : ℝ => (0 : ℝ))
      (a := a) (b := b)
      hv hW_cont hW_deriv (by intro t ht; trivial)
      hzero_cont hzero_deriv (by intro t ht; trivial) hWa
  intro x hx
  simpa using hEq hx

lemma wronskian_eq_zero_on_Icc_left_of_eq_zero
    {p q y₁ y₂ : ℝ → ℝ} {a b : ℝ}
    (hp : ContinuousOn p (Set.Icc a b))
    (hy₁ : ∀ x ∈ Set.Icc a b, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ Set.Icc a b,
      HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ Set.Icc a b, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ Set.Icc a b,
      HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (hWb : wronskian y₁ y₂ b = 0) :
    ∀ x ∈ Set.Icc a b, wronskian y₁ y₂ x = 0 := by
  classical
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hp
  let K : NNReal := Real.toNNReal C
  have hv :
      ∀ t ∈ Set.Ioc a b,
        LipschitzOnWith K (fun z : ℝ => -(p t) * z) Set.univ := by
    intro t ht
    exact (lipschitzWith_linear_wronskian_rhs
      (p := p) (K := K) (t := t)
      ((hC t ⟨le_of_lt ht.1, ht.2⟩).trans (Real.le_coe_toNNReal C))).lipschitzOnWith
  have hW_cont : ContinuousOn (wronskian y₁ y₂) (Set.Icc a b) := by
    intro x hx
    exact (hasDerivAt_wronskian_of_ode
      (hy₁ x hx) (hy₁' x hx) (hy₂ x hx) (hy₂' x hx)).continuousAt.continuousWithinAt
  have hW_deriv :
      ∀ t ∈ Set.Ioc a b,
        HasDerivWithinAt (wronskian y₁ y₂)
          ((fun z : ℝ => -(p t) * z) (wronskian y₁ y₂ t)) (Set.Iic t) t := by
    intro t ht
    have htIcc : t ∈ Set.Icc a b := ⟨le_of_lt ht.1, ht.2⟩
    simpa using
      (hasDerivAt_wronskian_of_ode
        (hy₁ t htIcc) (hy₁' t htIcc) (hy₂ t htIcc) (hy₂' t htIcc)).hasDerivWithinAt
  have hzero_cont : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Set.Icc a b) := continuous_const.continuousOn
  have hzero_deriv :
      ∀ t ∈ Set.Ioc a b,
        HasDerivWithinAt (fun _ : ℝ => (0 : ℝ))
          ((fun z : ℝ => -(p t) * z) ((fun _ : ℝ => (0 : ℝ)) t)) (Set.Iic t) t := by
    intro t ht
    simpa using (hasDerivAt_const (x := t) (c := (0 : ℝ))).hasDerivWithinAt
  have hEq :=
    ODE_solution_unique_of_mem_Icc_left (v := fun t z : ℝ => -(p t) * z)
      (s := fun _ : ℝ => Set.univ)
      (K := K) (f := wronskian y₁ y₂) (g := fun _ : ℝ => (0 : ℝ))
      (a := a) (b := b)
      hv hW_cont hW_deriv (by intro t ht; trivial)
      hzero_cont hzero_deriv (by intro t ht; trivial) hWb
  intro x hx
  simpa using hEq hx

theorem sturm_separation (p q y₁ y₂ : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (J : Set ℝ) (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
    (hJ_sub : Set.Icc a b ⊆ J)
    (hp : ContinuousOn p J) (hq : ContinuousOn q J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
    (hza : y₁ a = 0) (hzb : y₁ b = 0)
    (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0) :
    ∃! c, c ∈ Set.Ioo a b ∧ y₂ c = 0 := by
  have hJ_open_used : IsOpen J := hJ_open
  have hq_used : ContinuousOn q J := hq
  clear hJ_open_used hq_used
  have hy₁_Icc : ∀ x ∈ Set.Icc a b, HasDerivAt y₁ (deriv y₁ x) x := by
    intro x hx
    exact hy₁ x (hJ_sub hx)
  have hy₂_Icc : ∀ x ∈ Set.Icc a b, HasDerivAt y₂ (deriv y₂ x) x := by
    intro x hx
    exact hy₂ x (hJ_sub hx)
  have hW_ne_Icc : ∀ x ∈ Set.Icc a b, wronskian y₁ y₂ x ≠ 0 := by
    rcases hW with ⟨x₀, hx₀J, hW₀⟩
    have hW₀' : wronskian y₁ y₂ x₀ ≠ 0 := by
      simpa [wronskian] using hW₀
    have hJ_ord : Set.OrdConnected J := hJ_conn.ordConnected
    intro x hxIcc hWx
    have hxJ : x ∈ J := hJ_sub hxIcc
    rcases le_total x x₀ with hx_le_x₀ | hx₀_le_x
    · have hseg : Set.Icc x x₀ ⊆ J := hJ_ord.out hxJ hx₀J
      have hzero :=
        wronskian_eq_zero_on_Icc_right_of_eq_zero
          (p := p) (q := q) (y₁ := y₁) (y₂ := y₂)
          (a := x) (b := x₀)
          (hp.mono hseg)
          (by intro t ht; exact hy₁ t (hseg ht))
          (by intro t ht; exact hy₁' t (hseg ht))
          (by intro t ht; exact hy₂ t (hseg ht))
          (by intro t ht; exact hy₂' t (hseg ht))
          hWx x₀ ⟨hx_le_x₀, le_rfl⟩
      exact hW₀' hzero
    · have hseg : Set.Icc x₀ x ⊆ J := hJ_ord.out hx₀J hxJ
      have hzero :=
        wronskian_eq_zero_on_Icc_left_of_eq_zero
          (p := p) (q := q) (y₁ := y₁) (y₂ := y₂)
          (a := x₀) (b := x)
          (hp.mono hseg)
          (by intro t ht; exact hy₁ t (hseg ht))
          (by intro t ht; exact hy₁' t (hseg ht))
          (by intro t ht; exact hy₂ t (hseg ht))
          (by intro t ht; exact hy₂' t (hseg ht))
          hWx x₀ ⟨le_rfl, hx₀_le_x⟩
      exact hW₀' hzero
  exact existsUnique_y₂_zero_of_wronskian_ne_on_Icc
    hab hy₁_Icc hy₂_Icc hW_ne_Icc hza hzb hne
