import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

open Set
open scoped Topology

namespace Submission

lemma convex_nonpos_on_Icc_of_endpoints_nonpos
    {w : ℝ → ℝ}
    (hw : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) w)
    (hw0 : w 0 ≤ 0)
    (hw1 : w 1 ≤ 0) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, w x ≤ 0 := by
  intro x hx
  rcases hx with ⟨hx0, hx1⟩
  have h0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have h1_mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have h_nonneg_left : 0 ≤ 1 - x := by linarith
  have h_nonneg_right : 0 ≤ x := hx0
  have h_sum : (1 - x) + x = (1 : ℝ) := by ring
  have h_point : (1 - x) • (0 : ℝ) + x • (1 : ℝ) = x := by simp
  have hconv :=
    hw.2 h0_mem h1_mem h_nonneg_left h_nonneg_right h_sum
  rw [h_point] at hconv
  calc
    w x ≤ (1 - x) * w 0 + x * w 1 := by
      simpa [smul_eq_mul] using hconv
    _ ≤ (1 - x) * 0 + x * 0 := by
      gcongr
    _ = 0 := by ring

lemma convexOn_Icc_of_hasDerivAt2_nonneg_on_open_superset
    (J : Set ℝ)
    (hJ_sub : Set.Icc (0 : ℝ) 1 ⊆ J)
    (w w' w'' : ℝ → ℝ)
    (hw : ∀ x ∈ J, HasDerivAt w (w' x) x)
    (hw' : ∀ x ∈ J, HasDerivAt w' (w'' x) x)
    (hsecond : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ w'' x) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) w := by
  refine convexOn_of_hasDerivWithinAt2_nonneg
    (D := Set.Icc (0 : ℝ) 1) (f := w) (f' := w') (f'' := w'')
    (convex_Icc (0 : ℝ) 1) ?continuous ?first ?second ?nonneg
  · intro x hx
    exact (hw x (hJ_sub hx)).continuousAt.continuousWithinAt
  · intro x hx
    have hxJ : x ∈ J := hJ_sub (interior_subset hx)
    exact (hw x hxJ).hasDerivWithinAt
  · intro x hx
    have hxJ : x ∈ J := hJ_sub (interior_subset hx)
    exact (hw' x hxJ).hasDerivWithinAt
  · intro x hx
    exact hsecond x (by simpa [interior_Icc] using hx)

theorem bvp_comparison
    (J : Set ℝ) (hJ_open : IsOpen J)
    (hJ_sub : Set.Icc (0 : ℝ) 1 ⊆ J)
    (u v : ℝ → ℝ)
    (hu : ∀ x ∈ J, HasDerivAt u (deriv u x) x)
    (hu' : ∀ x ∈ J, HasDerivAt (deriv u) (deriv (deriv u) x) x)
    (hv : ∀ x ∈ J, HasDerivAt v (deriv v x) x)
    (hv' : ∀ x ∈ J, HasDerivAt (deriv v) (deriv (deriv v) x) x)
    (hineq : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      -deriv (deriv u) x ≤ -deriv (deriv v) x)
    (hu0 : u 0 ≤ v 0)
    (hu1 : u 1 ≤ v 1) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, u x ≤ v x := by
  have hJ_open_used : IsOpen J := hJ_open
  clear hJ_open_used
  let w : ℝ → ℝ := fun x => u x - v x

  have hw0 : w 0 ≤ 0 := by
    dsimp [w]
    linarith [hu0]

  have hw1 : w 1 ≤ 0 := by
    dsimp [w]
    linarith [hu1]

  have hw_convex : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) w := by
    apply convexOn_Icc_of_hasDerivAt2_nonneg_on_open_superset
      J hJ_sub
      w
      (fun x => deriv u x - deriv v x)
      (fun x => deriv (deriv u) x - deriv (deriv v) x)
    · intro x hxJ
      dsimp [w]
      exact (hu x hxJ).sub (hv x hxJ)
    · intro x hxJ
      exact (hu' x hxJ).sub (hv' x hxJ)
    · intro x hx
      have h := hineq x hx
      linarith

  intro x hx
  have hwx := convex_nonpos_on_Icc_of_endpoints_nonpos hw_convex hw0 hw1 x hx
  dsimp [w] at hwx
  linarith

end Submission
