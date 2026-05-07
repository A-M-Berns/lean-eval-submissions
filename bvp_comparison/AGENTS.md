# bvp_comparison working prompt

```text
We are trying to solve the Lean theorem `bvp_comparison` from the Lean evaluation benchmark:

https://lean-lang.org/eval/problems/#main-problems

The target theorem is the comparison principle for the Dirichlet BVP. The intended mathematical proof is:

1. Let `w x = u x - v x`.
2. The hypothesis `-deriv (deriv u) x ≤ -deriv (deriv v) x` on `(0,1)` implies
   `0 ≤ deriv (deriv u) x - deriv (deriv v) x`, i.e. `w'' ≥ 0`.
3. Therefore `w` is convex on `[0,1]`.
4. Since `w 0 ≤ 0` and `w 1 ≤ 0`, convexity gives `w x ≤ 0` for all `x ∈ [0,1]`.
5. Therefore `u x ≤ v x`.

Important tactical instruction: DO NOT try to prove global facts like

```lean
deriv (fun x => u x - v x) x = deriv u x - deriv v x
deriv (deriv (fun x => u x - v x)) x =
  deriv (deriv u) x - deriv (deriv v) x
```

unless absolutely forced.

Instead, use the Mathlib theorem

```lean
convexOn_of_hasDerivWithinAt2_nonneg
```

from

```lean
import Mathlib.Analysis.Convex.Deriv
```

and feed it custom derivative functions:

```lean
w   := fun x => u x - v x
w'  := fun x => deriv u x - deriv v x
w'' := fun x => deriv (deriv u) x - deriv (deriv v) x
```

The benchmark hypotheses give `HasDerivAt u (deriv u x) x`, `HasDerivAt v (deriv v x) x`, and similarly for `deriv u` and `deriv v`, on an open set `J` containing `[0,1]`. These should be converted to `HasDerivWithinAt` on `interior (Set.Icc 0 1)` using `.hasDerivWithinAt`, and subtraction should be handled with `.sub`.

Start with these imports:

```lean
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

open Set
open scoped Topology
```

First prove this auxiliary lemma, before touching derivatives:

```lean
lemma convex_nonpos_on_Icc_of_endpoints_nonpos
    {w : ℝ → ℝ}
    (hw : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) w)
    (hw0 : w 0 ≤ 0)
    (hw1 : w 1 ≤ 0) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, w x ≤ 0 := by
  intro x hx
  -- Use the defining convexity inequality with points 0 and 1,
  -- weights (1 - x) and x.
  -- Facts needed:
  --   0 ≤ 1 - x
  --   0 ≤ x
  --   (1 - x) + x = 1
  --   (1 - x) • (0 : ℝ) + x • (1 : ℝ) = x
  -- Then:
  --   w x ≤ (1 - x) * w 0 + x * w 1 ≤ 0
  sorry
```

Then prove a bridge lemma, preferably:

```lean
lemma convexOn_Icc_of_hasDerivAt2_nonneg_on_open_superset
    (J : Set ℝ) (hJ_open : IsOpen J)
    (hJ_sub : Set.Icc (0 : ℝ) 1 ⊆ J)
    (w w' w'' : ℝ → ℝ)
    (hw : ∀ x ∈ J, HasDerivAt w (w' x) x)
    (hw' : ∀ x ∈ J, HasDerivAt w' (w'' x) x)
    (hsecond : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ w'' x) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) w := by
  -- Apply `convexOn_of_hasDerivWithinAt2_nonneg`.
  -- Convex set: `convex_Icc (0 : ℝ) 1`.
  -- Continuity: derivative hypotheses imply continuity at each point of `[0,1]`.
  -- First derivative within interior:
  --   use `hw x hxJ` where `hxJ := hJ_sub (interior_subset hx)`,
  --   then `.hasDerivWithinAt`.
  -- Second derivative within interior:
  --   same with `hw'`.
  -- Nonnegative second derivative:
  --   convert `x ∈ interior (Icc 0 1)` to `x ∈ Ioo 0 1`;
  --   `simpa` or `rw [interior_Icc]`.
  sorry
```

Finally prove the benchmark theorem:

```lean
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
  let w : ℝ → ℝ := fun x => u x - v x

  have hw0 : w 0 ≤ 0 := by
    dsimp [w]
    linarith [hu0]

  have hw1 : w 1 ≤ 0 := by
    dsimp [w]
    linarith [hu1]

  have hw_convex : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) w := by
    apply convexOn_Icc_of_hasDerivAt2_nonneg_on_open_superset
      J hJ_open hJ_sub
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
```

Expected friction points:

* Exact theorem signature of `convexOn_of_hasDerivWithinAt2_nonneg`.
* The projection/use form of `ConvexOn`; inspect `Mathlib.Analysis.Convex.Function` if needed.
* `interior (Set.Icc 0 1)` simplification to `Set.Ioo 0 1`.
* Converting `HasDerivAt` to `HasDerivWithinAt`, likely via `.hasDerivWithinAt`.
* `ContinuousOn` from `HasDerivAt.continuousAt.continuousWithinAt`.

Suggested workflow:

1. Get `convex_nonpos_on_Icc_of_endpoints_nonpos` compiling first.
2. Then get the bridge lemma compiling.
3. Only then attempt the final benchmark theorem.
4. Keep all intermediate lemmas as general and clean as possible.
5. Avoid fighting global `deriv` simplification unless no other route works.
```
