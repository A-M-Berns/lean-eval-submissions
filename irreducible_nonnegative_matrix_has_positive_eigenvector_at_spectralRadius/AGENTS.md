# Perron-Frobenius Plan

Target:

```lean
theorem irreducible_nonnegative_matrix_has_positive_eigenvector_at_spectralRadius
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℝ) (hA : A.IsIrreducible) :
    ∃ v : n → ℝ,
      Module.End.HasEigenvector (Matrix.toLin' A) (spectralRadius ℝ A).toReal v ∧
        (∀ i, 0 < v i)
```

Relevant Mathlib APIs:

* `Matrix.IsIrreducible` in `Mathlib.LinearAlgebra.Matrix.Irreducible.Defs`.
  It bundles entrywise nonnegativity and strong connectivity.
* `Matrix.IsIrreducible.exists_pos` gives a positive entry in each row when the index type is
  nontrivial.
* `Matrix.isIrreducible_iff_exists_pow_pos` gives, for all `i j`, some `k > 0` with
  `0 < (A ^ k) i j`.
* `Matrix.pow_apply_pos_iff_nonempty_path` connects positive entries in powers to quiver paths.
* `spectralRadius`, `Real.spectralRadius_mem_spectrum_or`, and finite-dimensional
  `Module.End.hasEigenvalue_iff_mem_spectrum` are available.
* `Matrix.toLin'_apply` rewrites `Matrix.toLin' A v` to `A *ᵥ v`.

Statement issue:

The original benchmark statement had no `[Nonempty n]` assumption. In Mathlib,
`Matrix.IsIrreducible` is vacuous for `Empty`, so `(0 : Matrix Empty Empty ℝ).IsIrreducible`
is provable, but no `Module.End.HasEigenvector` can exist on `Empty → ℝ` because eigenvectors are
nonzero. The local scaffold now uses the corrected `[Nonempty n]` statement. See
`empty_matrix_isIrreducible` and `no_empty_eigenvector` in `Submission.lean`.

Phases:

1. Cone lemmas. Done in `Submission.lean`.
   Prove that entrywise nonnegative matrices preserve nonnegative vectors under `mulVec`, and that
   powers of an entrywise nonnegative matrix are entrywise nonnegative.

2. Irreducibility positivity upgrade. Done in `Submission.lean`.
   Prove a conditional theorem: if `v ≥ 0`, `v ≠ 0`,
   `Module.End.HasEigenvector (Matrix.toLin' A) r v`, and `0 < r`, then `∀ i, 0 < v i`.
   Use `Matrix.isIrreducible_iff_exists_pow_pos`, pick `j` with `0 < v j`, and propagate through
   `A ^ k`.

3. Spectral-radius/eigenvector bridge. Partially done.
   Test whether `(spectralRadius ℝ A).toReal ∈ spectrum ℝ A` follows for nonnegative irreducible
   matrices. Generic real spectrum only gives `ρ ∈ spectrum ∨ -ρ ∈ spectrum`, so this may require
   Perron-specific work. The helper
   `exists_eigenvector_at_spectralRadius_of_mem_spectrum` proves that membership in real spectrum
   is enough to obtain a Lean eigenvector. The helper
   `exists_positive_eigenvector_at_spectralRadius_of_positive_eigenvector_of_spectralRadius_le`
   proves the other useful reduction: if a positive eigenpair `(r, v)` is known and one can prove
   the Perron maximality bound `spectralRadius ℝ A ≤ ‖r‖₊`, then the same `v` is an eigenvector at
   `(spectralRadius ℝ A).toReal`.

   Update: the Perron maximality bound is now proved as
   `spectralRadius_le_of_positive_subeigenvector`. The proof is coordinate-level
   Collatz-Wielandt: for each real eigenvector `w`, compare `|w|` against a positive vector `v` at
   a coordinate maximizing `|w i| / v i`.

4. Nonnegative Perron vector existence. Partially reduced to a fixed point theorem.
   This is now the main missing theorem. Possible approaches:
   * prove/import Brouwer fixed point for compact convex finite-dimensional real sets;
   * prove a dedicated Sperner/KKM theorem for `stdSimplex`;
   * avoid topology with a direct minimization proof of Collatz-Wielandt existence, which still
     needs a compactness/boundary argument.
   None appears packaged under Perron-Frobenius or Brouwer/Schauder names. `Submission.lean` defines
   `normalizedOneAddMulVec`, proves it is a continuous self-map of `stdSimplex ℝ n`, and proves
   `exists_positive_eigenvector_of_normalizedOneAddMulVec_fixed`: any fixed point gives a positive
   eigenvalue and strictly positive eigenvector of `A`.

   Update: `exists_positive_eigenvector_at_spectralRadius_of_normalizedOneAddMulVec_has_fixedPoint`
   now proves the exact corrected benchmark conclusion from only the existence of a fixed point of
   `normalizedOneAddMulVec A hA.nonneg`. The remaining blocker is a Brouwer-style fixed point
   theorem for continuous self-maps of the finite-dimensional simplex.

5. Last-sorry removal plan.
   Add a Mathlib-level theorem:
   ```lean
   theorem stdSimplex.exists_isFixedPt_of_continuous
       [Fintype n] [Nonempty n]
       (f : stdSimplex ℝ n → stdSimplex ℝ n) (hf : Continuous f) :
       ∃ x, Function.IsFixedPt f x
   ```
   Then the benchmark theorem closes by applying this theorem to
   `normalizedOneAddMulVec A hA.nonneg` and `continuous_normalizedOneAddMulVec`.

   Search result: this Mathlib snapshot has only the interval IVT fixed-point theorem
   `exists_mem_Icc_isFixedPt_of_mapsTo` and Banach contraction fixed points. It does not appear to
   have a higher-dimensional Brouwer/Schauder theorem or a no-retraction theorem that would make
   Brouwer a short specialization.

5. Final assembly.
   Once a nonzero nonnegative eigenvector at `(spectralRadius ℝ A).toReal` exists, combine it with
   phase 2 and package as the benchmark theorem. The helper
   `exists_positive_eigenvector_at_spectralRadius_of_nonnegative_eigenvector` now performs this
   assembly and derives positivity of `(spectralRadius ℝ A).toReal` from nonnegativity plus
   irreducibility.

Expected difficulty:

The positivity upgrade and spectral-radius comparison are now done. The full theorem is blocked on
fixed-point existence for `stdSimplex`; Mathlib has compactness and continuity infrastructure, but
no obvious Brouwer/Schauder fixed point theorem in this snapshot.
