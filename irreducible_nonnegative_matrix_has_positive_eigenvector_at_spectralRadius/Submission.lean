import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Max
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Function.Defs
import Mathlib.Tactic
import Mathlib.Data.Real.Archimedean
import Mathlib.Topology.Order.IntermediateValue

open scoped ENNReal Matrix
open scoped unitInterval

namespace PerronFrobenius

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
lemma mulVec_nonneg_of_nonneg {A : Matrix n n ℝ} {v : n → ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hv : ∀ i, 0 ≤ v i) :
    ∀ i, 0 ≤ (A *ᵥ v) i := by
  intro i
  simpa [Matrix.mulVec, dotProduct] using
    Finset.sum_nonneg (fun j _ => mul_nonneg (hA i j) (hv j))

lemma pow_nonneg_of_nonneg {A : Matrix n n ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) :
    ∀ i j, 0 ≤ (A ^ k) i j :=
  Matrix.pow_apply_nonneg hA k

omit [DecidableEq n] in
lemma exists_pos_coord_of_nonneg_ne_zero {v : n → ℝ}
    (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne : v ≠ 0) :
    ∃ i, 0 < v i := by
  by_contra h
  apply hv_ne
  funext i
  exact le_antisymm (le_of_not_gt fun hi => h ⟨i, hi⟩) (hv_nonneg i)

lemma mulVec_pos_of_pow_entry_pos {A : Matrix n n ℝ} {v : n → ℝ}
    (hA_nonneg : ∀ i j, 0 ≤ A i j) (hv_nonneg : ∀ i, 0 ≤ v i)
    {k : ℕ} {i j : n} (hAij : 0 < (A ^ k) i j) (hvj : 0 < v j) :
    0 < ((A ^ k) *ᵥ v) i := by
  simpa [Matrix.mulVec, dotProduct] using
    Finset.sum_pos'
      (fun l _ => mul_nonneg (pow_nonneg_of_nonneg hA_nonneg k i l) (hv_nonneg l))
      ⟨j, Finset.mem_univ j, mul_pos hAij hvj⟩

lemma exists_pos_pow_self_of_irreducible {A : Matrix n n ℝ}
    (hA : A.IsIrreducible) (i : n) :
    ∃ k > 0, 0 < (A ^ k) i i :=
  (Matrix.isIrreducible_iff_exists_pow_pos (A := A) hA.nonneg).mp hA i i

lemma pow_self_pos_mul_of_pow_self_pos {A : Matrix n n ℝ}
    (hA_nonneg : ∀ i j, 0 ≤ A i j) {i : n} {k : ℕ}
    (hk_pos : 0 < (A ^ k) i i) :
    ∀ l : ℕ, 0 < l → 0 < (A ^ (k * l)) i i := by
  intro l hl
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hl)
  induction m with
  | zero =>
      simpa using hk_pos
  | succ m ih =>
      rw [Nat.mul_succ, pow_add, Matrix.mul_apply]
      exact Finset.sum_pos'
        (fun j _ =>
          mul_nonneg (pow_nonneg_of_nonneg hA_nonneg (k * (m + 1)) i j)
            (pow_nonneg_of_nonneg hA_nonneg k j i))
        ⟨i, Finset.mem_univ i, mul_pos (ih (Nat.succ_pos m)) hk_pos⟩

lemma not_isNilpotent_of_isIrreducible [Nonempty n] {A : Matrix n n ℝ}
    (hA : A.IsIrreducible) :
    ¬ IsNilpotent A := by
  rintro ⟨m, hm⟩
  let i : n := Classical.choice ‹Nonempty n›
  obtain ⟨k, hk, hk_pos⟩ := exists_pos_pow_self_of_irreducible hA i
  have hpos : 0 < (A ^ (k * (m + 1))) i i :=
    pow_self_pos_mul_of_pow_self_pos hA.nonneg hk_pos (m + 1) (Nat.succ_pos m)
  have hle : m ≤ k * (m + 1) := by
    calc
      m ≤ m + 1 := Nat.le_succ m
      _ = 1 * (m + 1) := by simp
      _ ≤ k * (m + 1) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hk)
  have hpow_zero : A ^ (k * (m + 1)) = 0 := pow_eq_zero_of_le hle hm
  have hzero_entry : (A ^ (k * (m + 1))) i i = 0 := by simp [hpow_zero]
  exact (not_lt_of_ge (le_of_eq hzero_entry)) hpos

lemma eigenvalue_ne_zero_of_irreducible_nonnegative_eigenvector
    {A : Matrix n n ℝ} {r : ℝ} {v : n → ℝ}
    (hA : A.IsIrreducible)
    (hv_eigen : Module.End.HasEigenvector (Matrix.toLin' A) r v)
    (hv_nonneg : ∀ i, 0 ≤ v i) :
    r ≠ 0 := by
  obtain ⟨j, hvj⟩ := exists_pos_coord_of_nonneg_ne_zero hv_nonneg hv_eigen.2
  obtain ⟨k, hk, hpow_pos⟩ := exists_pos_pow_self_of_irreducible hA j
  have hAv_pos : 0 < ((A ^ k) *ᵥ v) j :=
    mulVec_pos_of_pow_entry_pos hA.nonneg hv_nonneg hpow_pos hvj
  have hpow_eigen : (A ^ k) *ᵥ v = r ^ k • v := by
    calc
      (A ^ k) *ᵥ v = Matrix.toLin' (A ^ k) v := by rw [Matrix.toLin'_apply]
      _ = (Matrix.toLin' A ^ k) v := by
        exact congrArg (fun f : Module.End ℝ (n → ℝ) => f v) (Matrix.toLin'_pow A k)
      _ = r ^ k • v := hv_eigen.pow_apply k
  intro hr
  have hcoord_pos : 0 < r ^ k * v j := by
    simpa [hpow_eigen, Pi.smul_apply] using hAv_pos
  have hzero_coord : r ^ k * v j = 0 := by simp [hr, hk.ne']
  exact (not_lt_of_ge (le_of_eq hzero_coord)) hcoord_pos

lemma eigenvalue_pos_of_irreducible_nonnegative_eigenvector
    {A : Matrix n n ℝ} {r : ℝ} {v : n → ℝ}
    (hA : A.IsIrreducible)
    (hv_eigen : Module.End.HasEigenvector (Matrix.toLin' A) r v)
    (hv_nonneg : ∀ i, 0 ≤ v i) (hr_nonneg : 0 ≤ r) :
    0 < r :=
  lt_of_le_of_ne hr_nonneg
    (Ne.symm (eigenvalue_ne_zero_of_irreducible_nonnegative_eigenvector hA hv_eigen hv_nonneg))

omit [DecidableEq n] in
lemma mem_stdSimplex_ne_zero [Nonempty n] {v : n → ℝ}
    (hv : v ∈ stdSimplex ℝ n) :
    v ≠ 0 := by
  intro hzero
  have hsum : (∑ i, v i) = 0 := by simp [hzero]
  linarith [hv.2]

omit [DecidableEq n] in
lemma normalize_mem_stdSimplex {w : n → ℝ}
    (hw_nonneg : ∀ i, 0 ≤ w i) (hsum_pos : 0 < ∑ i, w i) :
    (fun i => (∑ j, w j)⁻¹ * w i) ∈ stdSimplex ℝ n := by
  constructor
  · intro i
    exact mul_nonneg (inv_nonneg.mpr hsum_pos.le) (hw_nonneg i)
  · rw [← Finset.mul_sum]
    field_simp [hsum_pos.ne']

lemma one_add_mulVec_sum_pos [Nonempty n] {A : Matrix n n ℝ} {v : n → ℝ}
    (hA_nonneg : ∀ i j, 0 ≤ A i j) (hv : v ∈ stdSimplex ℝ n) :
    0 < ∑ i, ((A + 1) *ᵥ v) i := by
  have hAv_nonneg : ∀ i, 0 ≤ (A *ᵥ v) i :=
    mulVec_nonneg_of_nonneg hA_nonneg hv.1
  have hsum_A_nonneg : 0 ≤ ∑ i, (A *ᵥ v) i :=
    Finset.sum_nonneg fun i _ => hAv_nonneg i
  have hpos : 0 < (∑ i, (A *ᵥ v) i) + 1 := by linarith
  simpa [Matrix.add_mulVec, Finset.sum_add_distrib, hv.2, add_comm, add_left_comm, add_assoc]
    using hpos

lemma normalize_one_add_mulVec_mem_stdSimplex [Nonempty n]
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j) (v : stdSimplex ℝ n) :
    (fun i =>
      (∑ j, ((A + 1) *ᵥ (v : n → ℝ)) j)⁻¹ *
        ((A + 1) *ᵥ (v : n → ℝ)) i) ∈ stdSimplex ℝ n := by
  refine normalize_mem_stdSimplex ?_ (one_add_mulVec_sum_pos hA_nonneg v.2)
  intro i
  rw [Matrix.add_mulVec, Pi.add_apply]
  exact add_nonneg (mulVec_nonneg_of_nonneg hA_nonneg v.2.1 i) (by simp)

noncomputable def normalizedOneAddMulVec [Nonempty n]
    (A : Matrix n n ℝ) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    stdSimplex ℝ n → stdSimplex ℝ n :=
  fun v =>
    ⟨(fun i =>
      (∑ j, ((A + 1) *ᵥ (v : n → ℝ)) j)⁻¹ *
        ((A + 1) *ᵥ (v : n → ℝ)) i),
      normalize_one_add_mulVec_mem_stdSimplex hA_nonneg v⟩

lemma continuous_normalizedOneAddMulVec [Nonempty n]
    (A : Matrix n n ℝ) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    Continuous (normalizedOneAddMulVec A hA_nonneg) := by
  apply Continuous.subtype_mk
  have hmul :
      Continuous fun v : stdSimplex ℝ n => (A + 1) *ᵥ (v : n → ℝ) :=
    (LinearMap.continuous_of_finiteDimensional ((A + 1).mulVecLin)).comp continuous_subtype_val
  have hsum :
      Continuous fun v : stdSimplex ℝ n => ∑ j, ((A + 1) *ᵥ (v : n → ℝ)) j :=
    continuous_finset_sum _ fun j _ => (continuous_apply j).comp hmul
  apply continuous_pi
  intro i
  exact (hsum.inv₀ fun v => (one_add_mulVec_sum_pos hA_nonneg v.2).ne').mul
    ((continuous_apply i).comp hmul)

lemma exists_nonnegative_eigenvector_of_normalized_one_add_fixed [Nonempty n]
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {v : n → ℝ} (hv : v ∈ stdSimplex ℝ n)
    (hfixed :
      (fun i =>
        (∑ j, ((A + 1) *ᵥ v) j)⁻¹ *
          ((A + 1) *ᵥ v) i) = v) :
    ∃ r : ℝ,
      Module.End.HasEigenvector (Matrix.toLin' A) r v ∧ 0 ≤ r ∧ ∀ i, 0 ≤ v i := by
  let s : ℝ := ∑ j, ((A + 1) *ᵥ v) j
  have hs_pos : 0 < s := one_add_mulVec_sum_pos hA_nonneg hv
  have hs_ne : s ≠ 0 := hs_pos.ne'
  have hw_eq : (A + 1) *ᵥ v = s • v := by
    funext i
    have hi := congrFun hfixed i
    calc
      ((A + 1) *ᵥ v) i = s * (s⁻¹ * ((A + 1) *ᵥ v) i) := by
        field_simp [hs_ne]
      _ = s * v i := by rw [hi]
      _ = (s • v) i := by simp
  have hA_eigen : A *ᵥ v = (s - 1) • v := by
    funext i
    have hi := congrFun hw_eq i
    have hi' : (A *ᵥ v) i + v i = s * v i := by
      simpa [Matrix.add_mulVec, Pi.smul_apply] using hi
    calc
      (A *ᵥ v) i = (s - 1) * v i := by nlinarith
      _ = ((s - 1) • v) i := by simp
  have hr_nonneg : 0 ≤ s - 1 := by
    have hAv_nonneg : ∀ i, 0 ≤ (A *ᵥ v) i :=
      mulVec_nonneg_of_nonneg hA_nonneg hv.1
    have hsum_A_nonneg : 0 ≤ ∑ i, (A *ᵥ v) i :=
      Finset.sum_nonneg fun i _ => hAv_nonneg i
    have hs_eq : s = (∑ i, (A *ᵥ v) i) + 1 := by
      simp [s, Matrix.add_mulVec, Finset.sum_add_distrib, hv.2, add_comm]
    rw [hs_eq]
    linarith
  refine ⟨s - 1, ⟨?_, mem_stdSimplex_ne_zero hv⟩, hr_nonneg, hv.1⟩
  · rw [Module.End.mem_eigenspace_iff]
    ext i
    simpa [Matrix.toLin'_apply, Pi.smul_apply] using congrFun hA_eigen i

lemma exists_nonnegative_eigenvector_of_normalizedOneAddMulVec_fixed [Nonempty n]
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {v : stdSimplex ℝ n}
    (hfixed : Function.IsFixedPt (normalizedOneAddMulVec A hA_nonneg) v) :
    ∃ r : ℝ,
      Module.End.HasEigenvector (Matrix.toLin' A) r (v : n → ℝ) ∧
        0 ≤ r ∧ ∀ i, 0 ≤ (v : n → ℝ) i := by
  apply exists_nonnegative_eigenvector_of_normalized_one_add_fixed hA_nonneg v.2
  exact congrArg Subtype.val hfixed

lemma exists_nonnegative_eigenvector_of_normalizedOneAddMulVec_has_fixedPoint [Nonempty n]
    {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j)
    (hfp : ∃ v : stdSimplex ℝ n,
      Function.IsFixedPt (normalizedOneAddMulVec A hA_nonneg) v) :
    ∃ r : ℝ, ∃ v : n → ℝ,
      Module.End.HasEigenvector (Matrix.toLin' A) r v ∧ 0 ≤ r ∧ ∀ i, 0 ≤ v i := by
  obtain ⟨v, hv⟩ := hfp
  obtain ⟨r, hr_eigen, hr_nonneg, hv_nonneg⟩ :=
    exists_nonnegative_eigenvector_of_normalizedOneAddMulVec_fixed hA_nonneg hv
  exact ⟨r, v, hr_eigen, hr_nonneg, hv_nonneg⟩

lemma positive_of_irreducible_nonnegative_eigenvector
    {A : Matrix n n ℝ} {r : ℝ} {v : n → ℝ}
    (hA : A.IsIrreducible)
    (hv_eigen : Module.End.HasEigenvector (Matrix.toLin' A) r v)
    (hv_nonneg : ∀ i, 0 ≤ v i) (hr : 0 < r) :
    ∀ i, 0 < v i := by
  obtain ⟨j, hvj⟩ := exists_pos_coord_of_nonneg_ne_zero hv_nonneg hv_eigen.2
  intro i
  obtain ⟨k, _hk_pos, hpow_pos⟩ :=
    (Matrix.isIrreducible_iff_exists_pow_pos (A := A) hA.nonneg).mp hA i j
  have hAv_pos : 0 < ((A ^ k) *ᵥ v) i :=
    mulVec_pos_of_pow_entry_pos hA.nonneg hv_nonneg hpow_pos hvj
  have hpow_eigen : (A ^ k) *ᵥ v = r ^ k • v := by
    calc
      (A ^ k) *ᵥ v = Matrix.toLin' (A ^ k) v := by rw [Matrix.toLin'_apply]
      _ = (Matrix.toLin' A ^ k) v := by
        exact congrArg (fun f : Module.End ℝ (n → ℝ) => f v) (Matrix.toLin'_pow A k)
      _ = r ^ k • v := hv_eigen.pow_apply k
  have hcoord_pos : 0 < r ^ k * v i := by
    simpa [hpow_eigen, Pi.smul_apply] using hAv_pos
  have hcoord_pos' : 0 < v i * r ^ k := by
    simpa [mul_comm] using hcoord_pos
  exact pos_of_mul_pos_left hcoord_pos' (le_of_lt (pow_pos hr k))

lemma exists_positive_eigenvector_of_normalizedOneAddMulVec_fixed [Nonempty n]
    {A : Matrix n n ℝ} (hA : A.IsIrreducible)
    {v : stdSimplex ℝ n}
    (hfixed : Function.IsFixedPt (normalizedOneAddMulVec A hA.nonneg) v) :
    ∃ r : ℝ,
      Module.End.HasEigenvector (Matrix.toLin' A) r (v : n → ℝ) ∧
        0 < r ∧ ∀ i, 0 < (v : n → ℝ) i := by
  obtain ⟨r, hr_eigen, hr_nonneg, hv_nonneg⟩ :=
    exists_nonnegative_eigenvector_of_normalizedOneAddMulVec_fixed hA.nonneg hfixed
  have hr_pos : 0 < r :=
    eigenvalue_pos_of_irreducible_nonnegative_eigenvector hA hr_eigen hv_nonneg hr_nonneg
  exact ⟨r, hr_eigen, hr_pos,
    positive_of_irreducible_nonnegative_eigenvector hA hr_eigen hv_nonneg hr_pos⟩

lemma exists_positive_eigenvector_of_normalizedOneAddMulVec_has_fixedPoint [Nonempty n]
    {A : Matrix n n ℝ} (hA : A.IsIrreducible)
    (hfp : ∃ v : stdSimplex ℝ n,
      Function.IsFixedPt (normalizedOneAddMulVec A hA.nonneg) v) :
    ∃ r : ℝ, ∃ v : n → ℝ,
      Module.End.HasEigenvector (Matrix.toLin' A) r v ∧ 0 < r ∧ ∀ i, 0 < v i := by
  obtain ⟨v, hv⟩ := hfp
  obtain ⟨r, hr_eigen, hr_pos, hv_pos⟩ :=
    exists_positive_eigenvector_of_normalizedOneAddMulVec_fixed hA hv
  exact ⟨r, v, hr_eigen, hr_pos, hv_pos⟩

lemma exists_positive_eigenvector_at_spectralRadius_of_nonnegative_eigenvector
    {A : Matrix n n ℝ} (hA : A.IsIrreducible)
    (hperron :
      ∃ v : n → ℝ,
        Module.End.HasEigenvector (Matrix.toLin' A) (spectralRadius ℝ A).toReal v ∧
          ∀ i, 0 ≤ v i) :
    ∃ v : n → ℝ,
      Module.End.HasEigenvector (Matrix.toLin' A) (spectralRadius ℝ A).toReal v ∧
        ∀ i, 0 < v i := by
  obtain ⟨v, hv_eigen, hv_nonneg⟩ := hperron
  have hρ_pos : 0 < (spectralRadius ℝ A).toReal :=
    eigenvalue_pos_of_irreducible_nonnegative_eigenvector hA hv_eigen hv_nonneg
      ENNReal.toReal_nonneg
  exact ⟨v, hv_eigen,
    positive_of_irreducible_nonnegative_eigenvector hA hv_eigen hv_nonneg hρ_pos⟩

lemma hasEigenvalue_toLin'_of_mem_spectrum
    {A : Matrix n n ℝ} {μ : ℝ} (hμ : μ ∈ spectrum ℝ A) :
    Module.End.HasEigenvalue (Matrix.toLin' A) μ := by
  rw [← Matrix.spectrum_toLin'] at hμ
  exact Module.End.HasEigenvalue.of_mem_spectrum hμ

lemma eigenvector_nnnorm_le_spectralRadius
    {A : Matrix n n ℝ} {r : ℝ} {v : n → ℝ}
    (hv : Module.End.HasEigenvector (Matrix.toLin' A) r v) :
    (‖r‖₊ : ℝ≥0∞) ≤ spectralRadius ℝ A := by
  have hmem : r ∈ spectrum ℝ A := by
    rw [← Matrix.spectrum_toLin']
    exact (Module.End.hasEigenvalue_of_hasEigenvector hv).mem_spectrum
  exact le_iSup₂ (α := ℝ≥0∞) r hmem

omit [DecidableEq n] in
lemma abs_mulVec_le_mulVec_abs {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j)
    (w : n → ℝ) :
    ∀ i, |(A *ᵥ w) i| ≤ (A *ᵥ fun j => |w j|) i := by
  intro i
  calc
    |(A *ᵥ w) i| = |∑ j, A i j * w j| := by
      simp [Matrix.mulVec, dotProduct]
    _ ≤ ∑ j, |A i j * w j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, A i j * |w j| := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [abs_mul, abs_of_nonneg (hA_nonneg i j)]
    _ = (A *ᵥ fun j => |w j|) i := by
      simp [Matrix.mulVec, dotProduct]

omit [DecidableEq n] in
lemma mulVec_abs_le_mul_mulVec_of_abs_le_mul
    {A : Matrix n n ℝ} {v w : n → ℝ} {c : ℝ}
    (hA_nonneg : ∀ i j, 0 ≤ A i j) (hw : ∀ j, |w j| ≤ c * v j) :
    ∀ i, (A *ᵥ fun j => |w j|) i ≤ c * (A *ᵥ v) i := by
  intro i
  calc
    (A *ᵥ fun j => |w j|) i = ∑ j, A i j * |w j| := by
      simp [Matrix.mulVec, dotProduct]
    _ ≤ ∑ j, A i j * (c * v j) := by
      exact Finset.sum_le_sum fun j _hj =>
        mul_le_mul_of_nonneg_left (hw j) (hA_nonneg i j)
    _ = c * (∑ j, A i j * v j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = c * (A *ᵥ v) i := by
      simp [Matrix.mulVec, dotProduct]

lemma eigenvalue_abs_le_of_positive_subeigenvector [Nonempty n]
    {A : Matrix n n ℝ} {r μ : ℝ} {v w : n → ℝ}
    (hA_nonneg : ∀ i j, 0 ≤ A i j) (hv_pos : ∀ i, 0 < v i)
    (hAv_le : ∀ i, (A *ᵥ v) i ≤ r * v i)
    (hw_eigen : Module.End.HasEigenvector (Matrix.toLin' A) μ w) :
    |μ| ≤ r := by
  obtain ⟨j, hwj_ne⟩ : ∃ j, w j ≠ 0 := by
    by_contra h
    apply hw_eigen.2
    funext j
    exact Classical.not_not.mp fun hj => h ⟨j, hj⟩
  let ratio : n → ℝ := fun i => |w i| / v i
  obtain ⟨i, _hi_mem, hi_max⟩ :
      ∃ i ∈ (Finset.univ : Finset n), ∀ j ∈ (Finset.univ : Finset n), ratio j ≤ ratio i :=
    Finset.exists_max_image (Finset.univ : Finset n) ratio
      ⟨Classical.choice ‹Nonempty n›, Finset.mem_univ _⟩
  let c : ℝ := ratio i
  have hc_eq : c = |w i| / v i := rfl
  have hj_ratio_pos : 0 < ratio j := div_pos (abs_pos.mpr hwj_ne) (hv_pos j)
  have hc_pos : 0 < c := lt_of_lt_of_le hj_ratio_pos (hi_max j (Finset.mem_univ j))
  have hwi_pos : 0 < |w i| := by
    have : 0 < c * v i := mul_pos hc_pos (hv_pos i)
    rwa [hc_eq, div_mul_cancel₀ _ (ne_of_gt (hv_pos i))] at this
  have hw_le : ∀ j, |w j| ≤ c * v j := by
    intro j
    have hratio : |w j| / v j ≤ c := hi_max j (Finset.mem_univ j)
    exact (div_le_iff₀ (hv_pos j)).mp hratio
  have hAw : A *ᵥ w = μ • w := by
    simpa [Matrix.toLin'_apply] using hw_eigen.apply_eq_smul
  have habs_eigen : |μ| * |w i| = |(A *ᵥ w) i| := by
    rw [hAw, Pi.smul_apply, smul_eq_mul, abs_mul]
  have hcvi_eq : c * v i = |w i| := by
    rw [hc_eq, div_mul_cancel₀ _ (ne_of_gt (hv_pos i))]
  have hmain : |μ| * |w i| ≤ r * |w i| := by
    calc
      |μ| * |w i| = |(A *ᵥ w) i| := habs_eigen
      _ ≤ (A *ᵥ fun j => |w j|) i := abs_mulVec_le_mulVec_abs hA_nonneg w i
      _ ≤ c * (A *ᵥ v) i := mulVec_abs_le_mul_mulVec_of_abs_le_mul hA_nonneg hw_le i
      _ ≤ c * (r * v i) := mul_le_mul_of_nonneg_left (hAv_le i) hc_pos.le
      _ = r * |w i| := by
        calc
          c * (r * v i) = r * (c * v i) := by ring
          _ = r * |w i| := by rw [hcvi_eq]
  nlinarith [hmain, hwi_pos]

lemma spectralRadius_le_of_positive_subeigenvector [Nonempty n]
    {A : Matrix n n ℝ} {r : ℝ} {v : n → ℝ}
    (hA_nonneg : ∀ i j, 0 ≤ A i j) (hr_nonneg : 0 ≤ r)
    (hv_pos : ∀ i, 0 < v i) (hAv_le : ∀ i, (A *ᵥ v) i ≤ r * v i) :
    spectralRadius ℝ A ≤ (‖r‖₊ : ℝ≥0∞) := by
  refine iSup₂_le fun μ hμ => ?_
  obtain ⟨w, hw_eigen⟩ := (hasEigenvalue_toLin'_of_mem_spectrum hμ).exists_hasEigenvector
  have hμ_abs_le : |μ| ≤ r :=
    eigenvalue_abs_le_of_positive_subeigenvector hA_nonneg hv_pos hAv_le hw_eigen
  have hnn : ‖μ‖₊ ≤ ‖r‖₊ := by
    rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hr_nonneg]
    exact hμ_abs_le
  exact_mod_cast hnn

lemma spectralRadius_toReal_eq_of_eigenvector_of_spectralRadius_le
    {A : Matrix n n ℝ} {r : ℝ} {v : n → ℝ}
    (hv : Module.End.HasEigenvector (Matrix.toLin' A) r v) (hr : 0 ≤ r)
    (hρ_le : spectralRadius ℝ A ≤ (‖r‖₊ : ℝ≥0∞)) :
    (spectralRadius ℝ A).toReal = r := by
  have hle : (‖r‖₊ : ℝ≥0∞) ≤ spectralRadius ℝ A :=
    eigenvector_nnnorm_le_spectralRadius hv
  have hρ_eq : spectralRadius ℝ A = (‖r‖₊ : ℝ≥0∞) :=
    le_antisymm hρ_le hle
  simp [hρ_eq, Real.norm_of_nonneg hr]

lemma exists_positive_eigenvector_at_spectralRadius_of_positive_eigenvector_of_spectralRadius_le
    {A : Matrix n n ℝ} {r : ℝ} {v : n → ℝ}
    (hv_eigen : Module.End.HasEigenvector (Matrix.toLin' A) r v)
    (hr_pos : 0 < r) (hv_pos : ∀ i, 0 < v i)
    (hρ_le : spectralRadius ℝ A ≤ (‖r‖₊ : ℝ≥0∞)) :
    ∃ w : n → ℝ,
      Module.End.HasEigenvector (Matrix.toLin' A) (spectralRadius ℝ A).toReal w ∧
        ∀ i, 0 < w i := by
  have hρ_eq :
      (spectralRadius ℝ A).toReal = r :=
    spectralRadius_toReal_eq_of_eigenvector_of_spectralRadius_le hv_eigen hr_pos.le hρ_le
  exact ⟨v, by simpa [hρ_eq] using hv_eigen, hv_pos⟩

lemma exists_positive_eigenvector_at_spectralRadius_of_positive_eigenvector [Nonempty n]
    {A : Matrix n n ℝ} {r : ℝ} {v : n → ℝ}
    (hA_nonneg : ∀ i j, 0 ≤ A i j)
    (hv_eigen : Module.End.HasEigenvector (Matrix.toLin' A) r v)
    (hr_pos : 0 < r) (hv_pos : ∀ i, 0 < v i) :
    ∃ w : n → ℝ,
      Module.End.HasEigenvector (Matrix.toLin' A) (spectralRadius ℝ A).toReal w ∧
        ∀ i, 0 < w i := by
  have hAv_eq : A *ᵥ v = r • v := by
    simpa [Matrix.toLin'_apply] using hv_eigen.apply_eq_smul
  have hAv_le : ∀ i, (A *ᵥ v) i ≤ r * v i := by
    intro i
    rw [hAv_eq, Pi.smul_apply, smul_eq_mul]
  exact
    exists_positive_eigenvector_at_spectralRadius_of_positive_eigenvector_of_spectralRadius_le
      hv_eigen hr_pos hv_pos
      (spectralRadius_le_of_positive_subeigenvector hA_nonneg hr_pos.le hv_pos hAv_le)

lemma exists_positive_eigenvector_at_spectralRadius_of_normalizedOneAddMulVec_fixed [Nonempty n]
    {A : Matrix n n ℝ} (hA : A.IsIrreducible)
    {v : stdSimplex ℝ n}
    (hfixed : Function.IsFixedPt (normalizedOneAddMulVec A hA.nonneg) v) :
    ∃ w : n → ℝ,
      Module.End.HasEigenvector (Matrix.toLin' A) (spectralRadius ℝ A).toReal w ∧
        ∀ i, 0 < w i := by
  obtain ⟨r, hr_eigen, hr_pos, hv_pos⟩ :=
    exists_positive_eigenvector_of_normalizedOneAddMulVec_fixed hA hfixed
  exact exists_positive_eigenvector_at_spectralRadius_of_positive_eigenvector hA.nonneg
    hr_eigen hr_pos hv_pos

lemma exists_positive_eigenvector_at_spectralRadius_of_normalizedOneAddMulVec_has_fixedPoint
    [Nonempty n] {A : Matrix n n ℝ} (hA : A.IsIrreducible)
    (hfp : ∃ v : stdSimplex ℝ n,
      Function.IsFixedPt (normalizedOneAddMulVec A hA.nonneg) v) :
    ∃ w : n → ℝ,
      Module.End.HasEigenvector (Matrix.toLin' A) (spectralRadius ℝ A).toReal w ∧
        ∀ i, 0 < w i := by
  obtain ⟨v, hv⟩ := hfp
  exact exists_positive_eigenvector_at_spectralRadius_of_normalizedOneAddMulVec_fixed hA hv

lemma exists_eigenvector_at_spectralRadius_of_mem_spectrum
    {A : Matrix n n ℝ}
    (hρ : (spectralRadius ℝ A).toReal ∈ spectrum ℝ A) :
    ∃ v : n → ℝ,
      Module.End.HasEigenvector (Matrix.toLin' A) (spectralRadius ℝ A).toReal v := by
  exact (hasEigenvalue_toLin'_of_mem_spectrum hρ).exists_hasEigenvector

lemma unitInterval_exists_isFixedPt_of_continuous
    (f : unitInterval → unitInterval) (hf : Continuous f) :
    ∃ x, Function.IsFixedPt f x := by
  obtain ⟨x, hx⟩ :=
    intermediate_value_univ₂ (a := (0 : unitInterval)) (b := (1 : unitInterval))
      continuous_subtype_val (continuous_subtype_val.comp hf)
      (unitInterval.nonneg (f 0)) (unitInterval.le_one (f 1))
  exact ⟨x, Subtype.ext hx.symm⟩

lemma stdSimplex_fin_two_exists_isFixedPt_of_continuous
    (f : stdSimplex ℝ (Fin 2) → stdSimplex ℝ (Fin 2))
    (hf : Continuous f) :
    ∃ x, Function.IsFixedPt f x := by
  let e := stdSimplexHomeomorphUnitInterval
  let g : unitInterval → unitInterval := fun x => e (f (e.symm x))
  have hg : Continuous g := e.continuous.comp (hf.comp e.symm.continuous)
  obtain ⟨x, hx⟩ := unitInterval_exists_isFixedPt_of_continuous g hg
  refine ⟨e.symm x, ?_⟩
  apply e.injective
  exact hx

lemma exists_positive_eigenvector_at_spectralRadius_fin_two
    {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.IsIrreducible) :
    ∃ v : Fin 2 → ℝ,
      Module.End.HasEigenvector (Matrix.toLin' A) (spectralRadius ℝ A).toReal v ∧
        (∀ i, 0 < v i) := by
  exact
    exists_positive_eigenvector_at_spectralRadius_of_normalizedOneAddMulVec_has_fixedPoint
      hA
      (stdSimplex_fin_two_exists_isFixedPt_of_continuous
        (normalizedOneAddMulVec A hA.nonneg)
        (continuous_normalizedOneAddMulVec A hA.nonneg))

/-- Integer grid points of mesh `1 / N` in the standard simplex. -/
def simplexGrid (N : ℕ) : Type _ :=
  {a : n → ℕ // ∑ i, a i = N}

namespace simplexGrid

noncomputable instance instFintype (N : ℕ) : Fintype (simplexGrid (n := n) N) :=
  Fintype.ofInjective
    (fun a : simplexGrid (n := n) N =>
      fun i : n =>
        (⟨a.1 i, Nat.lt_succ_of_le <| by
          have hi_le : a.1 i ≤ ∑ j, a.1 j :=
            Finset.single_le_sum (fun j _ => Nat.zero_le (a.1 j)) (Finset.mem_univ i)
          simpa [a.2] using hi_le⟩ : Fin (N + 1)))
    (by
      intro a b hab
      apply Subtype.ext
      funext i
      exact congrArg Fin.val (congrFun hab i))

noncomputable instance instDecidableEq (N : ℕ) :
    DecidableEq (simplexGrid (n := n) N) :=
  Classical.decEq _

noncomputable def toStdSimplex {N : ℕ} (hN : 0 < N) (a : simplexGrid (n := n) N) :
    stdSimplex ℝ n := by
  refine ⟨fun i => (a.1 i : ℝ) / (N : ℝ), ?_⟩
  constructor
  · intro i
    positivity
  · rw [← Finset.sum_div]
    rw [← Nat.cast_sum, a.2]
    field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)]

omit [DecidableEq n] in
lemma dist_toStdSimplex_le_of_forall_abs_sub_le {N : ℕ} (hN : 0 < N)
    {C : ℝ} (hC : 0 ≤ C) {a b : simplexGrid (n := n) N}
    (hcoord : ∀ i, |(a.1 i : ℝ) - (b.1 i : ℝ)| ≤ C) :
    dist (toStdSimplex hN a) (toStdSimplex hN b) ≤ C / (N : ℝ) := by
  change dist (fun i : n => (a.1 i : ℝ) / (N : ℝ))
      (fun i : n => (b.1 i : ℝ) / (N : ℝ)) ≤ C / (N : ℝ)
  rw [dist_pi_le_iff (div_nonneg hC (by positivity))]
  intro i
  rw [Real.dist_eq]
  have hdiv :
      (a.1 i : ℝ) / (N : ℝ) - (b.1 i : ℝ) / (N : ℝ) =
        ((a.1 i : ℝ) - (b.1 i : ℝ)) / (N : ℝ) := by
    ring
  rw [hdiv, abs_div]
  have hNabs : |(N : ℝ)| = (N : ℝ) := abs_of_pos (Nat.cast_pos.mpr hN)
  rw [hNabs]
  exact div_le_div_of_nonneg_right (hcoord i) (by positivity)

def vertex (N : ℕ) (i : n) : simplexGrid (n := n) N :=
  ⟨fun j => if j = i then N else 0, by simp⟩

@[simp]
lemma vertex_apply_self (N : ℕ) (i : n) :
    (vertex (n := n) N i).1 i = N := by
  simp [vertex]

@[simp]
lemma vertex_apply_ne (N : ℕ) {i j : n} (hij : j ≠ i) :
    (vertex (n := n) N i).1 j = 0 := by
  simp [vertex, hij]

lemma color_vertex_of_boundary {N : ℕ} (c : simplexGrid (n := n) N → n)
    (hc : ∀ (a : simplexGrid (n := n) N) (i : n), a.1 i = 0 → c a ≠ i) (i : n) :
    c (vertex (n := n) N i) = i := by
  by_contra hne
  have hzero : (vertex (n := n) N i).1 (c (vertex (n := n) N i)) = 0 := by
    exact vertex_apply_ne (n := n) N hne
  exact (hc (vertex (n := n) N i) (c (vertex (n := n) N i)) hzero) rfl

lemma color_surjective_of_boundary {N : ℕ} (c : simplexGrid (n := n) N → n)
    (hc : ∀ (a : simplexGrid (n := n) N) (i : n), a.1 i = 0 → c a ≠ i) :
    Function.Surjective c := by
  intro i
  exact ⟨vertex (n := n) N i, color_vertex_of_boundary c hc i⟩

lemma exists_color_of_boundary {N : ℕ} (c : simplexGrid (n := n) N → n)
    (hc : ∀ (a : simplexGrid (n := n) N) (i : n), a.1 i = 0 → c a ≠ i) (i : n) :
    ∃ a : simplexGrid (n := n) N, c a = i :=
  color_surjective_of_boundary c hc i

lemma image_univ_color_of_boundary {N : ℕ} (c : simplexGrid (n := n) N → n)
    (hc : ∀ (a : simplexGrid (n := n) N) (i : n), a.1 i = 0 → c a ≠ i) :
    (Finset.univ.image c : Finset n) = Finset.univ := by
  classical
  apply Finset.ext
  intro i
  simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
  exact exists_color_of_boundary c hc i

def UnitClose {N : ℕ} (a b : simplexGrid (n := n) N) : Prop :=
  ∀ j : n, |(a.1 j : ℝ) - (b.1 j : ℝ)| ≤ (1 : ℝ)

noncomputable def reindex {m : Type*} [Fintype m] (e : n ≃ m) {N : ℕ} :
    simplexGrid (n := n) N ≃ simplexGrid (n := m) N where
  toFun a :=
    ⟨fun j => a.1 (e.symm j), by
      simpa [a.2] using (Equiv.sum_comp e.symm a.1)⟩
  invFun a :=
    ⟨fun i => a.1 (e i), by
      simpa [a.2] using (Equiv.sum_comp e a.1)⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    simp
  right_inv a := by
    apply Subtype.ext
    funext i
    simp

omit [DecidableEq n] in
@[simp]
lemma reindex_apply {m : Type*} [Fintype m] (e : n ≃ m) {N : ℕ}
    (a : simplexGrid (n := n) N) (j : m) :
    ((reindex (n := n) e) a).1 j = a.1 (e.symm j) :=
  rfl

omit [DecidableEq n] in
@[simp]
lemma reindex_symm_apply {m : Type*} [Fintype m] (e : n ≃ m) {N : ℕ}
    (a : simplexGrid (n := m) N) (i : n) :
    ((reindex (n := n) e).symm a).1 i = a.1 (e i) :=
  rfl

omit [DecidableEq n] in
lemma unitClose_reindex_iff {m : Type*} [Fintype m] (e : n ≃ m) {N : ℕ}
    {a b : simplexGrid (n := n) N} :
    UnitClose (n := m) ((reindex (n := n) e) a) ((reindex (n := n) e) b) ↔
      UnitClose (n := n) a b := by
  constructor
  · intro h i
    simpa using h (e i)
  · intro h j
    simpa using h (e.symm j)

omit [DecidableEq n] in
lemma unitClose_refl {N : ℕ} (a : simplexGrid (n := n) N) :
    UnitClose (n := n) a a := by
  intro j
  simp

omit [DecidableEq n] in
lemma unitClose_symm {N : ℕ} {a b : simplexGrid (n := n) N}
    (h : UnitClose (n := n) a b) :
    UnitClose (n := n) b a := by
  intro j
  simpa [UnitClose, abs_sub_comm] using h j

def FullyLabeledUnitCluster {N : ℕ} (c : simplexGrid (n := n) N → n)
    (base : simplexGrid (n := n) N) : Prop :=
  ∀ i : n, ∃ a : simplexGrid (n := n) N, c a = i ∧ UnitClose (n := n) a base

noncomputable def reindexColor {m : Type*} [Fintype m] (e : n ≃ m) {N : ℕ}
    (c : simplexGrid (n := n) N → n) :
    simplexGrid (n := m) N → m :=
  fun a => e (c ((reindex (n := n) e).symm a))

omit [DecidableEq n] in
lemma fullyLabeledUnitCluster_of_reindexColor {m : Type*} [Fintype m] (e : n ≃ m)
    {N : ℕ} (c : simplexGrid (n := n) N → n)
    {base : simplexGrid (n := m) N}
    (hfull :
      FullyLabeledUnitCluster (n := m) (reindexColor (n := n) e c) base) :
    FullyLabeledUnitCluster (n := n) c ((reindex (n := n) e).symm base) := by
  intro i
  obtain ⟨a, hcolor, hclose⟩ := hfull (e i)
  refine ⟨(reindex (n := n) e).symm a, ?_, ?_⟩
  · exact e.injective hcolor
  · rw [← unitClose_reindex_iff (n := n) e]
    simpa using hclose

omit [DecidableEq n] in
lemma reindexColor_boundary {m : Type*} [Fintype m] (e : n ≃ m) {N : ℕ}
    (c : simplexGrid (n := n) N → n)
    (hc : ∀ (a : simplexGrid (n := n) N) (i : n), a.1 i = 0 → c a ≠ i) :
    ∀ (a : simplexGrid (n := m) N) (j : m),
      a.1 j = 0 → reindexColor (n := n) e c a ≠ j := by
  intro a j hj hcolor
  have hc_eq : c ((reindex (n := n) e).symm a) = e.symm j := by
    exact e.injective (by simpa [reindexColor] using hcolor)
  have hcoord :
      ((reindex (n := n) e).symm a).1 (e.symm j) = 0 := by
    simpa using hj
  exact hc ((reindex (n := n) e).symm a) (e.symm j) hcoord hc_eq

omit [DecidableEq n] in
lemma exists_fullyLabeledUnitCluster_of_reindexColor_exists {m : Type*} [Fintype m]
    (e : n ≃ m) {N : ℕ} (c : simplexGrid (n := n) N → n)
    (h :
      ∃ base : simplexGrid (n := m) N,
        FullyLabeledUnitCluster (n := m) (reindexColor (n := n) e c) base) :
    ∃ base : simplexGrid (n := n) N,
      FullyLabeledUnitCluster (n := n) c base := by
  obtain ⟨base, hbase⟩ := h
  exact ⟨(reindex (n := n) e).symm base,
    fullyLabeledUnitCluster_of_reindexColor e c hbase⟩

omit [DecidableEq n] in
lemma exists_fullyLabeledUnitCluster_of_fin_card_case [Nonempty n] {N : ℕ}
    (c : simplexGrid (n := n) N → n)
    (hc : ∀ (a : simplexGrid (n := n) N) (i : n), a.1 i = 0 → c a ≠ i)
    (hfin :
      ∀ cfin : simplexGrid (n := Fin (Fintype.card n)) N → Fin (Fintype.card n),
        (∀ (a : simplexGrid (n := Fin (Fintype.card n)) N) (i : Fin (Fintype.card n)),
          a.1 i = 0 → cfin a ≠ i) →
          ∃ base : simplexGrid (n := Fin (Fintype.card n)) N,
            FullyLabeledUnitCluster (n := Fin (Fintype.card n)) cfin base) :
    ∃ base : simplexGrid (n := n) N,
      FullyLabeledUnitCluster (n := n) c base := by
  classical
  let e : n ≃ Fin (Fintype.card n) := Fintype.equivFin n
  exact exists_fullyLabeledUnitCluster_of_reindexColor_exists e c
    (hfin (reindexColor (n := n) e c) (reindexColor_boundary e c hc))

noncomputable def unitNeighborhood (N : ℕ) (base : simplexGrid (n := n) N) :
    Finset (simplexGrid (n := n) N) :=
  by
    classical
    exact Finset.univ.filter fun a => UnitClose (n := n) a base

lemma mem_unitNeighborhood {N : ℕ} {base a : simplexGrid (n := n) N} :
    a ∈ unitNeighborhood (n := n) N base ↔ UnitClose (n := n) a base := by
  classical
  simp [unitNeighborhood]

lemma base_mem_unitNeighborhood {N : ℕ} (base : simplexGrid (n := n) N) :
    base ∈ unitNeighborhood (n := n) N base := by
  exact mem_unitNeighborhood.mpr (unitClose_refl base)

lemma color_mem_unitNeighborhood_image {N : ℕ} (c : simplexGrid (n := n) N → n)
    (base : simplexGrid (n := n) N) :
    c base ∈ ((unitNeighborhood (n := n) N base).image c : Finset n) := by
  classical
  rw [Finset.mem_image]
  exact ⟨base, base_mem_unitNeighborhood base, rfl⟩

lemma fullyLabeledUnitCluster_iff_image_eq_univ {N : ℕ}
    (c : simplexGrid (n := n) N → n) (base : simplexGrid (n := n) N) :
    FullyLabeledUnitCluster (n := n) c base ↔
      ((unitNeighborhood (n := n) N base).image c : Finset n) = Finset.univ := by
  classical
  constructor
  · intro h
    apply Finset.ext
    intro i
    simp only [Finset.mem_image, Finset.mem_univ, iff_true]
    obtain ⟨a, hcolor, hclose⟩ := h i
    exact ⟨a, mem_unitNeighborhood.mpr hclose, hcolor⟩
  · intro h i
    have hi : i ∈ ((unitNeighborhood (n := n) N base).image c : Finset n) := by
      rw [h]
      exact Finset.mem_univ i
    rw [Finset.mem_image] at hi
    obtain ⟨a, ha, hcolor⟩ := hi
    exact ⟨a, hcolor, mem_unitNeighborhood.mp ha⟩

lemma not_fullyLabeledUnitCluster_iff_exists_missing {N : ℕ}
    (c : simplexGrid (n := n) N → n) (base : simplexGrid (n := n) N) :
    ¬ FullyLabeledUnitCluster (n := n) c base ↔
      ∃ i : n, i ∉ ((unitNeighborhood (n := n) N base).image c : Finset n) := by
  classical
  rw [fullyLabeledUnitCluster_iff_image_eq_univ]
  constructor
  · intro h
    by_contra hmissing
    apply h
    apply Finset.ext
    intro i
    simp only [Finset.mem_univ, iff_true]
    exact by_contra fun hi => hmissing ⟨i, hi⟩
  · rintro ⟨i, hi⟩ himage
    rw [himage] at hi
    exact hi (Finset.mem_univ i)

noncomputable def missingLabelOfNotFull {N : ℕ}
    (c : simplexGrid (n := n) N → n)
    (hnot : ∀ base : simplexGrid (n := n) N,
      ¬ FullyLabeledUnitCluster (n := n) c base)
    (base : simplexGrid (n := n) N) : n :=
  Classical.choose (not_fullyLabeledUnitCluster_iff_exists_missing c base |>.mp (hnot base))

lemma missingLabelOfNotFull_spec {N : ℕ}
    (c : simplexGrid (n := n) N → n)
    (hnot : ∀ base : simplexGrid (n := n) N,
      ¬ FullyLabeledUnitCluster (n := n) c base)
    (base : simplexGrid (n := n) N) :
    missingLabelOfNotFull (n := n) c hnot base ∉
      ((unitNeighborhood (n := n) N base).image c : Finset n) :=
  Classical.choose_spec
    (not_fullyLabeledUnitCluster_iff_exists_missing c base |>.mp (hnot base))

lemma missingLabelOfNotFull_ne_color_of_unitClose {N : ℕ}
    (c : simplexGrid (n := n) N → n)
    (hnot : ∀ base : simplexGrid (n := n) N,
      ¬ FullyLabeledUnitCluster (n := n) c base)
    {base a : simplexGrid (n := n) N} (ha : UnitClose (n := n) a base) :
    missingLabelOfNotFull (n := n) c hnot base ≠ c a := by
  intro h
  have hmissing := missingLabelOfNotFull_spec (n := n) c hnot base
  apply hmissing
  rw [Finset.mem_image]
  exact ⟨a, mem_unitNeighborhood.mpr ha, h.symm⟩

lemma missingLabelOfNotFull_ne_color_self {N : ℕ}
    (c : simplexGrid (n := n) N → n)
    (hnot : ∀ base : simplexGrid (n := n) N,
      ¬ FullyLabeledUnitCluster (n := n) c base)
    (base : simplexGrid (n := n) N) :
    missingLabelOfNotFull (n := n) c hnot base ≠ c base :=
  missingLabelOfNotFull_ne_color_of_unitClose c hnot (unitClose_refl base)

lemma missingLabelOfNotFull_ne_vertex_label {N : ℕ}
    (c : simplexGrid (n := n) N → n)
    (hc : ∀ (a : simplexGrid (n := n) N) (i : n), a.1 i = 0 → c a ≠ i)
    (hnot : ∀ base : simplexGrid (n := n) N,
      ¬ FullyLabeledUnitCluster (n := n) c base)
    (i : n) :
    missingLabelOfNotFull (n := n) c hnot (vertex (n := n) N i) ≠ i := by
  intro hmi
  have hself := missingLabelOfNotFull_ne_color_self c hnot (vertex (n := n) N i)
  apply hself
  rw [color_vertex_of_boundary c hc i, hmi]

omit [DecidableEq n] in
lemma color_coord_pos_of_boundary {N : ℕ}
    (c : simplexGrid (n := n) N → n)
    (hc : ∀ (a : simplexGrid (n := n) N) (i : n), a.1 i = 0 → c a ≠ i)
    (a : simplexGrid (n := n) N) :
    0 < a.1 (c a) := by
  by_contra hnonpos
  have hzero : a.1 (c a) = 0 := Nat.eq_zero_of_not_pos hnonpos
  exact hc a (c a) hzero rfl

def GridStep {N : ℕ} (a b : simplexGrid (n := n) N) : Prop :=
  ∃ i j : n,
    i ≠ j ∧ 0 < a.1 i ∧
      b.1 i = a.1 i - 1 ∧
      b.1 j = a.1 j + 1 ∧
      ∀ k : n, k ≠ i → k ≠ j → b.1 k = a.1 k

def transfer {N : ℕ} (a : simplexGrid (n := n) N) {i j : n}
    (hij : i ≠ j) (hi : 0 < a.1 i) : simplexGrid (n := n) N := by
  refine ⟨Function.update (Function.update a.1 i (a.1 i - 1)) j (a.1 j + 1), ?_⟩
  let s : Finset n := Finset.univ.erase j
  have hi_mem_s : i ∈ s := by
    simp [s, hij]
  have hsum_orig : ∑ k, a.1 k = N := a.2
  have hsum_split :
      ∑ k, a.1 k = ∑ k ∈ s.erase i, a.1 k + a.1 i + a.1 j := by
    have hj_mem : j ∈ (Finset.univ : Finset n) := Finset.mem_univ j
    rw [← Finset.sum_erase_add _ _ hj_mem]
    rw [← Finset.sum_erase_add _ _ hi_mem_s]
  have hsum_new :
      ∑ k, Function.update (Function.update a.1 i (a.1 i - 1)) j (a.1 j + 1) k =
        (a.1 j + 1) + ((a.1 i - 1) + ∑ k ∈ s.erase i, a.1 k) := by
    have hj_mem : j ∈ (Finset.univ : Finset n) := Finset.mem_univ j
    rw [show (∑ k, Function.update (Function.update a.1 i (a.1 i - 1)) j (a.1 j + 1) k) =
        ∑ k ∈ (Finset.univ : Finset n),
          Function.update (Function.update a.1 i (a.1 i - 1)) j (a.1 j + 1) k by simp]
    rw [Finset.sum_update_of_mem hj_mem]
    rw [show (Finset.univ \ {j} : Finset n) = s by
      rw [Finset.sdiff_singleton_eq_erase]]
    rw [Finset.sum_update_of_mem hi_mem_s]
    rw [Finset.sdiff_singleton_eq_erase]
  rw [hsum_new]
  omega

@[simp]
lemma transfer_apply_sub {N : ℕ} (a : simplexGrid (n := n) N) {i j : n}
    (hij : i ≠ j) (hi : 0 < a.1 i) :
    (transfer (n := n) a hij hi).1 i = a.1 i - 1 := by
  simp [transfer, hij]

@[simp]
lemma transfer_apply_add {N : ℕ} (a : simplexGrid (n := n) N) {i j : n}
    (hij : i ≠ j) (hi : 0 < a.1 i) :
    (transfer (n := n) a hij hi).1 j = a.1 j + 1 := by
  simp [transfer]

@[simp]
lemma transfer_apply_of_ne {N : ℕ} (a : simplexGrid (n := n) N) {i j k : n}
    (hij : i ≠ j) (hi : 0 < a.1 i) (hki : k ≠ i) (hkj : k ≠ j) :
    (transfer (n := n) a hij hi).1 k = a.1 k := by
  simp [transfer, hki, hkj]

lemma gridStep_transfer {N : ℕ} (a : simplexGrid (n := n) N) {i j : n}
    (hij : i ≠ j) (hi : 0 < a.1 i) :
    GridStep (n := n) a (transfer (n := n) a hij hi) := by
  refine ⟨i, j, hij, hi, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro k hki hkj
    simp [hki, hkj]

lemma eq_transfer_of_gridStep {N : ℕ} {a b : simplexGrid (n := n) N}
    {i j : n} (hij : i ≠ j) (hi : 0 < a.1 i)
    (hbi : b.1 i = a.1 i - 1)
    (hbj : b.1 j = a.1 j + 1)
    (hrest : ∀ k : n, k ≠ i → k ≠ j → b.1 k = a.1 k) :
    b = transfer (n := n) a hij hi := by
  apply Subtype.ext
  funext k
  by_cases hki : k = i
  · subst k
    rw [hbi]
    simp
  · by_cases hkj : k = j
    · subst k
      rw [hbj]
      simp
    · rw [hrest k hki hkj]
      simp [hki, hkj]

omit [DecidableEq n] in
lemma gridStep_symm {N : ℕ} {a b : simplexGrid (n := n) N}
    (h : GridStep (n := n) a b) :
    GridStep (n := n) b a := by
  obtain ⟨i, j, hij, hi_pos, hbi, hbj, hrest⟩ := h
  refine ⟨j, i, Ne.symm hij, ?_, ?_, ?_, ?_⟩
  · rw [hbj]
    omega
  · rw [hbj]
    omega
  · rw [hbi]
    omega
  · intro k hkj hki
    exact (hrest k hki hkj).symm

omit [DecidableEq n] in
lemma gridStep_ne {N : ℕ} {a b : simplexGrid (n := n) N}
    (h : GridStep (n := n) a b) :
    a ≠ b := by
  obtain ⟨i, _j, _hij, hi_pos, hbi, _hbj, _hrest⟩ := h
  intro hab
  have hcoord : b.1 i = a.1 i := by rw [hab]
  omega

def GridAdj {N : ℕ} (a b : simplexGrid (n := n) N) : Prop :=
  GridStep (n := n) a b ∨ GridStep (n := n) b a

omit [DecidableEq n] in
lemma gridAdj_symm {N : ℕ} {a b : simplexGrid (n := n) N}
    (h : GridAdj (n := n) a b) :
    GridAdj (n := n) b a := by
  exact h.symm

omit [DecidableEq n] in
lemma gridAdj_of_gridStep {N : ℕ} {a b : simplexGrid (n := n) N}
    (h : GridStep (n := n) a b) :
    GridAdj (n := n) a b :=
  Or.inl h

omit [DecidableEq n] in
lemma gridAdj_iff_gridStep {N : ℕ} {a b : simplexGrid (n := n) N} :
    GridAdj (n := n) a b ↔ GridStep (n := n) a b := by
  constructor
  · rintro (h | h)
    · exact h
    · exact gridStep_symm h
  · exact Or.inl

noncomputable def gridNeighbors (N : ℕ) (a : simplexGrid (n := n) N) :
    Finset (simplexGrid (n := n) N) :=
  by
    classical
    exact Finset.univ.filter fun b => GridAdj (n := n) a b

lemma mem_gridNeighbors {N : ℕ} {a b : simplexGrid (n := n) N} :
    b ∈ gridNeighbors (n := n) N a ↔ GridAdj (n := n) a b := by
  classical
  simp [gridNeighbors]

lemma mem_gridNeighbors_iff_gridStep {N : ℕ} {a b : simplexGrid (n := n) N} :
    b ∈ gridNeighbors (n := n) N a ↔ GridStep (n := n) a b := by
  rw [mem_gridNeighbors, gridAdj_iff_gridStep]

lemma gridNeighbors_symm {N : ℕ} {a b : simplexGrid (n := n) N}
    (h : b ∈ gridNeighbors (n := n) N a) :
    a ∈ gridNeighbors (n := n) N b := by
  exact mem_gridNeighbors.mpr (gridAdj_symm (mem_gridNeighbors.mp h))

omit [DecidableEq n] in
lemma unitClose_of_gridStep {N : ℕ} {a b : simplexGrid (n := n) N}
    (h : GridStep (n := n) a b) :
    UnitClose (n := n) a b := by
  rintro k
  obtain ⟨i, j, hij, hi_pos, hbi, hbj, hrest⟩ := h
  by_cases hki : k = i
  · subst k
    have hcast : ((a.1 i - 1 : ℕ) : ℝ) = (a.1 i : ℝ) - 1 := by
      rw [Nat.cast_sub (Nat.succ_le_of_lt hi_pos)]
      norm_num
    rw [hbi, hcast]
    simp
  · by_cases hkj : k = j
    · subst k
      rw [hbj]
      norm_num
    · rw [hrest k hki hkj]
      simp

omit [DecidableEq n] in
lemma unitClose_of_gridStep_symm {N : ℕ} {a b : simplexGrid (n := n) N}
    (h : GridStep (n := n) a b) :
    UnitClose (n := n) b a :=
  unitClose_symm (unitClose_of_gridStep h)

lemma missingLabelOfNotFull_ne_color_of_gridStep {N : ℕ}
    (c : simplexGrid (n := n) N → n)
    (hnot : ∀ base : simplexGrid (n := n) N,
      ¬ FullyLabeledUnitCluster (n := n) c base)
    {a b : simplexGrid (n := n) N} (hab : GridStep (n := n) a b) :
    missingLabelOfNotFull (n := n) c hnot a ≠ c b :=
  missingLabelOfNotFull_ne_color_of_unitClose c hnot (unitClose_of_gridStep_symm hab)

lemma missingLabelOfNotFull_ne_color_of_gridStep_symm {N : ℕ}
    (c : simplexGrid (n := n) N → n)
    (hnot : ∀ base : simplexGrid (n := n) N,
      ¬ FullyLabeledUnitCluster (n := n) c base)
    {a b : simplexGrid (n := n) N} (hab : GridStep (n := n) a b) :
    missingLabelOfNotFull (n := n) c hnot b ≠ c a :=
  missingLabelOfNotFull_ne_color_of_unitClose c hnot (unitClose_of_gridStep hab)

lemma exists_full_cell_of_odd_door_graph {Cell : Type*} [Fintype Cell]
    (G : SimpleGraph (Option Cell)) [DecidableRel G.Adj]
    (CellFull : Cell → Prop)
    (hout : Odd (G.degree none))
    (hodd_full : ∀ cell : Cell, Odd (G.degree (some cell)) → CellFull cell) :
    ∃ cell : Cell, CellFull cell := by
  classical
  obtain ⟨v, hvne, hvodd⟩ :=
    G.exists_ne_odd_degree_of_exists_odd_degree none hout
  cases v with
  | none => exact False.elim (hvne rfl)
  | some cell => exact ⟨cell, hodd_full cell hvodd⟩

/-- A finite grid cell whose vertices all lie in one unit neighborhood. -/
structure UnitCell (N : ℕ) where
  verts : Finset (simplexGrid (n := n) N)
  base : simplexGrid (n := n) N
  close : ∀ a ∈ verts, UnitClose (n := n) a base

namespace UnitCell

noncomputable instance instFintype (N : ℕ) : Fintype (UnitCell (n := n) N) := by
  classical
  refine Fintype.ofEquiv
    {p : Finset (simplexGrid (n := n) N) × simplexGrid (n := n) N //
      ∀ a ∈ p.1, UnitClose (n := n) a p.2} ?_
  refine
    { toFun := fun p => ⟨p.1.1, p.1.2, p.2⟩
      invFun := fun cell => ⟨(cell.verts, cell.base), cell.close⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro p
    cases p with
    | mk val h =>
        cases val
        rfl
  · intro cell
    cases cell
    rfl

def colors {N : ℕ} (cell : UnitCell (n := n) N)
    (c : simplexGrid (n := n) N → n) : Finset n :=
  cell.verts.image c

def Full {N : ℕ} (cell : UnitCell (n := n) N)
    (c : simplexGrid (n := n) N → n) : Prop :=
  cell.colors c = Finset.univ

lemma fullyLabeledUnitCluster_of_full {N : ℕ}
    (cell : UnitCell (n := n) N) (c : simplexGrid (n := n) N → n)
    (hfull : cell.Full c) :
    FullyLabeledUnitCluster (n := n) c cell.base := by
  classical
  intro i
  have hi : i ∈ cell.colors c := by
    rw [hfull]
    exact Finset.mem_univ i
  rw [colors, Finset.mem_image] at hi
  obtain ⟨a, ha_mem, ha_color⟩ := hi
  exact ⟨a, ha_color, cell.close a ha_mem⟩

lemma exists_fullyLabeledUnitCluster_of_odd_door_graph {N : ℕ}
    (G : SimpleGraph (Option (UnitCell (n := n) N))) [DecidableRel G.Adj]
    (c : simplexGrid (n := n) N → n)
    (hout : Odd (G.degree none))
    (hodd_full :
      ∀ cell : UnitCell (n := n) N, Odd (G.degree (some cell)) → cell.Full c) :
    ∃ base : simplexGrid (n := n) N,
      FullyLabeledUnitCluster (n := n) c base := by
  obtain ⟨cell, hfull⟩ :=
    exists_full_cell_of_odd_door_graph G (fun cell : UnitCell (n := n) N => cell.Full c)
      hout hodd_full
  exact ⟨cell.base, cell.fullyLabeledUnitCluster_of_full c hfull⟩

end UnitCell

/--
A top-dimensional finite grid cell, represented only by the facts needed for the Sperner door
count: it has exactly one vertex per label in a full labeling, and all vertices lie in one unit
neighborhood.
-/
structure TopCell (N : ℕ) extends UnitCell (n := n) N where
  card_verts : verts.card = Fintype.card n

namespace TopCell

noncomputable instance instFintype (N : ℕ) : Fintype (TopCell (n := n) N) := by
  classical
  refine Fintype.ofEquiv
    {cell : UnitCell (n := n) N // cell.verts.card = Fintype.card n} ?_
  refine
    { toFun := fun cell => { toUnitCell := cell.1, card_verts := cell.2 }
      invFun := fun cell => ⟨cell.toUnitCell, cell.card_verts⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro cell
    cases cell with
    | mk val h =>
        cases val
        rfl
  · intro cell
    cases cell
    rfl

def colors {N : ℕ} (cell : TopCell (n := n) N)
    (c : simplexGrid (n := n) N → n) : Finset n :=
  cell.verts.image c

def Full {N : ℕ} (cell : TopCell (n := n) N)
    (c : simplexGrid (n := n) N → n) : Prop :=
  cell.colors c = Finset.univ

def faceDoors {N : ℕ} (cell : TopCell (n := n) N)
    (c : simplexGrid (n := n) N → n) (r : n) :
    Finset (Finset (simplexGrid (n := n) N)) :=
  cell.verts.powerset.filter fun face =>
    face.card + 1 = cell.verts.card ∧ face.image c = Finset.univ.erase r

def facets {N : ℕ} (cell : TopCell (n := n) N) :
    Finset (Finset (simplexGrid (n := n) N)) :=
  cell.verts.powerset.filter fun face => face.card + 1 = cell.verts.card

omit [DecidableEq n] in
lemma mem_facets {N : ℕ} {cell : TopCell (n := n) N}
    {face : Finset (simplexGrid (n := n) N)} :
    face ∈ cell.facets ↔ face ⊆ cell.verts ∧ face.card + 1 = cell.verts.card := by
  classical
  simp [facets]

lemma faceDoors_subset_facets {N : ℕ} (cell : TopCell (n := n) N)
    (c : simplexGrid (n := n) N → n) (r : n) :
    cell.faceDoors c r ⊆ cell.facets := by
  classical
  intro face hface
  rw [faceDoors, Finset.mem_filter] at hface
  rw [mem_facets]
  exact ⟨Finset.mem_powerset.mp hface.1, hface.2.1⟩

omit [DecidableEq n] in
lemma exists_erase_eq_of_mem_facets {N : ℕ} [DecidableEq (simplexGrid (n := n) N)]
    {cell : TopCell (n := n) N}
    {face : Finset (simplexGrid (n := n) N)}
    (hface : face ∈ cell.facets) :
    ∃ a ∈ cell.verts, a ∉ face ∧ face = cell.verts.erase a := by
  classical
  rw [mem_facets] at hface
  have hsub : face ⊆ cell.verts := hface.1
  have hcard : face.card + 1 = cell.verts.card := hface.2
  have hlt : face.card < cell.verts.card := by omega
  obtain ⟨a, ha_cell, ha_not_face⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨a, ha_cell, ha_not_face, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [Finset.mem_erase]
    exact ⟨fun hxa => ha_not_face (hxa ▸ hx), hsub hx⟩
  · rw [Finset.card_erase_of_mem ha_cell]
    omega

omit [DecidableEq n] in
lemma mem_facets_iff_exists_erase {N : ℕ} [DecidableEq (simplexGrid (n := n) N)]
    {cell : TopCell (n := n) N}
    {face : Finset (simplexGrid (n := n) N)} :
    face ∈ cell.facets ↔ ∃ a ∈ cell.verts, face = cell.verts.erase a := by
  classical
  constructor
  · intro hface
    obtain ⟨a, ha_cell, _ha_not_face, hface_eq⟩ := exists_erase_eq_of_mem_facets hface
    exact ⟨a, ha_cell, hface_eq⟩
  · rintro ⟨a, ha_cell, rfl⟩
    rw [mem_facets]
    exact ⟨Finset.erase_subset a cell.verts, Finset.card_erase_add_one ha_cell⟩

def oppositeFace {N : ℕ} (cell : TopCell (n := n) N)
    (c : simplexGrid (n := n) N → n) (r : n) :
    Finset (simplexGrid (n := n) N) :=
  cell.verts.filter fun a => c a ≠ r

lemma mem_oppositeFace {N : ℕ} {cell : TopCell (n := n) N}
    {c : simplexGrid (n := n) N → n} {r : n} {a : simplexGrid (n := n) N} :
    a ∈ cell.oppositeFace c r ↔ a ∈ cell.verts ∧ c a ≠ r := by
  classical
  simp [oppositeFace]

lemma oppositeFace_colors_of_full {N : ℕ} {cell : TopCell (n := n) N}
    {c : simplexGrid (n := n) N → n} {r : n}
    (hfull : cell.Full c) :
    (cell.oppositeFace c r).image c = Finset.univ.erase r := by
  classical
  apply Finset.ext
  intro i
  constructor
  · intro hi
    rw [Finset.mem_image] at hi
    obtain ⟨a, ha, hcolor⟩ := hi
    rw [mem_oppositeFace] at ha
    rw [Finset.mem_erase]
    exact ⟨by simpa [hcolor] using ha.2, Finset.mem_univ i⟩
  · intro hi
    rw [Finset.mem_erase] at hi
    have hi_colors : i ∈ cell.colors c := by
      rw [hfull]
      exact Finset.mem_univ i
    rw [colors, Finset.mem_image] at hi_colors
    obtain ⟨a, ha_mem, ha_color⟩ := hi_colors
    rw [Finset.mem_image]
    refine ⟨a, ?_, ha_color⟩
    rw [mem_oppositeFace]
    exact ⟨ha_mem, by
      intro hcr
      exact hi.1 (ha_color ▸ hcr)⟩

lemma color_injOn_verts_of_full {N : ℕ} {cell : TopCell (n := n) N}
    {c : simplexGrid (n := n) N → n}
    (hfull : cell.Full c) :
    Set.InjOn c cell.verts := by
  classical
  rw [← Finset.card_image_iff]
  have hcard_image :
      (cell.verts.image c).card = (Finset.univ : Finset n).card := by
    simpa [Full, colors] using congrArg Finset.card hfull
  simpa [cell.card_verts] using hcard_image

lemma oppositeFace_card_add_one_of_full {N : ℕ} {cell : TopCell (n := n) N}
    {c : simplexGrid (n := n) N → n} {r : n}
    (hfull : cell.Full c) :
    (cell.oppositeFace c r).card + 1 = cell.verts.card := by
  classical
  have hinj : Set.InjOn c cell.verts := color_injOn_verts_of_full hfull
  have hr_colors : r ∈ cell.colors c := by
    rw [hfull]
    exact Finset.mem_univ r
  rw [colors, Finset.mem_image] at hr_colors
  obtain ⟨a, ha_mem, ha_color⟩ := hr_colors
  have hface_eq : cell.oppositeFace c r = cell.verts.erase a := by
    apply Finset.ext
    intro x
    rw [mem_oppositeFace, Finset.mem_erase]
    constructor
    · intro hx
      exact ⟨by
        intro hxa
        exact hx.2 (hxa ▸ ha_color), hx.1⟩
    · intro hx
      refine ⟨hx.2, ?_⟩
      intro hcolor
      exact hx.1 (hinj hx.2 ha_mem (hcolor.trans ha_color.symm))
  rw [hface_eq, Finset.card_erase_of_mem ha_mem]
  have hpos : 0 < cell.verts.card := by
    rw [cell.card_verts]
    exact Fintype.card_pos_iff.mpr ⟨r⟩
  omega

lemma oppositeFace_mem_faceDoors_of_full {N : ℕ} {cell : TopCell (n := n) N}
    {c : simplexGrid (n := n) N → n} {r : n}
    (hfull : cell.Full c) :
    cell.oppositeFace c r ∈ cell.faceDoors c r := by
  classical
  rw [faceDoors, Finset.mem_filter]
  refine ⟨Finset.mem_powerset.mpr ?_, ?_, oppositeFace_colors_of_full hfull⟩
  · intro a ha
    exact (mem_oppositeFace.mp ha).1
  · exact oppositeFace_card_add_one_of_full hfull

lemma eq_oppositeFace_of_mem_faceDoors_of_full {N : ℕ} {cell : TopCell (n := n) N}
    {c : simplexGrid (n := n) N → n} {r : n}
    (hfull : cell.Full c) {face : Finset (simplexGrid (n := n) N)}
    (hface : face ∈ cell.faceDoors c r) :
    face = cell.oppositeFace c r := by
  classical
  have hinj : Set.InjOn c cell.verts := color_injOn_verts_of_full hfull
  have hface_sub : face ⊆ cell.verts := by
    rw [faceDoors, Finset.mem_filter] at hface
    exact Finset.mem_powerset.mp hface.1
  have hface_colors : face.image c = Finset.univ.erase r := by
    rw [faceDoors, Finset.mem_filter] at hface
    exact hface.2.2
  apply Finset.ext
  intro a
  constructor
  · intro ha
    rw [mem_oppositeFace]
    refine ⟨hface_sub ha, ?_⟩
    intro hcolor
    have hc_mem : c a ∈ face.image c := Finset.mem_image.mpr ⟨a, ha, rfl⟩
    rw [hface_colors, Finset.mem_erase] at hc_mem
    exact hc_mem.1 hcolor
  · intro ha
    rw [mem_oppositeFace] at ha
    have hc_mem : c a ∈ Finset.univ.erase r := by
      rw [Finset.mem_erase]
      exact ⟨ha.2, Finset.mem_univ (c a)⟩
    rw [← hface_colors, Finset.mem_image] at hc_mem
    obtain ⟨b, hb_mem, hb_color⟩ := hc_mem
    have hb_cell : b ∈ cell.verts := hface_sub hb_mem
    have hba : b = a := hinj hb_cell ha.1 hb_color
    simpa [hba] using hb_mem

lemma faceDoors_eq_singleton_oppositeFace_of_full {N : ℕ}
    {cell : TopCell (n := n) N}
    {c : simplexGrid (n := n) N → n} {r : n}
    (hfull : cell.Full c) :
    cell.faceDoors c r = {cell.oppositeFace c r} := by
  classical
  apply Finset.ext
  intro face
  constructor
  · intro hface
    rw [Finset.mem_singleton]
    exact eq_oppositeFace_of_mem_faceDoors_of_full hfull hface
  · intro hface
    rw [Finset.mem_singleton] at hface
    rw [hface]
    exact oppositeFace_mem_faceDoors_of_full hfull

lemma odd_card_faceDoors_of_full {N : ℕ} {cell : TopCell (n := n) N}
    {c : simplexGrid (n := n) N → n} {r : n}
    (hfull : cell.Full c) :
    Odd (cell.faceDoors c r).card := by
  rw [faceDoors_eq_singleton_oppositeFace_of_full hfull]
  norm_num

lemma face_mem_of_mem_faceDoors {N : ℕ} {cell : TopCell (n := n) N}
    {c : simplexGrid (n := n) N → n} {r : n}
    {face : Finset (simplexGrid (n := n) N)}
    (hface : face ∈ cell.faceDoors c r) :
    face ⊆ cell.verts := by
  classical
  rw [faceDoors, Finset.mem_filter] at hface
  exact Finset.mem_powerset.mp hface.1

lemma face_card_add_one_of_mem_faceDoors {N : ℕ} {cell : TopCell (n := n) N}
    {c : simplexGrid (n := n) N → n} {r : n}
    {face : Finset (simplexGrid (n := n) N)}
    (hface : face ∈ cell.faceDoors c r) :
    face.card + 1 = cell.verts.card := by
  classical
  rw [faceDoors, Finset.mem_filter] at hface
  exact hface.2.1

lemma face_colors_of_mem_faceDoors {N : ℕ} {cell : TopCell (n := n) N}
    {c : simplexGrid (n := n) N → n} {r : n}
    {face : Finset (simplexGrid (n := n) N)}
    (hface : face ∈ cell.faceDoors c r) :
    face.image c = Finset.univ.erase r := by
  classical
  rw [faceDoors, Finset.mem_filter] at hface
  exact hface.2.2

lemma color_injOn_face_of_mem_faceDoors {N : ℕ} {cell : TopCell (n := n) N}
    {c : simplexGrid (n := n) N → n} {r : n}
    {face : Finset (simplexGrid (n := n) N)}
    (hface : face ∈ cell.faceDoors c r) :
    Set.InjOn c face := by
  classical
  rw [← Finset.card_image_iff]
  have hface_card : face.card + 1 = Fintype.card n := by
    rw [face_card_add_one_of_mem_faceDoors hface, cell.card_verts]
  have himage_card : (face.image c).card + 1 = Fintype.card n := by
    rw [face_colors_of_mem_faceDoors hface]
    exact Finset.card_erase_add_one (Finset.mem_univ r)
  omega

lemma exists_erase_eq_of_mem_faceDoors {N : ℕ} [DecidableEq (simplexGrid (n := n) N)]
    {cell : TopCell (n := n) N}
    {c : simplexGrid (n := n) N → n} {r : n}
    {face : Finset (simplexGrid (n := n) N)}
    (hface : face ∈ cell.faceDoors c r) :
    ∃ a ∈ cell.verts, a ∉ face ∧ face = cell.verts.erase a := by
  classical
  have hsub : face ⊆ cell.verts := face_mem_of_mem_faceDoors hface
  have hcard : face.card + 1 = cell.verts.card := face_card_add_one_of_mem_faceDoors hface
  have hlt : face.card < cell.verts.card := by omega
  obtain ⟨a, ha_cell, ha_not_face⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨a, ha_cell, ha_not_face, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [Finset.mem_erase]
    exact ⟨fun hxa => ha_not_face (hxa ▸ hx), hsub hx⟩
  · rw [Finset.card_erase_of_mem ha_cell]
    omega

lemma mem_faceDoors_iff_exists_erase {N : ℕ} [DecidableEq (simplexGrid (n := n) N)]
    {cell : TopCell (n := n) N}
    {c : simplexGrid (n := n) N → n} {r : n}
    {face : Finset (simplexGrid (n := n) N)} :
    face ∈ cell.faceDoors c r ↔
      ∃ a ∈ cell.verts,
        face = cell.verts.erase a ∧ (cell.verts.erase a).image c = Finset.univ.erase r := by
  classical
  constructor
  · intro hface
    obtain ⟨a, ha_cell, _ha_not_face, hface_eq⟩ := exists_erase_eq_of_mem_faceDoors hface
    exact ⟨a, ha_cell, hface_eq, by
      rw [← hface_eq]
      exact face_colors_of_mem_faceDoors hface⟩
  · rintro ⟨a, ha_cell, hface_eq, hcolors⟩
    rw [faceDoors, Finset.mem_filter]
    refine ⟨Finset.mem_powerset.mpr ?_, ?_, ?_⟩
    · rw [hface_eq]
      exact Finset.erase_subset a cell.verts
    · rw [hface_eq, Finset.card_erase_of_mem ha_cell]
      have hpos : 0 < cell.verts.card := by
        exact Finset.card_pos.mpr ⟨a, ha_cell⟩
      omega
    · rw [hface_eq]
      exact hcolors

lemma image_erase_eq_colors_iff_exists_same_color_ne {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {cell : TopCell (n := n) N}
    {c : simplexGrid (n := n) N → n}
    {a : simplexGrid (n := n) N} (ha : a ∈ cell.verts) :
    (cell.verts.erase a).image c = cell.colors c ↔
      ∃ b ∈ cell.verts, b ≠ a ∧ c b = c a := by
  classical
  constructor
  · intro himage
    have hca : c a ∈ (cell.verts.erase a).image c := by
      rw [himage, colors, Finset.mem_image]
      exact ⟨a, ha, rfl⟩
    rw [Finset.mem_image] at hca
    obtain ⟨b, hb_erase, hb_color⟩ := hca
    rw [Finset.mem_erase] at hb_erase
    exact ⟨b, hb_erase.2, hb_erase.1, hb_color⟩
  · rintro ⟨b, hb_cell, hba, hb_color⟩
    apply Finset.ext
    intro i
    constructor
    · intro hi
      rw [Finset.mem_image] at hi
      obtain ⟨x, hx_erase, hx_color⟩ := hi
      rw [Finset.mem_erase] at hx_erase
      rw [colors, Finset.mem_image]
      exact ⟨x, hx_erase.2, hx_color⟩
    · intro hi
      rw [colors, Finset.mem_image] at hi
      obtain ⟨x, hx_cell, hx_color⟩ := hi
      rw [Finset.mem_image]
      by_cases hxa : x = a
      · refine ⟨b, ?_, ?_⟩
        · rw [Finset.mem_erase]
          exact ⟨hba, hb_cell⟩
        · rw [← hx_color, hxa]
          exact hb_color
      · refine ⟨x, ?_, hx_color⟩
        rw [Finset.mem_erase]
        exact ⟨hxa, hx_cell⟩

lemma erase_subset_colors_of_mem_faceDoors {N : ℕ} {cell : TopCell (n := n) N}
    {c : simplexGrid (n := n) N → n} {r : n}
    {face : Finset (simplexGrid (n := n) N)}
    (hface : face ∈ cell.faceDoors c r) :
    Finset.univ.erase r ⊆ cell.colors c := by
  classical
  intro i hi
  have hi_face : i ∈ face.image c := by
    rw [face_colors_of_mem_faceDoors hface]
    exact hi
  rw [Finset.mem_image] at hi_face
  obtain ⟨a, ha_face, ha_color⟩ := hi_face
  rw [colors, Finset.mem_image]
  exact ⟨a, face_mem_of_mem_faceDoors hface ha_face, ha_color⟩

lemma colors_eq_univ_of_mem_color_r_of_mem_faceDoors {N : ℕ}
    {cell : TopCell (n := n) N}
    {c : simplexGrid (n := n) N → n} {r : n}
    {face : Finset (simplexGrid (n := n) N)}
    (hface : face ∈ cell.faceDoors c r)
    (hr : r ∈ cell.colors c) :
    cell.Full c := by
  classical
  apply Finset.ext
  intro i
  constructor
  · intro _hi
    exact Finset.mem_univ i
  · intro _hi
    by_cases hir : i = r
    · simpa [hir] using hr
    · exact erase_subset_colors_of_mem_faceDoors hface (by
        rw [Finset.mem_erase]
        exact ⟨hir, Finset.mem_univ i⟩)

lemma color_r_notMem_of_not_full_of_mem_faceDoors {N : ℕ}
    {cell : TopCell (n := n) N}
    {c : simplexGrid (n := n) N → n} {r : n}
    {face : Finset (simplexGrid (n := n) N)}
    (hnotfull : ¬ cell.Full c)
    (hface : face ∈ cell.faceDoors c r) :
    r ∉ cell.colors c := by
  intro hr
  exact hnotfull (colors_eq_univ_of_mem_color_r_of_mem_faceDoors hface hr)

lemma colors_eq_erase_of_not_full_of_mem_faceDoors {N : ℕ}
    {cell : TopCell (n := n) N}
    {c : simplexGrid (n := n) N → n} {r : n}
    {face : Finset (simplexGrid (n := n) N)}
    (hnotfull : ¬ cell.Full c)
    (hface : face ∈ cell.faceDoors c r) :
    cell.colors c = Finset.univ.erase r := by
  classical
  apply Finset.ext
  intro i
  constructor
  · intro hi
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ i⟩
    intro hir
    exact color_r_notMem_of_not_full_of_mem_faceDoors hnotfull hface (by simpa [hir] using hi)
  · intro hi
    exact erase_subset_colors_of_mem_faceDoors hface hi

lemma color_ne_r_of_not_full_of_mem_faceDoors {N : ℕ}
    {cell : TopCell (n := n) N}
    {c : simplexGrid (n := n) N → n} {r : n}
    {face : Finset (simplexGrid (n := n) N)}
    (hnotfull : ¬ cell.Full c)
    (hface : face ∈ cell.faceDoors c r)
    {a : simplexGrid (n := n) N} (ha : a ∈ cell.verts) :
    c a ≠ r := by
  intro hcolor
  have hmem : c a ∈ cell.colors c := by
    rw [colors, Finset.mem_image]
    exact ⟨a, ha, rfl⟩
  have hrnot := color_r_notMem_of_not_full_of_mem_faceDoors hnotfull hface
  exact hrnot (by simpa [hcolor] using hmem)

lemma erase_mem_faceDoors_iff_exists_same_color_ne_of_not_full_of_mem_faceDoors {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {cell : TopCell (n := n) N}
    {c : simplexGrid (n := n) N → n} {r : n}
    {face : Finset (simplexGrid (n := n) N)}
    (hnotfull : ¬ cell.Full c)
    (hface : face ∈ cell.faceDoors c r)
    {a : simplexGrid (n := n) N} (ha : a ∈ cell.verts) :
    cell.verts.erase a ∈ cell.faceDoors c r ↔
      ∃ b ∈ cell.verts, b ≠ a ∧ c b = c a := by
  classical
  have hcolors : cell.colors c = Finset.univ.erase r :=
    colors_eq_erase_of_not_full_of_mem_faceDoors hnotfull hface
  constructor
  · intro ha_door
    have himage :
        (cell.verts.erase a).image c = cell.colors c := by
      rw [hcolors]
      exact face_colors_of_mem_faceDoors ha_door
    exact (image_erase_eq_colors_iff_exists_same_color_ne ha).mp himage
  · intro hdup
    rw [mem_faceDoors_iff_exists_erase]
    refine ⟨a, ha, rfl, ?_⟩
    rw [← hcolors]
    exact (image_erase_eq_colors_iff_exists_same_color_ne ha).mpr hdup

lemma exists_ne_faceDoor_of_not_full_of_mem_faceDoors {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {cell : TopCell (n := n) N}
    {c : simplexGrid (n := n) N → n} {r : n}
    {face : Finset (simplexGrid (n := n) N)}
    (hnotfull : ¬ cell.Full c)
    (hface : face ∈ cell.faceDoors c r) :
    ∃ face' ∈ cell.faceDoors c r, face' ≠ face := by
  classical
  obtain ⟨a, ha_cell, ha_not_face, hface_eq⟩ := exists_erase_eq_of_mem_faceDoors hface
  have hca_ne_r : c a ≠ r :=
    color_ne_r_of_not_full_of_mem_faceDoors hnotfull hface ha_cell
  have hca_mem_colors : c a ∈ Finset.univ.erase r := by
    rw [Finset.mem_erase]
    exact ⟨hca_ne_r, Finset.mem_univ (c a)⟩
  have hca_mem_face_image : c a ∈ face.image c := by
    rw [face_colors_of_mem_faceDoors hface]
    exact hca_mem_colors
  rw [Finset.mem_image] at hca_mem_face_image
  obtain ⟨b, hb_face, hb_color⟩ := hca_mem_face_image
  have hb_cell : b ∈ cell.verts := face_mem_of_mem_faceDoors hface hb_face
  have hba : b ≠ a := by
    intro h
    exact ha_not_face (h ▸ hb_face)
  refine ⟨cell.verts.erase b, ?_, ?_⟩
  · rw [erase_mem_faceDoors_iff_exists_same_color_ne_of_not_full_of_mem_faceDoors
      hnotfull hface hb_cell]
    exact ⟨a, ha_cell, Ne.symm hba, hb_color.symm⟩
  · intro h_eq
    have ha_mem_erase_b : a ∈ cell.verts.erase b := by
      rw [Finset.mem_erase]
      exact ⟨Ne.symm hba, ha_cell⟩
    exact ha_not_face (by simpa [h_eq] using ha_mem_erase_b)

lemma card_faceDoors_ne_one_of_not_full {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {cell : TopCell (n := n) N}
    {c : simplexGrid (n := n) N → n} {r : n}
    (hnotfull : ¬ cell.Full c) :
    (cell.faceDoors c r).card ≠ 1 := by
  classical
  intro hcard
  obtain ⟨face, hfaces⟩ := Finset.card_eq_one.mp hcard
  have hface : face ∈ cell.faceDoors c r := by
    rw [hfaces]
    exact Finset.mem_singleton_self face
  obtain ⟨face', hface', hne⟩ :=
    exists_ne_faceDoor_of_not_full_of_mem_faceDoors hnotfull hface
  rw [hfaces, Finset.mem_singleton] at hface'
  exact hne hface'

lemma faceDoors_eq_pair_of_not_full_of_mem_faceDoors {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {cell : TopCell (n := n) N}
    {c : simplexGrid (n := n) N → n} {r : n}
    {face : Finset (simplexGrid (n := n) N)}
    (hnotfull : ¬ cell.Full c)
    (hface : face ∈ cell.faceDoors c r) :
    ∃ a b : simplexGrid (n := n) N,
      a ∈ cell.verts ∧ b ∈ cell.verts ∧ a ≠ b ∧ c a = c b ∧
        cell.faceDoors c r = {cell.verts.erase a, cell.verts.erase b} := by
  classical
  obtain ⟨a, ha_cell, ha_not_face, hface_eq⟩ := exists_erase_eq_of_mem_faceDoors hface
  have hface_inj : Set.InjOn c face := color_injOn_face_of_mem_faceDoors hface
  have hca_ne_r : c a ≠ r :=
    color_ne_r_of_not_full_of_mem_faceDoors hnotfull hface ha_cell
  have hca_mem_face_image : c a ∈ face.image c := by
    rw [face_colors_of_mem_faceDoors hface, Finset.mem_erase]
    exact ⟨hca_ne_r, Finset.mem_univ (c a)⟩
  rw [Finset.mem_image] at hca_mem_face_image
  obtain ⟨b, hb_face, hb_color⟩ := hca_mem_face_image
  have hb_cell : b ∈ cell.verts := face_mem_of_mem_faceDoors hface hb_face
  have hba : b ≠ a := by
    intro h
    exact ha_not_face (h ▸ hb_face)
  have hb_door : cell.verts.erase b ∈ cell.faceDoors c r := by
    rw [erase_mem_faceDoors_iff_exists_same_color_ne_of_not_full_of_mem_faceDoors
      hnotfull hface hb_cell]
    exact ⟨a, ha_cell, Ne.symm hba, hb_color.symm⟩
  refine ⟨a, b, ha_cell, hb_cell, Ne.symm hba, hb_color.symm, ?_⟩
  apply Finset.ext
  intro face'
  constructor
  · intro hface'
    obtain ⟨x, hx_cell, _hx_not_face', hface'_eq⟩ :=
      exists_erase_eq_of_mem_faceDoors hface'
    rw [Finset.mem_insert, Finset.mem_singleton]
    by_cases hxa : x = a
    · left
      rw [hface'_eq, hxa]
    · right
      have hx_face : x ∈ face := by
        rw [hface_eq, Finset.mem_erase]
        exact ⟨hxa, hx_cell⟩
      have hdup :
          ∃ y ∈ cell.verts, y ≠ x ∧ c y = c x := by
        rw [← erase_mem_faceDoors_iff_exists_same_color_ne_of_not_full_of_mem_faceDoors
          hnotfull hface hx_cell]
        rwa [← hface'_eq]
      obtain ⟨y, hy_cell, hyx, hy_color⟩ := hdup
      have hya : y = a := by
        by_contra hya
        have hy_face : y ∈ face := by
          rw [hface_eq, Finset.mem_erase]
          exact ⟨hya, hy_cell⟩
        exact hyx (hface_inj hy_face hx_face hy_color)
      have hcx : c x = c b := by
        calc
          c x = c y := hy_color.symm
          _ = c a := by rw [hya]
          _ = c b := hb_color.symm
      have hxb : x = b := hface_inj hx_face hb_face hcx
      rw [hface'_eq, hxb]
  · intro hface'
    rw [Finset.mem_insert, Finset.mem_singleton] at hface'
    rcases hface' with hface' | hface'
    · rw [hface']
      rwa [hface_eq] at hface
    · rw [hface']
      exact hb_door

omit [DecidableEq n] in
lemma erase_ne_erase_of_mem_of_ne {N : ℕ} [DecidableEq (simplexGrid (n := n) N)]
    {cell : TopCell (n := n) N} {a b : simplexGrid (n := n) N}
    (hb : b ∈ cell.verts) (hab : a ≠ b) :
    cell.verts.erase a ≠ cell.verts.erase b := by
  intro h
  have hb_erase_a : b ∈ cell.verts.erase a := by
    rw [Finset.mem_erase]
    exact ⟨Ne.symm hab, hb⟩
  have hb_erase_b : b ∈ cell.verts.erase b := by
    rw [← h]
    exact hb_erase_a
  exact (Finset.notMem_erase b cell.verts) hb_erase_b

lemma card_faceDoors_eq_two_of_not_full_of_mem_faceDoors {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {cell : TopCell (n := n) N}
    {c : simplexGrid (n := n) N → n} {r : n}
    {face : Finset (simplexGrid (n := n) N)}
    (hnotfull : ¬ cell.Full c)
    (hface : face ∈ cell.faceDoors c r) :
    (cell.faceDoors c r).card = 2 := by
  classical
  obtain ⟨a, b, ha, hb, hab, _hcolor, hdoors⟩ :=
    faceDoors_eq_pair_of_not_full_of_mem_faceDoors hnotfull hface
  have hne : cell.verts.erase a ≠ cell.verts.erase b :=
    erase_ne_erase_of_mem_of_ne hb hab
  rw [hdoors]
  exact Finset.card_pair hne

lemma even_card_faceDoors_of_not_full {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {cell : TopCell (n := n) N}
    {c : simplexGrid (n := n) N → n} {r : n}
    (hnotfull : ¬ cell.Full c) :
    Even (cell.faceDoors c r).card := by
  classical
  by_cases hnonempty : (cell.faceDoors c r).Nonempty
  · obtain ⟨face, hface⟩ := hnonempty
    rw [card_faceDoors_eq_two_of_not_full_of_mem_faceDoors hnotfull hface]
    exact even_two
  · have hempty : cell.faceDoors c r = ∅ := by
      exact Finset.not_nonempty_iff_eq_empty.mp hnonempty
    rw [hempty]
    exact ⟨0, by simp⟩

lemma full_of_odd_card_faceDoors {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {cell : TopCell (n := n) N}
    {c : simplexGrid (n := n) N → n} {r : n}
    (hodd : Odd (cell.faceDoors c r).card) :
    cell.Full c := by
  by_contra hnotfull
  exact (Nat.not_even_iff_odd.2 hodd) (even_card_faceDoors_of_not_full hnotfull)

lemma exists_full_of_odd_sum_faceDoors {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    (c : simplexGrid (n := n) N → n) (r : n)
    (hodd :
      Odd ((Finset.univ : Finset (TopCell (n := n) N)).sum fun cell =>
        (cell.faceDoors c r).card)) :
    ∃ cell : TopCell (n := n) N, cell.Full c := by
  classical
  by_contra hnone
  have heven :
      Even ((Finset.univ : Finset (TopCell (n := n) N)).sum fun cell =>
        (cell.faceDoors c r).card) := by
    apply Finset.even_sum
    intro cell _hcell
    exact even_card_faceDoors_of_not_full (by
      intro hfull
      exact hnone ⟨cell, hfull⟩)
  exact (Nat.not_even_iff_odd.2 hodd) heven

lemma exists_fullyLabeledUnitCluster_of_odd_sum_faceDoors {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    (c : simplexGrid (n := n) N → n) (r : n)
    (hodd :
      Odd ((Finset.univ : Finset (TopCell (n := n) N)).sum fun cell =>
        (cell.faceDoors c r).card)) :
    ∃ base : simplexGrid (n := n) N,
      FullyLabeledUnitCluster (n := n) c base := by
  obtain ⟨cell, hfull⟩ := exists_full_of_odd_sum_faceDoors c r hodd
  exact ⟨cell.base, cell.fullyLabeledUnitCluster_of_full c hfull⟩

lemma not_forall_unitNeighborhood_image_ne_univ_of_odd_sum_faceDoors {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    (c : simplexGrid (n := n) N → n) (r : n)
    (hodd :
      Odd ((Finset.univ : Finset (TopCell (n := n) N)).sum fun cell =>
        (cell.faceDoors c r).card)) :
    ¬ ∀ base : simplexGrid (n := n) N,
      ((unitNeighborhood (n := n) N base).image c : Finset n) ≠ Finset.univ := by
  intro hforall
  obtain ⟨base, hfull⟩ := exists_fullyLabeledUnitCluster_of_odd_sum_faceDoors c r hodd
  exact hforall base ((fullyLabeledUnitCluster_iff_image_eq_univ c base).mp hfull)

lemma exists_fullyLabeledUnitCluster_of_family_odd_sum_faceDoors {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {Cell : Type*} [Fintype Cell]
    (toTopCell : Cell → TopCell (n := n) N)
    (c : simplexGrid (n := n) N → n) (r : n)
    (hodd :
      Odd ((Finset.univ : Finset Cell).sum fun cell =>
        ((toTopCell cell).faceDoors c r).card)) :
    ∃ base : simplexGrid (n := n) N,
      FullyLabeledUnitCluster (n := n) c base := by
  classical
  by_contra hnone
  have heven :
      Even ((Finset.univ : Finset Cell).sum fun cell =>
        ((toTopCell cell).faceDoors c r).card) := by
    apply Finset.even_sum
    intro cell _hcell
    exact even_card_faceDoors_of_not_full (by
      intro hfull
      exact hnone ⟨(toTopCell cell).base,
        (toTopCell cell).fullyLabeledUnitCluster_of_full c hfull⟩)
  exact (Nat.not_even_iff_odd.2 hodd) heven

lemma not_forall_unitNeighborhood_image_ne_univ_of_family_odd_sum_faceDoors {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {Cell : Type*} [Fintype Cell]
    (toTopCell : Cell → TopCell (n := n) N)
    (c : simplexGrid (n := n) N → n) (r : n)
    (hodd :
      Odd ((Finset.univ : Finset Cell).sum fun cell =>
        ((toTopCell cell).faceDoors c r).card)) :
    ¬ ∀ base : simplexGrid (n := n) N,
      ((unitNeighborhood (n := n) N base).image c : Finset n) ≠ Finset.univ := by
  intro hforall
  obtain ⟨base, hfull⟩ :=
    exists_fullyLabeledUnitCluster_of_family_odd_sum_faceDoors toTopCell c r hodd
  exact hforall base ((fullyLabeledUnitCluster_iff_image_eq_univ c base).mp hfull)

noncomputable def familyDoorIncidences {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {Cell : Type*} [Fintype Cell]
    (toTopCell : Cell → TopCell (n := n) N)
    (c : simplexGrid (n := n) N → n) (r : n) :
    Finset (Σ _cell : Cell, Finset (simplexGrid (n := n) N)) :=
  (Finset.univ : Finset Cell).sigma fun cell => (toTopCell cell).faceDoors c r

lemma mem_familyDoorIncidences {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {Cell : Type*} [Fintype Cell]
    (toTopCell : Cell → TopCell (n := n) N)
    (c : simplexGrid (n := n) N → n) (r : n)
    {door : Σ _cell : Cell, Finset (simplexGrid (n := n) N)} :
    door ∈ familyDoorIncidences toTopCell c r ↔
      door.2 ∈ (toTopCell door.1).faceDoors c r := by
  classical
  cases door
  simp [familyDoorIncidences]

lemma card_familyDoorIncidences {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {Cell : Type*} [Fintype Cell]
    (toTopCell : Cell → TopCell (n := n) N)
    (c : simplexGrid (n := n) N → n) (r : n) :
    (familyDoorIncidences toTopCell c r).card =
      (Finset.univ : Finset Cell).sum fun cell =>
        ((toTopCell cell).faceDoors c r).card := by
  classical
  simp [familyDoorIncidences]

lemma odd_card_familyDoorIncidences_iff {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {Cell : Type*} [Fintype Cell]
    (toTopCell : Cell → TopCell (n := n) N)
    (c : simplexGrid (n := n) N → n) (r : n) :
    Odd (familyDoorIncidences toTopCell c r).card ↔
      Odd ((Finset.univ : Finset Cell).sum fun cell =>
        ((toTopCell cell).faceDoors c r).card) := by
  rw [card_familyDoorIncidences]

lemma exists_fullyLabeledUnitCluster_of_odd_card_familyDoorIncidences {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {Cell : Type*} [Fintype Cell]
    (toTopCell : Cell → TopCell (n := n) N)
    (c : simplexGrid (n := n) N → n) (r : n)
    (hodd : Odd (familyDoorIncidences toTopCell c r).card) :
    ∃ base : simplexGrid (n := n) N,
      FullyLabeledUnitCluster (n := n) c base := by
  exact exists_fullyLabeledUnitCluster_of_family_odd_sum_faceDoors toTopCell c r
    ((odd_card_familyDoorIncidences_iff toTopCell c r).mp hodd)

lemma odd_card_familyDoorIncidences_of_even_odd_partition {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    (toTopCell : Cell → TopCell (n := n) N)
    (c : simplexGrid (n := n) N → n) (r : n)
    (internal exterior : Finset (Σ _cell : Cell, Finset (simplexGrid (n := n) N)))
    (hpartition : familyDoorIncidences toTopCell c r = internal ∪ exterior)
    (hdisj : Disjoint internal exterior)
    (hinternal : Even internal.card)
    (hexterior : Odd exterior.card) :
    Odd (familyDoorIncidences toTopCell c r).card := by
  rw [hpartition, Finset.card_union_of_disjoint hdisj]
  exact Even.add_odd hinternal hexterior

lemma exists_fullyLabeledUnitCluster_of_even_odd_incidence_partition {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    (toTopCell : Cell → TopCell (n := n) N)
    (c : simplexGrid (n := n) N → n) (r : n)
    (internal exterior : Finset (Σ _cell : Cell, Finset (simplexGrid (n := n) N)))
    (hpartition : familyDoorIncidences toTopCell c r = internal ∪ exterior)
    (hdisj : Disjoint internal exterior)
    (hinternal : Even internal.card)
    (hexterior : Odd exterior.card) :
    ∃ base : simplexGrid (n := n) N,
      FullyLabeledUnitCluster (n := n) c base := by
  exact exists_fullyLabeledUnitCluster_of_odd_card_familyDoorIncidences toTopCell c r
    (odd_card_familyDoorIncidences_of_even_odd_partition toTopCell c r
      internal exterior hpartition hdisj hinternal hexterior)

lemma even_card_finset_of_fixedPointFree_involution {α : Type*} [DecidableEq α]
    (s : Finset α) (mate : α → α)
    (hmem : ∀ x ∈ s, mate x ∈ s)
    (hinv : ∀ x ∈ s, mate (mate x) = x)
    (hfree : ∀ x ∈ s, mate x ≠ x) :
    Even s.card := by
  classical
  have H :
      ∀ n : ℕ, ∀ s : Finset α, s.card = n →
        (∀ x ∈ s, mate x ∈ s) →
        (∀ x ∈ s, mate (mate x) = x) →
        (∀ x ∈ s, mate x ≠ x) →
        Even s.card := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro s hcard hmem hinv hfree
        by_cases hs_empty : s = ∅
        · rw [hs_empty]
          exact ⟨0, by simp⟩
        · have hs_nonempty : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs_empty
          obtain ⟨x, hx⟩ := hs_nonempty
          let y := mate x
          have hy : y ∈ s := hmem x hx
          have hyx : y ≠ x := hfree x hx
          let s' := (s.erase x).erase y
          have hx_ne_y : x ≠ y := Ne.symm hyx
          have hcard_s' : s'.card + 2 = s.card := by
            have hy_erase_x : y ∈ s.erase x := by
              rw [Finset.mem_erase]
              exact ⟨hyx, hy⟩
            have h1 : s'.card + 1 = (s.erase x).card := by
              dsimp [s']
              exact Finset.card_erase_add_one hy_erase_x
            have h2 : (s.erase x).card + 1 = s.card :=
              Finset.card_erase_add_one hx
            omega
          have hcard_lt : s'.card < n := by
            rw [← hcard, ← hcard_s']
            omega
          have hmem' : ∀ z ∈ s', mate z ∈ s' := by
            intro z hz
            rw [Finset.mem_erase] at hz
            obtain ⟨hzy, hz_erase_x⟩ := hz
            rw [Finset.mem_erase] at hz_erase_x
            obtain ⟨hzx, hz_s⟩ := hz_erase_x
            have hmz_s : mate z ∈ s := hmem z hz_s
            have hmz_ne_x : mate z ≠ x := by
              intro hmzx
              have hz_eq_y : z = y := by
                calc
                  z = mate (mate z) := (hinv z hz_s).symm
                  _ = mate x := by rw [hmzx]
                  _ = y := rfl
              exact hzy hz_eq_y
            have hmz_ne_y : mate z ≠ y := by
              intro hmzy
              have hz_eq_x : z = x := by
                calc
                  z = mate (mate z) := (hinv z hz_s).symm
                  _ = mate y := by rw [hmzy]
                  _ = x := by
                    dsimp [y]
                    exact hinv x hx
              exact hzx hz_eq_x
            rw [Finset.mem_erase]
            exact ⟨hmz_ne_y, by
              rw [Finset.mem_erase]
              exact ⟨hmz_ne_x, hmz_s⟩⟩
          have hinv' : ∀ z ∈ s', mate (mate z) = z := by
            intro z hz
            exact hinv z
              (Finset.erase_subset x s ((Finset.erase_subset y (s.erase x)) hz))
          have hfree' : ∀ z ∈ s', mate z ≠ z := by
            intro z hz
            exact hfree z
              (Finset.erase_subset x s ((Finset.erase_subset y (s.erase x)) hz))
          have heven' : Even s'.card := ih s'.card hcard_lt s' rfl hmem' hinv' hfree'
          rw [← hcard_s']
          exact heven'.add even_two
  exact H s.card s rfl hmem hinv hfree

def IsExteriorFacet {N : ℕ} (F : Finset (simplexGrid (n := n) N)) : Prop :=
  ∃ q : n, ∀ a ∈ F, a.1 q = 0

noncomputable def familyInternalDoorIncidences {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {Cell : Type*} [Fintype Cell]
    (toTopCell : Cell → TopCell (n := n) N)
    (c : simplexGrid (n := n) N → n) (r : n) :
    Finset (Σ _cell : Cell, Finset (simplexGrid (n := n) N)) :=
  by
    classical
    exact (familyDoorIncidences toTopCell c r).filter fun incidence =>
      ¬ IsExteriorFacet (n := n) incidence.2

noncomputable def familyExteriorDoorIncidences {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {Cell : Type*} [Fintype Cell]
    (toTopCell : Cell → TopCell (n := n) N)
    (c : simplexGrid (n := n) N → n) (r : n) :
    Finset (Σ _cell : Cell, Finset (simplexGrid (n := n) N)) :=
  by
    classical
    exact (familyDoorIncidences toTopCell c r).filter fun incidence =>
      IsExteriorFacet (n := n) incidence.2

lemma mem_familyInternalDoorIncidences {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {Cell : Type*} [Fintype Cell]
    (toTopCell : Cell → TopCell (n := n) N)
    (c : simplexGrid (n := n) N → n) (r : n)
    {incidence : Σ _cell : Cell, Finset (simplexGrid (n := n) N)} :
    incidence ∈ familyInternalDoorIncidences toTopCell c r ↔
      incidence ∈ familyDoorIncidences toTopCell c r ∧
        ¬ IsExteriorFacet (n := n) incidence.2 := by
  classical
  simp [familyInternalDoorIncidences]

lemma mem_familyExteriorDoorIncidences {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {Cell : Type*} [Fintype Cell]
    (toTopCell : Cell → TopCell (n := n) N)
    (c : simplexGrid (n := n) N → n) (r : n)
    {incidence : Σ _cell : Cell, Finset (simplexGrid (n := n) N)} :
    incidence ∈ familyExteriorDoorIncidences toTopCell c r ↔
      incidence ∈ familyDoorIncidences toTopCell c r ∧
        IsExteriorFacet (n := n) incidence.2 := by
  classical
  simp [familyExteriorDoorIncidences]

lemma familyDoorIncidences_eq_internal_union_exterior {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    (toTopCell : Cell → TopCell (n := n) N)
    (c : simplexGrid (n := n) N → n) (r : n) :
    familyDoorIncidences toTopCell c r =
      familyInternalDoorIncidences toTopCell c r ∪
        familyExteriorDoorIncidences toTopCell c r := by
  classical
  apply Finset.ext
  intro incidence
  by_cases hex : IsExteriorFacet (n := n) incidence.2 <;>
    simp [familyInternalDoorIncidences, familyExteriorDoorIncidences, hex]

lemma disjoint_familyInternalDoorIncidences_exterior {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    (toTopCell : Cell → TopCell (n := n) N)
    (c : simplexGrid (n := n) N → n) (r : n) :
    Disjoint
      (familyInternalDoorIncidences toTopCell c r)
      (familyExteriorDoorIncidences toTopCell c r) := by
  classical
  rw [Finset.disjoint_left]
  intro incidence hint hext
  rw [mem_familyInternalDoorIncidences] at hint
  rw [mem_familyExteriorDoorIncidences] at hext
  exact hint.2 hext.2

lemma exists_fullyLabeledUnitCluster_of_family_internal_even_exterior_odd {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    (toTopCell : Cell → TopCell (n := n) N)
    (c : simplexGrid (n := n) N → n) (r : n)
    (hinternal : Even (familyInternalDoorIncidences toTopCell c r).card)
    (hexterior : Odd (familyExteriorDoorIncidences toTopCell c r).card) :
    ∃ base : simplexGrid (n := n) N,
      FullyLabeledUnitCluster (n := n) c base := by
  exact exists_fullyLabeledUnitCluster_of_even_odd_incidence_partition
    toTopCell c r
    (familyInternalDoorIncidences toTopCell c r)
    (familyExteriorDoorIncidences toTopCell c r)
    (familyDoorIncidences_eq_internal_union_exterior toTopCell c r)
    (disjoint_familyInternalDoorIncidences_exterior toTopCell c r)
    hinternal hexterior

lemma image_univ_erase_eq_of_eq_off {α β : Type*} [Fintype α] [DecidableEq α]
    [DecidableEq β] {f g : α → β} (hf : Function.Injective f)
    (hg : Function.Injective g) (q : α) (hfg : ∀ t : α, t ≠ q → f t = g t) :
    ((Finset.univ : Finset α).image f).erase (f q) =
      ((Finset.univ : Finset α).image g).erase (g q) := by
  classical
  apply Finset.ext
  intro x
  constructor
  · intro hx
    rw [Finset.mem_erase] at hx
    rw [Finset.mem_erase]
    rw [Finset.mem_image] at hx
    obtain ⟨t, _ht, hft⟩ := hx.2
    have htq : t ≠ q := by
      intro htq
      exact hx.1 (by rw [← hft, htq])
    refine ⟨?_, ?_⟩
    · intro hxgq
      have hgtq : g t = g q := by
        rw [← hfg t htq, hft, hxgq]
      exact htq (hg hgtq)
    · rw [Finset.mem_image]
      exact ⟨t, Finset.mem_univ t, by rw [← hfg t htq, hft]⟩
  · intro hx
    rw [Finset.mem_erase] at hx
    rw [Finset.mem_erase]
    rw [Finset.mem_image] at hx
    obtain ⟨t, _ht, hgt⟩ := hx.2
    have htq : t ≠ q := by
      intro htq
      exact hx.1 (by rw [← hgt, htq])
    refine ⟨?_, ?_⟩
    · intro hfq
      have hftq : f t = f q := by
        rw [hfg t htq, hgt, hfq]
      exact htq (hf hftq)
    · rw [Finset.mem_image]
      exact ⟨t, Finset.mem_univ t, by rw [hfg t htq, hgt]⟩

lemma finset_insert_erase_comm {α : Type*} [DecidableEq α]
    (S : Finset α) {a b x y : α}
    (hab : a ≠ b) (hxb : x ≠ b) (hya : y ≠ a) :
    insert y ((insert x (S.erase a)).erase b) =
      insert x ((insert y (S.erase b)).erase a) := by
  classical
  apply Finset.ext
  intro z
  by_cases hzy : z = y
  · subst z
    simp [hya]
  · by_cases hzx : z = x
    · subst z
      simp [hzy, hxb]
    · by_cases hza : z = a
      · subst z
        simp [hzy, hzx, hab]
      · by_cases hzb : z = b
        · subst z
          simp [hzy, hzx]
        · simp [hzy, hzx, hza, hzb]

structure FamilyInteriorFacetNeighborData {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    (toTopCell : Cell → TopCell (n := n) N) where
  other :
    Cell → Finset (simplexGrid (n := n) N) → Cell
  other_mem :
    ∀ (cell : Cell) (face : Finset (simplexGrid (n := n) N))
      (_hfacet : face ∈ (toTopCell cell).facets)
      (_hint : ¬ IsExteriorFacet (n := n) face),
      face ∈ (toTopCell (other cell face)).facets
  other_ne :
    ∀ (cell : Cell) (face : Finset (simplexGrid (n := n) N))
      (_hfacet : face ∈ (toTopCell cell).facets)
      (_hint : ¬ IsExteriorFacet (n := n) face),
      other cell face ≠ cell
  other_involutive :
    ∀ (cell : Cell) (face : Finset (simplexGrid (n := n) N))
      (_hfacet : face ∈ (toTopCell cell).facets)
      (_hint : ¬ IsExteriorFacet (n := n) face),
      other (other cell face) face = cell

namespace FamilyInteriorFacetNeighborData

noncomputable def incidenceMate {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    {toTopCell : Cell → TopCell (n := n) N}
    (D : FamilyInteriorFacetNeighborData toTopCell)
    (_c : simplexGrid (n := n) N → n) (_r : n)
    (incidence : Σ _cell : Cell, Finset (simplexGrid (n := n) N)) :
    Σ _cell : Cell, Finset (simplexGrid (n := n) N) :=
  ⟨D.other incidence.1 incidence.2, incidence.2⟩

lemma incidenceMate_mem {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    {toTopCell : Cell → TopCell (n := n) N}
    (D : FamilyInteriorFacetNeighborData toTopCell)
    (c : simplexGrid (n := n) N → n) (r : n)
    (incidence : Σ _cell : Cell, Finset (simplexGrid (n := n) N))
    (hinc : incidence ∈ familyInternalDoorIncidences toTopCell c r) :
    D.incidenceMate c r incidence ∈ familyInternalDoorIncidences toTopCell c r := by
  classical
  rw [mem_familyInternalDoorIncidences] at hinc ⊢
  refine ⟨?_, hinc.2⟩
  rw [mem_familyDoorIncidences]
  rw [mem_familyDoorIncidences] at hinc
  have hfacet := D.other_mem incidence.1 incidence.2
      (TopCell.faceDoors_subset_facets (toTopCell incidence.1) c r hinc.1) hinc.2
  have hcolors := face_colors_of_mem_faceDoors hinc.1
  rw [TopCell.mem_facets] at hfacet
  rw [TopCell.faceDoors, Finset.mem_filter]
  exact ⟨Finset.mem_powerset.mpr hfacet.1, hfacet.2, hcolors⟩

lemma incidenceMate_involutive {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    {toTopCell : Cell → TopCell (n := n) N}
    (D : FamilyInteriorFacetNeighborData toTopCell)
    (c : simplexGrid (n := n) N → n) (r : n)
    (incidence : Σ _cell : Cell, Finset (simplexGrid (n := n) N))
    (hinc : incidence ∈ familyInternalDoorIncidences toTopCell c r) :
    D.incidenceMate c r (D.incidenceMate c r incidence) = incidence := by
  classical
  rw [mem_familyInternalDoorIncidences] at hinc
  rw [mem_familyDoorIncidences] at hinc
  apply Sigma.ext
  · exact D.other_involutive incidence.1 incidence.2
      (TopCell.faceDoors_subset_facets (toTopCell incidence.1) c r hinc.1) hinc.2
  · simp [incidenceMate]

lemma incidenceMate_fixedPointFree {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    {toTopCell : Cell → TopCell (n := n) N}
    (D : FamilyInteriorFacetNeighborData toTopCell)
    (c : simplexGrid (n := n) N → n) (r : n)
    (incidence : Σ _cell : Cell, Finset (simplexGrid (n := n) N))
    (hinc : incidence ∈ familyInternalDoorIncidences toTopCell c r) :
    D.incidenceMate c r incidence ≠ incidence := by
  classical
  intro h
  rw [mem_familyInternalDoorIncidences] at hinc
  rw [mem_familyDoorIncidences] at hinc
  have hcell : D.other incidence.1 incidence.2 = incidence.1 := congrArg Sigma.fst h
  exact D.other_ne incidence.1 incidence.2
    (TopCell.faceDoors_subset_facets (toTopCell incidence.1) c r hinc.1) hinc.2 hcell

lemma even_card_internalDoorIncidences {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    {toTopCell : Cell → TopCell (n := n) N}
    (D : FamilyInteriorFacetNeighborData toTopCell)
    (c : simplexGrid (n := n) N → n) (r : n) :
    Even (familyInternalDoorIncidences toTopCell c r).card := by
  exact even_card_finset_of_fixedPointFree_involution
    (familyInternalDoorIncidences toTopCell c r)
    (D.incidenceMate c r)
    (D.incidenceMate_mem c r)
    (D.incidenceMate_involutive c r)
    (D.incidenceMate_fixedPointFree c r)

end FamilyInteriorFacetNeighborData

lemma boundary_coord_eq_missing_of_face_colors_erase {N : ℕ}
    {c : simplexGrid (n := n) N → n} {r q : n}
    {F : Finset (simplexGrid (n := n) N)}
    (hc : ∀ (a : simplexGrid (n := n) N) (i : n), a.1 i = 0 → c a ≠ i)
    (hcolors : F.image c = Finset.univ.erase r)
    (hq : ∀ a ∈ F, a.1 q = 0) :
    q = r := by
  classical
  by_contra hqr
  have hq_mem : q ∈ F.image c := by
    rw [hcolors]
    simp [hqr]
  rw [Finset.mem_image] at hq_mem
  obtain ⟨a, haF, hca⟩ := hq_mem
  exact hc a q (hq a haF) hca

lemma fullyLabeledUnitCluster_of_full {N : ℕ}
    (cell : TopCell (n := n) N) (c : simplexGrid (n := n) N → n)
    (hfull : cell.Full c) :
    FullyLabeledUnitCluster (n := n) c cell.base := by
  exact cell.toUnitCell.fullyLabeledUnitCluster_of_full c hfull

lemma exists_fullyLabeledUnitCluster_of_odd_door_graph {N : ℕ}
    (G : SimpleGraph (Option (TopCell (n := n) N))) [DecidableRel G.Adj]
    (c : simplexGrid (n := n) N → n)
    (hout : Odd (G.degree none))
    (hodd_full :
      ∀ cell : TopCell (n := n) N, Odd (G.degree (some cell)) → cell.Full c) :
    ∃ base : simplexGrid (n := n) N,
      FullyLabeledUnitCluster (n := n) c base := by
  obtain ⟨cell, hfull⟩ :=
    exists_full_cell_of_odd_door_graph G (fun cell : TopCell (n := n) N => cell.Full c)
      hout hodd_full
  exact ⟨cell.base, cell.fullyLabeledUnitCluster_of_full c hfull⟩

lemma exists_fullyLabeledUnitCluster_of_door_graph_faceDegrees {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    (G : SimpleGraph (Option (TopCell (n := n) N))) [DecidableRel G.Adj]
    (c : simplexGrid (n := n) N → n) (r : n)
    (hout : Odd (G.degree none))
    (hdegree :
      ∀ cell : TopCell (n := n) N, G.degree (some cell) = (cell.faceDoors c r).card) :
    ∃ base : simplexGrid (n := n) N,
      FullyLabeledUnitCluster (n := n) c base := by
  refine exists_fullyLabeledUnitCluster_of_odd_door_graph G c hout ?_
  intro cell hodd
  exact full_of_odd_card_faceDoors (by
    rw [← hdegree cell]
    exact hodd)

lemma exists_fullyLabeledUnitCluster_of_family_door_graph {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {Cell : Type*} [Fintype Cell]
    (toTopCell : Cell → TopCell (n := n) N)
    (G : SimpleGraph (Option Cell)) [DecidableRel G.Adj]
    (c : simplexGrid (n := n) N → n) (r : n)
    (hout : Odd (G.degree none))
    (hdegree :
      ∀ cell : Cell, G.degree (some cell) = ((toTopCell cell).faceDoors c r).card) :
    ∃ base : simplexGrid (n := n) N,
      FullyLabeledUnitCluster (n := n) c base := by
  have hodd_full :
      ∀ cell : Cell, Odd (G.degree (some cell)) → (toTopCell cell).Full c := by
    intro cell hodd
    exact full_of_odd_card_faceDoors (by
      rw [← hdegree cell]
      exact hodd)
  obtain ⟨cell, hfull⟩ :=
    exists_full_cell_of_odd_door_graph G
      (fun cell : Cell => (toTopCell cell).Full c) hout hodd_full
  exact ⟨(toTopCell cell).base,
    (toTopCell cell).fullyLabeledUnitCluster_of_full c hfull⟩

structure DoorGraphFamilyData {N : ℕ}
    (c : simplexGrid (n := n) N → n) (r : n) where
  Cell : Type*
  fintypeCell : Fintype Cell
  toTopCell : Cell → TopCell (n := n) N
  G : SimpleGraph (Option Cell)
  decidableAdj : DecidableRel G.Adj
  outside_odd : Odd (G.degree none)
  degree_eq_faceDoors :
    ∀ cell : Cell, G.degree (some cell) = ((toTopCell cell).faceDoors c r).card

lemma exists_fullyLabeledUnitCluster_of_doorGraphFamilyData {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {c : simplexGrid (n := n) N → n} {r : n}
    (D : DoorGraphFamilyData (n := n) c r) :
    ∃ base : simplexGrid (n := n) N,
      FullyLabeledUnitCluster (n := n) c base := by
  letI := D.fintypeCell
  letI := D.decidableAdj
  exact exists_fullyLabeledUnitCluster_of_family_door_graph
    D.toTopCell D.G c r D.outside_odd D.degree_eq_faceDoors

lemma not_forall_unitNeighborhood_image_ne_univ_of_doorGraphFamilyData {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {c : simplexGrid (n := n) N → n} {r : n}
    (D : DoorGraphFamilyData (n := n) c r) :
    ¬ ∀ base : simplexGrid (n := n) N,
      ((unitNeighborhood (n := n) N base).image c : Finset n) ≠ Finset.univ := by
  intro hforall
  obtain ⟨base, hfull⟩ := exists_fullyLabeledUnitCluster_of_doorGraphFamilyData D
  exact hforall base ((fullyLabeledUnitCluster_iff_image_eq_univ c base).mp hfull)

lemma not_forall_unitNeighborhood_image_ne_univ_of_fin_card_doorGraphFamilyData [Nonempty n]
    {N : ℕ} (c : simplexGrid (n := n) N → n)
    (hc : ∀ (a : simplexGrid (n := n) N) (i : n), a.1 i = 0 → c a ≠ i)
    (hfin :
      ∀ cfin : simplexGrid (n := Fin (Fintype.card n)) N → Fin (Fintype.card n),
        (∀ (a : simplexGrid (n := Fin (Fintype.card n)) N) (i : Fin (Fintype.card n)),
          a.1 i = 0 → cfin a ≠ i) →
          ∃ r : Fin (Fintype.card n),
            Nonempty (DoorGraphFamilyData (n := Fin (Fintype.card n)) cfin r)) :
    ¬ ∀ base : simplexGrid (n := n) N,
      ((unitNeighborhood (n := n) N base).image c : Finset n) ≠ Finset.univ := by
  intro hforall
  have hcluster :
      ∃ base : simplexGrid (n := n) N,
        FullyLabeledUnitCluster (n := n) c base := by
    refine exists_fullyLabeledUnitCluster_of_fin_card_case c hc ?_
    intro cfin hcfin
    obtain ⟨r, ⟨D⟩⟩ := hfin cfin hcfin
    exact exists_fullyLabeledUnitCluster_of_doorGraphFamilyData D
  obtain ⟨base, hfull⟩ := hcluster
  exact hforall base ((fullyLabeledUnitCluster_iff_image_eq_univ c base).mp hfull)

structure CubeSliceAnchor (k N : ℕ) where
  b : Fin k → ℕ
  m : ℕ
  hm_pos : 0 < m
  hm_lt : m < k
  hsum : (∑ i, b i) + m = N

namespace CubeSliceAnchor

lemma b_le_N {k N : ℕ} (A : CubeSliceAnchor k N) (i : Fin k) :
    A.b i ≤ N := by
  have hi_le_sum : A.b i ≤ ∑ j, A.b j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (A.b j)) (Finset.mem_univ i)
  have hsum_le : ∑ j, A.b j ≤ N := by
    have hsum := A.hsum
    omega
  exact hi_le_sum.trans hsum_le

noncomputable instance instFintype (k N : ℕ) :
    Fintype (CubeSliceAnchor k N) := by
  classical
  refine Fintype.ofEquiv
    {p : (Fin k → Fin (N + 1)) × Fin (k + 1) //
      0 < p.2.1 ∧ p.2.1 < k ∧ (∑ i : Fin k, (p.1 i).1) + p.2.1 = N} ?_
  refine
    { toFun := fun p =>
        { b := fun i => (p.1.1 i).1
          m := p.1.2.1
          hm_pos := p.2.1
          hm_lt := p.2.2.1
          hsum := p.2.2.2 }
      invFun := fun A =>
        ⟨(fun i => ⟨A.b i, Nat.lt_succ_of_le (A.b_le_N i)⟩,
          ⟨A.m, Nat.lt_succ_of_lt A.hm_lt⟩),
          A.hm_pos, A.hm_lt, by simpa using A.hsum⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro p
    cases p with
    | mk val h =>
        cases val with
        | mk b m =>
            simp
  · intro A
    cases A
    rfl

end CubeSliceAnchor

def sliceVertex {k N : ℕ} (A : CubeSliceAnchor k N)
    (S : Finset (Fin k)) (hS : S.card = A.m) :
    simplexGrid (n := Fin k) N :=
  ⟨fun i => A.b i + if i ∈ S then 1 else 0, by
    have h01 :
        (∑ i : Fin k, (if i ∈ S then 1 else 0 : ℕ)) = S.card := by
      simp
    rw [Finset.sum_add_distrib, h01, hS, A.hsum]⟩

@[simp]
lemma sliceVertex_apply {k N : ℕ} (A : CubeSliceAnchor k N)
    (S : Finset (Fin k)) (hS : S.card = A.m) (i : Fin k) :
    (sliceVertex A S hS).1 i = A.b i + if i ∈ S then 1 else 0 :=
  rfl

lemma unitClose_sliceVertex_sliceVertex {k N : ℕ} (A : CubeSliceAnchor k N)
    {S T : Finset (Fin k)} (hS : S.card = A.m) (hT : T.card = A.m) :
    UnitClose (n := Fin k) (sliceVertex A S hS) (sliceVertex A T hT) := by
  intro i
  by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T <;>
    simp [sliceVertex, hiS, hiT]

lemma sliceVertex_injective {k N : ℕ} (A : CubeSliceAnchor k N)
    {S T : Finset (Fin k)} {hS : S.card = A.m} {hT : T.card = A.m}
    (h : sliceVertex A S hS = sliceVertex A T hT) :
    S = T := by
  classical
  apply Finset.ext
  intro i
  by_cases hiS : i ∈ S
  · by_cases hiT : i ∈ T
    · simp [hiS, hiT]
    · have hcoord := congrArg (fun a : simplexGrid (n := Fin k) N => a.1 i) h
      simp [sliceVertex, hiS, hiT] at hcoord
  · by_cases hiT : i ∈ T
    · have hcoord := congrArg (fun a : simplexGrid (n := Fin k) N => a.1 i) h
      simp [sliceVertex, hiS, hiT] at hcoord
    · simp [hiS, hiT]

lemma sliceVertex_insert_erase_eq_transfer {k N : ℕ} [NeZero k]
    (A : CubeSliceAnchor k N) {S : Finset (Fin k)} (hS : S.card = A.m)
    {i j : Fin k} (hij : i ≠ j) (hiS : i ∈ S) (hjS : j ∉ S)
    {hT : (insert j (S.erase i)).card = A.m} :
    sliceVertex A (insert j (S.erase i)) hT =
      transfer (n := Fin k) (sliceVertex A S hS) hij (by
        rw [sliceVertex_apply]
        simp [hiS]) := by
  apply Subtype.ext
  funext l
  by_cases hli : l = i
  · subst l
    simp [sliceVertex, hij, hiS]
  · by_cases hlj : l = j
    · subst l
      simp [sliceVertex, hjS]
    · have hli' : l ≠ i := hli
      have hlj' : l ≠ j := hlj
      simp [sliceVertex, hli', hlj']

/-- The ordered multiset union of two subsets of `Fin k`, used in the sorted-subset
description of the hypersimplex alcove triangulation. -/
noncomputable def sortedUnionList {k : ℕ} (S T : Finset (Fin k)) : List (Fin k) :=
  Multiset.sort (S.val + T.val)

/-- Alternating half of the sorted multiset union.  With zero-indexing, parity `0` is the
first, third, ... entries and parity `1` is the second, fourth, ... entries. -/
noncomputable def sortedAlternatingPart {k : ℕ} (parity : ℕ)
    (S T : Finset (Fin k)) : Finset (Fin k) :=
  (((sortedUnionList S T).zipIdx.filter fun p => decide (p.2 % 2 = parity)).map
      fun p => p.1).toFinset

/-- Sturmfels sortedness for a pair of subsets: after sorting the multiset union and
splitting alternating entries, the two resulting sets are the original two sets, in either
order.  This is the finite combinatorial predicate for hypersimplex alcoves. -/
def SortedSubsetPair {k : ℕ} (S T : Finset (Fin k)) : Prop :=
  (S = sortedAlternatingPart 0 S T ∧ T = sortedAlternatingPart 1 S T) ∨
    (S = sortedAlternatingPart 1 S T ∧ T = sortedAlternatingPart 0 S T)

structure HypersimplexAlcove (k m : ℕ) where
  verts : Finset (Finset (Fin k))
  card_verts : verts.card = k
  each_card : ∀ S ∈ verts, S.card = m
  pairwise_sorted : ∀ ⦃S : Finset (Fin k)⦄, S ∈ verts →
    ∀ ⦃T : Finset (Fin k)⦄, T ∈ verts → SortedSubsetPair S T
  maximal_sorted : ∀ T : Finset (Fin k), T.card = m →
    (∀ S ∈ verts, SortedSubsetPair S T) → T ∈ verts

namespace HypersimplexAlcove

noncomputable instance instFintype (k m : ℕ) :
    Fintype (HypersimplexAlcove k m) := by
  classical
  refine Fintype.ofEquiv
    {verts : Finset (Finset (Fin k)) //
      verts.card = k ∧
        (∀ S ∈ verts, S.card = m) ∧
        (∀ ⦃S : Finset (Fin k)⦄, S ∈ verts →
          ∀ ⦃T : Finset (Fin k)⦄, T ∈ verts → SortedSubsetPair S T) ∧
        (∀ T : Finset (Fin k), T.card = m →
          (∀ S ∈ verts, SortedSubsetPair S T) → T ∈ verts)} ?_
  refine
    { toFun := fun p =>
        { verts := p.1
          card_verts := p.2.1
          each_card := p.2.2.1
          pairwise_sorted := p.2.2.2.1
          maximal_sorted := p.2.2.2.2 }
      invFun := fun A =>
        ⟨A.verts, A.card_verts, A.each_card, A.pairwise_sorted, A.maximal_sorted⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro p
    cases p
    rfl
  · intro A
    cases A
    rfl

lemma nonempty {k m : ℕ} [NeZero k] (A : HypersimplexAlcove k m) :
    A.verts.Nonempty := by
  apply Finset.card_pos.mp
  rw [A.card_verts]
  exact Nat.pos_of_ne_zero (NeZero.ne k)

noncomputable def baseSubset {k m : ℕ} [NeZero k]
    (A : HypersimplexAlcove k m) : {S // S ∈ A.verts} :=
  ⟨Classical.choose A.nonempty, Classical.choose_spec A.nonempty⟩

lemma baseSubset_mem {k m : ℕ} [NeZero k] (A : HypersimplexAlcove k m) :
    (A.baseSubset).1 ∈ A.verts :=
  (A.baseSubset).2

lemma baseSubset_card {k m : ℕ} [NeZero k] (A : HypersimplexAlcove k m) :
    (A.baseSubset).1.card = m :=
  A.each_card (A.baseSubset).1 A.baseSubset_mem

lemma sorted_of_mem {k m : ℕ} (A : HypersimplexAlcove k m)
    {S T : Finset (Fin k)} (hS : S ∈ A.verts) (hT : T ∈ A.verts) :
    SortedSubsetPair S T :=
  A.pairwise_sorted hS hT

lemma mem_of_sorted_with_all {k m : ℕ} (A : HypersimplexAlcove k m)
    {T : Finset (Fin k)} (hT : T.card = m)
    (hsorted : ∀ S ∈ A.verts, SortedSubsetPair S T) :
    T ∈ A.verts :=
  A.maximal_sorted T hT hsorted

end HypersimplexAlcove

structure AlcoveCell (k N : ℕ) [NeZero k] where
  anchor : CubeSliceAnchor k N
  alcove : HypersimplexAlcove k anchor.m

/--
An implementation-facing presentation of hypersimplex alcoves.

`HypersimplexAlcove` is semantic: a maximal sorted finset of vertices.  This chart system keeps
named vertices and a named neighbor across each facet, which is the data needed to construct the
global door pairing without reproving the classification of sorted collections from scratch.
-/
structure HypersimplexAlcoveChartSystem (k : ℕ) [NeZero k] where
  Chart : ℕ → Type*
  fintypeChart : ∀ m : ℕ, Fintype (Chart m)
  decidableEqChart : ∀ m : ℕ, DecidableEq (Chart m)
  toAlcove : ∀ {m : ℕ}, Chart m → HypersimplexAlcove k m
  vertex : ∀ {m : ℕ}, Chart m → Fin k → Finset (Fin k)
  vertex_mem :
    ∀ {m : ℕ} (C : Chart m) (q : Fin k), vertex C q ∈ (toAlcove C).verts
  verts_eq_image :
    ∀ {m : ℕ} (C : Chart m),
      (toAlcove C).verts = (Finset.univ : Finset (Fin k)).image (vertex C)
  vertex_injective :
    ∀ {m : ℕ} (C : Chart m), Function.Injective (vertex C)
  neighbor : ∀ {m : ℕ}, Chart m → Fin k → Option (Chart m)
  neighbor_shares_facet :
    ∀ {m : ℕ} (C : Chart m) (q : Fin k) (D : Chart m),
      neighbor C q = some D →
        ∃ q' : Fin k,
          (toAlcove C).verts.erase (vertex C q) =
            (toAlcove D).verts.erase (vertex D q')
  neighbor_ne :
    ∀ {m : ℕ} (C : Chart m) (q : Fin k) (D : Chart m),
      neighbor C q = some D → D ≠ C
  neighbor_involutive :
    ∀ {m : ℕ} (C : Chart m) (q : Fin k) (D : Chart m),
      neighbor C q = some D → ∃ q' : Fin k, neighbor D q' = some C

structure ChartAlcoveCell (k N : ℕ) [NeZero k]
    (Sys : HypersimplexAlcoveChartSystem k) where
  anchor : CubeSliceAnchor k N
  chart : Sys.Chart anchor.m

namespace AlcoveCell

noncomputable instance instFintype (k N : ℕ) [NeZero k] :
    Fintype (AlcoveCell k N) := by
  classical
  refine Fintype.ofEquiv (Σ A : CubeSliceAnchor k N, HypersimplexAlcove k A.m) ?_
  refine
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun cell => ⟨cell.anchor, cell.alcove⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro p
    cases p
    rfl
  · intro cell
    cases cell
    rfl

noncomputable instance instDecidableEq (k N : ℕ) [NeZero k] :
    DecidableEq (AlcoveCell k N) :=
  Classical.decEq _

noncomputable def verts {k N : ℕ} [NeZero k] (cell : AlcoveCell k N) :
    Finset (simplexGrid (n := Fin k) N) :=
  cell.alcove.verts.attach.image fun S =>
    sliceVertex cell.anchor S.1 (cell.alcove.each_card S.1 S.2)

lemma mem_verts {k N : ℕ} [NeZero k] (cell : AlcoveCell k N)
    {a : simplexGrid (n := Fin k) N} :
    a ∈ cell.verts ↔
      ∃ S : Finset (Fin k), ∃ hS : S ∈ cell.alcove.verts,
        sliceVertex cell.anchor S (cell.alcove.each_card S hS) = a := by
  classical
  simp [verts]

lemma card_verts {k N : ℕ} [NeZero k] (cell : AlcoveCell k N) :
    cell.verts.card = Fintype.card (Fin k) := by
  classical
  rw [verts]
  have hinj :
      Function.Injective
        (fun S : {S // S ∈ cell.alcove.verts} =>
          sliceVertex cell.anchor S.1 (cell.alcove.each_card S.1 S.2)) := by
    intro S T h
    apply Subtype.ext
    exact sliceVertex_injective cell.anchor h
  rw [Finset.card_image_of_injective _ hinj]
  rw [Finset.card_attach, cell.alcove.card_verts]
  simp

noncomputable def base {k N : ℕ} [NeZero k] (cell : AlcoveCell k N) :
    simplexGrid (n := Fin k) N :=
  sliceVertex cell.anchor cell.alcove.baseSubset.1 cell.alcove.baseSubset_card

lemma base_mem_verts {k N : ℕ} [NeZero k] (cell : AlcoveCell k N) :
    cell.base ∈ cell.verts := by
  classical
  rw [mem_verts]
  exact ⟨cell.alcove.baseSubset.1, cell.alcove.baseSubset_mem, rfl⟩

noncomputable def toTopCell {k N : ℕ} [NeZero k] (cell : AlcoveCell k N) :
    TopCell (n := Fin k) N where
  verts := cell.verts
  base := cell.base
  close := by
    intro a ha
    rw [mem_verts] at ha
    obtain ⟨S, hS, rfl⟩ := ha
    exact unitClose_sliceVertex_sliceVertex cell.anchor
      (cell.alcove.each_card S hS) cell.alcove.baseSubset_card
  card_verts := cell.card_verts

@[simp]
lemma toTopCell_verts {k N : ℕ} [NeZero k] (cell : AlcoveCell k N) :
    cell.toTopCell.verts = cell.verts :=
  rfl

@[simp]
lemma toTopCell_base {k N : ℕ} [NeZero k] (cell : AlcoveCell k N) :
    cell.toTopCell.base = cell.base :=
  rfl

noncomputable def facetErasing {k N : ℕ} [NeZero k] (cell : AlcoveCell k N)
    (S : Finset (Fin k)) (hS : S ∈ cell.alcove.verts) :
    Finset (simplexGrid (n := Fin k) N) :=
  cell.verts.erase (sliceVertex cell.anchor S (cell.alcove.each_card S hS))

lemma erasedVertex_mem_verts {k N : ℕ} [NeZero k] (cell : AlcoveCell k N)
    {S : Finset (Fin k)} (hS : S ∈ cell.alcove.verts) :
    sliceVertex cell.anchor S (cell.alcove.each_card S hS) ∈ cell.verts := by
  classical
  rw [mem_verts]
  exact ⟨S, hS, rfl⟩

lemma facetErasing_mem_facets {k N : ℕ} [NeZero k] (cell : AlcoveCell k N)
    {S : Finset (Fin k)} (hS : S ∈ cell.alcove.verts) :
    cell.facetErasing S hS ∈ cell.toTopCell.facets := by
  classical
  rw [TopCell.mem_facets]
  constructor
  · intro a ha
    exact Finset.erase_subset _ _ ha
  · exact Finset.card_erase_add_one (cell.erasedVertex_mem_verts hS)

lemma mem_facetErasing {k N : ℕ} [NeZero k] (cell : AlcoveCell k N)
    {S : Finset (Fin k)} (hS : S ∈ cell.alcove.verts)
    {a : simplexGrid (n := Fin k) N} :
    a ∈ cell.facetErasing S hS ↔
      ∃ T : Finset (Fin k), ∃ hT : T ∈ cell.alcove.verts.erase S,
        sliceVertex cell.anchor T
          (cell.alcove.each_card T (Finset.erase_subset S cell.alcove.verts hT)) = a := by
  classical
  constructor
  · intro ha
    rw [facetErasing, Finset.mem_erase] at ha
    obtain ⟨ha_ne, ha_cell⟩ := ha
    rw [mem_verts] at ha_cell
    obtain ⟨T, hT, hTa⟩ := ha_cell
    have hTS : T ≠ S := by
      intro h
      subst T
      exact ha_ne hTa.symm
    refine ⟨T, ?_, ?_⟩
    · rw [Finset.mem_erase]
      exact ⟨hTS, hT⟩
    · simpa using hTa
  · rintro ⟨T, hT, hTa⟩
    rw [facetErasing, Finset.mem_erase]
    have hTmem : T ∈ cell.alcove.verts := Finset.erase_subset S cell.alcove.verts hT
    constructor
    · intro ha_eq
      have hverts :
          sliceVertex cell.anchor T (cell.alcove.each_card T hTmem) =
            sliceVertex cell.anchor S (cell.alcove.each_card S hS) := by
        exact hTa.trans ha_eq
      have hTS : T = S := sliceVertex_injective cell.anchor hverts
      exact (Finset.mem_erase.mp hT).1 hTS
    · rw [mem_verts]
      exact ⟨T, hTmem, hTa⟩

lemma facetErasing_eq_of_erase_eq {k N : ℕ} [NeZero k]
    (cell cell' : AlcoveCell k N)
    (hanchor : cell'.anchor = cell.anchor)
    {S T : Finset (Fin k)}
    (hS : S ∈ cell.alcove.verts) (hT : T ∈ cell'.alcove.verts)
    (hfacet : cell.alcove.verts.erase S = cell'.alcove.verts.erase T) :
    cell.facetErasing S hS = cell'.facetErasing T hT := by
  classical
  cases cell with
  | mk A alc =>
  cases cell' with
  | mk A' alc' =>
  dsimp at hanchor hS hT hfacet ⊢
  subst A'
  apply Finset.ext
  intro a
  rw [mem_facetErasing, mem_facetErasing]
  constructor
  · rintro ⟨U, hU, hUa⟩
    have hU' : U ∈ alc'.verts.erase T := by
      rwa [← hfacet]
    refine ⟨U, hU', ?_⟩
    simpa using hUa
  · rintro ⟨U, hU, hUa⟩
    have hU' : U ∈ alc.verts.erase S := by
      rwa [hfacet]
    refine ⟨U, hU', ?_⟩
    simpa using hUa

lemma mem_facets_iff_exists_facetErasing {k N : ℕ} [NeZero k]
    (cell : AlcoveCell k N) {face : Finset (simplexGrid (n := Fin k) N)} :
    face ∈ cell.toTopCell.facets ↔
      ∃ S : Finset (Fin k), ∃ hS : S ∈ cell.alcove.verts,
        face = cell.facetErasing S hS := by
  classical
  constructor
  · intro hface
    obtain ⟨a, ha_cell, hface_eq⟩ :=
      (TopCell.mem_facets_iff_exists_erase (cell := cell.toTopCell)).mp hface
    change a ∈ cell.verts at ha_cell
    rw [mem_verts] at ha_cell
    obtain ⟨S, hS, hSa⟩ := ha_cell
    refine ⟨S, hS, ?_⟩
    rw [facetErasing, hface_eq]
    congr 1
    exact hSa.symm
  · rintro ⟨S, hS, rfl⟩
    exact cell.facetErasing_mem_facets hS

lemma mem_faceDoors_of_mem_facets_of_colors {k N : ℕ} [NeZero k]
    {cell : AlcoveCell k N} {c : simplexGrid (n := Fin k) N → Fin k}
    {r : Fin k} {face : Finset (simplexGrid (n := Fin k) N)}
    (hfacet : face ∈ cell.toTopCell.facets)
    (hcolors : face.image c = Finset.univ.erase r) :
    face ∈ cell.toTopCell.faceDoors c r := by
  classical
  rw [TopCell.mem_facets] at hfacet
  rw [TopCell.faceDoors, Finset.mem_filter]
  exact ⟨Finset.mem_powerset.mpr hfacet.1, hfacet.2, hcolors⟩

def IsAlcoveFacet {k N : ℕ} [NeZero k]
    (F : Finset (simplexGrid (n := Fin k) N)) : Prop :=
  ∃ cell : AlcoveCell k N, F ∈ cell.toTopCell.facets

noncomputable def cellsIncidentToFacet {k N : ℕ} [NeZero k]
    (F : Finset (simplexGrid (n := Fin k) N)) : Finset (AlcoveCell k N) :=
  (Finset.univ : Finset (AlcoveCell k N)).filter fun cell =>
    F ∈ cell.toTopCell.facets

lemma mem_cellsIncidentToFacet {k N : ℕ} [NeZero k]
    {F : Finset (simplexGrid (n := Fin k) N)} {cell : AlcoveCell k N} :
    cell ∈ cellsIncidentToFacet F ↔ F ∈ cell.toTopCell.facets := by
  classical
  simp [cellsIncidentToFacet]

lemma isAlcoveFacet_iff_nonempty_cellsIncidentToFacet {k N : ℕ} [NeZero k]
    {F : Finset (simplexGrid (n := Fin k) N)} :
    IsAlcoveFacet F ↔ (cellsIncidentToFacet F).Nonempty := by
  classical
  constructor
  · rintro ⟨cell, hcell⟩
    exact ⟨cell, (mem_cellsIncidentToFacet (F := F)).mpr hcell⟩
  · rintro ⟨cell, hcell⟩
    exact ⟨cell, (mem_cellsIncidentToFacet (F := F)).mp hcell⟩

noncomputable def doorFacets {k N : ℕ} [NeZero k]
    (c : simplexGrid (n := Fin k) N → Fin k) (r : Fin k) :
    Finset (Finset (simplexGrid (n := Fin k) N)) :=
  by
    classical
    exact Finset.univ.filter fun F =>
      IsAlcoveFacet F ∧ F.image c = Finset.univ.erase r

noncomputable def exteriorDoorFacets {k N : ℕ} [NeZero k]
    (c : simplexGrid (n := Fin k) N → Fin k) (r : Fin k) :
    Finset (Finset (simplexGrid (n := Fin k) N)) :=
  by
    classical
    exact doorFacets c r |>.filter fun F => IsExteriorFacet (n := Fin k) F

lemma mem_doorFacets {k N : ℕ} [NeZero k]
    (c : simplexGrid (n := Fin k) N → Fin k) (r : Fin k)
    {F : Finset (simplexGrid (n := Fin k) N)} :
    F ∈ doorFacets c r ↔ IsAlcoveFacet F ∧ F.image c = Finset.univ.erase r := by
  classical
  simp [doorFacets]

lemma mem_exteriorDoorFacets {k N : ℕ} [NeZero k]
    (c : simplexGrid (n := Fin k) N → Fin k) (r : Fin k)
    {F : Finset (simplexGrid (n := Fin k) N)} :
    F ∈ exteriorDoorFacets c r ↔
      F ∈ doorFacets c r ∧ IsExteriorFacet (n := Fin k) F := by
  classical
  simp [exteriorDoorFacets]

noncomputable def doorIncidences {k N : ℕ} [NeZero k]
    (c : simplexGrid (n := Fin k) N → Fin k) (r : Fin k) :
    Finset (Σ _cell : AlcoveCell k N, Finset (simplexGrid (n := Fin k) N)) :=
  familyDoorIncidences (fun cell : AlcoveCell k N => cell.toTopCell) c r

noncomputable def internalDoorIncidences {k N : ℕ} [NeZero k]
    (c : simplexGrid (n := Fin k) N → Fin k) (r : Fin k) :
    Finset (Σ _cell : AlcoveCell k N, Finset (simplexGrid (n := Fin k) N)) :=
  by
    classical
    exact (doorIncidences c r).filter fun incidence =>
      ¬ IsExteriorFacet (n := Fin k) incidence.2

noncomputable def exteriorDoorIncidences {k N : ℕ} [NeZero k]
    (c : simplexGrid (n := Fin k) N → Fin k) (r : Fin k) :
    Finset (Σ _cell : AlcoveCell k N, Finset (simplexGrid (n := Fin k) N)) :=
  by
    classical
    exact (doorIncidences c r).filter fun incidence =>
      IsExteriorFacet (n := Fin k) incidence.2

lemma mem_internalDoorIncidences {k N : ℕ} [NeZero k]
    (c : simplexGrid (n := Fin k) N → Fin k) (r : Fin k)
    {incidence : Σ _cell : AlcoveCell k N, Finset (simplexGrid (n := Fin k) N)} :
    incidence ∈ internalDoorIncidences c r ↔
      incidence ∈ doorIncidences c r ∧ ¬ IsExteriorFacet (n := Fin k) incidence.2 := by
  classical
  simp [internalDoorIncidences]

lemma mem_exteriorDoorIncidences {k N : ℕ} [NeZero k]
    (c : simplexGrid (n := Fin k) N → Fin k) (r : Fin k)
    {incidence : Σ _cell : AlcoveCell k N, Finset (simplexGrid (n := Fin k) N)} :
    incidence ∈ exteriorDoorIncidences c r ↔
      incidence ∈ doorIncidences c r ∧ IsExteriorFacet (n := Fin k) incidence.2 := by
  classical
  simp [exteriorDoorIncidences]

lemma face_mem_of_mem_doorIncidences {k N : ℕ} [NeZero k]
    {c : simplexGrid (n := Fin k) N → Fin k} {r : Fin k}
    {incidence : Σ _cell : AlcoveCell k N, Finset (simplexGrid (n := Fin k) N)}
    (hinc : incidence ∈ doorIncidences c r) :
    incidence.2 ∈ (incidence.1.toTopCell).faceDoors c r := by
  classical
  simpa [doorIncidences] using
    (mem_familyDoorIncidences
      (fun cell : AlcoveCell k N => cell.toTopCell) c r).mp hinc

lemma face_mem_facets_of_mem_doorIncidences {k N : ℕ} [NeZero k]
    {c : simplexGrid (n := Fin k) N → Fin k} {r : Fin k}
    {incidence : Σ _cell : AlcoveCell k N, Finset (simplexGrid (n := Fin k) N)}
    (hinc : incidence ∈ doorIncidences c r) :
    incidence.2 ∈ incidence.1.toTopCell.facets := by
  exact TopCell.faceDoors_subset_facets incidence.1.toTopCell c r
    (face_mem_of_mem_doorIncidences hinc)

lemma face_colors_of_mem_doorIncidences {k N : ℕ} [NeZero k]
    {c : simplexGrid (n := Fin k) N → Fin k} {r : Fin k}
    {incidence : Σ _cell : AlcoveCell k N, Finset (simplexGrid (n := Fin k) N)}
    (hinc : incidence ∈ doorIncidences c r) :
    incidence.2.image c = Finset.univ.erase r := by
  exact face_colors_of_mem_faceDoors (face_mem_of_mem_doorIncidences hinc)

lemma face_mem_doorFacets_of_mem_doorIncidences {k N : ℕ} [NeZero k]
    {c : simplexGrid (n := Fin k) N → Fin k} {r : Fin k}
    {incidence : Σ _cell : AlcoveCell k N, Finset (simplexGrid (n := Fin k) N)}
    (hinc : incidence ∈ doorIncidences c r) :
    incidence.2 ∈ doorFacets c r := by
  rw [mem_doorFacets]
  exact ⟨⟨incidence.1, face_mem_facets_of_mem_doorIncidences hinc⟩,
    face_colors_of_mem_doorIncidences hinc⟩

lemma face_mem_exteriorDoorFacets_of_mem_exteriorDoorIncidences {k N : ℕ} [NeZero k]
    {c : simplexGrid (n := Fin k) N → Fin k} {r : Fin k}
    {incidence : Σ _cell : AlcoveCell k N, Finset (simplexGrid (n := Fin k) N)}
    (hinc : incidence ∈ exteriorDoorIncidences c r) :
    incidence.2 ∈ exteriorDoorFacets c r := by
  rw [mem_exteriorDoorIncidences] at hinc
  rw [mem_exteriorDoorFacets]
  exact ⟨face_mem_doorFacets_of_mem_doorIncidences hinc.1, hinc.2⟩

lemma boundary_coord_eq_missing_of_mem_exteriorDoorFacets {k N : ℕ} [NeZero k]
    {c : simplexGrid (n := Fin k) N → Fin k} {r q : Fin k}
    (hc : ∀ (a : simplexGrid (n := Fin k) N) (i : Fin k), a.1 i = 0 → c a ≠ i)
    {F : Finset (simplexGrid (n := Fin k) N)}
    (hF : F ∈ exteriorDoorFacets c r)
    (hq : ∀ a ∈ F, a.1 q = 0) :
    q = r := by
  rw [mem_exteriorDoorFacets] at hF
  rw [mem_doorFacets] at hF
  exact boundary_coord_eq_missing_of_face_colors_erase hc hF.1.2 hq

lemma boundary_coord_eq_missing_of_mem_exteriorDoorIncidences {k N : ℕ} [NeZero k]
    {c : simplexGrid (n := Fin k) N → Fin k} {r q : Fin k}
    (hc : ∀ (a : simplexGrid (n := Fin k) N) (i : Fin k), a.1 i = 0 → c a ≠ i)
    {incidence : Σ _cell : AlcoveCell k N, Finset (simplexGrid (n := Fin k) N)}
    (hinc : incidence ∈ exteriorDoorIncidences c r)
    (hq : ∀ a ∈ incidence.2, a.1 q = 0) :
    q = r := by
  rw [mem_exteriorDoorIncidences] at hinc
  exact boundary_coord_eq_missing_of_face_colors_erase hc
    (face_colors_of_mem_doorIncidences hinc.1) hq

lemma face_subset_missing_boundary_of_mem_exteriorDoorIncidences {k N : ℕ} [NeZero k]
    {c : simplexGrid (n := Fin k) N → Fin k} {r : Fin k}
    (hc : ∀ (a : simplexGrid (n := Fin k) N) (i : Fin k), a.1 i = 0 → c a ≠ i)
    {incidence : Σ _cell : AlcoveCell k N, Finset (simplexGrid (n := Fin k) N)}
    (hinc : incidence ∈ exteriorDoorIncidences c r) :
    ∀ a ∈ incidence.2, a.1 r = 0 := by
  rw [mem_exteriorDoorIncidences] at hinc
  obtain ⟨q, hq⟩ := hinc.2
  have hqr : q = r := boundary_coord_eq_missing_of_face_colors_erase hc
    (face_colors_of_mem_doorIncidences hinc.1) hq
  subst q
  exact hq

lemma doorIncidences_eq_internal_union_exterior {k N : ℕ} [NeZero k]
    (c : simplexGrid (n := Fin k) N → Fin k) (r : Fin k) :
    doorIncidences c r =
      internalDoorIncidences c r ∪ exteriorDoorIncidences c r := by
  classical
  apply Finset.ext
  intro incidence
  by_cases hex : IsExteriorFacet (n := Fin k) incidence.2 <;>
    simp [internalDoorIncidences, exteriorDoorIncidences, hex]

lemma disjoint_internalDoorIncidences_exterior {k N : ℕ} [NeZero k]
    (c : simplexGrid (n := Fin k) N → Fin k) (r : Fin k) :
    Disjoint (internalDoorIncidences c r) (exteriorDoorIncidences c r) := by
  classical
  rw [Finset.disjoint_left]
  intro incidence hint hext
  rw [mem_internalDoorIncidences] at hint
  rw [mem_exteriorDoorIncidences] at hext
  exact hint.2 hext.2

lemma odd_card_doorIncidences_of_internal_even_exterior_odd {k N : ℕ} [NeZero k]
    (c : simplexGrid (n := Fin k) N → Fin k) (r : Fin k)
    (hinternal : Even (internalDoorIncidences c r).card)
    (hexterior : Odd (exteriorDoorIncidences c r).card) :
    Odd (doorIncidences c r).card := by
  exact odd_card_familyDoorIncidences_of_even_odd_partition
    (fun cell : AlcoveCell k N => cell.toTopCell) c r
    (internalDoorIncidences c r) (exteriorDoorIncidences c r)
    (doorIncidences_eq_internal_union_exterior c r)
    (disjoint_internalDoorIncidences_exterior c r)
    hinternal hexterior

lemma exists_fullyLabeledUnitCluster_of_internal_even_exterior_odd {k N : ℕ} [NeZero k]
    (c : simplexGrid (n := Fin k) N → Fin k) (r : Fin k)
    (hinternal : Even (internalDoorIncidences c r).card)
    (hexterior : Odd (exteriorDoorIncidences c r).card) :
    ∃ base : simplexGrid (n := Fin k) N,
      FullyLabeledUnitCluster (n := Fin k) c base := by
  exact exists_fullyLabeledUnitCluster_of_odd_card_familyDoorIncidences
    (fun cell : AlcoveCell k N => cell.toTopCell) c r
    (odd_card_doorIncidences_of_internal_even_exterior_odd c r hinternal hexterior)

lemma even_card_internalDoorIncidences_of_fixedPointFree_mate {k N : ℕ} [NeZero k]
    (c : simplexGrid (n := Fin k) N → Fin k) (r : Fin k)
    (mate :
      (Σ _cell : AlcoveCell k N, Finset (simplexGrid (n := Fin k) N)) →
        (Σ _cell : AlcoveCell k N, Finset (simplexGrid (n := Fin k) N)))
    (hmem : ∀ incidence ∈ internalDoorIncidences c r,
      mate incidence ∈ internalDoorIncidences c r)
    (hinv : ∀ incidence ∈ internalDoorIncidences c r,
      mate (mate incidence) = incidence)
    (hfree : ∀ incidence ∈ internalDoorIncidences c r,
      mate incidence ≠ incidence) :
    Even (internalDoorIncidences c r).card := by
  exact even_card_finset_of_fixedPointFree_involution
    (internalDoorIncidences c r) mate hmem hinv hfree

lemma exists_fullyLabeledUnitCluster_of_internal_mate_exterior_odd {k N : ℕ} [NeZero k]
    (c : simplexGrid (n := Fin k) N → Fin k) (r : Fin k)
    (mate :
      (Σ _cell : AlcoveCell k N, Finset (simplexGrid (n := Fin k) N)) →
        (Σ _cell : AlcoveCell k N, Finset (simplexGrid (n := Fin k) N)))
    (hmem : ∀ incidence ∈ internalDoorIncidences c r,
      mate incidence ∈ internalDoorIncidences c r)
    (hinv : ∀ incidence ∈ internalDoorIncidences c r,
      mate (mate incidence) = incidence)
    (hfree : ∀ incidence ∈ internalDoorIncidences c r,
      mate incidence ≠ incidence)
    (hexterior : Odd (exteriorDoorIncidences c r).card) :
    ∃ base : simplexGrid (n := Fin k) N,
      FullyLabeledUnitCluster (n := Fin k) c base := by
  exact exists_fullyLabeledUnitCluster_of_internal_even_exterior_odd c r
    (even_card_internalDoorIncidences_of_fixedPointFree_mate
      c r mate hmem hinv hfree)
    hexterior

structure IncidenceParityCertificate {k N : ℕ} [NeZero k]
    (c : simplexGrid (n := Fin k) N → Fin k) (r : Fin k) where
  mate :
    (Σ _cell : AlcoveCell k N, Finset (simplexGrid (n := Fin k) N)) →
      (Σ _cell : AlcoveCell k N, Finset (simplexGrid (n := Fin k) N))
  mate_mem : ∀ incidence ∈ internalDoorIncidences c r,
    mate incidence ∈ internalDoorIncidences c r
  mate_involutive : ∀ incidence ∈ internalDoorIncidences c r,
    mate (mate incidence) = incidence
  mate_fixedPointFree : ∀ incidence ∈ internalDoorIncidences c r,
    mate incidence ≠ incidence
  exterior_odd : Odd (exteriorDoorIncidences c r).card

structure InteriorFacetPairingData (k N : ℕ) [NeZero k] where
  other :
    (cell : AlcoveCell k N) →
      (face : Finset (simplexGrid (n := Fin k) N)) → AlcoveCell k N
  other_mem :
    ∀ (cell : AlcoveCell k N) (face : Finset (simplexGrid (n := Fin k) N))
      (_hfacet : face ∈ cell.toTopCell.facets)
      (_hint : ¬ IsExteriorFacet (n := Fin k) face),
      face ∈ (other cell face).toTopCell.facets
  other_ne :
    ∀ (cell : AlcoveCell k N) (face : Finset (simplexGrid (n := Fin k) N))
      (_hfacet : face ∈ cell.toTopCell.facets)
      (_hint : ¬ IsExteriorFacet (n := Fin k) face),
      other cell face ≠ cell
  other_involutive :
    ∀ (cell : AlcoveCell k N) (face : Finset (simplexGrid (n := Fin k) N))
      (_hfacet : face ∈ cell.toTopCell.facets)
      (_hint : ¬ IsExteriorFacet (n := Fin k) face),
      other (other cell face) face = cell
  incidence_mate :
    (simplexGrid (n := Fin k) N → Fin k) → Fin k →
      (Σ _cell : AlcoveCell k N, Finset (simplexGrid (n := Fin k) N)) →
        (Σ _cell : AlcoveCell k N, Finset (simplexGrid (n := Fin k) N))
  incidence_mate_mem :
    ∀ (c : simplexGrid (n := Fin k) N → Fin k) (r : Fin k)
      (incidence : Σ _cell : AlcoveCell k N, Finset (simplexGrid (n := Fin k) N)),
      incidence ∈ internalDoorIncidences c r →
        incidence_mate c r incidence ∈ internalDoorIncidences c r
  incidence_mate_involutive :
    ∀ (c : simplexGrid (n := Fin k) N → Fin k) (r : Fin k)
      (incidence : Σ _cell : AlcoveCell k N, Finset (simplexGrid (n := Fin k) N)),
      incidence ∈ internalDoorIncidences c r →
        incidence_mate c r (incidence_mate c r incidence) = incidence
  incidence_mate_fixedPointFree :
    ∀ (c : simplexGrid (n := Fin k) N → Fin k) (r : Fin k)
      (incidence : Σ _cell : AlcoveCell k N, Finset (simplexGrid (n := Fin k) N)),
      incidence ∈ internalDoorIncidences c r →
        incidence_mate c r incidence ≠ incidence

structure InteriorFacetNeighborData (k N : ℕ) [NeZero k] where
  other :
    (cell : AlcoveCell k N) →
      (face : Finset (simplexGrid (n := Fin k) N)) → AlcoveCell k N
  other_mem :
    ∀ (cell : AlcoveCell k N) (face : Finset (simplexGrid (n := Fin k) N))
      (_hfacet : face ∈ cell.toTopCell.facets)
      (_hint : ¬ IsExteriorFacet (n := Fin k) face),
      face ∈ (other cell face).toTopCell.facets
  other_ne :
    ∀ (cell : AlcoveCell k N) (face : Finset (simplexGrid (n := Fin k) N))
      (_hfacet : face ∈ cell.toTopCell.facets)
      (_hint : ¬ IsExteriorFacet (n := Fin k) face),
      other cell face ≠ cell
  other_involutive :
    ∀ (cell : AlcoveCell k N) (face : Finset (simplexGrid (n := Fin k) N))
      (_hfacet : face ∈ cell.toTopCell.facets)
      (_hint : ¬ IsExteriorFacet (n := Fin k) face),
      other (other cell face) face = cell

noncomputable def InteriorFacetNeighborData.incidenceMate {k N : ℕ} [NeZero k]
    (D : InteriorFacetNeighborData k N)
    (_c : simplexGrid (n := Fin k) N → Fin k) (_r : Fin k)
    (incidence : Σ _cell : AlcoveCell k N, Finset (simplexGrid (n := Fin k) N)) :
    Σ _cell : AlcoveCell k N, Finset (simplexGrid (n := Fin k) N) :=
  ⟨D.other incidence.1 incidence.2, incidence.2⟩

lemma InteriorFacetNeighborData.incidenceMate_mem {k N : ℕ} [NeZero k]
    (D : InteriorFacetNeighborData k N)
    (c : simplexGrid (n := Fin k) N → Fin k) (r : Fin k)
    (incidence : Σ _cell : AlcoveCell k N, Finset (simplexGrid (n := Fin k) N))
    (hinc : incidence ∈ internalDoorIncidences c r) :
    D.incidenceMate c r incidence ∈ internalDoorIncidences c r := by
  classical
  rw [mem_internalDoorIncidences] at hinc ⊢
  refine ⟨?_, hinc.2⟩
  rw [doorIncidences, mem_familyDoorIncidences]
  rw [doorIncidences, mem_familyDoorIncidences] at hinc
  exact mem_faceDoors_of_mem_facets_of_colors
    (D.other_mem incidence.1 incidence.2
      (TopCell.faceDoors_subset_facets incidence.1.toTopCell c r hinc.1) hinc.2)
    (face_colors_of_mem_faceDoors hinc.1)

lemma InteriorFacetNeighborData.incidenceMate_involutive {k N : ℕ} [NeZero k]
    (D : InteriorFacetNeighborData k N)
    (c : simplexGrid (n := Fin k) N → Fin k) (r : Fin k)
    (incidence : Σ _cell : AlcoveCell k N, Finset (simplexGrid (n := Fin k) N))
    (hinc : incidence ∈ internalDoorIncidences c r) :
    D.incidenceMate c r (D.incidenceMate c r incidence) = incidence := by
  classical
  rw [mem_internalDoorIncidences] at hinc
  rw [doorIncidences, mem_familyDoorIncidences] at hinc
  apply Sigma.ext
  · exact D.other_involutive incidence.1 incidence.2
      (TopCell.faceDoors_subset_facets incidence.1.toTopCell c r hinc.1) hinc.2
  · simp [incidenceMate]

lemma InteriorFacetNeighborData.incidenceMate_fixedPointFree {k N : ℕ} [NeZero k]
    (D : InteriorFacetNeighborData k N)
    (c : simplexGrid (n := Fin k) N → Fin k) (r : Fin k)
    (incidence : Σ _cell : AlcoveCell k N, Finset (simplexGrid (n := Fin k) N))
    (hinc : incidence ∈ internalDoorIncidences c r) :
    D.incidenceMate c r incidence ≠ incidence := by
  classical
  intro h
  rw [mem_internalDoorIncidences] at hinc
  rw [doorIncidences, mem_familyDoorIncidences] at hinc
  have hcell : D.other incidence.1 incidence.2 = incidence.1 := by
    exact congrArg Sigma.fst h
  exact D.other_ne incidence.1 incidence.2
    (TopCell.faceDoors_subset_facets incidence.1.toTopCell c r hinc.1) hinc.2 hcell

noncomputable def InteriorFacetNeighborData.toInteriorFacetPairingData {k N : ℕ}
    [NeZero k] (D : InteriorFacetNeighborData k N) : InteriorFacetPairingData k N where
  other := D.other
  other_mem := D.other_mem
  other_ne := D.other_ne
  other_involutive := D.other_involutive
  incidence_mate := D.incidenceMate
  incidence_mate_mem := D.incidenceMate_mem
  incidence_mate_involutive := D.incidenceMate_involutive
  incidence_mate_fixedPointFree := D.incidenceMate_fixedPointFree

structure ExteriorDoorParityData (k N : ℕ) [NeZero k] where
  exterior_card_eq :
    ∀ (c : simplexGrid (n := Fin k) N → Fin k) (r : Fin k),
      (exteriorDoorIncidences c r).card = (exteriorDoorFacets c r).card
  exterior_facets_odd :
    ∀ (_hcardN : k < N)
      (c : simplexGrid (n := Fin k) N → Fin k) (r : Fin k),
      (∀ (a : simplexGrid (n := Fin k) N) (i : Fin k), a.1 i = 0 → c a ≠ i) →
        Odd (exteriorDoorFacets c r).card

structure AlcoveSpernerData (k N : ℕ) [NeZero k] where
  interior : InteriorFacetPairingData k N
  exterior : ExteriorDoorParityData k N

lemma exists_fullyLabeledUnitCluster_of_incidenceParityCertificate {k N : ℕ} [NeZero k]
    {c : simplexGrid (n := Fin k) N → Fin k} {r : Fin k}
    (cert : IncidenceParityCertificate c r) :
    ∃ base : simplexGrid (n := Fin k) N,
      FullyLabeledUnitCluster (n := Fin k) c base := by
  exact exists_fullyLabeledUnitCluster_of_internal_mate_exterior_odd c r
    cert.mate cert.mate_mem cert.mate_involutive cert.mate_fixedPointFree cert.exterior_odd

lemma nonempty_alcoveSpernerData_of_alcove_pseudomanifold {k N : ℕ} [NeZero k] :
    Nonempty (AlcoveSpernerData k N) := by
  /-
  Core finite combinatorial theorem for the alcove/cube-slice triangulation:
  * every non-boundary facet has a paired adjacent cell;
  * exterior facets are counted once;
  * exterior Sperner doors have odd cardinality by boundary recursion.
  -/
  sorry

lemma nonempty_interiorFacetPairingData_of_alcove_pseudomanifold {k N : ℕ} [NeZero k] :
    Nonempty (InteriorFacetPairingData k N) := by
  obtain ⟨D⟩ := nonempty_alcoveSpernerData_of_alcove_pseudomanifold (k := k) (N := N)
  exact ⟨D.interior⟩

lemma nonempty_exteriorDoorParityData_of_alcove_boundary {k N : ℕ} [NeZero k] :
    Nonempty (ExteriorDoorParityData k N) := by
  obtain ⟨D⟩ := nonempty_alcoveSpernerData_of_alcove_pseudomanifold (k := k) (N := N)
  exact ⟨D.exterior⟩

/--
Interior pseudomanifold statement for the alcove triangulation of all cube slices.

For every non-exterior door incidence, the same facet is incident to a unique cell on the other
side.  Packaged as a fixed-point-free involution because this is exactly the data needed for the
finite parity argument.
 -/
lemma exists_internalDoorIncidence_mate_of_alcove_facets {k N : ℕ} [NeZero k]
    (c : simplexGrid (n := Fin k) N → Fin k) (r : Fin k) :
    ∃ mate :
        (Σ _cell : AlcoveCell k N, Finset (simplexGrid (n := Fin k) N)) →
          (Σ _cell : AlcoveCell k N, Finset (simplexGrid (n := Fin k) N)),
      (∀ incidence ∈ internalDoorIncidences c r,
        mate incidence ∈ internalDoorIncidences c r) ∧
      (∀ incidence ∈ internalDoorIncidences c r,
        mate (mate incidence) = incidence) ∧
      (∀ incidence ∈ internalDoorIncidences c r,
        mate incidence ≠ incidence) := by
  classical
  obtain ⟨D⟩ := nonempty_interiorFacetPairingData_of_alcove_pseudomanifold (k := k) (N := N)
  exact ⟨D.incidence_mate c r, D.incidence_mate_mem c r,
    D.incidence_mate_involutive c r, D.incidence_mate_fixedPointFree c r⟩

lemma card_exteriorDoorIncidences_eq_card_exteriorDoorFacets_of_alcove_boundary {k N : ℕ}
    [NeZero k]
    (c : simplexGrid (n := Fin k) N → Fin k) (r : Fin k) :
    (exteriorDoorIncidences c r).card = (exteriorDoorFacets c r).card := by
  classical
  obtain ⟨D⟩ := nonempty_exteriorDoorParityData_of_alcove_boundary (k := k) (N := N)
  exact D.exterior_card_eq c r

lemma odd_card_exteriorDoorFacets_of_boundary_recursion {k N : ℕ} [NeZero k]
    (hcardN : k < N)
    (c : simplexGrid (n := Fin k) N → Fin k) (r : Fin k)
    (hc : ∀ (a : simplexGrid (n := Fin k) N) (i : Fin k), a.1 i = 0 → c a ≠ i) :
    Odd (exteriorDoorFacets c r).card := by
  classical
  obtain ⟨D⟩ := nonempty_exteriorDoorParityData_of_alcove_boundary (k := k) (N := N)
  exact D.exterior_facets_odd hcardN c r hc

/--
Boundary parity statement for the alcove triangulation.

Exterior `r`-doors are forced by the Sperner boundary condition to lie on the face `x_r = 0`.
After deleting that coordinate and color, they are exactly the full facets in the boundary
simplex, so their number is odd by the lower-dimensional Sperner parity recursion.
-/
lemma odd_card_exteriorDoorIncidences_of_alcove_boundary {k N : ℕ} [NeZero k]
    (hcardN : k < N)
    (c : simplexGrid (n := Fin k) N → Fin k) (r : Fin k)
    (hc : ∀ (a : simplexGrid (n := Fin k) N) (i : Fin k), a.1 i = 0 → c a ≠ i) :
    Odd (exteriorDoorIncidences c r).card := by
  rw [card_exteriorDoorIncidences_eq_card_exteriorDoorFacets_of_alcove_boundary]
  exact odd_card_exteriorDoorFacets_of_boundary_recursion hcardN c r hc

lemma exists_incidenceParityCertificate_of_alcove_triangulation {k N : ℕ} [NeZero k]
    (hcardN : k < N)
    (c : simplexGrid (n := Fin k) N → Fin k)
    (hc : ∀ (a : simplexGrid (n := Fin k) N) (i : Fin k), a.1 i = 0 → c a ≠ i) :
    ∃ r : Fin k, Nonempty (IncidenceParityCertificate c r) := by
  classical
  let r : Fin k := 0
  obtain ⟨mate, hmem, hinv, hfree⟩ :=
    exists_internalDoorIncidence_mate_of_alcove_facets c r
  exact ⟨r, ⟨
    { mate := mate
      mate_mem := hmem
      mate_involutive := hinv
      mate_fixedPointFree := hfree
      exterior_odd := odd_card_exteriorDoorIncidences_of_alcove_boundary
        hcardN c r hc }⟩⟩

lemma exists_fin_card_incidenceParityCertificate_of_card_lt
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {N : ℕ} (hcardN : Fintype.card n < N) :
    ∀ cfin : simplexGrid (n := Fin (Fintype.card n)) N → Fin (Fintype.card n),
      (∀ (a : simplexGrid (n := Fin (Fintype.card n)) N) (i : Fin (Fintype.card n)),
        a.1 i = 0 → cfin a ≠ i) →
        ∃ r : Fin (Fintype.card n), Nonempty (IncidenceParityCertificate cfin r) := by
  intro cfin hcfin
  have hk : Fintype.card n ≠ 0 := Fintype.card_ne_zero
  letI : NeZero (Fintype.card n) := ⟨hk⟩
  exact exists_incidenceParityCertificate_of_alcove_triangulation hcardN cfin hcfin

end AlcoveCell

/--
Global implementation-facing presentation of the alcove triangulation of the whole integer
simplex.

This is the interface wanted for the circuit/Stanley/Lam-Postnikov model.  Unlike
`HypersimplexAlcoveChartSystem`, the neighbor operation is allowed to move between different
cube-slice anchors.  That matters for facets on cube walls: they are paired with a cell in a
neighboring slice unless they are genuine exterior facets of the global simplex.
-/
structure GlobalAlcoveChartSystem (k N : ℕ) [NeZero k] where
  Code : Type*
  fintypeCode : Fintype Code
  decidableEqCode : DecidableEq Code
  toCell : Code → AlcoveCell k N
  codeOf : AlcoveCell k N → Code
  toCell_codeOf : ∀ cell : AlcoveCell k N, toCell (codeOf cell) = cell
  codeOf_toCell : ∀ code : Code, codeOf (toCell code) = code
  vertex : Code → Fin k → simplexGrid (n := Fin k) N
  vertex_mem :
    ∀ (C : Code) (q : Fin k), vertex C q ∈ (toCell C).toTopCell.verts
  verts_eq_image :
    ∀ C : Code,
      (toCell C).toTopCell.verts = (Finset.univ : Finset (Fin k)).image (vertex C)
  vertex_injective :
    ∀ C : Code, Function.Injective (vertex C)
  facet_index_exists :
    ∀ (C : Code) (face : Finset (simplexGrid (n := Fin k) N)),
      face ∈ (toCell C).toTopCell.facets →
        ∃ q : Fin k, face = (toCell C).toTopCell.verts.erase (vertex C q)
  neighbor : Code → Fin k → Option Code
  neighbor_shares_facet :
    ∀ (C : Code) (q : Fin k) (D : Code),
      neighbor C q = some D →
        ∃ q' : Fin k,
          (toCell C).toTopCell.verts.erase (vertex C q) =
            (toCell D).toTopCell.verts.erase (vertex D q')
  neighbor_none_exterior :
    ∀ (C : Code) (q : Fin k),
      neighbor C q = none →
        IsExteriorFacet (n := Fin k) ((toCell C).toTopCell.verts.erase (vertex C q))
  neighbor_ne_cell :
    ∀ (C : Code) (q : Fin k) (D : Code),
      neighbor C q = some D → toCell D ≠ toCell C
  neighbor_back_to_cell :
    ∀ (C D E : Code) (q q' : Fin k),
      neighbor C q = some D →
        (toCell C).toTopCell.verts.erase (vertex C q) =
          (toCell D).toTopCell.verts.erase (vertex D q') →
        neighbor D q' = some E →
          toCell E = toCell C

namespace GlobalAlcoveChartSystem

noncomputable instance instFintypeCode {k N : ℕ} [NeZero k]
    (Sys : GlobalAlcoveChartSystem k N) : Fintype Sys.Code :=
  Sys.fintypeCode

noncomputable instance instDecidableEqCode {k N : ℕ} [NeZero k]
    (Sys : GlobalAlcoveChartSystem k N) : DecidableEq Sys.Code :=
  Sys.decidableEqCode

lemma exists_neighbor_of_not_exterior {k N : ℕ} [NeZero k]
    (Sys : GlobalAlcoveChartSystem k N) (C : Sys.Code) (q : Fin k)
    (hint :
      ¬ IsExteriorFacet (n := Fin k)
        ((Sys.toCell C).toTopCell.verts.erase (Sys.vertex C q))) :
    ∃ D : Sys.Code, Sys.neighbor C q = some D := by
  classical
  cases h : Sys.neighbor C q with
  | none =>
      exact False.elim (hint (Sys.neighbor_none_exterior C q h))
  | some D =>
      exact ⟨D, rfl⟩

lemma facet_mem_of_erase_vertex {k N : ℕ} [NeZero k]
    (Sys : GlobalAlcoveChartSystem k N) (C : Sys.Code) (q : Fin k) :
    (Sys.toCell C).toTopCell.verts.erase (Sys.vertex C q) ∈
      (Sys.toCell C).toTopCell.facets := by
  classical
  rw [TopCell.mem_facets_iff_exists_erase]
  exact ⟨Sys.vertex C q, Sys.vertex_mem C q, rfl⟩

lemma facet_mem_codeOf {k N : ℕ} [NeZero k]
    (Sys : GlobalAlcoveChartSystem k N) {cell : AlcoveCell k N}
    {face : Finset (simplexGrid (n := Fin k) N)}
    (hfacet : face ∈ cell.toTopCell.facets) :
    face ∈ (Sys.toCell (Sys.codeOf cell)).toTopCell.facets := by
  simpa only [Sys.toCell_codeOf cell] using hfacet

@[irreducible]
noncomputable def other {k N : ℕ} [NeZero k]
    (Sys : GlobalAlcoveChartSystem k N)
    (cell : AlcoveCell k N)
    (face : Finset (simplexGrid (n := Fin k) N)) :
    AlcoveCell k N := by
  classical
  exact
    if hfacet : face ∈ cell.toTopCell.facets then
      let C := Sys.codeOf cell
      let q := Classical.choose (Sys.facet_index_exists C face (by
        simpa [C] using Sys.facet_mem_codeOf hfacet))
      if hint : ¬ IsExteriorFacet (n := Fin k) face then
        Sys.toCell (Classical.choose (Sys.exists_neighbor_of_not_exterior C q (by
          have hq := Classical.choose_spec
            (Sys.facet_index_exists C face (by
              simpa [C] using Sys.facet_mem_codeOf hfacet))
          rw [hq] at hint
          simpa using hint)))
      else cell
    else cell

lemma other_eq_toCell_neighbor_of_nonexterior_facet {k N : ℕ} [NeZero k]
    (Sys : GlobalAlcoveChartSystem k N)
    {cell : AlcoveCell k N}
    {face : Finset (simplexGrid (n := Fin k) N)}
    (hfacet : face ∈ cell.toTopCell.facets)
    (hint : ¬ IsExteriorFacet (n := Fin k) face) :
    let C := Sys.codeOf cell
    let q := Classical.choose (Sys.facet_index_exists C face (by
      simpa [C] using Sys.facet_mem_codeOf hfacet))
    ∃ D : Sys.Code,
      Sys.neighbor C q = some D ∧ Sys.other cell face = Sys.toCell D := by
  classical
  unfold other
  rw [dif_pos hfacet, dif_pos hint]
  refine ⟨Classical.choose
    (Sys.exists_neighbor_of_not_exterior
      (Sys.codeOf cell)
      (Classical.choose (Sys.facet_index_exists (Sys.codeOf cell) face (by
        exact Sys.facet_mem_codeOf hfacet))) ?_), ?_, rfl⟩
  · have hq := Classical.choose_spec
      (Sys.facet_index_exists (Sys.codeOf cell) face (by
        exact Sys.facet_mem_codeOf hfacet))
    rw [hq] at hint
    simpa using hint
  · exact Classical.choose_spec
      (Sys.exists_neighbor_of_not_exterior
        (Sys.codeOf cell)
        (Classical.choose (Sys.facet_index_exists (Sys.codeOf cell) face (by
          exact Sys.facet_mem_codeOf hfacet))) (by
          have hq := Classical.choose_spec
            (Sys.facet_index_exists (Sys.codeOf cell) face (by
              exact Sys.facet_mem_codeOf hfacet))
          rw [hq] at hint
          simpa using hint))

lemma other_mem_of_nonexterior {k N : ℕ} [NeZero k]
    (Sys : GlobalAlcoveChartSystem k N)
    {cell : AlcoveCell k N}
    {face : Finset (simplexGrid (n := Fin k) N)}
    (hfacet : face ∈ cell.toTopCell.facets)
    (hint : ¬ IsExteriorFacet (n := Fin k) face) :
    face ∈ (Sys.other cell face).toTopCell.facets := by
  classical
  let C := Sys.codeOf cell
  let q := Classical.choose (Sys.facet_index_exists C face (by
    simpa [C] using Sys.facet_mem_codeOf hfacet))
  have hq : face = (Sys.toCell C).toTopCell.verts.erase (Sys.vertex C q) :=
    Classical.choose_spec (Sys.facet_index_exists C face (by
      simpa [C] using Sys.facet_mem_codeOf hfacet))
  obtain ⟨D, hnei, hother⟩ :=
    Sys.other_eq_toCell_neighbor_of_nonexterior_facet hfacet hint
  obtain ⟨q', hshared⟩ := Sys.neighbor_shares_facet C q D hnei
  rw [hother, hq, hshared]
  exact Sys.facet_mem_of_erase_vertex D q'

lemma other_ne_of_nonexterior {k N : ℕ} [NeZero k]
    (Sys : GlobalAlcoveChartSystem k N)
    {cell : AlcoveCell k N}
    {face : Finset (simplexGrid (n := Fin k) N)}
    (hfacet : face ∈ cell.toTopCell.facets)
    (hint : ¬ IsExteriorFacet (n := Fin k) face) :
    Sys.other cell face ≠ cell := by
  classical
  let C := Sys.codeOf cell
  let q := Classical.choose (Sys.facet_index_exists C face (by
    simpa [C] using Sys.facet_mem_codeOf hfacet))
  obtain ⟨D, hnei, hother⟩ :=
    Sys.other_eq_toCell_neighbor_of_nonexterior_facet hfacet hint
  intro h
  exact Sys.neighbor_ne_cell C q D hnei (by
    rw [hother] at h
    simpa [C, Sys.toCell_codeOf cell] using h)

lemma other_involutive_of_nonexterior {k N : ℕ} [NeZero k]
    (Sys : GlobalAlcoveChartSystem k N)
    {cell : AlcoveCell k N}
    {face : Finset (simplexGrid (n := Fin k) N)}
    (hfacet : face ∈ cell.toTopCell.facets)
    (hint : ¬ IsExteriorFacet (n := Fin k) face) :
    Sys.other (Sys.other cell face) face = cell := by
  classical
  let C := Sys.codeOf cell
  let q := Classical.choose (Sys.facet_index_exists C face (by
    simpa [C] using Sys.facet_mem_codeOf hfacet))
  have hq : face = (Sys.toCell C).toTopCell.verts.erase (Sys.vertex C q) :=
    Classical.choose_spec (Sys.facet_index_exists C face (by
      simpa [C] using Sys.facet_mem_codeOf hfacet))
  obtain ⟨D, hnei, hother⟩ :=
    Sys.other_eq_toCell_neighbor_of_nonexterior_facet hfacet hint
  obtain ⟨_q', hshared⟩ := Sys.neighbor_shares_facet C q D hnei
  have hfacet₂ : face ∈ (Sys.toCell D).toTopCell.facets := by
    rw [hq, hshared]
    exact Sys.facet_mem_of_erase_vertex D _q'
  let C₂ := Sys.codeOf (Sys.toCell D)
  let q₂ := Classical.choose (Sys.facet_index_exists C₂ face (by
    simpa [C₂, Sys.codeOf_toCell D] using hfacet₂))
  have hq₂ :
      face = (Sys.toCell C₂).toTopCell.verts.erase (Sys.vertex C₂ q₂) :=
    Classical.choose_spec (Sys.facet_index_exists C₂ face (by
      simpa [C₂, Sys.codeOf_toCell D] using hfacet₂))
  have hshared₂ :
      (Sys.toCell C).toTopCell.verts.erase (Sys.vertex C q) =
        (Sys.toCell D).toTopCell.verts.erase (Sys.vertex D q₂) := by
    have hq₂D :
        face = (Sys.toCell D).toTopCell.verts.erase (Sys.vertex D q₂) := by
      simpa [C₂, Sys.codeOf_toCell D] using hq₂
    exact hq.symm.trans hq₂D
  obtain ⟨E, hback, hother₂⟩ :=
    Sys.other_eq_toCell_neighbor_of_nonexterior_facet
      (cell := Sys.toCell D) (face := face) hfacet₂ hint
  have hbackD : Sys.neighbor D q₂ = some E := by
    simpa [C₂, Sys.codeOf_toCell D, q₂] using hback
  have hE : Sys.toCell E = Sys.toCell C :=
    Sys.neighbor_back_to_cell C D E q q₂ hnei hshared₂ hbackD
  rw [hother, hother₂]
  simpa [C, Sys.toCell_codeOf cell] using hE

noncomputable def toInteriorFacetNeighborData {k N : ℕ} [NeZero k]
    (Sys : GlobalAlcoveChartSystem k N) :
    AlcoveCell.InteriorFacetNeighborData k N where
  other := Sys.other
  other_mem := fun _cell _face hfacet hint =>
    Sys.other_mem_of_nonexterior hfacet hint
  other_ne := fun _cell _face hfacet hint =>
    Sys.other_ne_of_nonexterior hfacet hint
  other_involutive := fun _cell _face hfacet hint =>
    Sys.other_involutive_of_nonexterior hfacet hint

noncomputable def toInteriorFacetPairingData {k N : ℕ} [NeZero k]
    (Sys : GlobalAlcoveChartSystem k N) :
    AlcoveCell.InteriorFacetPairingData k N :=
  Sys.toInteriorFacetNeighborData.toInteriorFacetPairingData

end GlobalAlcoveChartSystem

namespace CircuitAlcove

def finCycleSucc {k : ℕ} [NeZero k] (i : Fin k) : Fin k :=
  if h : i.1 + 1 < k then ⟨i.1 + 1, h⟩ else 0

lemma finCycleSucc_ne {k : ℕ} [NeZero k] [Fact (1 < k)] (i : Fin k) :
    finCycleSucc i ≠ i := by
  intro hEq
  by_cases h : i.1 + 1 < k
  · have hval := congrArg Fin.val hEq
    simp [finCycleSucc, h] at hval
  · have hval := congrArg Fin.val hEq
    simp [finCycleSucc, h] at hval
    have hk : 1 < k := Fact.out
    have hi : i.1 < k := i.2
    omega

def finCyclePred {k : ℕ} [NeZero k] [Fact (1 < k)] (i : Fin k) : Fin k :=
  if h : i.1 = 0 then ⟨k - 1, by omega⟩ else ⟨i.1 - 1, by omega⟩

lemma finCycleSucc_pred {k : ℕ} [NeZero k] [Fact (1 < k)] (i : Fin k) :
    finCycleSucc (finCyclePred i) = i := by
  apply Fin.ext
  by_cases hi : i.1 = 0
  · have hk : 1 < k := Fact.out
    have hnot : ¬ (k - 1 + 1 < k) := by omega
    simp [finCyclePred, hi, finCycleSucc, hnot]
  · have hi_pos : 0 < i.1 := Nat.pos_of_ne_zero hi
    have hi_lt : i.1 < k := i.2
    have hlt : i.1 - 1 + 1 < k := by omega
    simp [finCyclePred, hi, finCycleSucc, hlt]
    omega

lemma finCyclePred_succ {k : ℕ} [NeZero k] [Fact (1 < k)] (i : Fin k) :
    finCyclePred (finCycleSucc i) = i := by
  apply Fin.ext
  by_cases hnext : i.1 + 1 < k
  · have hne : i.1 + 1 ≠ 0 := by omega
    simp [finCycleSucc, hnext, finCyclePred]
  · have hi_lt : i.1 < k := i.2
    simp [finCycleSucc, hnext, finCyclePred]
    omega

lemma finCycleSucc_injective {k : ℕ} [NeZero k] [Fact (1 < k)] :
    Function.Injective (finCycleSucc : Fin k → Fin k) := by
  intro a b h
  calc
    a = finCyclePred (finCycleSucc a) := (finCyclePred_succ a).symm
    _ = finCyclePred (finCycleSucc b) := by rw [h]
    _ = b := finCyclePred_succ b

lemma finCyclePred_ne {k : ℕ} [NeZero k] [Fact (1 < k)] (i : Fin k) :
    finCyclePred i ≠ i := by
  intro hEq
  by_cases h : i.1 = 0
  · have hval := congrArg Fin.val hEq
    simp [finCyclePred, h] at hval
    have hk : 1 < k := Fact.out
    omega
  · have hval := congrArg Fin.val hEq
    simp [finCyclePred, h] at hval
    have hi : i.1 < k := i.2
    omega

def cyclicAdjacent {k : ℕ} [NeZero k] (a b : Fin k) : Prop :=
  finCycleSucc a = b ∨ finCycleSucc b = a

lemma cyclicAdjacent_comm {k : ℕ} [NeZero k] {a b : Fin k} :
    cyclicAdjacent a b ↔ cyclicAdjacent b a := by
  unfold cyclicAdjacent
  constructor <;> intro h <;> exact h.symm

/--
A concrete code for one circuit/alcove cell in the Lam-Postnikov model.

The vertices form a closed cyclic sequence.  At time `t`, the edge label is `word t`, meaning
that the next vertex is obtained by moving one unit from coordinate `word t` to the cyclic
successor coordinate `word t + 1`.  The `close` field records the cube-slice fact needed by the
Sperner proof: all vertices lie in one unit neighborhood.
-/
structure Code (k N : ℕ) [NeZero k] [Fact (1 < k)] where
  vertex : Fin k → simplexGrid (n := Fin k) N
  word : Equiv.Perm (Fin k)
  positive : ∀ t : Fin k, 0 < (vertex t).1 (word t)
  step :
    ∀ t : Fin k,
      vertex (finCycleSucc t) =
        transfer (n := Fin k) (vertex t) (i := word t) (j := finCycleSucc (word t))
          (Ne.symm (finCycleSucc_ne (word t))) (positive t)
  vertex_injective : Function.Injective vertex
  close : ∀ t : Fin k, UnitClose (n := Fin k) (vertex t) (vertex 0)

namespace Code

def incomingLabel {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Code k N) (q : Fin k) : Fin k :=
  C.word (finCyclePred q)

def outgoingLabel {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Code k N) (q : Fin k) : Fin k :=
  C.word q

lemma incomingLabel_ne_outgoingLabel {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Code k N) (q : Fin k) :
    C.incomingLabel q ≠ C.outgoingLabel q := by
  intro h
  exact finCyclePred_ne q (C.word.injective h)

/--
The Lam-Postnikov interior swap case for the facet obtained by deleting vertex `q`.
If the incoming and outgoing edge labels are not cyclic neighbors, the neighboring circuit is
obtained by swapping these two consecutive edge labels.  If they are cyclic neighbors, the facet
is on a cube/hypersimplex boundary and must be handled by the cube-wall/exterior case.
-/
def swapAllowed {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Code k N) (q : Fin k) : Prop :=
  ¬ cyclicAdjacent (C.incomingLabel q) (C.outgoingLabel q)

def swappedWord {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Code k N) (q : Fin k) : Equiv.Perm (Fin k) :=
  (Equiv.swap (finCyclePred q) q).trans C.word

@[simp]
lemma swappedWord_apply_pred {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Code k N) (q : Fin k) :
    C.swappedWord q (finCyclePred q) = C.outgoingLabel q := by
  simp [swappedWord, outgoingLabel]

@[simp]
lemma swappedWord_apply_self {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Code k N) (q : Fin k) :
    C.swappedWord q q = C.incomingLabel q := by
  simp [swappedWord, incomingLabel]

lemma swappedWord_apply_of_ne {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Code k N) (q t : Fin k) (htp : t ≠ finCyclePred q) (htq : t ≠ q) :
    C.swappedWord q t = C.word t := by
  rw [swappedWord, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne htp htq]

noncomputable def verts {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Code k N) : Finset (simplexGrid (n := Fin k) N) :=
  (Finset.univ : Finset (Fin k)).image C.vertex

lemma mem_verts {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Code k N) {a : simplexGrid (n := Fin k) N} :
    a ∈ C.verts ↔ ∃ t : Fin k, C.vertex t = a := by
  classical
  simp [verts]

lemma vertex_mem_verts {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Code k N) (t : Fin k) :
    C.vertex t ∈ C.verts := by
  classical
  rw [mem_verts]
  exact ⟨t, rfl⟩

lemma card_verts {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Code k N) :
    C.verts.card = Fintype.card (Fin k) := by
  classical
  rw [verts, Finset.card_image_of_injective _ C.vertex_injective]
  simp

noncomputable def toTopCell {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Code k N) : TopCell (n := Fin k) N where
  verts := C.verts
  base := C.vertex 0
  close := by
    intro a ha
    rw [mem_verts] at ha
    obtain ⟨t, rfl⟩ := ha
    exact C.close t
  card_verts := C.card_verts

noncomputable def facet {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Code k N) (q : Fin k) : Finset (simplexGrid (n := Fin k) N) :=
  C.toTopCell.verts.erase (C.vertex q)

@[simp]
lemma facet_def {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Code k N) (q : Fin k) :
    C.facet q = C.toTopCell.verts.erase (C.vertex q) :=
  rfl

lemma vertex_notMem_facet_self {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Code k N) (q : Fin k) :
    C.vertex q ∉ C.facet q := by
  classical
  simp [facet]

lemma vertex_mem_facet_iff {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Code k N) (q t : Fin k) :
    C.vertex t ∈ C.facet q ↔ t ≠ q := by
  classical
  rw [facet, Finset.mem_erase]
  constructor
  · intro h htq
    exact h.1 (by rw [htq])
  · intro htq
    exact ⟨fun h => htq (C.vertex_injective h), C.vertex_mem_verts t⟩

lemma facet_subset_verts {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Code k N) (q : Fin k) :
    C.facet q ⊆ C.toTopCell.verts := by
  classical
  exact Finset.erase_subset _ _

lemma facet_card_add_one {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Code k N) (q : Fin k) :
    (C.facet q).card + 1 = C.toTopCell.verts.card := by
  classical
  rw [facet, Finset.card_erase_add_one]
  exact C.vertex_mem_verts q

lemma erase_vertex_mem_facets {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Code k N) (q : Fin k) :
    C.toTopCell.verts.erase (C.vertex q) ∈ C.toTopCell.facets := by
  classical
  rw [TopCell.mem_facets_iff_exists_erase]
  exact ⟨C.vertex q, C.vertex_mem_verts q, rfl⟩

lemma facet_mem_facets {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Code k N) (q : Fin k) :
    C.facet q ∈ C.toTopCell.facets := by
  simpa [facet] using C.erase_vertex_mem_facets q

lemma mem_facets_iff_exists_erase_vertex {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Code k N) (face : Finset (simplexGrid (n := Fin k) N)) :
    face ∈ C.toTopCell.facets ↔
      ∃ q : Fin k, face = C.toTopCell.verts.erase (C.vertex q) := by
  classical
  rw [TopCell.mem_facets_iff_exists_erase]
  constructor
  · rintro ⟨a, ha, hface⟩
    change a ∈ C.verts at ha
    rw [mem_verts] at ha
    obtain ⟨q, hq⟩ := ha
    exact ⟨q, by rw [hface, hq]⟩
  · rintro ⟨q, hface⟩
    exact ⟨C.vertex q, C.vertex_mem_verts q, hface⟩

lemma mem_facets_iff_exists_facet {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Code k N) (face : Finset (simplexGrid (n := Fin k) N)) :
    face ∈ C.toTopCell.facets ↔ ∃ q : Fin k, face = C.facet q := by
  rw [mem_facets_iff_exists_erase_vertex]
  rfl

end Code

/--
Subset-level form of a circuit alcove inside a cube slice.

Each step replaces `word t` in the current `m`-subset by its cyclic successor.  The coordinate
lemma `sliceVertex_insert_erase_eq_transfer` turns that subset replacement into the grid
transfer step used by `Code`.
-/
structure SubsetCircuit (k N : ℕ) [NeZero k] [Fact (1 < k)] where
  anchor : CubeSliceAnchor k N
  subset : Fin k → Finset (Fin k)
  word : Equiv.Perm (Fin k)
  subset_card : ∀ t : Fin k, (subset t).card = anchor.m
  source_mem : ∀ t : Fin k, word t ∈ subset t
  target_notMem : ∀ t : Fin k, finCycleSucc (word t) ∉ subset t
  replace_subset :
    ∀ t : Fin k,
      subset (finCycleSucc t) =
        insert (finCycleSucc (word t)) ((subset t).erase (word t))
  subset_injective : Function.Injective subset

structure RawSubsetCircuit (k N : ℕ) where
  anchor : CubeSliceAnchor k N
  subset : Fin k → Finset (Fin k)
  word : Equiv.Perm (Fin k)

namespace RawSubsetCircuit

noncomputable instance instFintype (k N : ℕ) : Fintype (RawSubsetCircuit k N) := by
  classical
  refine Fintype.ofEquiv
    (CubeSliceAnchor k N × (Fin k → Finset (Fin k)) × Equiv.Perm (Fin k)) ?_
  refine
    { toFun := fun p => ⟨p.1, p.2.1, p.2.2⟩
      invFun := fun C => (C.anchor, C.subset, C.word)
      left_inv := ?_
      right_inv := ?_ }
  · intro p
    cases p with
    | mk A rest =>
        cases rest
        rfl
  · intro C
    cases C
    rfl

def IsValid {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : RawSubsetCircuit k N) : Prop :=
  (∀ t : Fin k, (C.subset t).card = C.anchor.m) ∧
  (∀ t : Fin k, C.word t ∈ C.subset t) ∧
  (∀ t : Fin k, finCycleSucc (C.word t) ∉ C.subset t) ∧
  (∀ t : Fin k,
    C.subset (finCycleSucc t) =
      insert (finCycleSucc (C.word t)) ((C.subset t).erase (C.word t))) ∧
  Function.Injective C.subset

abbrev Valid (k N : ℕ) [NeZero k] [Fact (1 < k)] :=
  {C : RawSubsetCircuit k N // C.IsValid}

noncomputable instance instFintypeValid (k N : ℕ) [NeZero k] [Fact (1 < k)] :
    Fintype (Valid k N) := by
  classical
  infer_instance

noncomputable instance instDecidableEqValid (k N : ℕ) [NeZero k] [Fact (1 < k)] :
    DecidableEq (Valid k N) := by
  classical
  infer_instance

noncomputable def toSubsetCircuit {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Valid k N) : SubsetCircuit k N where
  anchor := C.1.anchor
  subset := C.1.subset
  word := C.1.word
  subset_card := C.2.1
  source_mem := C.2.2.1
  target_notMem := C.2.2.2.1
  replace_subset := C.2.2.2.2.1
  subset_injective := C.2.2.2.2.2

noncomputable def swapCandidate {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Valid k N) (q : Fin k) : RawSubsetCircuit k N where
  anchor := C.1.anchor
  subset := fun t =>
    if t = q then
      insert (finCycleSucc (C.1.word q)) ((C.1.subset (finCyclePred q)).erase (C.1.word q))
    else C.1.subset t
  word := (Equiv.swap (finCyclePred q) q).trans C.1.word

@[simp]
lemma swapCandidate_anchor {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Valid k N) (q : Fin k) :
    (swapCandidate C q).anchor = C.1.anchor :=
  rfl

@[simp]
lemma swapCandidate_subset_self {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Valid k N) (q : Fin k) :
    (swapCandidate C q).subset q =
      insert (finCycleSucc (C.1.word q)) ((C.1.subset (finCyclePred q)).erase (C.1.word q)) := by
  simp [swapCandidate]

lemma swapCandidate_subset_of_ne {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Valid k N) (q t : Fin k) (ht : t ≠ q) :
    (swapCandidate C q).subset t = C.1.subset t := by
  simp [swapCandidate, ht]

@[simp]
lemma swapCandidate_word_pred {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Valid k N) (q : Fin k) :
    (swapCandidate C q).word (finCyclePred q) = C.1.word q := by
  simp [swapCandidate]

@[simp]
lemma swapCandidate_word_self {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Valid k N) (q : Fin k) :
    (swapCandidate C q).word q = C.1.word (finCyclePred q) := by
  simp [swapCandidate]

lemma swapCandidate_word_of_ne {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Valid k N) (q t : Fin k) (htp : t ≠ finCyclePred q) (htq : t ≠ q) :
    (swapCandidate C q).word t = C.1.word t := by
  simp [swapCandidate, Equiv.swap_apply_of_ne_of_ne htp htq]

lemma outgoing_mem_pred_of_swapAllowed {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Valid k N) (q : Fin k)
    (hallowed : ¬ cyclicAdjacent (C.1.word (finCyclePred q)) (C.1.word q)) :
    C.1.word q ∈ C.1.subset (finCyclePred q) := by
  classical
  let p := finCyclePred q
  have hrep := C.2.2.2.2.1 p
  have hpq : finCycleSucc p = q := by
    simpa [p] using finCycleSucc_pred q
  rw [hpq] at hrep
  have hmem : C.1.word q ∈ C.1.subset q := C.2.2.1 q
  rw [hrep] at hmem
  rw [Finset.mem_insert] at hmem
  rcases hmem with hhit | herase
  · exact False.elim (hallowed (Or.inl hhit.symm))
  · exact (Finset.mem_erase.mp herase).2

lemma succ_outgoing_notMem_pred_of_swapAllowed {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Valid k N) (q : Fin k)
    (hallowed : ¬ cyclicAdjacent (C.1.word (finCyclePred q)) (C.1.word q)) :
    finCycleSucc (C.1.word q) ∉ C.1.subset (finCyclePred q) := by
  classical
  intro hmem_pred
  let p := finCyclePred q
  have hrep := C.2.2.2.2.1 p
  have hpq : finCycleSucc p = q := by
    simpa [p] using finCycleSucc_pred q
  rw [hpq] at hrep
  have hne_source : finCycleSucc (C.1.word q) ≠ C.1.word p := by
    intro h
    exact hallowed (Or.inr h)
  have hmem_erase :
      finCycleSucc (C.1.word q) ∈ (C.1.subset p).erase (C.1.word p) := by
    rw [Finset.mem_erase]
    exact ⟨hne_source, hmem_pred⟩
  have hmem_q : finCycleSucc (C.1.word q) ∈ C.1.subset q := by
    rw [hrep]
    exact Finset.mem_insert_of_mem hmem_erase
  exact C.2.2.2.1 q hmem_q

lemma swapCandidate_subset_card_of_swapAllowed {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Valid k N) (q : Fin k)
    (hallowed : ¬ cyclicAdjacent (C.1.word (finCyclePred q)) (C.1.word q)) :
    ∀ t : Fin k, ((swapCandidate C q).subset t).card = (swapCandidate C q).anchor.m := by
  intro t
  by_cases htq : t = q
  · subst t
    rw [swapCandidate_subset_self, swapCandidate_anchor]
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_erase_of_mem (outgoing_mem_pred_of_swapAllowed C q hallowed)]
      rw [C.2.1 (finCyclePred q)]
      exact Nat.sub_add_cancel C.1.anchor.hm_pos
    · simp [succ_outgoing_notMem_pred_of_swapAllowed C q hallowed]
  · rw [swapCandidate_subset_of_ne C q t htq, swapCandidate_anchor]
    exact C.2.1 t

lemma swapCandidate_source_mem_of_swapAllowed {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Valid k N) (q : Fin k)
    (hallowed : ¬ cyclicAdjacent (C.1.word (finCyclePred q)) (C.1.word q)) :
    ∀ t : Fin k, (swapCandidate C q).word t ∈ (swapCandidate C q).subset t := by
  intro t
  by_cases htq : t = q
  · subst t
    rw [swapCandidate_word_self, swapCandidate_subset_self]
    rw [Finset.mem_insert, Finset.mem_erase]
    right
    constructor
    · intro hxy
      have hpq : finCyclePred q = q := C.1.word.injective hxy
      exact finCyclePred_ne q hpq
    · exact C.2.2.1 (finCyclePred q)
  · by_cases htp : t = finCyclePred q
    · subst t
      rw [swapCandidate_word_pred, swapCandidate_subset_of_ne C q (finCyclePred q)
        (finCyclePred_ne q)]
      exact outgoing_mem_pred_of_swapAllowed C q hallowed
    · rw [swapCandidate_word_of_ne C q t htp htq, swapCandidate_subset_of_ne C q t htq]
      exact C.2.2.1 t

lemma swapCandidate_target_notMem_of_swapAllowed {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Valid k N) (q : Fin k)
    (hallowed : ¬ cyclicAdjacent (C.1.word (finCyclePred q)) (C.1.word q)) :
    ∀ t : Fin k, finCycleSucc ((swapCandidate C q).word t) ∉ (swapCandidate C q).subset t := by
  intro t
  by_cases htq : t = q
  · subst t
    rw [swapCandidate_word_self, swapCandidate_subset_self]
    rw [Finset.mem_insert, Finset.mem_erase]
    intro hmem
    rcases hmem with hhit | herase
    · have hxy : C.1.word (finCyclePred q) = C.1.word q :=
        finCycleSucc_injective hhit
      have hpq : finCyclePred q = q := C.1.word.injective hxy
      exact finCyclePred_ne q hpq
    · exact C.2.2.2.1 (finCyclePred q) herase.2
  · by_cases htp : t = finCyclePred q
    · subst t
      rw [swapCandidate_word_pred, swapCandidate_subset_of_ne C q (finCyclePred q)
        (finCyclePred_ne q)]
      exact succ_outgoing_notMem_pred_of_swapAllowed C q hallowed
    · rw [swapCandidate_word_of_ne C q t htp htq, swapCandidate_subset_of_ne C q t htq]
      exact C.2.2.2.1 t

lemma swapCandidate_replace_of_ne_self_pred {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Valid k N) (q t : Fin k) (htq : t ≠ q) (htp : t ≠ finCyclePred q) :
    (swapCandidate C q).subset (finCycleSucc t) =
      insert (finCycleSucc ((swapCandidate C q).word t))
        (((swapCandidate C q).subset t).erase ((swapCandidate C q).word t)) := by
  have hsucc_ne_q : finCycleSucc t ≠ q := by
    intro h
    have hpred := congrArg finCyclePred h
    rw [finCyclePred_succ t] at hpred
    exact htp hpred
  rw [swapCandidate_subset_of_ne C q (finCycleSucc t) hsucc_ne_q]
  rw [swapCandidate_word_of_ne C q t htp htq]
  rw [swapCandidate_subset_of_ne C q t htq]
  exact C.2.2.2.2.1 t

lemma swapCandidate_replace_pred {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Valid k N) (q : Fin k) :
    (swapCandidate C q).subset (finCycleSucc (finCyclePred q)) =
      insert (finCycleSucc ((swapCandidate C q).word (finCyclePred q)))
        (((swapCandidate C q).subset (finCyclePred q)).erase
          ((swapCandidate C q).word (finCyclePred q))) := by
  rw [finCycleSucc_pred q]
  rw [swapCandidate_subset_self]
  rw [swapCandidate_word_pred]
  rw [swapCandidate_subset_of_ne C q (finCyclePred q) (finCyclePred_ne q)]

lemma swapCandidate_replace_self_of_swapAllowed {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Valid k N) (q : Fin k)
    (hallowed : ¬ cyclicAdjacent (C.1.word (finCyclePred q)) (C.1.word q)) :
    (swapCandidate C q).subset (finCycleSucc q) =
      insert (finCycleSucc ((swapCandidate C q).word q))
        (((swapCandidate C q).subset q).erase ((swapCandidate C q).word q)) := by
  rw [swapCandidate_subset_of_ne C q (finCycleSucc q) (finCycleSucc_ne q)]
  rw [C.2.2.2.2.1 q]
  rw [swapCandidate_word_self]
  rw [swapCandidate_subset_self]
  let p := finCyclePred q
  let a := C.1.word p
  let b := C.1.word q
  have hrep_p := C.2.2.2.2.1 p
  have hpq : finCycleSucc p = q := by
    simpa [p] using finCycleSucc_pred q
  rw [hpq] at hrep_p
  rw [show C.1.subset q = insert (finCycleSucc a) ((C.1.subset p).erase a) by
    simpa [a] using hrep_p]
  exact finset_insert_erase_comm (C.1.subset p)
    (a := a) (b := b) (x := finCycleSucc a) (y := finCycleSucc b)
    (by
      intro hab
      exact finCyclePred_ne q (C.1.word.injective (by simpa [p, a, b] using hab)))
    (by
      intro hxb
      exact hallowed (Or.inl (by simpa [a, b] using hxb)))
    (by
      intro hya
      exact hallowed (Or.inr (by simpa [a, b] using hya)))

lemma swapCandidate_replace_of_swapAllowed {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Valid k N) (q : Fin k)
    (hallowed : ¬ cyclicAdjacent (C.1.word (finCyclePred q)) (C.1.word q)) :
    ∀ t : Fin k,
      (swapCandidate C q).subset (finCycleSucc t) =
        insert (finCycleSucc ((swapCandidate C q).word t))
          (((swapCandidate C q).subset t).erase ((swapCandidate C q).word t)) := by
  intro t
  by_cases htq : t = q
  · subst t
    exact swapCandidate_replace_self_of_swapAllowed C q hallowed
  · by_cases htp : t = finCyclePred q
    · subst t
      exact swapCandidate_replace_pred C q
    · exact swapCandidate_replace_of_ne_self_pred C q t htq htp

lemma eq_word_of_mem_notMem_succ {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Valid k N) {t x : Fin k}
    (hmem : x ∈ C.1.subset t) (hnot : x ∉ C.1.subset (finCycleSucc t)) :
    x = C.1.word t := by
  by_contra hx
  exact hnot (by
    rw [C.2.2.2.2.1 t]
    exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hx, hmem⟩))

lemma eq_succ_word_of_notMem_mem_succ {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Valid k N) {t x : Fin k}
    (hnot : x ∉ C.1.subset t) (hmem : x ∈ C.1.subset (finCycleSucc t)) :
    x = finCycleSucc (C.1.word t) := by
  rw [C.2.2.2.2.1 t, Finset.mem_insert, Finset.mem_erase] at hmem
  rcases hmem with hhit | herase
  · exact hhit
  · exact False.elim (hnot herase.2)

lemma swapCandidate_subset_self_ne_original_pred {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Valid k N) (q : Fin k)
    (hallowed : ¬ cyclicAdjacent (C.1.word (finCyclePred q)) (C.1.word q)) :
    (swapCandidate C q).subset q ≠ C.1.subset (finCyclePred q) := by
  intro h
  have hmem : C.1.word q ∈ (swapCandidate C q).subset q := by
    rw [h]
    exact outgoing_mem_pred_of_swapAllowed C q hallowed
  rw [swapCandidate_subset_self, Finset.mem_insert, Finset.mem_erase] at hmem
  rcases hmem with hhit | herase
  · exact finCycleSucc_ne (C.1.word q) hhit.symm
  · exact herase.1 rfl

lemma swapCandidate_subset_self_ne_original_self {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Valid k N) (q : Fin k) :
    (swapCandidate C q).subset q ≠ C.1.subset q := by
  intro h
  have hmem : finCycleSucc (C.1.word q) ∈ C.1.subset q := by
    rw [← h, swapCandidate_subset_self]
    exact Finset.mem_insert_self _ _
  exact C.2.2.2.1 q hmem

lemma swapCandidate_subset_self_ne_original_succ {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Valid k N) (q : Fin k)
    (hallowed : ¬ cyclicAdjacent (C.1.word (finCyclePred q)) (C.1.word q)) :
    (swapCandidate C q).subset q ≠ C.1.subset (finCycleSucc q) := by
  intro h
  let p := finCyclePred q
  let a := C.1.word p
  let b := C.1.word q
  have ha_mem_candidate : a ∈ (swapCandidate C q).subset q := by
    rw [swapCandidate_subset_self, Finset.mem_insert, Finset.mem_erase]
    right
    constructor
    · intro hab
      exact finCyclePred_ne q (C.1.word.injective (by simpa [p, a, b] using hab))
    · exact C.2.2.1 p
  have ha_not_mem_succ : a ∉ C.1.subset (finCycleSucc q) := by
    intro ha
    have hrep_q := C.2.2.2.2.1 q
    rw [hrep_q, Finset.mem_insert, Finset.mem_erase] at ha
    rcases ha with hhit | herase
    · exact hallowed (Or.inr (by simpa [a, b] using hhit.symm))
    · have ha_not_q : a ∉ C.1.subset q := by
        have hrep_p := C.2.2.2.2.1 p
        have hpq : finCycleSucc p = q := by
          simpa [p] using finCycleSucc_pred q
        rw [hpq] at hrep_p
        rw [hrep_p, Finset.mem_insert, Finset.mem_erase]
        intro hmem
        rcases hmem with hhit | herase'
        · exact finCycleSucc_ne a (by simpa [a] using hhit.symm)
        · exact herase'.1 rfl
      exact ha_not_q herase.2
  exact ha_not_mem_succ (by rw [← h]; exact ha_mem_candidate)

lemma swapCandidate_isValid_of_swapAllowed_of_replace_injective {k N : ℕ}
    [NeZero k] [Fact (1 < k)]
    (C : Valid k N) (q : Fin k)
    (hallowed : ¬ cyclicAdjacent (C.1.word (finCyclePred q)) (C.1.word q))
    (hreplace :
      ∀ t : Fin k,
        (swapCandidate C q).subset (finCycleSucc t) =
          insert (finCycleSucc ((swapCandidate C q).word t))
            (((swapCandidate C q).subset t).erase ((swapCandidate C q).word t)))
    (hinj : Function.Injective (swapCandidate C q).subset) :
    (swapCandidate C q).IsValid :=
  ⟨swapCandidate_subset_card_of_swapAllowed C q hallowed,
    swapCandidate_source_mem_of_swapAllowed C q hallowed,
    swapCandidate_target_notMem_of_swapAllowed C q hallowed,
    hreplace,
    hinj⟩

end RawSubsetCircuit

namespace SubsetCircuit

noncomputable def vertex {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : SubsetCircuit k N) (t : Fin k) : simplexGrid (n := Fin k) N :=
  sliceVertex C.anchor (C.subset t) (C.subset_card t)

lemma vertex_injective {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : SubsetCircuit k N) : Function.Injective C.vertex := by
  intro t u h
  exact C.subset_injective (sliceVertex_injective C.anchor h)

lemma close {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : SubsetCircuit k N) (t : Fin k) :
    UnitClose (n := Fin k) (C.vertex t) (C.vertex 0) :=
  unitClose_sliceVertex_sliceVertex C.anchor (C.subset_card t) (C.subset_card 0)

noncomputable def toCode {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : SubsetCircuit k N) : Code k N where
  vertex := C.vertex
  word := C.word
  positive := by
    intro t
    rw [vertex, sliceVertex_apply]
    have hmem := C.source_mem t
    simp [hmem]
  step := by
    intro t
    change
      sliceVertex C.anchor (C.subset (finCycleSucc t)) (C.subset_card (finCycleSucc t)) =
        transfer (n := Fin k)
          (sliceVertex C.anchor (C.subset t) (C.subset_card t))
          (i := C.word t) (j := finCycleSucc (C.word t))
          (Ne.symm (finCycleSucc_ne (C.word t))) _
    convert sliceVertex_insert_erase_eq_transfer C.anchor (C.subset_card t)
      (Ne.symm (finCycleSucc_ne (C.word t)))
      (C.source_mem t) (C.target_notMem t)
      (hT := by
        rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_erase_of_mem (C.source_mem t), C.subset_card t]
          exact Nat.sub_add_cancel C.anchor.hm_pos
        · simp [C.target_notMem t]) using 1
    apply Subtype.ext
    funext x
    simp [sliceVertex, C.replace_subset t]
  vertex_injective := C.vertex_injective
  close := C.close

@[simp]
lemma toCode_vertex {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : SubsetCircuit k N) :
    C.toCode.vertex = C.vertex :=
  rfl

@[simp]
lemma toCode_word {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : SubsetCircuit k N) :
    C.toCode.word = C.word :=
  rfl

end SubsetCircuit

/--
Primary target for the explicit Lam-Postnikov construction.

This version stores actual subset circuits as the cell codes.  The fields `toCell`,
`cell_verts`, and `neighbor_*` are precisely the global triangulation theorem for these circuits.
It converts mechanically to `Model`.
-/
structure SubsetModel (k N : ℕ) [NeZero k] [Fact (1 < k)] where
  CellCode : Type*
  fintypeCellCode : Fintype CellCode
  decidableEqCellCode : DecidableEq CellCode
  circuit : CellCode → SubsetCircuit k N
  toCell : CellCode → AlcoveCell k N
  codeOf : AlcoveCell k N → CellCode
  toCell_codeOf : ∀ cell : AlcoveCell k N, toCell (codeOf cell) = cell
  codeOf_toCell : ∀ C : CellCode, codeOf (toCell C) = C
  cell_verts :
    ∀ C : CellCode, (toCell C).toTopCell.verts = (circuit C).toCode.verts
  neighbor : CellCode → Fin k → Option CellCode
  neighbor_shares_facet :
    ∀ (C : CellCode) (q : Fin k) (D : CellCode),
      neighbor C q = some D →
        ∃ q' : Fin k,
          (toCell C).toTopCell.verts.erase ((circuit C).vertex q) =
            (toCell D).toTopCell.verts.erase ((circuit D).vertex q')
  neighbor_none_exterior :
    ∀ (C : CellCode) (q : Fin k),
      neighbor C q = none →
        IsExteriorFacet (n := Fin k)
          ((toCell C).toTopCell.verts.erase ((circuit C).vertex q))
  neighbor_ne_cell :
    ∀ (C : CellCode) (q : Fin k) (D : CellCode),
      neighbor C q = some D → toCell D ≠ toCell C
  neighbor_back_to_cell :
    ∀ (C D E : CellCode) (q q' : Fin k),
      neighbor C q = some D →
        (toCell C).toTopCell.verts.erase ((circuit C).vertex q) =
          (toCell D).toTopCell.verts.erase ((circuit D).vertex q') →
        neighbor D q' = some E →
          toCell E = toCell C

namespace SubsetModel

end SubsetModel

/--
Concrete remaining target for the interior pseudomanifold theorem.

The cell codes are exactly the finite subtype `RawSubsetCircuit.Valid k N`; the fields here say
that these valid circuit codes are equivalent to the semantic alcove cells and carry the correct
facet-neighbor operation.
-/
structure ValidSubsetModelData (k N : ℕ) [NeZero k] [Fact (1 < k)] where
  toCell : RawSubsetCircuit.Valid k N → AlcoveCell k N
  codeOf : AlcoveCell k N → RawSubsetCircuit.Valid k N
  toCell_codeOf : ∀ cell : AlcoveCell k N, toCell (codeOf cell) = cell
  codeOf_toCell : ∀ C : RawSubsetCircuit.Valid k N, codeOf (toCell C) = C
  cell_verts :
    ∀ C : RawSubsetCircuit.Valid k N,
      (toCell C).toTopCell.verts = (RawSubsetCircuit.toSubsetCircuit C).toCode.verts
  neighbor : RawSubsetCircuit.Valid k N → Fin k → Option (RawSubsetCircuit.Valid k N)
  neighbor_shares_facet :
    ∀ (C : RawSubsetCircuit.Valid k N) (q : Fin k) (D : RawSubsetCircuit.Valid k N),
      neighbor C q = some D →
        ∃ q' : Fin k,
          (toCell C).toTopCell.verts.erase ((RawSubsetCircuit.toSubsetCircuit C).vertex q) =
            (toCell D).toTopCell.verts.erase ((RawSubsetCircuit.toSubsetCircuit D).vertex q')
  neighbor_none_exterior :
    ∀ (C : RawSubsetCircuit.Valid k N) (q : Fin k),
      neighbor C q = none →
        IsExteriorFacet (n := Fin k)
          ((toCell C).toTopCell.verts.erase ((RawSubsetCircuit.toSubsetCircuit C).vertex q))
  neighbor_ne_cell :
    ∀ (C : RawSubsetCircuit.Valid k N) (q : Fin k) (D : RawSubsetCircuit.Valid k N),
      neighbor C q = some D → toCell D ≠ toCell C
  neighbor_back_to_cell :
    ∀ (C D E : RawSubsetCircuit.Valid k N) (q q' : Fin k),
      neighbor C q = some D →
        (toCell C).toTopCell.verts.erase ((RawSubsetCircuit.toSubsetCircuit C).vertex q) =
          (toCell D).toTopCell.verts.erase ((RawSubsetCircuit.toSubsetCircuit D).vertex q') →
        neighbor D q' = some E →
          toCell E = toCell C

namespace ValidSubsetModelData

noncomputable def toSubsetModel {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (D : ValidSubsetModelData k N) : SubsetModel k N where
  CellCode := RawSubsetCircuit.Valid k N
  fintypeCellCode := RawSubsetCircuit.instFintypeValid k N
  decidableEqCellCode := RawSubsetCircuit.instDecidableEqValid k N
  circuit := RawSubsetCircuit.toSubsetCircuit
  toCell := D.toCell
  codeOf := D.codeOf
  toCell_codeOf := D.toCell_codeOf
  codeOf_toCell := D.codeOf_toCell
  cell_verts := D.cell_verts
  neighbor := D.neighbor
  neighbor_shares_facet := D.neighbor_shares_facet
  neighbor_none_exterior := D.neighbor_none_exterior
  neighbor_ne_cell := D.neighbor_ne_cell
  neighbor_back_to_cell := D.neighbor_back_to_cell

end ValidSubsetModelData

/--
Finite circuit presentation of all global alcove cells.

`CellCode` is intended to be the Lam-Postnikov minimal-circuit/permutation code.  The fields
below are exactly the missing finite geometry:
* every semantic `AlcoveCell` has a circuit code and vice versa;
* the vertices of the semantic cell are the vertices of the circuit;
* `neighbor C q` is the cell across the facet obtained by deleting the `q`-th circuit vertex,
  or `none` exactly at a true exterior facet.

Once this is instantiated by the explicit circuit/permutation construction, the existing
Sperner parity machinery receives a `GlobalAlcoveChartSystem` without further geometric work.
-/
structure Model (k N : ℕ) [NeZero k] [Fact (1 < k)] where
  CellCode : Type*
  fintypeCellCode : Fintype CellCode
  decidableEqCellCode : DecidableEq CellCode
  circuit : CellCode → Code k N
  toCell : CellCode → AlcoveCell k N
  codeOf : AlcoveCell k N → CellCode
  toCell_codeOf : ∀ cell : AlcoveCell k N, toCell (codeOf cell) = cell
  codeOf_toCell : ∀ C : CellCode, codeOf (toCell C) = C
  cell_verts :
    ∀ C : CellCode, (toCell C).toTopCell.verts = (circuit C).verts
  neighbor : CellCode → Fin k → Option CellCode
  neighbor_shares_facet :
    ∀ (C : CellCode) (q : Fin k) (D : CellCode),
      neighbor C q = some D →
        ∃ q' : Fin k,
          (toCell C).toTopCell.verts.erase ((circuit C).vertex q) =
            (toCell D).toTopCell.verts.erase ((circuit D).vertex q')
  neighbor_none_exterior :
    ∀ (C : CellCode) (q : Fin k),
      neighbor C q = none →
        IsExteriorFacet (n := Fin k)
          ((toCell C).toTopCell.verts.erase ((circuit C).vertex q))
  neighbor_ne_cell :
    ∀ (C : CellCode) (q : Fin k) (D : CellCode),
      neighbor C q = some D → toCell D ≠ toCell C
  neighbor_back_to_cell :
    ∀ (C D E : CellCode) (q q' : Fin k),
      neighbor C q = some D →
        (toCell C).toTopCell.verts.erase ((circuit C).vertex q) =
          (toCell D).toTopCell.verts.erase ((circuit D).vertex q') →
        neighbor D q' = some E →
          toCell E = toCell C

namespace Model

lemma vertex_mem_cell {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (M : Model k N) (C : M.CellCode) (q : Fin k) :
    (M.circuit C).vertex q ∈ (M.toCell C).toTopCell.verts := by
  rw [M.cell_verts C]
  exact (M.circuit C).vertex_mem_verts q

lemma cell_verts_eq_image {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (M : Model k N) (C : M.CellCode) :
    (M.toCell C).toTopCell.verts =
      (Finset.univ : Finset (Fin k)).image (fun q => (M.circuit C).vertex q) := by
  rw [M.cell_verts C, Code.verts]

noncomputable def toGlobalAlcoveChartSystem {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (M : Model k N) : GlobalAlcoveChartSystem k N where
  Code := M.CellCode
  fintypeCode := M.fintypeCellCode
  decidableEqCode := M.decidableEqCellCode
  toCell := M.toCell
  codeOf := M.codeOf
  toCell_codeOf := M.toCell_codeOf
  codeOf_toCell := M.codeOf_toCell
  vertex := fun C q => (M.circuit C).vertex q
  vertex_mem := M.vertex_mem_cell
  verts_eq_image := M.cell_verts_eq_image
  vertex_injective := fun C => (M.circuit C).vertex_injective
  facet_index_exists := by
    intro C face hface
    rw [TopCell.mem_facets_iff_exists_erase] at hface
    obtain ⟨v, hv, hface_eq⟩ := hface
    rw [M.cell_verts C, Code.mem_verts] at hv
    obtain ⟨q, hq⟩ := hv
    refine ⟨q, ?_⟩
    rw [hface_eq, M.cell_verts C, ← hq]
  neighbor := M.neighbor
  neighbor_shares_facet := M.neighbor_shares_facet
  neighbor_none_exterior := M.neighbor_none_exterior
  neighbor_ne_cell := M.neighbor_ne_cell
  neighbor_back_to_cell := M.neighbor_back_to_cell

noncomputable def toInteriorFacetPairingData {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (M : Model k N) : AlcoveCell.InteriorFacetPairingData k N :=
  M.toGlobalAlcoveChartSystem.toInteriorFacetPairingData

lemma nonempty_interiorFacetPairingData {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (M : Model k N) : Nonempty (AlcoveCell.InteriorFacetPairingData k N) :=
  ⟨M.toInteriorFacetPairingData⟩

noncomputable def toAlcoveSpernerData {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (M : Model k N) (E : AlcoveCell.ExteriorDoorParityData k N) :
    AlcoveCell.AlcoveSpernerData k N where
  interior := M.toInteriorFacetPairingData
  exterior := E

lemma nonempty_alcoveSpernerData {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (M : Model k N) (E : AlcoveCell.ExteriorDoorParityData k N) :
    Nonempty (AlcoveCell.AlcoveSpernerData k N) :=
  ⟨M.toAlcoveSpernerData E⟩

end Model

namespace SubsetModel

noncomputable def toModel {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (M : SubsetModel k N) : Model k N where
  CellCode := M.CellCode
  fintypeCellCode := M.fintypeCellCode
  decidableEqCellCode := M.decidableEqCellCode
  circuit := fun C => (M.circuit C).toCode
  toCell := M.toCell
  codeOf := M.codeOf
  toCell_codeOf := M.toCell_codeOf
  codeOf_toCell := M.codeOf_toCell
  cell_verts := M.cell_verts
  neighbor := M.neighbor
  neighbor_shares_facet := by
    intro C q D hnei
    exact M.neighbor_shares_facet C q D hnei
  neighbor_none_exterior := by
    intro C q hnei
    exact M.neighbor_none_exterior C q hnei
  neighbor_ne_cell := M.neighbor_ne_cell
  neighbor_back_to_cell := M.neighbor_back_to_cell

noncomputable def toInteriorFacetPairingData {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (M : SubsetModel k N) : AlcoveCell.InteriorFacetPairingData k N :=
  M.toModel.toInteriorFacetPairingData

noncomputable def toAlcoveSpernerData {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (M : SubsetModel k N) (E : AlcoveCell.ExteriorDoorParityData k N) :
    AlcoveCell.AlcoveSpernerData k N :=
  M.toModel.toAlcoveSpernerData E

end SubsetModel

namespace ValidSubsetModelData

noncomputable def toInteriorFacetPairingData {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (D : ValidSubsetModelData k N) : AlcoveCell.InteriorFacetPairingData k N :=
  D.toSubsetModel.toInteriorFacetPairingData

noncomputable def toAlcoveSpernerData {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (D : ValidSubsetModelData k N) (E : AlcoveCell.ExteriorDoorParityData k N) :
    AlcoveCell.AlcoveSpernerData k N :=
  D.toSubsetModel.toAlcoveSpernerData E

lemma nonempty_interiorFacetPairingData {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (D : ValidSubsetModelData k N) :
    Nonempty (AlcoveCell.InteriorFacetPairingData k N) :=
  ⟨D.toInteriorFacetPairingData⟩

lemma nonempty_alcoveSpernerData {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (D : ValidSubsetModelData k N) (E : AlcoveCell.ExteriorDoorParityData k N) :
    Nonempty (AlcoveCell.AlcoveSpernerData k N) :=
  ⟨D.toAlcoveSpernerData E⟩

end ValidSubsetModelData

namespace RawSubsetCircuit

noncomputable def validToTopCell {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Valid k N) : TopCell (n := Fin k) N :=
  (toSubsetCircuit C).toCode.toTopCell

lemma swapCandidate_vertex_of_ne {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Valid k N) (q t : Fin k) (htq : t ≠ q)
    (hvalid : (swapCandidate C q).IsValid) :
    (toSubsetCircuit ⟨swapCandidate C q, hvalid⟩).vertex t =
      (toSubsetCircuit C).vertex t := by
  apply Subtype.ext
  funext i
  simp [SubsetCircuit.vertex, toSubsetCircuit, swapCandidate, htq]

lemma swapCandidate_facet_eq {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Valid k N) (q : Fin k) (hvalid : (swapCandidate C q).IsValid) :
    (validToTopCell C).verts.erase ((toSubsetCircuit C).vertex q) =
      (validToTopCell ⟨swapCandidate C q, hvalid⟩).verts.erase
        ((toSubsetCircuit ⟨swapCandidate C q, hvalid⟩).vertex q) := by
  classical
  change
    ((Finset.univ : Finset (Fin k)).image (toSubsetCircuit C).vertex).erase
        ((toSubsetCircuit C).vertex q) =
      ((Finset.univ : Finset (Fin k)).image
        (toSubsetCircuit ⟨swapCandidate C q, hvalid⟩).vertex).erase
        ((toSubsetCircuit ⟨swapCandidate C q, hvalid⟩).vertex q)
  exact image_univ_erase_eq_of_eq_off
    (toSubsetCircuit C).vertex_injective
    (toSubsetCircuit ⟨swapCandidate C q, hvalid⟩).vertex_injective
    q (by
      intro t htq
      exact (swapCandidate_vertex_of_ne C q t htq hvalid).symm)

lemma swapCandidate_facet_mem {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (C : Valid k N) (q : Fin k) (hvalid : (swapCandidate C q).IsValid) :
    (validToTopCell C).verts.erase ((toSubsetCircuit C).vertex q) ∈
      (validToTopCell ⟨swapCandidate C q, hvalid⟩).facets := by
  classical
  rw [swapCandidate_facet_eq C q hvalid]
  rw [TopCell.mem_facets_iff_exists_erase]
  exact ⟨(toSubsetCircuit ⟨swapCandidate C q, hvalid⟩).vertex q,
    by
      change (toSubsetCircuit ⟨swapCandidate C q, hvalid⟩).vertex q ∈
        (toSubsetCircuit ⟨swapCandidate C q, hvalid⟩).toCode.verts
      exact (toSubsetCircuit ⟨swapCandidate C q, hvalid⟩).toCode.vertex_mem_verts q,
    rfl⟩

structure ValidIncidenceParityCertificate {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (c : simplexGrid (n := Fin k) N → Fin k) (r : Fin k) where
  mate :
    (Σ _cell : Valid k N, Finset (simplexGrid (n := Fin k) N)) →
      (Σ _cell : Valid k N, Finset (simplexGrid (n := Fin k) N))
  mate_mem : ∀ incidence ∈
      familyInternalDoorIncidences (n := Fin k) validToTopCell c r,
    mate incidence ∈ familyInternalDoorIncidences (n := Fin k) validToTopCell c r
  mate_involutive : ∀ incidence ∈
      familyInternalDoorIncidences (n := Fin k) validToTopCell c r,
    mate (mate incidence) = incidence
  mate_fixedPointFree : ∀ incidence ∈
      familyInternalDoorIncidences (n := Fin k) validToTopCell c r,
    mate incidence ≠ incidence
  exterior_odd :
    Odd (familyExteriorDoorIncidences (n := Fin k) validToTopCell c r).card

structure ValidNeighborParityData {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (c : simplexGrid (n := Fin k) N → Fin k) (r : Fin k) where
  neighborData :
    FamilyInteriorFacetNeighborData (n := Fin k)
      (Cell := Valid k N) validToTopCell
  exterior_odd :
    Odd (familyExteriorDoorIncidences (n := Fin k) validToTopCell c r).card

structure ValidPseudomanifoldData (k N : ℕ) [NeZero k] [Fact (1 < k)] where
  other_exists_unique :
    ∀ (C : Valid k N) (face : Finset (simplexGrid (n := Fin k) N)),
      face ∈ (validToTopCell C).facets →
      ¬ IsExteriorFacet (n := Fin k) face →
        ∃ D : Valid k N,
          D ≠ C ∧
          face ∈ (validToTopCell D).facets ∧
          ∀ E : Valid k N,
            face ∈ (validToTopCell E).facets → E = C ∨ E = D

namespace ValidPseudomanifoldData

noncomputable def other {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (D : ValidPseudomanifoldData k N)
    (C : Valid k N) (face : Finset (simplexGrid (n := Fin k) N)) :
    Valid k N := by
  classical
  exact
    if hfacet : face ∈ (validToTopCell C).facets then
      if hint : ¬ IsExteriorFacet (n := Fin k) face then
        Classical.choose (D.other_exists_unique C face hfacet hint)
      else C
    else C

lemma other_spec {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (D : ValidPseudomanifoldData k N)
    {C : Valid k N} {face : Finset (simplexGrid (n := Fin k) N)}
    (hfacet : face ∈ (validToTopCell C).facets)
    (hint : ¬ IsExteriorFacet (n := Fin k) face) :
    let C' := D.other C face
    C' ≠ C ∧
      face ∈ (validToTopCell C').facets ∧
      ∀ E : Valid k N,
        face ∈ (validToTopCell E).facets → E = C ∨ E = C' := by
  classical
  unfold other
  rw [dif_pos hfacet, dif_pos hint]
  exact Classical.choose_spec (D.other_exists_unique C face hfacet hint)

noncomputable def toFamilyInteriorFacetNeighborData {k N : ℕ} [NeZero k] [Fact (1 < k)]
    (D : ValidPseudomanifoldData k N) :
    FamilyInteriorFacetNeighborData (n := Fin k)
      (Cell := Valid k N) validToTopCell where
  other := D.other
  other_mem := by
    intro C face hfacet hint
    exact (D.other_spec hfacet hint).2.1
  other_ne := by
    intro C face hfacet hint
    exact (D.other_spec hfacet hint).1
  other_involutive := by
    intro C face hfacet hint
    let C' := D.other C face
    have hspec := D.other_spec hfacet hint
    have hfacet' : face ∈ (validToTopCell C').facets := hspec.2.1
    have hspec' := D.other_spec hfacet' hint
    have hother_facet : face ∈ (validToTopCell (D.other C' face)).facets := hspec'.2.1
    have hother_ne : D.other C' face ≠ C' := hspec'.1
    rcases hspec.2.2 (D.other C' face) hother_facet with hEq | hEq
    · exact hEq
    · exact False.elim (hother_ne hEq)

end ValidPseudomanifoldData

noncomputable def validNeighborParityData_of_pseudomanifold_exterior {k N : ℕ}
    [NeZero k] [Fact (1 < k)]
    {c : simplexGrid (n := Fin k) N → Fin k} {r : Fin k}
    (P : ValidPseudomanifoldData k N)
    (hexterior :
      Odd (familyExteriorDoorIncidences (n := Fin k) validToTopCell c r).card) :
    ValidNeighborParityData c r where
  neighborData := P.toFamilyInteriorFacetNeighborData
  exterior_odd := hexterior

noncomputable def ValidNeighborParityData.toValidIncidenceParityCertificate {k N : ℕ}
    [NeZero k] [Fact (1 < k)]
    {c : simplexGrid (n := Fin k) N → Fin k} {r : Fin k}
    (D : ValidNeighborParityData c r) :
    ValidIncidenceParityCertificate c r where
  mate := D.neighborData.incidenceMate c r
  mate_mem := D.neighborData.incidenceMate_mem c r
  mate_involutive := D.neighborData.incidenceMate_involutive c r
  mate_fixedPointFree := D.neighborData.incidenceMate_fixedPointFree c r
  exterior_odd := D.exterior_odd

lemma even_card_valid_internalDoorIncidences_of_fixedPointFree_mate {k N : ℕ}
    [NeZero k] [Fact (1 < k)]
    (c : simplexGrid (n := Fin k) N → Fin k) (r : Fin k)
    (cert : ValidIncidenceParityCertificate c r) :
    Even (familyInternalDoorIncidences (n := Fin k) validToTopCell c r).card := by
  exact even_card_finset_of_fixedPointFree_involution
    (familyInternalDoorIncidences (n := Fin k) validToTopCell c r)
    cert.mate cert.mate_mem cert.mate_involutive cert.mate_fixedPointFree

lemma exists_fullyLabeledUnitCluster_of_validIncidenceParityCertificate {k N : ℕ}
    [NeZero k] [Fact (1 < k)]
    {c : simplexGrid (n := Fin k) N → Fin k} {r : Fin k}
    (cert : ValidIncidenceParityCertificate c r) :
    ∃ base : simplexGrid (n := Fin k) N,
      FullyLabeledUnitCluster (n := Fin k) c base := by
  exact exists_fullyLabeledUnitCluster_of_family_internal_even_exterior_odd
    (n := Fin k) validToTopCell c r
    (even_card_valid_internalDoorIncidences_of_fixedPointFree_mate c r cert)
    cert.exterior_odd

lemma exists_fullyLabeledUnitCluster_of_validNeighborParityData {k N : ℕ}
    [NeZero k] [Fact (1 < k)]
    {c : simplexGrid (n := Fin k) N → Fin k} {r : Fin k}
    (D : ValidNeighborParityData c r) :
    ∃ base : simplexGrid (n := Fin k) N,
      FullyLabeledUnitCluster (n := Fin k) c base :=
  exists_fullyLabeledUnitCluster_of_validIncidenceParityCertificate
    D.toValidIncidenceParityCertificate

end RawSubsetCircuit

end CircuitAlcove

namespace ChartAlcoveCell

noncomputable instance instFintype {k N : ℕ} [NeZero k]
    (Sys : HypersimplexAlcoveChartSystem k) :
    Fintype (ChartAlcoveCell k N Sys) := by
  classical
  letI (m : ℕ) : Fintype (Sys.Chart m) := Sys.fintypeChart m
  refine Fintype.ofEquiv (Σ A : CubeSliceAnchor k N, Sys.Chart A.m) ?_
  refine
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun cell => ⟨cell.anchor, cell.chart⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro p
    cases p
    rfl
  · intro cell
    cases cell
    rfl

noncomputable instance instDecidableEq {k N : ℕ} [NeZero k]
    (Sys : HypersimplexAlcoveChartSystem k) :
    DecidableEq (ChartAlcoveCell k N Sys) :=
  Classical.decEq _

noncomputable def toAlcoveCell {k N : ℕ} [NeZero k]
    {Sys : HypersimplexAlcoveChartSystem k} (cell : ChartAlcoveCell k N Sys) :
    AlcoveCell k N where
  anchor := cell.anchor
  alcove := Sys.toAlcove cell.chart

noncomputable def vertex {k N : ℕ} [NeZero k]
    {Sys : HypersimplexAlcoveChartSystem k} (cell : ChartAlcoveCell k N Sys)
    (q : Fin k) : simplexGrid (n := Fin k) N :=
  sliceVertex cell.anchor (Sys.vertex cell.chart q)
    ((Sys.toAlcove cell.chart).each_card
      (Sys.vertex cell.chart q) (Sys.vertex_mem cell.chart q))

lemma vertex_mem_toAlcoveCell {k N : ℕ} [NeZero k]
    {Sys : HypersimplexAlcoveChartSystem k} (cell : ChartAlcoveCell k N Sys)
    (q : Fin k) :
    cell.vertex q ∈ cell.toAlcoveCell.verts := by
  classical
  rw [AlcoveCell.mem_verts]
  exact ⟨Sys.vertex cell.chart q, Sys.vertex_mem cell.chart q, rfl⟩

noncomputable def toTopCell {k N : ℕ} [NeZero k]
    {Sys : HypersimplexAlcoveChartSystem k} (cell : ChartAlcoveCell k N Sys) :
    TopCell (n := Fin k) N :=
  cell.toAlcoveCell.toTopCell

lemma toTopCell_verts_eq_image_vertex {k N : ℕ} [NeZero k]
    {Sys : HypersimplexAlcoveChartSystem k} (cell : ChartAlcoveCell k N Sys) :
    cell.toTopCell.verts = (Finset.univ : Finset (Fin k)).image (cell.vertex) := by
  classical
  apply Finset.ext
  intro a
  constructor
  · intro ha
    change a ∈ cell.toAlcoveCell.verts at ha
    rw [AlcoveCell.mem_verts] at ha
    obtain ⟨S, hS, hSa⟩ := ha
    have hSimg : S ∈ (Finset.univ : Finset (Fin k)).image (Sys.vertex cell.chart) := by
      change S ∈ (Sys.toAlcove cell.chart).verts at hS
      rwa [Sys.verts_eq_image cell.chart] at hS
    rw [Finset.mem_image] at hSimg
    obtain ⟨q, hq, hqS⟩ := hSimg
    rw [Finset.mem_image]
    refine ⟨q, hq, ?_⟩
    subst S
    simpa [vertex] using hSa
  · intro ha
    rw [Finset.mem_image] at ha
    obtain ⟨q, _hq, hqa⟩ := ha
    rw [← hqa]
    exact cell.vertex_mem_toAlcoveCell q

lemma mem_facets_iff_exists_erase_vertex {k N : ℕ} [NeZero k]
    {Sys : HypersimplexAlcoveChartSystem k} (cell : ChartAlcoveCell k N Sys)
    {face : Finset (simplexGrid (n := Fin k) N)} :
    face ∈ cell.toTopCell.facets ↔
      ∃ q : Fin k, face = cell.toTopCell.verts.erase (cell.vertex q) := by
  classical
  constructor
  · intro hface
    have hface' : face ∈ cell.toAlcoveCell.toTopCell.facets := hface
    obtain ⟨S, hS, hface_eq⟩ :=
      (AlcoveCell.mem_facets_iff_exists_facetErasing cell.toAlcoveCell).mp hface'
    have hSimg : S ∈ (Finset.univ : Finset (Fin k)).image (Sys.vertex cell.chart) := by
      change S ∈ (Sys.toAlcove cell.chart).verts at hS
      rwa [Sys.verts_eq_image cell.chart] at hS
    rw [Finset.mem_image] at hSimg
    obtain ⟨q, _hqmem, hqS⟩ := hSimg
    refine ⟨q, ?_⟩
    subst S
    simpa [toTopCell, vertex, toAlcoveCell, AlcoveCell.facetErasing] using hface_eq
  · rintro ⟨q, rfl⟩
    have hv : cell.vertex q ∈ cell.toAlcoveCell.verts :=
      cell.vertex_mem_toAlcoveCell q
    rw [toTopCell, TopCell.mem_facets_iff_exists_erase]
    exact ⟨cell.vertex q, hv, rfl⟩

noncomputable def neighborCell {k N : ℕ} [NeZero k]
    {Sys : HypersimplexAlcoveChartSystem k} (cell : ChartAlcoveCell k N Sys)
    (q : Fin k) : Option (ChartAlcoveCell k N Sys) :=
  (Sys.neighbor cell.chart q).map fun chart' =>
    { anchor := cell.anchor, chart := chart' }

structure BoundaryData {k : ℕ} [NeZero k] (Sys : HypersimplexAlcoveChartSystem k) where
  neighbor_none_exterior :
    ∀ {N : ℕ} (cell : ChartAlcoveCell k N Sys) (q : Fin k),
      cell.neighborCell q = none →
        IsExteriorFacet (n := Fin k) (cell.toTopCell.verts.erase (cell.vertex q))

lemma neighborCell_none_imp_exterior {k N : ℕ} [NeZero k]
    {Sys : HypersimplexAlcoveChartSystem k} (B : BoundaryData Sys)
    (cell : ChartAlcoveCell k N Sys)
    (q : Fin k) (hnei : cell.neighborCell q = none) :
    IsExteriorFacet (n := Fin k)
      (cell.toTopCell.verts.erase (cell.vertex q)) :=
  B.neighbor_none_exterior cell q hnei

lemma exists_neighborCell_of_not_exterior {k N : ℕ} [NeZero k]
    {Sys : HypersimplexAlcoveChartSystem k} (B : BoundaryData Sys)
    (cell : ChartAlcoveCell k N Sys)
    (q : Fin k)
    (hint : ¬ IsExteriorFacet (n := Fin k)
      (cell.toTopCell.verts.erase (cell.vertex q))) :
    ∃ cell' : ChartAlcoveCell k N Sys, cell.neighborCell q = some cell' := by
  classical
  cases hnei : cell.neighborCell q with
  | none =>
      exact False.elim (hint (cell.neighborCell_none_imp_exterior B q hnei))
  | some cell' =>
      exact ⟨cell', rfl⟩

lemma neighborCell_shares_facet {k N : ℕ} [NeZero k]
    {Sys : HypersimplexAlcoveChartSystem k} {cell cell' : ChartAlcoveCell k N Sys}
    {q : Fin k} (hnei : cell.neighborCell q = some cell') :
    ∃ q' : Fin k,
      cell.toTopCell.verts.erase (cell.vertex q) =
        cell'.toTopCell.verts.erase (cell'.vertex q') := by
  classical
  cases hchart : Sys.neighbor cell.chart q with
  | none =>
      simp [neighborCell, hchart] at hnei
  | some chart' =>
      have hcell' : cell' = { anchor := cell.anchor, chart := chart' } := by
        simpa [neighborCell, hchart] using hnei.symm
      subst cell'
      obtain ⟨q', hfacet⟩ := Sys.neighbor_shares_facet cell.chart q chart' hchart
      refine ⟨q', ?_⟩
      have hgrid :=
        AlcoveCell.facetErasing_eq_of_erase_eq cell.toAlcoveCell
          ({ anchor := cell.anchor, alcove := Sys.toAlcove chart' } : AlcoveCell k N)
          rfl
          (Sys.vertex_mem cell.chart q) (Sys.vertex_mem chart' q') hfacet
      simpa [toTopCell, vertex, toAlcoveCell, AlcoveCell.facetErasing] using hgrid

@[irreducible]
noncomputable def other {k N : ℕ} [NeZero k]
    {Sys : HypersimplexAlcoveChartSystem k} (B : BoundaryData Sys)
    (cell : ChartAlcoveCell k N Sys)
    (face : Finset (simplexGrid (n := Fin k) N)) :
    ChartAlcoveCell k N Sys := by
  classical
  exact
    if hfacet : face ∈ cell.toTopCell.facets then
      let q := Classical.choose ((cell.mem_facets_iff_exists_erase_vertex).mp hfacet)
      if hint : ¬ IsExteriorFacet (n := Fin k) face then
        Classical.choose
          (cell.exists_neighborCell_of_not_exterior B q (by
            have hq := Classical.choose_spec
              ((cell.mem_facets_iff_exists_erase_vertex).mp hfacet)
            rwa [hq] at hint))
      else cell
    else cell

lemma other_eq_neighbor_of_nonexterior_facet {k N : ℕ} [NeZero k]
    {Sys : HypersimplexAlcoveChartSystem k} (B : BoundaryData Sys)
    {cell : ChartAlcoveCell k N Sys}
    {face : Finset (simplexGrid (n := Fin k) N)}
    (hfacet : face ∈ cell.toTopCell.facets)
    (hint : ¬ IsExteriorFacet (n := Fin k) face) :
    let q := Classical.choose ((cell.mem_facets_iff_exists_erase_vertex).mp hfacet)
    cell.neighborCell q = some (other B cell face) := by
  classical
  unfold other
  rw [dif_pos hfacet, dif_pos hint]
  exact Classical.choose_spec
    (cell.exists_neighborCell_of_not_exterior B
      (Classical.choose ((cell.mem_facets_iff_exists_erase_vertex).mp hfacet)) (by
        have hq := Classical.choose_spec
          ((cell.mem_facets_iff_exists_erase_vertex).mp hfacet)
        rwa [hq] at hint))

lemma other_mem_of_nonexterior {k N : ℕ} [NeZero k]
    {Sys : HypersimplexAlcoveChartSystem k} (B : BoundaryData Sys)
    {cell : ChartAlcoveCell k N Sys}
    {face : Finset (simplexGrid (n := Fin k) N)}
    (hfacet : face ∈ cell.toTopCell.facets)
    (hint : ¬ IsExteriorFacet (n := Fin k) face) :
    face ∈ (other B cell face).toTopCell.facets := by
  classical
  let q := Classical.choose ((cell.mem_facets_iff_exists_erase_vertex).mp hfacet)
  let cell₂ := other B cell face
  have hq : face = cell.toTopCell.verts.erase (cell.vertex q) :=
    Classical.choose_spec ((cell.mem_facets_iff_exists_erase_vertex).mp hfacet)
  have hnei : cell.neighborCell q = some cell₂ := by
    simpa [q] using other_eq_neighbor_of_nonexterior_facet B hfacet hint
  obtain ⟨q', hshared⟩ := neighborCell_shares_facet hnei
  change face ∈ cell₂.toTopCell.facets
  have hface_eq : face = cell₂.toTopCell.verts.erase (cell₂.vertex q') :=
    hq.trans hshared
  rw [hface_eq]
  have hv : cell₂.vertex q' ∈ cell₂.toAlcoveCell.verts :=
    cell₂.vertex_mem_toAlcoveCell q'
  rw [toTopCell, TopCell.mem_facets_iff_exists_erase]
  exact ⟨cell₂.vertex q', hv, rfl⟩

end ChartAlcoveCell

noncomputable def orderedVertex {k N : ℕ} [NeZero k]
    (start : simplexGrid (n := Fin k) N) (order : Equiv.Perm (Fin k))
    (hpos : 0 < start.1 (order 0)) (t : Fin k) :
    simplexGrid (n := Fin k) N :=
  if ht : t = 0 then start
  else
    transfer (n := Fin k) start
      (by
        intro h
        exact ht (order.injective h).symm)
      hpos

@[simp]
lemma orderedVertex_zero {k N : ℕ} [NeZero k]
    (start : simplexGrid (n := Fin k) N) (order : Equiv.Perm (Fin k))
    (hpos : 0 < start.1 (order 0)) :
    orderedVertex start order hpos 0 = start := by
  simp [orderedVertex]

lemma orderedVertex_of_ne_zero {k N : ℕ} [NeZero k]
    (start : simplexGrid (n := Fin k) N) (order : Equiv.Perm (Fin k))
    (hpos : 0 < start.1 (order 0)) {t : Fin k} (ht : t ≠ 0) :
    orderedVertex start order hpos t =
      transfer (n := Fin k) start
        (by
          intro h
          exact ht (order.injective h).symm)
        hpos := by
  simp [orderedVertex, ht]

lemma unitClose_orderedVertex {k N : ℕ} [NeZero k]
    (start : simplexGrid (n := Fin k) N) (order : Equiv.Perm (Fin k))
    (hpos : 0 < start.1 (order 0)) (t : Fin k) :
    UnitClose (n := Fin k) (orderedVertex start order hpos t) start := by
  by_cases ht : t = 0
  · subst t
    exact unitClose_refl start
  · rw [orderedVertex_of_ne_zero start order hpos ht]
    exact unitClose_of_gridStep_symm
      (gridStep_transfer (n := Fin k) start
        (by
          intro h
          exact ht (order.injective h).symm)
        hpos)

lemma orderedVertex_apply_source_of_ne_zero {k N : ℕ} [NeZero k]
    (start : simplexGrid (n := Fin k) N) (order : Equiv.Perm (Fin k))
    (hpos : 0 < start.1 (order 0)) {t : Fin k} (ht : t ≠ 0) :
    (orderedVertex start order hpos t).1 (order 0) = start.1 (order 0) - 1 := by
  rw [orderedVertex_of_ne_zero start order hpos ht]
  simp

lemma orderedVertex_apply_target_of_ne_zero {k N : ℕ} [NeZero k]
    (start : simplexGrid (n := Fin k) N) (order : Equiv.Perm (Fin k))
    (hpos : 0 < start.1 (order 0)) {t : Fin k} (ht : t ≠ 0) :
    (orderedVertex start order hpos t).1 (order t) = start.1 (order t) + 1 := by
  rw [orderedVertex_of_ne_zero start order hpos ht]
  simp

lemma orderedVertex_apply_of_ne_source_target {k N : ℕ} [NeZero k]
    (start : simplexGrid (n := Fin k) N) (order : Equiv.Perm (Fin k))
    (hpos : 0 < start.1 (order 0)) {t : Fin k} (ht : t ≠ 0)
    {j : Fin k} (hj0 : j ≠ order 0) (hjt : j ≠ order t) :
    (orderedVertex start order hpos t).1 j = start.1 j := by
  rw [orderedVertex_of_ne_zero start order hpos ht]
  exact transfer_apply_of_ne (n := Fin k) start
    (by
      intro h
      exact ht (order.injective h).symm)
    hpos hj0 hjt

lemma orderedVertex_injective {k N : ℕ} [NeZero k]
    (start : simplexGrid (n := Fin k) N) (order : Equiv.Perm (Fin k))
    (hpos : 0 < start.1 (order 0)) :
    Function.Injective (orderedVertex start order hpos) := by
  intro t u htu
  by_cases ht : t = 0
  · subst t
    by_cases hu : u = 0
    · exact hu.symm
    · have hcoord :
          start.1 (order 0) = (orderedVertex start order hpos u).1 (order 0) := by
        simpa using congrArg (fun a : simplexGrid (n := Fin k) N => a.1 (order 0)) htu
      rw [orderedVertex_apply_source_of_ne_zero start order hpos hu] at hcoord
      exact False.elim (by omega)
  · by_cases hu : u = 0
    · subst u
      have hcoord :
          (orderedVertex start order hpos t).1 (order 0) = start.1 (order 0) := by
        simpa using congrArg (fun a : simplexGrid (n := Fin k) N => a.1 (order 0)) htu
      rw [orderedVertex_apply_source_of_ne_zero start order hpos ht] at hcoord
      exact False.elim (by omega)
    · by_contra hne
      have hord_ne : order t ≠ order u := by
        intro h
        exact hne (order.injective h)
      have hcoord := congrArg (fun a : simplexGrid (n := Fin k) N => a.1 (order t)) htu
      have hright :
          (orderedVertex start order hpos u).1 (order t) = start.1 (order t) := by
        exact orderedVertex_apply_of_ne_source_target start order hpos hu
          (by
            intro h
            exact ht (order.injective h))
          hord_ne
      have hcoord' :
          (orderedVertex start order hpos t).1 (order t) =
            (orderedVertex start order hpos u).1 (order t) := by
        simpa using hcoord
      rw [orderedVertex_apply_target_of_ne_zero start order hpos ht, hright] at hcoord'
      omega

noncomputable def orderedVerts {k N : ℕ} [NeZero k]
    (start : simplexGrid (n := Fin k) N) (order : Equiv.Perm (Fin k))
    (hpos : 0 < start.1 (order 0)) :
    Finset (simplexGrid (n := Fin k) N) :=
  (Finset.univ : Finset (Fin k)).image (orderedVertex start order hpos)

lemma mem_orderedVerts {k N : ℕ} [NeZero k]
    (start : simplexGrid (n := Fin k) N) (order : Equiv.Perm (Fin k))
    (hpos : 0 < start.1 (order 0)) {a : simplexGrid (n := Fin k) N} :
    a ∈ orderedVerts start order hpos ↔
      ∃ t : Fin k, orderedVertex start order hpos t = a := by
  classical
  simp [orderedVerts]

lemma card_orderedVerts {k N : ℕ} [NeZero k]
    (start : simplexGrid (n := Fin k) N) (order : Equiv.Perm (Fin k))
    (hpos : 0 < start.1 (order 0)) :
    (orderedVerts start order hpos).card = Fintype.card (Fin k) := by
  classical
  rw [orderedVerts, Finset.card_image_of_injective _ (orderedVertex_injective start order hpos)]
  rfl

noncomputable def orderedTopCell {k N : ℕ} [NeZero k]
    (start : simplexGrid (n := Fin k) N) (order : Equiv.Perm (Fin k))
    (hpos : 0 < start.1 (order 0)) :
    TopCell (n := Fin k) N where
  verts := orderedVerts start order hpos
  base := start
  close := by
    intro a ha
    rw [mem_orderedVerts] at ha
    obtain ⟨t, ht⟩ := ha
    rw [← ht]
    exact unitClose_orderedVertex start order hpos t
  card_verts := card_orderedVerts start order hpos

structure OrderedCell (k N : ℕ) [NeZero k] where
  start : simplexGrid (n := Fin k) N
  order : Equiv.Perm (Fin k)
  source_pos : 0 < start.1 (order 0)

namespace OrderedCell

noncomputable instance instFintype (k N : ℕ) [NeZero k] :
    Fintype (OrderedCell k N) := by
  classical
  refine Fintype.ofEquiv
    {p : simplexGrid (n := Fin k) N × Equiv.Perm (Fin k) // 0 < p.1.1 (p.2 0)} ?_
  refine
    { toFun := fun p => ⟨p.1.1, p.1.2, p.2⟩
      invFun := fun cell => ⟨(cell.start, cell.order), cell.source_pos⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro p
    cases p with
    | mk val h =>
        cases val
        rfl
  · intro cell
    cases cell
    rfl

noncomputable def toTopCell {k N : ℕ} [NeZero k] (cell : OrderedCell k N) :
    TopCell (n := Fin k) N :=
  orderedTopCell cell.start cell.order cell.source_pos

@[simp]
lemma toTopCell_verts {k N : ℕ} [NeZero k] (cell : OrderedCell k N) :
    (cell.toTopCell).verts = orderedVerts cell.start cell.order cell.source_pos :=
  rfl

@[simp]
lemma toTopCell_base {k N : ℕ} [NeZero k] (cell : OrderedCell k N) :
    (cell.toTopCell).base = cell.start :=
  rfl

lemma vertex_mem_toTopCell {k N : ℕ} [NeZero k] (cell : OrderedCell k N) (t : Fin k) :
    orderedVertex cell.start cell.order cell.source_pos t ∈ cell.toTopCell.verts := by
  classical
  rw [toTopCell_verts, mem_orderedVerts]
  exact ⟨t, rfl⟩

lemma close_vertex_to_start {k N : ℕ} [NeZero k] (cell : OrderedCell k N) (t : Fin k) :
    UnitClose (n := Fin k)
      (orderedVertex cell.start cell.order cell.source_pos t) cell.start :=
  unitClose_orderedVertex cell.start cell.order cell.source_pos t

end OrderedCell

structure DoorGraphData {N : ℕ} (c : simplexGrid (n := n) N → n) (r : n) where
  G : SimpleGraph (Option (TopCell (n := n) N))
  decidableAdj : DecidableRel G.Adj
  outside_odd : Odd (G.degree none)
  degree_eq_faceDoors :
    ∀ cell : TopCell (n := n) N, G.degree (some cell) = (cell.faceDoors c r).card

lemma exists_fullyLabeledUnitCluster_of_doorGraphData {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {c : simplexGrid (n := n) N → n} {r : n}
    (D : DoorGraphData (n := n) c r) :
    ∃ base : simplexGrid (n := n) N,
      FullyLabeledUnitCluster (n := n) c base := by
  letI := D.decidableAdj
  exact exists_fullyLabeledUnitCluster_of_door_graph_faceDegrees
    D.G c r D.outside_odd D.degree_eq_faceDoors

lemma not_forall_unitNeighborhood_image_ne_univ_of_doorGraphData {N : ℕ}
    [DecidableEq (simplexGrid (n := n) N)]
    {c : simplexGrid (n := n) N → n} {r : n}
    (D : DoorGraphData (n := n) c r) :
    ¬ ∀ base : simplexGrid (n := n) N,
      ((unitNeighborhood (n := n) N base).image c : Finset n) ≠ Finset.univ := by
  intro hforall
  obtain ⟨base, hfull⟩ := exists_fullyLabeledUnitCluster_of_doorGraphData D
  exact hforall base ((fullyLabeledUnitCluster_iff_image_eq_univ c base).mp hfull)

lemma not_forall_unitNeighborhood_image_ne_univ_of_fin_card_doorGraphData [Nonempty n]
    {N : ℕ} (c : simplexGrid (n := n) N → n)
    (hc : ∀ (a : simplexGrid (n := n) N) (i : n), a.1 i = 0 → c a ≠ i)
    (hfin :
      ∀ cfin : simplexGrid (n := Fin (Fintype.card n)) N → Fin (Fintype.card n),
        (∀ (a : simplexGrid (n := Fin (Fintype.card n)) N) (i : Fin (Fintype.card n)),
          a.1 i = 0 → cfin a ≠ i) →
          ∃ r : Fin (Fintype.card n),
            Nonempty (DoorGraphData (n := Fin (Fintype.card n)) cfin r)) :
    ¬ ∀ base : simplexGrid (n := n) N,
      ((unitNeighborhood (n := n) N base).image c : Finset n) ≠ Finset.univ := by
  intro hforall
  have hcluster :
      ∃ base : simplexGrid (n := n) N,
        FullyLabeledUnitCluster (n := n) c base := by
    refine exists_fullyLabeledUnitCluster_of_fin_card_case c hc ?_
    intro cfin hcfin
    obtain ⟨r, ⟨D⟩⟩ := hfin cfin hcfin
    exact exists_fullyLabeledUnitCluster_of_doorGraphData D
  obtain ⟨base, hfull⟩ := hcluster
  exact hforall base ((fullyLabeledUnitCluster_iff_image_eq_univ c base).mp hfull)

lemma not_forall_unitNeighborhood_image_ne_univ_of_fin_card_alcoveCell_odd_sum
    [Nonempty n] {N : ℕ} (c : simplexGrid (n := n) N → n)
    (hc : ∀ (a : simplexGrid (n := n) N) (i : n), a.1 i = 0 → c a ≠ i)
    (hfin :
      ∀ cfin : simplexGrid (n := Fin (Fintype.card n)) N → Fin (Fintype.card n),
        (∀ (a : simplexGrid (n := Fin (Fintype.card n)) N) (i : Fin (Fintype.card n)),
          a.1 i = 0 → cfin a ≠ i) →
          ∃ r : Fin (Fintype.card n),
            Odd ((Finset.univ : Finset (AlcoveCell (Fintype.card n) N)).sum fun cell =>
              ((AlcoveCell.toTopCell cell).faceDoors cfin r).card)) :
    ¬ ∀ base : simplexGrid (n := n) N,
      ((unitNeighborhood (n := n) N base).image c : Finset n) ≠ Finset.univ := by
  intro hforall
  have hcluster :
      ∃ base : simplexGrid (n := n) N,
        FullyLabeledUnitCluster (n := n) c base := by
    refine exists_fullyLabeledUnitCluster_of_fin_card_case c hc ?_
    intro cfin hcfin
    obtain ⟨r, hodd⟩ := hfin cfin hcfin
    exact exists_fullyLabeledUnitCluster_of_family_odd_sum_faceDoors
      (fun cell : AlcoveCell (Fintype.card n) N => AlcoveCell.toTopCell cell)
      cfin r hodd
  obtain ⟨base, hfull⟩ := hcluster
  exact hforall base ((fullyLabeledUnitCluster_iff_image_eq_univ c base).mp hfull)

lemma not_forall_unitNeighborhood_image_ne_univ_of_fin_card_alcoveCell_incidence_parity
    [Nonempty n] {N : ℕ} (c : simplexGrid (n := n) N → n)
    (hc : ∀ (a : simplexGrid (n := n) N) (i : n), a.1 i = 0 → c a ≠ i)
    (hfin :
      ∀ cfin : simplexGrid (n := Fin (Fintype.card n)) N → Fin (Fintype.card n),
        (∀ (a : simplexGrid (n := Fin (Fintype.card n)) N) (i : Fin (Fintype.card n)),
          a.1 i = 0 → cfin a ≠ i) →
          ∃ r : Fin (Fintype.card n),
            Even (AlcoveCell.internalDoorIncidences cfin r).card ∧
              Odd (AlcoveCell.exteriorDoorIncidences cfin r).card) :
    ¬ ∀ base : simplexGrid (n := n) N,
      ((unitNeighborhood (n := n) N base).image c : Finset n) ≠ Finset.univ := by
  intro hforall
  have hcluster :
      ∃ base : simplexGrid (n := n) N,
        FullyLabeledUnitCluster (n := n) c base := by
    refine exists_fullyLabeledUnitCluster_of_fin_card_case c hc ?_
    intro cfin hcfin
    obtain ⟨r, hinternal, hexterior⟩ := hfin cfin hcfin
    exact AlcoveCell.exists_fullyLabeledUnitCluster_of_internal_even_exterior_odd
      cfin r hinternal hexterior
  obtain ⟨base, hfull⟩ := hcluster
  exact hforall base ((fullyLabeledUnitCluster_iff_image_eq_univ c base).mp hfull)

lemma not_forall_unitNeighborhood_image_ne_univ_of_fin_card_alcoveCell_certificate
    [Nonempty n] {N : ℕ} (c : simplexGrid (n := n) N → n)
    (hc : ∀ (a : simplexGrid (n := n) N) (i : n), a.1 i = 0 → c a ≠ i)
    (hfin :
      ∀ cfin : simplexGrid (n := Fin (Fintype.card n)) N → Fin (Fintype.card n),
        (∀ (a : simplexGrid (n := Fin (Fintype.card n)) N) (i : Fin (Fintype.card n)),
          a.1 i = 0 → cfin a ≠ i) →
          ∃ r : Fin (Fintype.card n),
            Nonempty (AlcoveCell.IncidenceParityCertificate cfin r)) :
    ¬ ∀ base : simplexGrid (n := n) N,
      ((unitNeighborhood (n := n) N base).image c : Finset n) ≠ Finset.univ := by
  intro hforall
  have hcluster :
      ∃ base : simplexGrid (n := n) N,
        FullyLabeledUnitCluster (n := n) c base := by
    refine exists_fullyLabeledUnitCluster_of_fin_card_case c hc ?_
    intro cfin hcfin
    obtain ⟨r, ⟨cert⟩⟩ := hfin cfin hcfin
    exact AlcoveCell.exists_fullyLabeledUnitCluster_of_incidenceParityCertificate cert
  obtain ⟨base, hfull⟩ := hcluster
  exact hforall base ((fullyLabeledUnitCluster_iff_image_eq_univ c base).mp hfull)

lemma not_forall_unitNeighborhood_image_ne_univ_of_fin_card_validCircuit_certificate
    [Nonempty n] [Fact (1 < Fintype.card n)] {N : ℕ}
    (c : simplexGrid (n := n) N → n)
    (hc : ∀ (a : simplexGrid (n := n) N) (i : n), a.1 i = 0 → c a ≠ i)
    (hfin :
      ∀ cfin : simplexGrid (n := Fin (Fintype.card n)) N → Fin (Fintype.card n),
        (∀ (a : simplexGrid (n := Fin (Fintype.card n)) N) (i : Fin (Fintype.card n)),
          a.1 i = 0 → cfin a ≠ i) →
          ∃ r : Fin (Fintype.card n),
            Nonempty
              (CircuitAlcove.RawSubsetCircuit.ValidIncidenceParityCertificate cfin r)) :
    ¬ ∀ base : simplexGrid (n := n) N,
      ((unitNeighborhood (n := n) N base).image c : Finset n) ≠ Finset.univ := by
  intro hforall
  have hcluster :
      ∃ base : simplexGrid (n := n) N,
        FullyLabeledUnitCluster (n := n) c base := by
    refine exists_fullyLabeledUnitCluster_of_fin_card_case c hc ?_
    intro cfin hcfin
    obtain ⟨r, ⟨cert⟩⟩ := hfin cfin hcfin
    exact
      CircuitAlcove.RawSubsetCircuit.exists_fullyLabeledUnitCluster_of_validIncidenceParityCertificate
        cert
  obtain ⟨base, hfull⟩ := hcluster
  exact hforall base ((fullyLabeledUnitCluster_iff_image_eq_univ c base).mp hfull)

lemma not_forall_unitNeighborhood_image_ne_univ_of_fin_card_validCircuit_neighborData
    [Nonempty n] [Fact (1 < Fintype.card n)] {N : ℕ}
    (c : simplexGrid (n := n) N → n)
    (hc : ∀ (a : simplexGrid (n := n) N) (i : n), a.1 i = 0 → c a ≠ i)
    (hfin :
      ∀ cfin : simplexGrid (n := Fin (Fintype.card n)) N → Fin (Fintype.card n),
        (∀ (a : simplexGrid (n := Fin (Fintype.card n)) N) (i : Fin (Fintype.card n)),
          a.1 i = 0 → cfin a ≠ i) →
          ∃ r : Fin (Fintype.card n),
            Nonempty (CircuitAlcove.RawSubsetCircuit.ValidNeighborParityData cfin r)) :
    ¬ ∀ base : simplexGrid (n := n) N,
      ((unitNeighborhood (n := n) N base).image c : Finset n) ≠ Finset.univ := by
  exact not_forall_unitNeighborhood_image_ne_univ_of_fin_card_validCircuit_certificate
    c hc (by
      intro cfin hcfin
      obtain ⟨r, ⟨D⟩⟩ := hfin cfin hcfin
      exact ⟨r, ⟨D.toValidIncidenceParityCertificate⟩⟩)

lemma not_forall_unitNeighborhood_image_ne_univ_of_fin_card_validCircuit_pseudomanifold
    [Nonempty n] [Fact (1 < Fintype.card n)] {N : ℕ}
    (c : simplexGrid (n := n) N → n)
    (hc : ∀ (a : simplexGrid (n := n) N) (i : n), a.1 i = 0 → c a ≠ i)
    (P : CircuitAlcove.RawSubsetCircuit.ValidPseudomanifoldData
      (Fintype.card n) N)
    (hfinExterior :
      ∀ cfin : simplexGrid (n := Fin (Fintype.card n)) N → Fin (Fintype.card n),
        (∀ (a : simplexGrid (n := Fin (Fintype.card n)) N) (i : Fin (Fintype.card n)),
          a.1 i = 0 → cfin a ≠ i) →
          ∃ r : Fin (Fintype.card n),
            Odd (familyExteriorDoorIncidences (n := Fin (Fintype.card n))
              CircuitAlcove.RawSubsetCircuit.validToTopCell cfin r).card) :
    ¬ ∀ base : simplexGrid (n := n) N,
      ((unitNeighborhood (n := n) N base).image c : Finset n) ≠ Finset.univ := by
  exact not_forall_unitNeighborhood_image_ne_univ_of_fin_card_validCircuit_neighborData
    c hc (by
      intro cfin hcfin
      obtain ⟨r, hexterior⟩ := hfinExterior cfin hcfin
      exact ⟨r, ⟨
        CircuitAlcove.RawSubsetCircuit.validNeighborParityData_of_pseudomanifold_exterior
          P hexterior⟩⟩)

lemma not_forall_unitNeighborhood_image_ne_univ_of_fin_card_orderedCell_odd_sum
    [Nonempty n] {N : ℕ} (c : simplexGrid (n := n) N → n)
    (hc : ∀ (a : simplexGrid (n := n) N) (i : n), a.1 i = 0 → c a ≠ i)
    (hfin :
      ∀ cfin : simplexGrid (n := Fin (Fintype.card n)) N → Fin (Fintype.card n),
        (∀ (a : simplexGrid (n := Fin (Fintype.card n)) N) (i : Fin (Fintype.card n)),
          a.1 i = 0 → cfin a ≠ i) →
          ∃ r : Fin (Fintype.card n),
            Odd ((Finset.univ : Finset (OrderedCell (Fintype.card n) N)).sum fun cell =>
              ((OrderedCell.toTopCell cell).faceDoors cfin r).card)) :
    ¬ ∀ base : simplexGrid (n := n) N,
      ((unitNeighborhood (n := n) N base).image c : Finset n) ≠ Finset.univ := by
  intro hforall
  have hcluster :
      ∃ base : simplexGrid (n := n) N,
        FullyLabeledUnitCluster (n := n) c base := by
    refine exists_fullyLabeledUnitCluster_of_fin_card_case c hc ?_
    intro cfin hcfin
    obtain ⟨r, hodd⟩ := hfin cfin hcfin
    exact exists_fullyLabeledUnitCluster_of_family_odd_sum_faceDoors
      (fun cell : OrderedCell (Fintype.card n) N => OrderedCell.toTopCell cell)
      cfin r hodd
  obtain ⟨base, hfull⟩ := hcluster
  exact hforall base ((fullyLabeledUnitCluster_iff_image_eq_univ c base).mp hfull)

end TopCell

omit [DecidableEq n] in
lemma one_lt_card_of_not_subsingleton [Nonempty n] (h : ¬ Subsingleton n) :
    1 < Fintype.card n := by
  by_contra hle
  exact h (Fintype.card_le_one_iff_subsingleton.mp (by omega))

theorem sperner_grid_not_forall_unit_neighborhood_image_ne_univ [Nonempty n]
    (N : ℕ) (_hN : 0 < N) (hcardN : Fintype.card n < N)
    (c : simplexGrid (n := n) N → n)
    (hc : ∀ (a : simplexGrid (n := n) N) (i : n), a.1 i = 0 → c a ≠ i) :
    ¬ ∀ base : simplexGrid (n := n) N,
      ((unitNeighborhood (n := n) N base).image c : Finset n) ≠ Finset.univ := by
  /-
  Equivalent contradiction form of the remaining Sperner proof. Under this assumption each unit
  neighborhood has a missing label; `missingLabelOfNotFull` packages those choices, and the
  odd-door argument should contradict the boundary behavior above.
  -/
  classical
  by_cases hsub : Subsingleton n
  · intro hforall
    haveI := hsub
    let base : simplexGrid (n := n) N := vertex (n := n) N (Classical.choice ‹Nonempty n›)
    have hfull :
        ((unitNeighborhood (n := n) N base).image c : Finset n) = Finset.univ := by
      apply Finset.ext
      intro i
      constructor
      · intro _hi
        exact Finset.mem_univ i
      · intro _hi
        have hi : i = c base := Subsingleton.elim _ _
        rw [hi]
        exact color_mem_unitNeighborhood_image c base
    exact hforall base hfull
  ·
    intro hforall
    exact
      (TopCell.not_forall_unitNeighborhood_image_ne_univ_of_fin_card_alcoveCell_certificate
        c hc (TopCell.AlcoveCell.exists_fin_card_incidenceParityCertificate_of_card_lt
          (n := n) hcardN)) hforall

omit [DecidableEq n] in
lemma forall_abs_sub_le_mesh {N : ℕ} (a b : simplexGrid (n := n) N) (j : n) :
    |(a.1 j : ℝ) - (b.1 j : ℝ)| ≤ (N : ℝ) := by
  have haj_le : a.1 j ≤ N := by
    have hle : a.1 j ≤ ∑ k, a.1 k :=
      Finset.single_le_sum (fun k _ => Nat.zero_le (a.1 k)) (Finset.mem_univ j)
    simpa [a.2] using hle
  have hbj_le : b.1 j ≤ N := by
    have hle : b.1 j ≤ ∑ k, b.1 k :=
      Finset.single_le_sum (fun k _ => Nat.zero_le (b.1 k)) (Finset.mem_univ j)
    simpa [b.2] using hle
  rw [abs_sub_le_iff]
  constructor
  · have hb_nonneg : 0 ≤ (b.1 j : ℝ) := by positivity
    have ha_le : (a.1 j : ℝ) ≤ (N : ℝ) := by exact_mod_cast haj_le
    linarith
  · have ha_nonneg : 0 ≤ (a.1 j : ℝ) := by positivity
    have hb_le : (b.1 j : ℝ) ≤ (N : ℝ) := by exact_mod_cast hbj_le
    linarith

end simplexGrid

omit [DecidableEq n] in
lemma exists_coord_gt_of_not_fixed
    (f : stdSimplex ℝ n → stdSimplex ℝ n)
    (x : stdSimplex ℝ n)
    (h : f x ≠ x) :
    ∃ i, (f x).1 i < x.1 i := by
  by_contra hle
  apply h
  apply Subtype.ext
  funext i
  have hxi_le : x.1 i ≤ (f x).1 i := by
    exact le_of_not_gt fun hi => hle ⟨i, hi⟩
  have hsum_diff : ∑ j, ((f x).1 j - x.1 j) = 0 := by
    rw [Finset.sum_sub_distrib, (f x).2.2, x.2.2, sub_self]
  have hdiff_nonneg : ∀ j, 0 ≤ (f x).1 j - x.1 j := by
    intro j
    exact sub_nonneg.mpr (le_of_not_gt fun hj => hle ⟨j, hj⟩)
  have hi_diff_zero : (f x).1 i - x.1 i = 0 := by
    have hi_le_sum :
        (f x).1 i - x.1 i ≤ ∑ j, ((f x).1 j - x.1 j) :=
      Finset.single_le_sum (fun j _ => hdiff_nonneg j) (Finset.mem_univ i)
    linarith
  exact sub_eq_zero.mp hi_diff_zero

noncomputable def spernerColor
    (f : stdSimplex ℝ n → stdSimplex ℝ n)
    (hnofix : ∀ x, f x ≠ x)
    {N : ℕ} (hN : 0 < N)
    (a : simplexGrid (n := n) N) : n :=
  Classical.choose
    (exists_coord_gt_of_not_fixed f (simplexGrid.toStdSimplex hN a)
      (hnofix _))

omit [DecidableEq n] in
lemma spernerColor_spec
    (f : stdSimplex ℝ n → stdSimplex ℝ n)
    (hnofix : ∀ x, f x ≠ x)
    {N : ℕ} (hN : 0 < N)
    (a : simplexGrid (n := n) N) :
    (f (simplexGrid.toStdSimplex hN a)).1 (spernerColor f hnofix hN a) <
      (simplexGrid.toStdSimplex hN a).1 (spernerColor f hnofix hN a) :=
  Classical.choose_spec
    (exists_coord_gt_of_not_fixed f (simplexGrid.toStdSimplex hN a)
      (hnofix _))

omit [DecidableEq n] in
lemma spernerColor_boundary
    (f : stdSimplex ℝ n → stdSimplex ℝ n)
    (hnofix : ∀ x, f x ≠ x)
    {N : ℕ} (hN : 0 < N)
    (a : simplexGrid (n := n) N) {i : n}
    (hi : a.1 i = 0) :
    spernerColor f hnofix hN a ≠ i := by
  intro hcolor
  have hlt := spernerColor_spec f hnofix hN a
  rw [hcolor] at hlt
  have hcoord_zero : (simplexGrid.toStdSimplex hN a).1 i = 0 := by
    simp [simplexGrid.toStdSimplex, hi]
  rw [hcoord_zero] at hlt
  exact not_lt_of_ge ((f (simplexGrid.toStdSimplex hN a)).2.1 i) hlt

lemma spernerColor_vertex
    (f : stdSimplex ℝ n → stdSimplex ℝ n)
    (hnofix : ∀ x, f x ≠ x)
    {N : ℕ} (hN : 0 < N) (i : n) :
    spernerColor f hnofix hN (simplexGrid.vertex (n := n) N i) = i := by
  exact simplexGrid.color_vertex_of_boundary
    (spernerColor f hnofix hN)
    (fun a j hj => spernerColor_boundary f hnofix hN a hj) i

lemma exists_fixed_of_exists_approx
    {X : Type*} [MetricSpace X] [CompactSpace X]
    {f : X → X} (hf : Continuous f)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ x, dist (f x) x < ε) :
    ∃ x, Function.IsFixedPt f x := by
  let t : ℕ → Set X := fun k => {x | dist (f x) x ≤ ((k + 1 : ℕ) : ℝ)⁻¹}
  have htcl : ∀ k, IsClosed (t k) := by
    intro k
    have hdist : Continuous fun x => dist (f x) x := by fun_prop
    exact isClosed_le hdist continuous_const
  have htn : ∀ k, (t k).Nonempty := by
    intro k
    have hε : 0 < (((k + 1 : ℕ) : ℝ)⁻¹) := by positivity
    obtain ⟨x, hx⟩ := happrox _ hε
    exact ⟨x, le_of_lt hx⟩
  have htd : ∀ k, t (k + 1) ⊆ t k := by
    intro k x hx
    exact hx.trans <|
      (inv_le_inv₀ (by positivity : 0 < (((k + 2 : ℕ) : ℝ)))
        (by positivity : 0 < (((k + 1 : ℕ) : ℝ)))).2 (by norm_num)
  have ht0 : IsCompact (t 0) := by
    exact isCompact_univ.of_isClosed_subset (htcl 0) (by intro x hx; simp)
  obtain ⟨x, hx⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t htd htn ht0 htcl
  have hx_le : ∀ k, dist (f x) x ≤ (((k + 1 : ℕ) : ℝ)⁻¹) := by
    intro k
    exact Set.mem_iInter.mp hx k
  have hdist_zero : dist (f x) x = 0 := by
    by_contra hne
    have hpos : 0 < dist (f x) x := by
      exact lt_of_le_of_ne dist_nonneg (by simpa [eq_comm] using hne)
    obtain ⟨m, hm_pos, hm_lt⟩ := Real.exists_nat_pos_inv_lt hpos
    have hm_succ_le : (((m + 1 : ℕ) : ℝ)⁻¹) ≤ ((m : ℝ)⁻¹) := by
      exact (inv_le_inv₀ (by positivity : 0 < (((m + 1 : ℕ) : ℝ)))
        (by exact_mod_cast hm_pos)).2 (by norm_num)
    have hle := hx_le m
    linarith
  exact ⟨x, dist_eq_zero.mp hdist_zero⟩

omit [DecidableEq n] in
lemma stdSimplex_dist_lt_of_forall_coord_lt_add [Nonempty n]
    {x y : stdSimplex ℝ n} {η ε : ℝ}
    (hη : 0 < η) (hε : (Fintype.card n : ℝ) * η < ε)
    (hcoord : ∀ i, y.1 i < x.1 i + η) :
    dist y x < ε := by
  classical
  have hcard_pos_nat : 0 < Fintype.card n := Fintype.card_pos_iff.mpr ‹Nonempty n›
  have hcard_pos : 0 < (Fintype.card n : ℝ) := by exact_mod_cast hcard_pos_nat
  have hε_pos : 0 < ε := lt_of_lt_of_le (mul_pos hcard_pos hη) hε.le
  change dist (y : n → ℝ) (x : n → ℝ) < ε
  rw [dist_pi_lt_iff hε_pos]
  intro i
  rw [Real.dist_eq]
  rw [abs_lt]
  constructor
  · have hsum_diff : ∑ j, (y.1 j - x.1 j) = 0 := by
      rw [Finset.sum_sub_distrib, y.2.2, x.2.2, sub_self]
    let s : Finset n := Finset.univ.erase i
    have hsum_erase :
        x.1 i - y.1 i = s.sum (fun j => y.1 j - x.1 j) := by
      have hmem : i ∈ (Finset.univ : Finset n) := Finset.mem_univ i
      rw [← Finset.sum_erase_add _ _ hmem] at hsum_diff
      dsimp [s]
      linarith
    have hsum_le :
        s.sum (fun j => y.1 j - x.1 j) ≤ s.sum (fun _j => η) := by
      exact Finset.sum_le_sum fun j _hj => le_of_lt (by linarith [hcoord j])
    have hcard_le :
        (s.card : ℝ) * η ≤ (Fintype.card n : ℝ) * η := by
      have hs_card_le : s.card ≤ Fintype.card n := by
        dsimp [s]
        exact Finset.card_erase_le
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hs_card_le) hη.le
    have hlower : x.1 i - y.1 i < ε := by
      calc
        x.1 i - y.1 i = s.sum (fun j => y.1 j - x.1 j) := hsum_erase
        _ ≤ s.sum (fun _j => η) := hsum_le
        _ = (s.card : ℝ) * η := by simp [nsmul_eq_mul]
        _ ≤ (Fintype.card n : ℝ) * η := hcard_le
        _ < ε := hε
    have hneg := neg_lt_neg hlower
    have hEq : -(x.1 i - y.1 i) = y.1 i - x.1 i := by ring
    rwa [hEq] at hneg
  · have hupper : y.1 i - x.1 i < η := by linarith [hcoord i]
    have hη_le : η ≤ (Fintype.card n : ℝ) * η := by
      have hcard_ge_one_nat : 1 ≤ Fintype.card n := Nat.succ_le_of_lt hcard_pos_nat
      calc
        η = (1 : ℝ) * η := by ring
        _ ≤ (Fintype.card n : ℝ) * η :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard_ge_one_nat) hη.le
    exact hupper.trans (hη_le.trans_lt hε)

omit [DecidableEq n] in
lemma stdSimplex_coord_lt_add_of_dist_lt
    {x y : stdSimplex ℝ n} {η : ℝ} (hxy : dist x y < η) (i : n) :
    x.1 i < y.1 i + η := by
  have hcoord :
      dist ((x : n → ℝ) i) ((y : n → ℝ) i) < η := by
    exact (dist_le_pi_dist (x : n → ℝ) (y : n → ℝ) i).trans_lt (by simpa using hxy)
  rw [Real.dist_eq] at hcoord
  have hxsub : x.1 i - y.1 i < η := (abs_lt.mp hcoord).2
  linarith

omit [DecidableEq n] in
lemma exists_nat_pos_card_div_lt [Nonempty n] {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ N : ℕ, 0 < N ∧ (Fintype.card n : ℝ) / (N : ℝ) < ρ := by
  classical
  obtain ⟨N, hN_gt⟩ := exists_nat_gt ((Fintype.card n : ℝ) / ρ)
  have hcard_nonneg : 0 ≤ (Fintype.card n : ℝ) := by positivity
  have hN_pos_real : 0 < (N : ℝ) := by
    have hquot_nonneg : 0 ≤ (Fintype.card n : ℝ) / ρ := div_nonneg hcard_nonneg hρ.le
    exact lt_of_le_of_lt hquot_nonneg hN_gt
  have hN_pos : 0 < N := Nat.cast_pos.mp hN_pos_real
  refine ⟨N, hN_pos, ?_⟩
  rw [div_lt_iff₀ hN_pos_real]
  have hmul : (Fintype.card n : ℝ) < (N : ℝ) * ρ := by
    exact (div_lt_iff₀ hρ).mp hN_gt
  linarith

omit [DecidableEq n] in
lemma sperner_grid_exists_fully_labeled_coord_cell_coarse [Nonempty n]
    (N : ℕ) (c : simplexGrid (n := n) N → n)
    (hc : ∀ (a : simplexGrid (n := n) N) (i : n), a.1 i = 0 → c a ≠ i) :
    ∃ base : simplexGrid (n := n) N,
      ∀ i : n, ∃ a : simplexGrid (n := n) N,
        c a = i ∧ ∀ j : n, |(a.1 j : ℝ) - (base.1 j : ℝ)| ≤ (N : ℝ) := by
  classical
  let i₀ : n := Classical.choice ‹Nonempty n›
  let base : simplexGrid (n := n) N := simplexGrid.vertex (n := n) N i₀
  refine ⟨base, fun i => ?_⟩
  obtain ⟨a, ha⟩ := simplexGrid.exists_color_of_boundary c hc i
  exact ⟨a, ha, fun j => simplexGrid.forall_abs_sub_le_mesh a base j⟩

omit [DecidableEq n] in
lemma sperner_grid_exists_fully_labeled_coord_cell_of_mesh_le_card [Nonempty n]
    (N : ℕ) (hNcard : N ≤ Fintype.card n) (c : simplexGrid (n := n) N → n)
    (hc : ∀ (a : simplexGrid (n := n) N) (i : n), a.1 i = 0 → c a ≠ i) :
    ∃ base : simplexGrid (n := n) N,
      ∀ i : n, ∃ a : simplexGrid (n := n) N,
        c a = i ∧
          ∀ j : n, |(a.1 j : ℝ) - (base.1 j : ℝ)| ≤ (Fintype.card n : ℝ) := by
  classical
  obtain ⟨base, hbase⟩ :=
    sperner_grid_exists_fully_labeled_coord_cell_coarse (n := n) N c hc
  refine ⟨base, fun i => ?_⟩
  obtain ⟨a, hcolor, hcoord⟩ := hbase i
  refine ⟨a, hcolor, fun j => ?_⟩
  exact (hcoord j).trans (by exact_mod_cast hNcard)

/--
The genuine finite Sperner parity/counting step, in its sharp grid-cell form.

This says that a Sperner coloring of the integer grid has a fully labeled unit cluster. A standard
proof uses the Freudenthal triangulation and the odd-door parity argument.
-/
theorem sperner_grid_exists_unit_neighborhood_image_eq_univ [Nonempty n]
    (N : ℕ) (_hN : 0 < N) (hcardN : Fintype.card n < N)
    (c : simplexGrid (n := n) N → n)
    (hc : ∀ (a : simplexGrid (n := n) N) (i : n), a.1 i = 0 → c a ≠ i) :
    ∃ base : simplexGrid (n := n) N,
      ((simplexGrid.unitNeighborhood (n := n) N base).image c : Finset n) = Finset.univ := by
  classical
  by_contra h
  exact simplexGrid.sperner_grid_not_forall_unit_neighborhood_image_ne_univ
    (n := n) N _hN hcardN c hc (by
      intro base hbase
      exact h ⟨base, hbase⟩)

theorem sperner_grid_exists_fully_labeled_unit_cluster [Nonempty n]
    (N : ℕ) (hN : 0 < N) (hcardN : Fintype.card n < N)
    (c : simplexGrid (n := n) N → n)
    (hc : ∀ (a : simplexGrid (n := n) N) (i : n), a.1 i = 0 → c a ≠ i) :
    ∃ base : simplexGrid (n := n) N,
      simplexGrid.FullyLabeledUnitCluster (n := n) c base := by
  obtain ⟨base, hbase⟩ :=
    sperner_grid_exists_unit_neighborhood_image_eq_univ (n := n) N hN hcardN c hc
  exact ⟨base, (simplexGrid.fullyLabeledUnitCluster_iff_image_eq_univ c base).mpr hbase⟩

/--
The high-resolution case of the coordinate-cell theorem follows from the sharp unit-cluster
Sperner statement.
-/
theorem sperner_grid_exists_fully_labeled_coord_cell_of_card_lt_mesh [Nonempty n]
    (N : ℕ) (hN : 0 < N) (hcardN : Fintype.card n < N)
    (c : simplexGrid (n := n) N → n)
    (hc : ∀ (a : simplexGrid (n := n) N) (i : n), a.1 i = 0 → c a ≠ i) :
    ∃ base : simplexGrid (n := n) N,
      ∀ i : n, ∃ a : simplexGrid (n := n) N,
        c a = i ∧
          ∀ j : n, |(a.1 j : ℝ) - (base.1 j : ℝ)| ≤ (Fintype.card n : ℝ) := by
  classical
  obtain ⟨base, hbase⟩ :=
    sperner_grid_exists_fully_labeled_unit_cluster (n := n) N hN hcardN c hc
  have hcard_one : (1 : ℝ) ≤ (Fintype.card n : ℝ) := by
    have hcard_pos : 0 < Fintype.card n := Fintype.card_pos_iff.mpr ‹Nonempty n›
    exact_mod_cast Nat.succ_le_of_lt hcard_pos
  refine ⟨base, fun i => ?_⟩
  obtain ⟨a, hcolor, hcoord⟩ := hbase i
  exact ⟨a, hcolor, fun j => (hcoord j).trans hcard_one⟩

/--
Coordinate-only finite Sperner core for the integer grid of the standard simplex.

Given a coloring satisfying the Sperner boundary condition, some grid cell has all labels and
all its displayed vertices are within `card n` integer-coordinate steps of a base vertex. This is
the only remaining combinatorial theorem needed by the Brouwer-style fixed point argument below.
-/
theorem sperner_grid_exists_fully_labeled_coord_cell [Nonempty n]
    (N : ℕ) (hN : 0 < N) (c : simplexGrid (n := n) N → n)
    (hc : ∀ (a : simplexGrid (n := n) N) (i : n), a.1 i = 0 → c a ≠ i) :
    ∃ base : simplexGrid (n := n) N,
      ∀ i : n, ∃ a : simplexGrid (n := n) N,
        c a = i ∧
          ∀ j : n, |(a.1 j : ℝ) - (base.1 j : ℝ)| ≤ (Fintype.card n : ℝ) := by
  classical
  by_cases hsub : Subsingleton n
  · haveI := hsub
    let i₀ : n := Classical.choice ‹Nonempty n›
    let base : simplexGrid (n := n) N := simplexGrid.vertex (n := n) N i₀
    refine ⟨base, fun i => ⟨base, Subsingleton.elim _ _, fun j => ?_⟩⟩
    simp
  by_cases hNcard : N ≤ Fintype.card n
  · exact sperner_grid_exists_fully_labeled_coord_cell_of_mesh_le_card
      (n := n) N hNcard c hc
  · exact sperner_grid_exists_fully_labeled_coord_cell_of_card_lt_mesh
      (n := n) N hN (Nat.lt_of_not_ge hNcard) c hc

/--
Finite Sperner core for the integer grid of the standard simplex, with the coordinate cell converted
to the metric mesh estimate used by the analytic part of the proof.
-/
theorem sperner_grid_exists_fully_labeled_cell [Nonempty n]
    (N : ℕ) (hN : 0 < N) (c : simplexGrid (n := n) N → n)
    (hc : ∀ (a : simplexGrid (n := n) N) (i : n), a.1 i = 0 → c a ≠ i) :
    ∃ base : simplexGrid (n := n) N,
      ∀ i : n, ∃ a : simplexGrid (n := n) N,
        c a = i ∧
          dist (simplexGrid.toStdSimplex hN a) (simplexGrid.toStdSimplex hN base) ≤
            (Fintype.card n : ℝ) / (N : ℝ) := by
  classical
  obtain ⟨base, hcell⟩ :=
    sperner_grid_exists_fully_labeled_coord_cell (n := n) N hN c hc
  refine ⟨base, fun i => ?_⟩
  obtain ⟨a, hcolor, hcoord⟩ := hcell i
  exact ⟨a, hcolor,
    simplexGrid.dist_toStdSimplex_le_of_forall_abs_sub_le hN (by positivity) hcoord⟩

/--
Finite Sperner-grid core. For the no-fixed-point coloring induced by `f`, every requested mesh
scale contains a fully labeled grid cell whose embedded vertices lie near one base vertex.
-/
theorem sperner_grid_exists_fully_labeled_small_cell [Nonempty n]
    (f : stdSimplex ℝ n → stdSimplex ℝ n)
    (hnofix : ∀ x, f x ≠ x) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ (N : ℕ) (hN : 0 < N) (base : simplexGrid (n := n) N),
      ∀ i : n, ∃ a : simplexGrid (n := n) N,
        spernerColor f hnofix hN a = i ∧
          dist (simplexGrid.toStdSimplex hN a) (simplexGrid.toStdSimplex hN base) < ρ := by
  classical
  obtain ⟨N, hN, hmesh⟩ := exists_nat_pos_card_div_lt (n := n) hρ
  obtain ⟨base, hcell⟩ :=
    sperner_grid_exists_fully_labeled_cell (n := n) N hN
      (spernerColor f hnofix hN)
      (fun a i hi => spernerColor_boundary f hnofix hN a hi)
  refine ⟨N, hN, base, fun i => ?_⟩
  obtain ⟨a, hcolor, hdist⟩ := hcell i
  exact ⟨a, hcolor, hdist.trans_lt hmesh⟩

/--
Sperner-grid one-sided approximation for the standard simplex.

This is the remaining finite-combinatorial core: construct a sufficiently fine labeled grid using
`spernerColor`, apply Sperner's lemma to obtain a fully labeled small cell, and turn that cell into
the coordinate inequalities below.
-/
theorem sperner_grid_exists_one_sided_approx_of_continuous [Nonempty n]
    (f : stdSimplex ℝ n → stdSimplex ℝ n) (hf : Continuous f) :
    ∀ η : ℝ, 0 < η → ∃ x, ∀ i, (f x).1 i < x.1 i + η := by
  classical
  intro η hη
  by_cases hfixed : ∃ x, Function.IsFixedPt f x
  · obtain ⟨x, hx⟩ := hfixed
    refine ⟨x, fun i => ?_⟩
    rw [hx]
    linarith
  · have hnofix : ∀ x, f x ≠ x := by
      intro x hx
      exact hfixed ⟨x, hx⟩
    have hη2 : 0 < η / 2 := half_pos hη
    have huc : UniformContinuous f := CompactSpace.uniformContinuous_of_continuous hf
    obtain ⟨δ, hδ_pos, hδ⟩ := (Metric.uniformContinuous_iff.mp huc) (η / 2) hη2
    let ρ := min δ (η / 2)
    have hρ_pos : 0 < ρ := lt_min hδ_pos hη2
    obtain ⟨N, hN, base, hcell⟩ :=
      sperner_grid_exists_fully_labeled_small_cell f hnofix ρ hρ_pos
    refine ⟨simplexGrid.toStdSimplex hN base, fun i => ?_⟩
    obtain ⟨a, hcolor, hdist⟩ := hcell i
    let xa := simplexGrid.toStdSimplex hN a
    let xb := simplexGrid.toStdSimplex hN base
    have hdist_delta : dist xa xb < δ := hdist.trans_le (min_le_left _ _)
    have hdist_eta : dist xa xb < η / 2 := hdist.trans_le (min_le_right _ _)
    have hf_dist : dist (f xa) (f xb) < η / 2 := hδ hdist_delta
    have hf_coord : (f xb).1 i < (f xa).1 i + η / 2 :=
      stdSimplex_coord_lt_add_of_dist_lt (by simpa [dist_comm] using hf_dist) i
    have hcolor_lt : (f xa).1 i < xa.1 i := by
      have hspec := spernerColor_spec f hnofix hN a
      simpa [hcolor, xa] using hspec
    have hbase_coord : xa.1 i < xb.1 i + η / 2 :=
      stdSimplex_coord_lt_add_of_dist_lt hdist_eta i
    change (f xb).1 i < xb.1 i + η
    linarith

theorem sperner_grid_exists_approx_fixed_point_of_continuous [Nonempty n]
    (f : stdSimplex ℝ n → stdSimplex ℝ n) (hf : Continuous f) :
    ∀ ε : ℝ, 0 < ε → ∃ x, dist (f x) x < ε := by
  intro ε hε
  classical
  let η := ε / ((Fintype.card n : ℝ) + 1)
  have hcard_nonneg : 0 ≤ (Fintype.card n : ℝ) := by positivity
  have hden_pos : 0 < (Fintype.card n : ℝ) + 1 := by positivity
  have hη : 0 < η := div_pos hε hden_pos
  obtain ⟨x, hx⟩ := sperner_grid_exists_one_sided_approx_of_continuous f hf η hη
  refine ⟨x, stdSimplex_dist_lt_of_forall_coord_lt_add hη ?_ hx⟩
  dsimp [η]
  have hlt : (Fintype.card n : ℝ) < (Fintype.card n : ℝ) + 1 := by linarith
  field_simp [hden_pos.ne']
  nlinarith

theorem stdSimplex_exists_approx_fixed_point_of_continuous [Nonempty n]
    (f : stdSimplex ℝ n → stdSimplex ℝ n) (hf : Continuous f) :
    ∀ ε : ℝ, 0 < ε → ∃ x, dist (f x) x < ε :=
  sperner_grid_exists_approx_fixed_point_of_continuous f hf

/--
The missing Mathlib ingredient for the general Perron-Frobenius route: Brouwer fixed point
specialized to the standard simplex.
-/
theorem stdSimplex_exists_isFixedPt_of_continuous [Nonempty n]
    (f : stdSimplex ℝ n → stdSimplex ℝ n) (hf : Continuous f) :
    ∃ x, Function.IsFixedPt f x := by
  exact exists_fixed_of_exists_approx hf
    (stdSimplex_exists_approx_fixed_point_of_continuous f hf)

/--
The exact benchmark statement has no `[Nonempty n]` assumption. Under Mathlib's definition,
irreducibility is vacuous for the empty index type, while `HasEigenvector` still requires a
nonzero vector. This is a blocker for proving the theorem exactly as stated.
-/
lemma empty_matrix_isIrreducible : (0 : Matrix Empty Empty ℝ).IsIrreducible := by
  constructor
  · intro i
    cases i
  · intro i
    cases i

lemma no_empty_eigenvector :
    ¬ ∃ v : Empty → ℝ,
      Module.End.HasEigenvector (Matrix.toLin' (0 : Matrix Empty Empty ℝ))
        (spectralRadius ℝ (0 : Matrix Empty Empty ℝ)).toReal v := by
  rintro ⟨v, hv⟩
  apply hv.2
  funext i
  cases i

end PerronFrobenius

/-!
# Perron-Frobenius benchmark scaffold

Benchmark statement:
`irreducible_nonnegative_matrix_has_positive_eigenvector_at_spectralRadius`.

Mathlib has useful ingredients:
* `Matrix.IsIrreducible` bundles entrywise nonnegativity and strong connectivity.
* `Matrix.isIrreducible_iff_exists_pow_pos` converts irreducibility to positive entries in powers.
* `spectralRadius` and finite-dimensional spectrum/eigenvalue bridges are available.

Main missing bridge to test/prove:
fixed-point existence for the continuous self-map `normalizedOneAddMulVec A hA.nonneg` of
`stdSimplex ℝ n`. Once a fixed point exists, the scaffold now constructs a positive eigenvector
and uses a Collatz-Wielandt coordinate comparison to identify its eigenvalue with
`(spectralRadius ℝ A).toReal`.
The corrected benchmark statement includes `[Nonempty n]`: `Matrix.IsIrreducible` is vacuous for
`Empty`, while `HasEigenvector` cannot hold on `Empty → ℝ`.

Phases:
1. Cone mechanics: nonnegative vectors are preserved by `A.mulVec` and by powers of `A`.
2. Irreducibility upgrade: if `v ≥ 0`, `v ≠ 0`, `A.mulVec v = r • v`, and `0 < r`, then `v > 0`.
3. Collatz-Wielandt bound: a positive subeigenvector `A.mulVec v ≤ r • v` bounds every real
   eigenvalue by `r`, hence `spectralRadius ℝ A ≤ ‖r‖₊`.
4. Perron existence: construct or import a fixed point of `normalizedOneAddMulVec`.
   This appears to be the remaining theorem not currently packaged in Mathlib.

Plan to remove the last `sorry`:

* Add a Mathlib-level theorem, not a Perron-specific axiom:
  `stdSimplex.exists_isFixedPt_of_continuous :
    ∀ f : stdSimplex ℝ n → stdSimplex ℝ n, Continuous f →
      ∃ x, Function.IsFixedPt f x`.
* Prove it by one of two routes:
  1. General Brouwer fixed point for compact convex subsets of finite-dimensional real normed
     spaces, then specialize to `stdSimplex`.
  2. A dedicated Sperner/KKM proof for `stdSimplex`; this is narrower but still requires
     substantial combinatorial topology infrastructure.
* Once that theorem exists, the final proof below is one line using
  `continuous_normalizedOneAddMulVec`.

The current Mathlib snapshot has the interval fixed-point theorem
`exists_mem_Icc_isFixedPt_of_mapsTo` and Banach's contraction theorem, but no higher-dimensional
Brouwer/Schauder theorem found under the topology, convexity, or algebraic-topology APIs.
-/

theorem irreducible_nonnegative_matrix_has_positive_eigenvector_at_spectralRadius
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℝ) (hA : A.IsIrreducible) :
    ∃ v : n → ℝ,
      Module.End.HasEigenvector (Matrix.toLin' A) (spectralRadius ℝ A).toReal v ∧
        (∀ i, 0 < v i) := by
  exact
    PerronFrobenius.exists_positive_eigenvector_at_spectralRadius_of_normalizedOneAddMulVec_has_fixedPoint
      hA
      (PerronFrobenius.stdSimplex_exists_isFixedPt_of_continuous
        (PerronFrobenius.normalizedOneAddMulVec A hA.nonneg)
        (PerronFrobenius.continuous_normalizedOneAddMulVec A hA.nonneg))
