import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Data.Finset.Max
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

open scoped ENNReal

namespace PerronFrobenius

variable {n : Type*} [Fintype n] [DecidableEq n]

section LinearAlgebraPart

open scoped Matrix

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

end LinearAlgebraPart


section ScarfLib


section fiberlemma

open Finset


variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

lemma injOn_sdiff (s : Finset α) (f : α → β) (h : s.card = (Finset.image f s).card + 1) : ∃ a b, a ∈ s ∧ b ∈ s ∧ f a = f b ∧ a ≠ b ∧ Set.InjOn f (s \ ({a, b} : Finset α)) := by
  have of_card_domain_eq_card_image_succ  (s : Finset α) (f : α → β) (h : s.card = (Finset.image f s).card + 1) :
  ∃ a b, a ∈ s ∧ b ∈ s ∧ f a = f b ∧ a ≠ b := by
    suffices ¬ Set.InjOn f s by
      contrapose! this
      tauto
    by_contra h1
    linarith [Finset.card_image_of_injOn h1]
  obtain ⟨a, b, as, bs, h1, h2⟩ := of_card_domain_eq_card_image_succ s f h
  have absub : {a, b} ⊆ s :=  Finset.insert_subset as (Finset.singleton_subset_iff.mpr bs)
  use a, b
  repeat apply And.intro;assumption
  rw [←Finset.coe_sdiff]
  apply Finset.injOn_of_card_image_eq
  rw [Finset.card_sdiff]
  · have : (Finset.image f (s \ {a, b})).card = (Finset.image f s).card - 1 := by
      have aux1 : ∀ c, c ∈ s → c ≠ a → c ≠ b → f c ≠ f a := by
        intro c cs ca cb fcfa
        have cardabc : ({a, b, c} : Finset α).card = 3 := by
          rw [Finset.card_eq_three]
          use a, b, c
          tauto
        have abcss : {a, b, c} ⊆ s := by
          apply Finset.insert_subset as
          apply Finset.insert_subset bs (by simp [cs])
        have : (image f s).card < s.card - 1 :=
          calc
            _ = (image f ((s \ {a, b, c}) ∪ {a, b, c})).card :=
              congrArg _ (congrArg _ (Eq.symm (sdiff_union_of_subset abcss)))
            _ = (image f (s \ {a, b, c}) ∪ image f {a, b, c}).card :=
              congrArg _ (Finset.image_union _ _)
            _ ≤ (image f (s \ {a, b, c})).card + (image f {a, b, c}).card :=
              Finset.card_union_le _ _
            _ = (image f (s \ {a, b, c})).card + 1 := by
              simp [Finset.card_eq_one]
              exact ⟨f a, by simp [←h1, fcfa]⟩
            _ ≤ (s \ {a, b, c}).card + 1 := by
              simp [Finset.card_image_le]
            _ = s.card - 3 + 1 := by
              rw [Finset.card_sdiff_of_subset abcss, cardabc]
            _ < _ := by
              have : 2 < s.card := by
                have := Finset.card_le_card abcss
                omega
              omega
        omega
      have aux2 : Finset.image f (s \ {a, b}) = Finset.image f s \ {f a} := by
        ext x
        constructor <;> intro h1'
        · obtain ⟨c, csdiff, fcx⟩ := Finset.mem_image.1 h1'
          obtain ⟨cs, cneab⟩ := Finset.mem_sdiff.1 csdiff
          simp at cneab
          simp
          exact ⟨⟨c, cs, fcx⟩, by simp [← fcx]; exact aux1 c cs cneab.1 cneab.2⟩
        · simp at h1'
          obtain ⟨c, cs, fcx⟩ := h1'.1
          simp [←fcx]
          use c
          simp [cs]
          by_contra! hf
          by_cases ceqa : c = a
          · rw [ceqa] at fcx; rw [fcx] at h1'; tauto
          · rw [hf ceqa, ←h1] at fcx; rw [fcx] at h1; tauto
      rw [aux2, Finset.card_sdiff_of_subset (by simp; exact ⟨a, as, rfl⟩), card_singleton]
    have hpair_inter : #(({a, b} : Finset α) ∩ s) = 2 := by
      have hinter : ({a, b} : Finset α) ∩ s = {a, b} := Finset.inter_eq_left.mpr absub
      rw [hinter, Finset.card_pair h2]
    rw [this, hpair_inter, h]
    omega

end fiberlemma


open Classical
open Finset

variable {T : Type*} [Inhabited T]
variable {Idx : Type*}

class IndexedLOrder (Idx T :Type*) where
  IST : Idx → LinearOrder T

instance : FunLike (IndexedLOrder Idx T) Idx (LinearOrder T) where
  coe := fun a => a.IST
  coe_injective' := fun f g h => by cases f; cases g; congr


variable [IST : IndexedLOrder Idx T]

set_option quotPrecheck false

local notation  lhs "<[" i "]" rhs => (IST i).lt lhs rhs
local notation  lhs "≤[" i "]" rhs => (IST i).le lhs rhs

namespace IndexedLOrder
variable (sigma : Finset T) (C : Finset Idx)


def isDominant  :=
  ∀ y, ∃ i ∈ C, ∀ x ∈ sigma,  y ≤[i] x

variable {sigma C} in
lemma Nonempty_of_Dominant (h : IST.isDominant sigma C) : C.Nonempty := by
  obtain ⟨j,hj⟩ := h default
  exact ⟨j, hj.1⟩


omit [Inhabited T] in
lemma Dominant_of_subset (sigma τ : Finset T) (C : Finset Idx) :
  τ ⊆ sigma → isDominant sigma C  → isDominant τ C := by
    intro h1 h2 y
    obtain ⟨j,hj⟩:= h2 y
    use j,hj.1
    intro x hx
    exact hj.2 x (h1 hx)

omit [Inhabited T] in
lemma Dominant_of_supset (sigma : Finset T) (C D: Finset Idx) :
  C ⊆ D → isDominant sigma C  → isDominant sigma D := by
    intro h1 h2 y
    obtain ⟨j,hj⟩:= h2 y
    use j,(h1 hj.1)
    intro x hx
    exact hj.2 x hx

abbrev mini {sigma : Finset T} (h2 : sigma.Nonempty) (i : Idx) : T := @Finset.min' _ (IST i) _ h2

omit [Inhabited T] in
lemma keylemma_of_dominant {sigma : Finset T} {C: Finset Idx} (h1 : IST.isDominant sigma C) (h2: sigma.Nonempty): sigma  = C.image (mini h2)  :=
  by
    ext a
    constructor
    · intro ha
      rw [mem_image]
      by_contra  hm
      push Not at hm
      obtain ⟨i,hi1,hi2⟩ := h1 a
      replace hm := hm i hi1
      rw [mini] at hm
      have ha1 := @Finset.le_min' _ (IST i) _ h2 a hi2
      have ha2 := @Finset.min'_le _ (IST i) _ _ ha
      apply hm
      refine @eq_of_le_of_ge _ (IST i).toPartialOrder _ _ ha2 ha1
    · suffices h: ∀ x ∈ C, mini h2 x = a → a ∈ sigma from
      by simp;exact h
      intro _ _ ha
      simp [mini,<-ha,Finset.min'_mem]

omit [Inhabited T] in
lemma card_le_of_domiant {sigma : Finset T} {C: Finset Idx} (h1 : IST.isDominant sigma C) : sigma.card  ≤  C.card  := by
  by_cases h2 : sigma.Nonempty
  · rw [keylemma_of_dominant h1 h2]
    apply Finset.card_image_le
  · rw [not_nonempty_iff_eq_empty] at h2
    simp only [h2, card_empty, zero_le]

omit [Inhabited T] in
lemma empty_Dominant (h : D.Nonempty) : IST.isDominant Finset.empty D := by
  intro y
  obtain ⟨j,hj⟩ := h
  use j
  constructor
  · exact hj
  · intro x hx
    contradiction

abbrev isCell  := isDominant sigma C

abbrev isRoom :=  isCell sigma C ∧ C.card = sigma.card

lemma sigma_nonempty_of_room {sigma : Finset T} {C : Finset Idx} (h : isRoom sigma C) : sigma.Nonempty  := by
  have hC : C.Nonempty := Nonempty_of_Dominant h.1
  have hCpos : 0 < C.card := Finset.card_pos.2 hC
  have h_card : sigma.card = C.card := h.2.symm
  have hpos : 0 < sigma.card := by rwa [h_card]
  exact Finset.card_pos.1 hpos

abbrev isDoor  :=  isCell sigma C ∧ C.card = sigma.card + 1


variable [DecidableEq T] [DecidableEq Idx]

inductive isDoorof (τ : Finset T) (D : Finset Idx) (sigma : Finset T) (C : Finset Idx) : Prop
  | idoor (h0 : isCell sigma C) (h1 : isDoor τ D) (x :T) (h1 : x ∉ τ) (h2 : insert x τ = sigma) (h3 : D = C)
  | odoor (h0 : isCell sigma C) (h1 : isDoor τ D) (j :Idx) (h1 : j ∉ C) (h2 : τ = sigma) (h3 : D = insert j C)

omit [Inhabited T] in
lemma isCell_of_door (h1 : isDoorof τ D sigma C) : IST.isCell τ D := by
  cases h1
  · rename_i h0 _ j h1 h3 h4
    rw [h4]
    exact IST.Dominant_of_subset _ _ C (by simp [<-h3]) h0
  · rename_i h0 _ j h1 h2' h3
    rw [h2', h3]
    exact IST.Dominant_of_supset _ _ _ (Finset.subset_insert j C) h0

variable {sigma C} in
omit [Inhabited T] in
lemma isRoom_of_Door (h1 : isDoorof τ D sigma C) : IST.isRoom sigma C := by
  cases h1
  · rename_i h0 h2 x h3 h4 h5
    constructor
    · exact h0
    · simp only [<-h5, h2.2, <-h4, h3, not_false_eq_true, Finset.card_insert_of_notMem]
  · rename_i h0 h2 x h3 h4 h5
    constructor
    · exact h0
    · have h6 := Finset.card_insert_of_notMem h3
      subst h4
      replace h5 : D.card = (insert x C).card := by rw [h5]
      rw [h6] at h5
      rw [h2.2] at h5
      exact Eq.symm $ (add_left_inj _).1 h5

omit [Inhabited T] in
lemma room_is_not_door (h1 : IST.isRoom sigma C) : ∀ τ D,  ¬ (isDoorof sigma C τ D) := by
  intro τ D hd
  unfold isRoom at h1
  cases hd with
  | idoor h0 hd  x h2 h3 h4 =>
    unfold isDoor at hd
    obtain ⟨_,hd⟩ := hd
    have cond : #sigma = #sigma +1 := by rw [h1.2] at hd; assumption
    simp at cond
  | odoor h0 hd j h2 h3 h4 =>
    unfold isDoor at hd
    obtain ⟨_,hd⟩ := hd
    have cond : #sigma = #sigma +1 := by rw [h1.2] at hd; assumption
    simp at cond

variable (τ D) in
abbrev isOutsideDoor := IST.isDoor τ D ∧ τ = Finset.empty

variable (τ D) in
abbrev isInternalDoor := IST.isDoor τ D ∧ τ.Nonempty


omit [Inhabited T] [DecidableEq T] [DecidableEq Idx] in
lemma outsidedoor_singleton (i : Idx) : IST.isOutsideDoor Finset.empty {i} := by
  constructor
  · rw [isDoor,isCell,isDominant]
    constructor
    · intro y; use i
      constructor
      · exact Finset.mem_singleton.2 (rfl)
      · intro x hx
        contradiction
    · simp only [Finset.card_singleton]
      rfl
  · rfl



omit [Inhabited T] [DecidableEq T] [DecidableEq Idx] in
lemma outsidedoor_is_singleton (h : IST.isOutsideDoor τ  D) :  τ = Finset.empty ∧  ∃ i, D = {i} := by
  obtain ⟨h1, h2⟩ := h
  subst h2
  obtain ⟨_,h3⟩ := h1
  replace h4 : D.card = 1 := by
    simp_all
    rfl
  exact ⟨rfl, Finset.card_eq_one.1 h4⟩



section KeyLemma


def M_set (τ : Finset T) (D : Finset Idx) (i : Idx) (h_nonempty : τ.Nonempty) : Set T :=
  {y : T | ∀ k ∈ D, k ≠ i → mini h_nonempty k <[k] y}


def is_maximal_in_M_set (τ : Finset T) (D : Finset Idx) (i : Idx) (h_nonempty : τ.Nonempty) (x : T) : Prop :=
  x ∈ M_set τ D i h_nonempty ∧ ∀ y ∈ M_set τ D i h_nonempty, y ≤[i] x


noncomputable def m_element [Fintype T] (τ : Finset T) (D : Finset Idx) (i : Idx) (h_nonempty : τ.Nonempty)
    (h : (M_set τ D i h_nonempty).Nonempty) : T :=
  @Finset.max' _ (IST i) (M_set τ D i h_nonempty).toFinset (Set.toFinset_nonempty.mpr h)


omit[Inhabited T][DecidableEq T][DecidableEq Idx] in
theorem m_element_is_maximal [Fintype T] (τ : Finset T) (D : Finset Idx) (i : Idx) (h_nonempty : τ.Nonempty)
    (h : (M_set τ D i h_nonempty).Nonempty) :
    is_maximal_in_M_set τ D i h_nonempty (m_element τ D i h_nonempty h) := by
  unfold is_maximal_in_M_set m_element
  let s_finset := (M_set τ D i h_nonempty).toFinset
  have h_nonempty_finset: s_finset.Nonempty := Set.toFinset_nonempty.mpr h
  constructor
  · rw [←Set.mem_toFinset]
    exact @Finset.max'_mem _ (IST i) s_finset h_nonempty_finset
  · intros y hy
    rw [←Set.mem_toFinset] at hy
    apply @Finset.le_max' _ (IST i)
    exact hy


omit [Inhabited T] in
lemma sublemma_3_1 [Fintype T] (τ : Finset T) (D : Finset Idx)
    (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty) :
    ∀ i ∈ D, (IST.isDominant τ (D.erase i) ↔
      (∃ a b, a ∈ D ∧ b ∈ D ∧ a ≠ b ∧
       mini h_nonempty a = mini h_nonempty b ∧
       (i = a ∨ i = b) ∧
       M_set τ D i h_nonempty = ∅)) := by
  intro i hi
  constructor
  · intro h_dom
    have h_card : D.card = τ.card + 1 := h_door.2
    have h_image_card : D.card = (D.image (mini h_nonempty)).card + 1 := by
      have h_dominant : IST.isDominant τ D := h_door.1
      have h_image_sub : D.image (mini h_nonempty) ⊆ τ := by
        intro x hx
        simp at hx
        obtain ⟨j, _, hj_eq⟩ := hx
        rw [←hj_eq, mini]
        exact @Finset.min'_mem _ (IST j) τ h_nonempty
      have h_image_eq : D.image (mini h_nonempty) = τ := by
        convert (keylemma_of_dominant h_dominant h_nonempty).symm
      rw [h_card, h_image_eq]
    obtain ⟨a, b, ha_mem, hb_mem, h_eq_mini, h_ne, _⟩ := injOn_sdiff D (mini h_nonempty) h_image_card
    use a, b, ha_mem, hb_mem, h_ne, h_eq_mini
    by_cases h_case : i = a ∨ i = b
    · constructor
      · exact h_case
      · ext y
        simp [M_set]
        obtain ⟨k, hk_in_erase, hk_dom⟩ := h_dom y
        have hk_in_D : k ∈ D := (Finset.mem_erase.mp hk_in_erase).2
        have hk_ne_i : k ≠ i := (Finset.mem_erase.mp hk_in_erase).1
        use k, hk_in_D, hk_ne_i
    · push Not at h_case
      obtain ⟨h_i_ne_a, h_i_ne_b⟩ := h_case

      have h_a_in_erase : a ∈ D.erase i := Finset.mem_erase.mpr ⟨h_i_ne_a.symm, ha_mem⟩
      have h_b_in_erase : b ∈ D.erase i := Finset.mem_erase.mpr ⟨h_i_ne_b.symm, hb_mem⟩

      have h_not_inj : ¬Set.InjOn (mini h_nonempty) (D.erase i : Set Idx) := by
        intro h_inj
        exact h_ne (h_inj h_a_in_erase h_b_in_erase h_eq_mini)

      have h_image_lt : ((D.erase i).image (mini h_nonempty)).card < (D.erase i).card := by
        by_contra h_not_lt
        push Not at h_not_lt
        have h_eq : ((D.erase i).image (mini h_nonempty)).card = (D.erase i).card :=
          le_antisymm Finset.card_image_le h_not_lt
        have h_inj : Set.InjOn (mini h_nonempty) (D.erase i : Set Idx) :=
          Finset.injOn_of_card_image_eq h_eq
        exact h_not_inj h_inj
      exfalso
      have h_dom_image := keylemma_of_dominant h_dom h_nonempty
      have h_tau_eq_image : τ.card = ((D.erase i).image (mini h_nonempty)).card := by
        congr; ext; simp [h_dom_image]
      have h_tau_eq_erase : τ.card = (D.erase i).card := by
        rw [Finset.card_erase_of_mem hi, h_door.2]; simp
      rw [h_tau_eq_erase] at h_tau_eq_image
      rw [h_tau_eq_image] at h_image_lt
      exact not_lt.mpr (le_refl _) h_image_lt
  · rintro ⟨a, b, ha_mem, hb_mem, h_ne, h_eq_mini, h_i_case, h_Mi_empty⟩
    intro y
    unfold M_set at h_Mi_empty
    simp only [Set.mem_setOf_eq, Set.eq_empty_iff_forall_notMem] at h_Mi_empty
    specialize h_Mi_empty y
    push Not at h_Mi_empty
    obtain ⟨k, hk_mem, hk_ne_i, hk_not_lt⟩ := h_Mi_empty
    use k
    constructor
    · exact Finset.mem_erase.mpr ⟨hk_ne_i, hk_mem⟩
    · intro x hx
      letI : LinearOrder T := IST k
      have h_y_le_mini : y ≤[k] mini h_nonempty k := hk_not_lt
      have h_mini_le_x : mini h_nonempty k ≤[k] x := Finset.min'_le τ x hx
      exact @le_trans _ (IST k).toPreorder _ _ _ h_y_le_mini h_mini_le_x


omit [Inhabited T] in
lemma sublemma_3_2 [Fintype T] (τ : Finset T) (D : Finset Idx) (x : T)
    (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty) (h_not_mem : x ∉ τ)
    (a b : Idx) (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b)
    (h_eq : mini h_nonempty a = mini h_nonempty b) :
    IST.isDominant (insert x τ) D ↔
    (∃ i ∈ ({a, b} : Finset Idx), (M_set τ D i h_nonempty).Nonempty ∧
     is_maximal_in_M_set τ D i h_nonempty x) := by
  constructor
  · intro h_dominant
    have h_insert_nonempty : (insert x τ).Nonempty := Finset.insert_nonempty x τ
    have h_min_eq_image : D.image (mini h_insert_nonempty) = insert x τ := by
      convert (keylemma_of_dominant h_dominant h_insert_nonempty).symm
    have h_x_is_min : ∃ i ∈ D, mini h_insert_nonempty i = x := by
      have h_x_in_image : x ∈ D.image (mini h_insert_nonempty) := by
        rw [h_min_eq_image]
        exact Finset.mem_insert_self x τ
      exact Finset.mem_image.mp h_x_in_image
    obtain ⟨i, hi_mem, hi_eq⟩ := h_x_is_min
    have h_is_room : isRoom (insert x τ) D := by
      unfold isRoom
      constructor
      · exact h_dominant
      · rw [Finset.card_insert_of_notMem h_not_mem, h_door.2]
    have h_inj_insert : Set.InjOn (mini h_insert_nonempty) (D : Set Idx) := by
      apply Finset.injOn_of_card_image_eq
      rw [h_min_eq_image, h_is_room.2]
    have h_mini_lt_x : ∀ k ∈ D, k ≠ i → mini h_nonempty k <[k] x := by
      intros k hk_mem hk_ne_i
      have h_mini_cases : mini h_insert_nonempty k = mini h_nonempty k ∨ mini h_insert_nonempty k = x := by
        letI := IST k
        unfold mini
        by_cases h : τ.min' h_nonempty ≤[k] x
        · left
          apply le_antisymm
          · apply Finset.min'_le
            exact Finset.mem_insert_of_mem (Finset.min'_mem _ h_nonempty)
          · apply Finset.le_min'
            intro y hy
            cases Finset.mem_insert.mp hy with
            | inl h_eq => rw [h_eq]; exact h
            | inr h_mem => exact Finset.min'_le _ _ h_mem
        · right
          apply le_antisymm
          · apply Finset.min'_le
            exact Finset.mem_insert_self _ _
          · apply Finset.le_min'
            intro y hy
            cases Finset.mem_insert.mp hy with
            | inl h_eq => rw [h_eq]
            | inr h_mem => exact le_of_not_ge (fun h_le => h (le_trans (Finset.min'_le _ _ h_mem) h_le))
      have h_mini_neq_x : mini h_insert_nonempty k ≠ x := by
        intro h_eq
        have h_inj : Set.InjOn (mini h_insert_nonempty) (D : Set Idx) := h_inj_insert
        have hi_mem_D : i ∈ D := hi_mem
        have hk_mem_D : k ∈ D := hk_mem
        have h_mini_i_eq_x : mini h_insert_nonempty i = x := hi_eq
        exact hk_ne_i (h_inj hi_mem_D hk_mem_D (h_mini_i_eq_x.trans h_eq.symm)).symm
      letI := IST k
      have h_mini_eq_k : mini h_insert_nonempty k = mini h_nonempty k := by
        cases h_mini_cases with
        | inl h => exact h
        | inr h => exact absurd h h_mini_neq_x
      apply lt_of_le_of_ne
      · have h_le : mini h_insert_nonempty k ≤[k] x := by
          apply @Finset.min'_le _ (IST k)
          exact Finset.mem_insert_self x τ
        rw [h_mini_eq_k] at h_le
        exact h_le
      · exact fun h_eq_x => h_not_mem (h_eq_x ▸ Finset.min'_mem τ h_nonempty)
    have h_x_le_mini_i : x ≤[i] mini h_nonempty i := by
      letI := IST i
      rw [← hi_eq]
      unfold mini
      apply Finset.min'_le
      · exact Finset.mem_insert_of_mem (Finset.min'_mem _ h_nonempty)
    have h_i_in_ab : i ∈ ({a, b} : Finset Idx) := by
      by_cases hik : i = a ∨ i = b
      · simp [hik]
      · push Not at hik
        obtain ⟨hia, hib⟩ := hik
        have h_mini_eq_for_ne_i : ∀ k ∈ D, k ≠ i → mini h_insert_nonempty k = mini h_nonempty k := by
          intros k hk_mem hk_ne_i
          have h_cases : mini h_insert_nonempty k = mini h_nonempty k ∨ mini h_insert_nonempty k = x := by
            letI := IST k
            by_cases h : τ.min' h_nonempty ≤[k] x
            · left
              apply le_antisymm
              · apply Finset.min'_le
                exact Finset.mem_insert_of_mem (Finset.min'_mem _ h_nonempty)
              · apply Finset.le_min'
                intro y hy
                cases Finset.mem_insert.mp hy with
                | inl h_eq_x => rw [h_eq_x]; exact h
                | inr h_mem => exact Finset.min'_le _ _ h_mem
            · right
              apply le_antisymm
              · apply Finset.min'_le
                exact Finset.mem_insert_self _ _
              · apply Finset.le_min'
                intro y hy
                cases Finset.mem_insert.mp hy with
                | inl h_eq_x => rw [h_eq_x]
                | inr h_mem => exact le_of_not_ge (fun h_le => h (le_trans (Finset.min'_le _ _ h_mem) h_le))
          have h_mini_neq_x : mini h_insert_nonempty k ≠ x := by
            intro h_eq_k_x
            exact hk_ne_i (h_inj_insert hk_mem hi_mem (h_eq_k_x.trans hi_eq.symm))
          cases h_cases with
          | inl h => exact h
          | inr h => exact absurd h h_mini_neq_x
        have h_mini_a_eq : mini h_insert_nonempty a = mini h_nonempty a := h_mini_eq_for_ne_i a ha (Ne.symm hia)
        have h_mini_b_eq : mini h_insert_nonempty b = mini h_nonempty b := h_mini_eq_for_ne_i b hb (Ne.symm hib)
        have h_contr : mini h_insert_nonempty a = mini h_insert_nonempty b := by
          rw [h_mini_a_eq, h_mini_b_eq, h_eq]
        exact (hab (h_inj_insert ha hb h_contr)).elim
    use i, h_i_in_ab
    constructor
    · have h_nonempty_M : (M_set τ D i h_nonempty).Nonempty := by
        use x
        unfold M_set
        apply Set.mem_setOf.mpr
        intro k hk_mem hk_ne_i
        exact h_mini_lt_x k hk_mem hk_ne_i
      exact h_nonempty_M
    · unfold is_maximal_in_M_set
      constructor
      · unfold M_set
        apply Set.mem_setOf.mpr
        intro k hk_mem hk_ne_i
        exact h_mini_lt_x k hk_mem hk_ne_i
      · intros y hy
        letI := IST i
        unfold M_set at hy
        simp at hy
        obtain ⟨k, hk_in_D, h_y_le_all⟩ := h_dominant y
        by_cases hik : k = i
        · subst hik
          exact h_y_le_all x (Finset.mem_insert_self x τ)
        · have h_lt_y : mini h_nonempty k <[k] y := hy k hk_in_D hik
          have h_mini_mem : mini h_nonempty k ∈ τ := by
            unfold mini
            exact @Finset.min'_mem _ (IST k) _ h_nonempty
          have h_mini_mem_insert : mini h_nonempty k ∈ insert x τ := Finset.mem_insert_of_mem h_mini_mem
          have h_le_m : y ≤[k] mini h_nonempty k := h_y_le_all (mini h_nonempty k) h_mini_mem_insert
          letI := IST k
          exact absurd (lt_of_lt_of_le h_lt_y h_le_m) (lt_irrefl _)

  · rintro ⟨i, hi_mem_ab, h_M_nonempty, h_x_is_max⟩
    have h_x_in_M : x ∈ M_set τ D i h_nonempty := h_x_is_max.1
    unfold isDominant
    intro y
    have h_dom_tau := h_door.1
    obtain ⟨k, hk_in_D, hk_dom⟩ := h_dom_tau y
    by_cases h_k_eq_i : k = i
    · subst h_k_eq_i
      have hk_in_D : k ∈ D := by
        cases Finset.mem_insert.mp hi_mem_ab with
        | inl hk_eq_a => rwa [hk_eq_a]
        | inr hk_eq_b => have : k = b := Finset.mem_singleton.mp hk_eq_b; rw [this]; exact hb
      letI := IST k
      by_cases h_y_le_x : y ≤[k] x
      · use k, hk_in_D
        intro z hz
        cases Finset.mem_insert.mp hz with
        | inl h_z_eq_x => rw [h_z_eq_x]; exact h_y_le_x
        | inr h_z_in_tau => exact hk_dom z h_z_in_tau
      · have h_x_lt_y : x <[k] y := lt_of_not_ge h_y_le_x
        have h_y_not_in_M : y ∉ M_set τ D k h_nonempty := by
          intro h_y_in_M
          have h_y_le_x : y ≤[k] x := h_x_is_max.2 y h_y_in_M
          exact not_le.mpr h_x_lt_y h_y_le_x
        simp [M_set] at h_y_not_in_M
        push Not at h_y_not_in_M
        obtain ⟨j, hj_in_D, hj_ne_k, hj_not_lt⟩ := h_y_not_in_M
        use j, hj_in_D
        intro z hz
        cases Finset.mem_insert.mp hz with
        | inl h_z_eq_x =>
          rw [h_z_eq_x]
          letI := IST j
          have h_mini_lt_x : mini h_nonempty j <[j] x := h_x_in_M j hj_in_D hj_ne_k
          have h_y_le_mini : y ≤[j] mini h_nonempty j := le_of_not_gt hj_not_lt
          exact le_of_lt (lt_of_le_of_lt h_y_le_mini h_mini_lt_x)
        | inr h_z_in_tau =>
          letI := IST j
          have h_y_le_mini : y ≤[j] mini h_nonempty j := le_of_not_gt hj_not_lt
          have h_mini_le_z : mini h_nonempty j ≤[j] z := Finset.min'_le τ z h_z_in_tau
          exact le_trans h_y_le_mini h_mini_le_z
    · use k, hk_in_D
      intro z hz
      cases Finset.mem_insert.mp hz with
      | inl h_z_eq_x =>
        rw [h_z_eq_x]
        letI := IST k
        have h_y_le_mini : y ≤[k] mini h_nonempty k := hk_dom (mini h_nonempty k) (Finset.min'_mem τ h_nonempty)
        have h_mini_lt_x : mini h_nonempty k <[k] x := h_x_in_M k hk_in_D h_k_eq_i
        exact le_of_lt (lt_of_le_of_lt h_y_le_mini h_mini_lt_x)
      | inr h_z_in_tau =>
        exact hk_dom z h_z_in_tau



omit [Inhabited T][DecidableEq T] in
lemma M_sets_disjoint [Fintype T] (τ : Finset T) (D : Finset Idx) (a b : Idx)
    (h_nonempty : τ.Nonempty) (h_door : IST.isDoor τ D)
    (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b)
    (h_eq : mini h_nonempty a = mini h_nonempty b) :
    M_set τ D a h_nonempty ∩ M_set τ D b h_nonempty = ∅ := by
  ext y
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false]
  constructor
  · intro ⟨h_in_a, h_in_b⟩
    unfold M_set at h_in_a h_in_b
    have h_b_ne_a : b ≠ a := hab.symm
    have h_mini_b_lt_y : mini h_nonempty b <[b] y := h_in_a b hb h_b_ne_a
    have h_mini_a_lt_y : mini h_nonempty a <[a] y := h_in_b a ha hab
    rw [h_eq] at h_mini_a_lt_y
    obtain ⟨k, hk_in_D, hk_dom⟩ := h_door.1 y
    have h_mini_b_mem : mini h_nonempty b ∈ τ := by
      unfold mini
      exact @Finset.min'_mem _ (IST b) _ h_nonempty
    have h_y_le_mini_b : y ≤[k] mini h_nonempty b := hk_dom (mini h_nonempty b) h_mini_b_mem
    by_cases hk_eq_a : k = a
    · subst hk_eq_a
      letI := IST k
      exact not_le.mpr h_mini_a_lt_y h_y_le_mini_b
    · by_cases hk_eq_b : k = b
      · subst hk_eq_b
        letI := IST k
        exact not_le.mpr h_mini_b_lt_y h_y_le_mini_b
      · have h_mini_k_lt_y : mini h_nonempty k <[k] y := h_in_a k hk_in_D hk_eq_a
        have h_mini_k_mem : mini h_nonempty k ∈ τ := by
          unfold mini
          exact @Finset.min'_mem _ (IST k) _ h_nonempty
        have h_y_le_mini_k : y ≤[k] mini h_nonempty k := hk_dom (mini h_nonempty k) h_mini_k_mem
        letI := IST k
        exact not_le.mpr h_mini_k_lt_y h_y_le_mini_k
  · intro h
    exact False.elim h

omit [Inhabited T][DecidableEq T] in
lemma m_element_not_in_tau [Fintype T] (τ : Finset T) (D : Finset Idx) (i a b : Idx)
    (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty)
    (ha_mem : a ∈ D) (hb_mem : b ∈ D) (hab : a ≠ b)
    (h_eq_mini : mini h_nonempty a = mini h_nonempty b)
    (h_M_nonempty : (M_set τ D i h_nonempty).Nonempty)
    (h_i_is : i = a ∨ i = b) :
    m_element τ D i h_nonempty h_M_nonempty ∉ τ := by
  let m_i := m_element τ D i h_nonempty h_M_nonempty
  have h_max : is_maximal_in_M_set τ D i h_nonempty m_i :=
    m_element_is_maximal τ D i h_nonempty h_M_nonempty
  intro h_m_in_tau
  obtain ⟨k, hk_mem, hk_dom⟩ := h_door.1 m_i
  by_cases hk_eq_i : k = i
  · subst hk_eq_i
    have h_m_le_mini : m_i ≤[k] mini h_nonempty k := hk_dom (mini h_nonempty k) (by
      unfold mini
      exact @Finset.min'_mem _ (IST k) _ h_nonempty)
    have h_m_eq_mini : m_i = mini h_nonempty k := by
      letI := IST k
      have h_mini_le_m : mini h_nonempty k ≤[k] m_i := Finset.min'_le τ m_i h_m_in_tau
      exact le_antisymm h_m_le_mini h_mini_le_m
    have h_m_in_M : m_i ∈ M_set τ D k h_nonempty := h_max.1
    unfold M_set at h_m_in_M
    cases h_i_is with
    | inl hi_eq_a =>
      subst hi_eq_a
      have h_mini_b_lt_m : mini h_nonempty b <[b] m_i := h_m_in_M b hb_mem hab.symm
      rw [h_m_eq_mini, h_eq_mini] at h_mini_b_lt_m
      letI := IST b
      exact lt_irrefl (mini h_nonempty b) h_mini_b_lt_m
    | inr hi_eq_b =>
      subst hi_eq_b
      have h_mini_a_lt_m : mini h_nonempty a <[a] m_i := h_m_in_M a ha_mem hab
      rw [h_m_eq_mini, ← h_eq_mini] at h_mini_a_lt_m
      letI := IST a
      exact lt_irrefl (mini h_nonempty a) h_mini_a_lt_m
  · have h_m_in_M : m_i ∈ M_set τ D i h_nonempty := h_max.1
    unfold M_set at h_m_in_M
    have h_mini_k_lt_m : mini h_nonempty k <[k] m_i := h_m_in_M k hk_mem hk_eq_i
    have h_m_le_mini_k : m_i ≤[k] mini h_nonempty k := hk_dom (mini h_nonempty k) (by
      unfold mini
      exact @Finset.min'_mem _ (IST k) _ h_nonempty)
    letI := IST k
    exact not_le.mpr h_mini_k_lt_m h_m_le_mini_k

omit [Inhabited T] in
lemma odoor_index_in_pair [Fintype T] (τ : Finset T) (D : Finset Idx) (C : Finset Idx)
    (a b j : Idx) (_h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty)
    (ha_mem : a ∈ D) (hb_mem : b ∈ D) (hab : a ≠ b)
    (h_eq_mini : mini h_nonempty a = mini h_nonempty b)
    (h_dom : IST.isDominant τ C) (h_room_card : C.card = τ.card)
    (_hj_not_mem : j ∉ C) (hc_eq : D = insert j C) :
    j ∈ ({a, b} : Finset Idx) := by
  by_contra h_not_in
  simp only [Finset.mem_insert, Finset.mem_singleton] at h_not_in
  push Not at h_not_in
  obtain ⟨hj_ne_a, hj_ne_b⟩ := h_not_in
  have ha_in_C : a ∈ C := by
    have ha_in_D : a ∈ D := ha_mem
    rw [hc_eq] at ha_in_D
    cases Finset.mem_insert.mp ha_in_D with
    | inl h_eq => exact absurd h_eq (Ne.symm hj_ne_a)
    | inr h_mem => exact h_mem
  have hb_in_C : b ∈ C := by
    have hb_in_D : b ∈ D := hb_mem
    rw [hc_eq] at hb_in_D
    cases Finset.mem_insert.mp hb_in_D with
    | inl h_eq => exact absurd h_eq (Ne.symm hj_ne_b)
    | inr h_mem => exact h_mem
  have h_inj_C : Set.InjOn (mini h_nonempty) (C : Set Idx) := by
    apply Finset.injOn_of_card_image_eq
    have h_tau_eq_C_image : τ = C.image (mini h_nonempty) := by
      convert keylemma_of_dominant h_dom h_nonempty
    rw [←h_tau_eq_C_image]
    exact h_room_card.symm
  exact hab (h_inj_C ha_in_C hb_in_C h_eq_mini)

omit [Inhabited T] [DecidableEq T] [DecidableEq Idx] in
lemma maximal_element_unique [Fintype T] (τ : Finset T) (D : Finset Idx) (i : Idx)
    (h_nonempty : τ.Nonempty) (h_M_nonempty : (M_set τ D i h_nonempty).Nonempty)
    (x : T) (h_x_max : is_maximal_in_M_set τ D i h_nonempty x) :
    x = m_element τ D i h_nonempty h_M_nonempty := by
  let m_i := m_element τ D i h_nonempty h_M_nonempty
  have h_mi_max : is_maximal_in_M_set τ D i h_nonempty m_i :=
    m_element_is_maximal τ D i h_nonempty h_M_nonempty
  letI := IST i
  have h_x_in_M : x ∈ M_set τ D i h_nonempty := h_x_max.1
  have h_mi_in_M : m_i ∈ M_set τ D i h_nonempty := h_mi_max.1
  have h_x_le_mi : x ≤[i] m_i := h_mi_max.2 x h_x_in_M
  have h_mi_le_x : m_i ≤[i] x := h_x_max.2 m_i h_mi_in_M
  exact le_antisymm h_x_le_mi h_mi_le_x

omit [Inhabited T] in
lemma idoor_determines_element [Fintype T] (τ : Finset T) (D : Finset Idx)
    (a b : Idx) (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty)
    (ha_mem : a ∈ D) (hb_mem : b ∈ D) (hab : a ≠ b)
    (h_eq_mini : mini h_nonempty a = mini h_nonempty b)
    (h_Ma_nonempty : (M_set τ D a h_nonempty).Nonempty)
    (h_Mb_nonempty : (M_set τ D b h_nonempty).Nonempty)
    (x : T) (h_room : IST.isRoom (insert x τ) D)
    (hx_not_mem : x ∉ τ) :
    x = m_element τ D a h_nonempty h_Ma_nonempty ∨
    x = m_element τ D b h_nonempty h_Mb_nonempty := by
  have h_dom : IST.isDominant (insert x τ) D := h_room.1
  have h_exists_max : ∃ i ∈ ({a, b} : Finset Idx), (M_set τ D i h_nonempty).Nonempty ∧
      is_maximal_in_M_set τ D i h_nonempty x := by
    apply (sublemma_3_2 τ D x h_door h_nonempty hx_not_mem a b ha_mem hb_mem hab h_eq_mini).mp
    exact h_dom
  obtain ⟨i, hi_mem, hi_nonempty, hi_max⟩ := h_exists_max
  have h_x_eq_mi : x = m_element τ D i h_nonempty hi_nonempty :=
    maximal_element_unique τ D i h_nonempty hi_nonempty x hi_max
  cases Finset.mem_insert.mp hi_mem with
  | inl hi_eq_a =>
    left
    subst hi_eq_a
    exact h_x_eq_mi
  | inr hi_eq_b =>
    right
    have heq : i = b := Finset.mem_singleton.mp hi_eq_b
    subst heq
    exact h_x_eq_mi


omit [Inhabited T] in
theorem internal_door_two_rooms [Fintype T] (τ : Finset T) (D : Finset Idx)
    (h_int_door : IST.isInternalDoor τ D) :
    ∃ (sigma₁ sigma₂ : Finset T) (C₁ C₂ : Finset Idx),
      (sigma₁, C₁) ≠ (sigma₂, C₂) ∧
      IST.isRoom sigma₁ C₁ ∧
      IST.isRoom sigma₂ C₂ ∧
      isDoorof τ D sigma₁ C₁ ∧
      isDoorof τ D sigma₂ C₂ ∧
      (∀ sigma C, IST.isRoom sigma C → isDoorof τ D sigma C →
       (sigma = sigma₁ ∧ C = C₁) ∨ (sigma = sigma₂ ∧ C = C₂)) := by
  obtain ⟨h_door, h_nonempty⟩ := h_int_door
  have h_card : D.card = τ.card + 1 := h_door.2
  have h_image_card : D.card = (D.image (mini h_nonempty)).card + 1 := by
    have h_dominant : IST.isDominant τ D := h_door.1
    have h_image_eq : D.image (mini h_nonempty) = τ := by
      convert (keylemma_of_dominant h_dominant h_nonempty).symm
    rw [h_card, h_image_eq]
  obtain ⟨a, b, ha_mem, hb_mem, h_eq_mini, hab, _⟩ := injOn_sdiff D (mini h_nonempty) h_image_card
  have h_disjoint : M_set τ D a h_nonempty ∩ M_set τ D b h_nonempty = ∅ :=
    M_sets_disjoint τ D a b h_nonempty h_door ha_mem hb_mem hab h_eq_mini
  by_cases h_Ma_nonempty : (M_set τ D a h_nonempty).Nonempty
  · by_cases h_Mb_nonempty : (M_set τ D b h_nonempty).Nonempty
    · let m_a := m_element τ D a h_nonempty h_Ma_nonempty
      let m_b := m_element τ D b h_nonempty h_Mb_nonempty
      have h_ma_max : is_maximal_in_M_set τ D a h_nonempty m_a :=
        m_element_is_maximal τ D a h_nonempty h_Ma_nonempty
      have h_mb_max : is_maximal_in_M_set τ D b h_nonempty m_b :=
        m_element_is_maximal τ D b h_nonempty h_Mb_nonempty
      have h_ma_ne_mb : m_a ≠ m_b := by
        intro h_eq
        have h_ma_in_Ma : m_a ∈ M_set τ D a h_nonempty := h_ma_max.1
        have h_mb_in_Mb : m_b ∈ M_set τ D b h_nonempty := h_mb_max.1
        rw [h_eq] at h_ma_in_Ma
        have h_in_inter : m_b ∈ M_set τ D a h_nonempty ∩ M_set τ D b h_nonempty :=
          ⟨h_ma_in_Ma, h_mb_in_Mb⟩
        rw [h_disjoint] at h_in_inter
        exact Set.notMem_empty m_b h_in_inter
      have h_ma_not_mem : m_a ∉ τ :=
        m_element_not_in_tau τ D a a b h_door h_nonempty ha_mem hb_mem hab h_eq_mini h_Ma_nonempty (Or.inl rfl)
      have h_mb_not_mem : m_b ∉ τ :=
        m_element_not_in_tau τ D b a b h_door h_nonempty ha_mem hb_mem hab h_eq_mini h_Mb_nonempty (Or.inr rfl)
      use insert m_a τ, insert m_b τ, D, D
      constructor
      · intro h_pair_eq
        have h_eq : insert m_a τ = insert m_b τ := congr_arg Prod.fst h_pair_eq
        have : m_a = m_b := by
          have h_ma_in : m_a ∈ insert m_a τ := Finset.mem_insert_self m_a τ
          rw [h_eq] at h_ma_in
          cases Finset.mem_insert.mp h_ma_in with
          | inl h => exact h
          | inr h => exact absurd h h_ma_not_mem
        exact h_ma_ne_mb this
      constructor
      · constructor
        · apply (sublemma_3_2 τ D m_a h_door h_nonempty h_ma_not_mem a b ha_mem hb_mem hab h_eq_mini).mpr
          use a, by simp
        · rw [Finset.card_insert_of_notMem h_ma_not_mem, h_card]
      constructor
      · constructor
        · apply (sublemma_3_2 τ D m_b h_door h_nonempty h_mb_not_mem a b ha_mem hb_mem hab h_eq_mini).mpr
          use b, by simp
        · rw [Finset.card_insert_of_notMem h_mb_not_mem, h_card]
      constructor
      · apply isDoorof.idoor
        · apply (sublemma_3_2 τ D m_a h_door h_nonempty h_ma_not_mem a b ha_mem hb_mem hab h_eq_mini).mpr
          use a, by simp
        · exact h_door
        · exact h_ma_not_mem
        · rfl
        · rfl
      constructor
      · apply isDoorof.idoor
        · apply (sublemma_3_2 τ D m_b h_door h_nonempty h_mb_not_mem a b ha_mem hb_mem hab h_eq_mini).mpr
          use b, by simp
        · exact h_door
        · exact h_mb_not_mem
        · rfl
        · rfl
      · intros sigma C h_room h_door_rel
        cases h_door_rel with
        | idoor h0 _ x hx_not_mem hx_eq hc_eq =>
          subst hx_eq hc_eq
          have h_insert_room : IST.isRoom (insert x τ) D := by
            constructor
            · exact h0
            · rw [Finset.card_insert_of_notMem hx_not_mem, h_card]
          cases idoor_determines_element τ D a b h_door h_nonempty ha_mem hb_mem hab h_eq_mini
              h_Ma_nonempty h_Mb_nonempty x h_insert_room hx_not_mem with
          | inl h_x_eq_ma => left; exact ⟨h_x_eq_ma ▸ rfl, rfl⟩
          | inr h_x_eq_mb => right; exact ⟨h_x_eq_mb ▸ rfl, rfl⟩
        | odoor h0 _ j hj_not_mem hj_eq hc_eq =>
          subst hj_eq
          have h_card_eq : C.card = τ.card := h_room.2
          have h_card_D : D.card = τ.card + 1 := h_door.2
          have h_card_insert : (insert j C).card = C.card + 1 := Finset.card_insert_of_notMem hj_not_mem
          rw [hc_eq] at h_card_D
          rw [h_card_insert] at h_card_D
          rw [h_card_eq] at h_card_D
          have hj_in_ab : j = a ∨ j = b := by
            by_contra h_not_in
            push Not at h_not_in
            obtain ⟨hj_ne_a, hj_ne_b⟩ := h_not_in
            have ha_in_C : a ∈ C := by
              have ha_in_D : a ∈ D := ha_mem
              rw [hc_eq] at ha_in_D
              cases Finset.mem_insert.mp ha_in_D with
              | inl h_eq => exact False.elim (hj_ne_a h_eq.symm)
              | inr h_mem => exact h_mem
            have hb_in_C : b ∈ C := by
              have hb_in_D : b ∈ D := hb_mem
              rw [hc_eq] at hb_in_D
              cases Finset.mem_insert.mp hb_in_D with
              | inl h_eq => exact False.elim (hj_ne_b h_eq.symm)
              | inr h_mem => exact h_mem
            have h_inj_C : Set.InjOn (mini h_nonempty) (C : Set Idx) := by
              apply Finset.injOn_of_card_image_eq
              have h_tau_eq_C_image : τ = C.image (mini h_nonempty) := by
                convert keylemma_of_dominant h0 h_nonempty
              rw [←h_tau_eq_C_image]
              exact h_card_eq.symm
            have h_a_ne_b : a ≠ b := hab
            have h_mini_eq : mini h_nonempty a = mini h_nonempty b := h_eq_mini
            exact h_a_ne_b (h_inj_C ha_in_C hb_in_C h_mini_eq)
          cases hj_in_ab with
          | inl hj_eq_a =>
            have h_dom_C : IST.isDominant τ C := h0
            rw [show C = D.erase j by rw [hc_eq]; exact (Finset.erase_insert hj_not_mem).symm] at h_dom_C
            have hj_eq_a_mem : j ∈ D := by rw [hj_eq_a]; exact ha_mem
            have h_contra := (sublemma_3_1 τ D h_door h_nonempty j hj_eq_a_mem).mp h_dom_C
            obtain ⟨a', b', ha'_mem, hb'_mem, ha'b'_ne, h_eq_mini', h_j_in_pair, h_M_empty⟩ := h_contra
            have h_Mj_nonempty : (M_set τ D j h_nonempty).Nonempty := by
              rw [hj_eq_a]; exact h_Ma_nonempty
            rw [h_M_empty] at h_Mj_nonempty
            exact False.elim (Set.not_nonempty_empty h_Mj_nonempty)
          | inr hj_eq_b =>
            have h_dom_C : IST.isDominant τ C := h0
            rw [show C = D.erase j by rw [hc_eq]; exact (Finset.erase_insert hj_not_mem).symm] at h_dom_C
            have hj_eq_b_mem : j ∈ D := by rw [hj_eq_b]; exact hb_mem
            have h_contra := (sublemma_3_1 τ D h_door h_nonempty j hj_eq_b_mem).mp h_dom_C
            obtain ⟨a', b', ha'_mem, hb'_mem, ha'b'_ne, h_eq_mini', h_j_in_pair, h_M_empty⟩ := h_contra
            have h_Mj_nonempty : (M_set τ D j h_nonempty).Nonempty := by
              rw [hj_eq_b]; exact h_Mb_nonempty
            rw [h_M_empty] at h_Mj_nonempty
            exact False.elim (Set.not_nonempty_empty h_Mj_nonempty)
    · let m_a := m_element τ D a h_nonempty h_Ma_nonempty
      have h_ma_max : is_maximal_in_M_set τ D a h_nonempty m_a :=
        m_element_is_maximal τ D a h_nonempty h_Ma_nonempty
      have h_ma_not_mem : m_a ∉ τ :=
        m_element_not_in_tau τ D a a b h_door h_nonempty ha_mem hb_mem hab h_eq_mini h_Ma_nonempty (Or.inl rfl)
      have h_Mb_empty : M_set τ D b h_nonempty = ∅ := Set.not_nonempty_iff_eq_empty.mp h_Mb_nonempty
      use insert m_a τ, τ, D, D.erase b
      constructor
      · intro h_pair_eq
        have h_eq : insert m_a τ = τ := congr_arg Prod.fst h_pair_eq
        have h_ma_in : m_a ∈ insert m_a τ := Finset.mem_insert_self m_a τ
        rw [h_eq] at h_ma_in
        exact h_ma_not_mem h_ma_in
      constructor
      · constructor
        · apply (sublemma_3_2 τ D m_a h_door h_nonempty h_ma_not_mem a b ha_mem hb_mem hab h_eq_mini).mpr
          use a, by simp
        · rw [Finset.card_insert_of_notMem h_ma_not_mem, h_card]
      constructor
      · constructor
        · apply (sublemma_3_1 τ D h_door h_nonempty b hb_mem).mpr
          use a, b, ha_mem, hb_mem, hab, h_eq_mini, (Or.inr rfl), h_Mb_empty
        · rw [Finset.card_erase_of_mem hb_mem, h_card]
          simp
      constructor
      · apply isDoorof.idoor
        · apply (sublemma_3_2 τ D m_a h_door h_nonempty h_ma_not_mem a b ha_mem hb_mem hab h_eq_mini).mpr
          use a, by simp
        · exact h_door
        · exact h_ma_not_mem
        · rfl
        · rfl
      constructor
      · apply isDoorof.odoor
        · apply (sublemma_3_1 τ D h_door h_nonempty b hb_mem).mpr
          use a, b, ha_mem, hb_mem, hab, h_eq_mini, (Or.inr rfl), h_Mb_empty
        · exact h_door
        · exact Finset.notMem_erase b D
        · rfl
        · exact (Finset.insert_erase hb_mem).symm
      · intros sigma C h_room h_door_rel
        cases h_door_rel with
        | idoor h0 _ x hx_not_mem hx_eq hc_eq =>
          subst hx_eq hc_eq
          have h_dom : IST.isDominant (insert x τ) D := h0
          have h_exists_max : ∃ i ∈ ({a, b} : Finset Idx), (M_set τ D i h_nonempty).Nonempty ∧ is_maximal_in_M_set τ D i h_nonempty x := by
            apply (sublemma_3_2 τ D x h_door h_nonempty hx_not_mem a b ha_mem hb_mem hab h_eq_mini).mp h_dom
          obtain ⟨i, hi_mem, hi_nonempty, hi_max⟩ := h_exists_max
          cases Finset.mem_insert.mp hi_mem with
          | inl hi_eq_a =>
            subst hi_eq_a
            have h_x_eq_ma : x = m_a := maximal_element_unique τ D i h_nonempty hi_nonempty x hi_max
            left; exact ⟨h_x_eq_ma ▸ rfl, rfl⟩
          | inr hi_eq_b =>
            have : i = b := Finset.mem_singleton.mp hi_eq_b; subst this
            rw [h_Mb_empty] at hi_nonempty
            exact False.elim (Set.not_nonempty_empty hi_nonempty)
         | odoor h0 _ j hj_not_mem hj_eq hc_eq =>
           subst hj_eq
           have h_card_eq : C.card = τ.card := h_room.2
           have h_card_D : D.card = τ.card + 1 := h_door.2
           have h_card_insert : (insert j C).card = C.card + 1 := Finset.card_insert_of_notMem hj_not_mem
           rw [hc_eq, h_card_insert, h_card_eq] at h_card_D
           have hj_in_ab : j ∈ ({a, b} : Finset Idx) :=
             odoor_index_in_pair τ D C a b j h_door h_nonempty ha_mem hb_mem hab h_eq_mini h0 h_card_eq hj_not_mem hc_eq
           cases Finset.mem_insert.mp hj_in_ab with
           | inl hj_eq_a =>
             subst hj_eq_a
             exfalso
             have h_dom_C : IST.isDominant τ C := h_room.1
             rw [show C = D.erase j by rw [hc_eq]; exact (Finset.erase_insert hj_not_mem).symm] at h_dom_C
             have h_contra := (sublemma_3_1 τ D h_door h_nonempty j ha_mem).mp h_dom_C
             obtain ⟨_, _, _, _, _, _, _, h_M_empty⟩ := h_contra
             exact (Set.not_nonempty_iff_eq_empty.mpr h_M_empty) h_Ma_nonempty
           | inr hj_eq_b =>
             have hj_eq_b : j = b := Finset.mem_singleton.mp hj_eq_b
             subst hj_eq_b
             right
             exact ⟨rfl, (hc_eq ▸ (Finset.erase_insert hj_not_mem).symm)⟩
  · have h_Ma_empty : M_set τ D a h_nonempty = ∅ := Set.not_nonempty_iff_eq_empty.mp h_Ma_nonempty
    by_cases h_Mb_nonempty : (M_set τ D b h_nonempty).Nonempty
    · let m_b := m_element τ D b h_nonempty h_Mb_nonempty
      have h_mb_max : is_maximal_in_M_set τ D b h_nonempty m_b :=
        m_element_is_maximal τ D b h_nonempty h_Mb_nonempty
      have h_mb_not_mem : m_b ∉ τ :=
        m_element_not_in_tau τ D b a b h_door h_nonempty ha_mem hb_mem hab h_eq_mini h_Mb_nonempty (Or.inr rfl)
      use insert m_b τ, τ, D, D.erase a
      constructor
      · intro h_pair_eq
        have h_eq : insert m_b τ = τ := congr_arg Prod.fst h_pair_eq
        have h_mb_in : m_b ∈ insert m_b τ := Finset.mem_insert_self m_b τ
        rw [h_eq] at h_mb_in
        exact h_mb_not_mem h_mb_in
      constructor
      · constructor
        · apply (sublemma_3_2 τ D m_b h_door h_nonempty h_mb_not_mem a b ha_mem hb_mem hab h_eq_mini).mpr
          use b, by simp
        · rw [Finset.card_insert_of_notMem h_mb_not_mem, h_card]
      constructor
      · constructor
        · apply (sublemma_3_1 τ D h_door h_nonempty a ha_mem).mpr
          use a, b, ha_mem, hb_mem, hab, h_eq_mini, (Or.inl rfl), h_Ma_empty
        · rw [Finset.card_erase_of_mem ha_mem, h_card]
          simp
      constructor
      · apply isDoorof.idoor
        · apply (sublemma_3_2 τ D m_b h_door h_nonempty h_mb_not_mem a b ha_mem hb_mem hab h_eq_mini).mpr
          use b, by simp
        · exact h_door
        · exact h_mb_not_mem
        · rfl
        · rfl
      constructor
      · apply isDoorof.odoor
        · apply (sublemma_3_1 τ D h_door h_nonempty a ha_mem).mpr
          use a, b, ha_mem, hb_mem, hab, h_eq_mini, (Or.inl rfl), h_Ma_empty
        · exact h_door
        · exact Finset.notMem_erase a D
        · rfl
        · exact (Finset.insert_erase ha_mem).symm
      · intros sigma C h_room h_door_rel
        cases h_door_rel with
        | idoor h0 _ x hx_not_mem hx_eq hc_eq =>
          subst hx_eq hc_eq
          have h_dom : IST.isDominant (insert x τ) D := h0
          have h_exists_max : ∃ i ∈ ({a, b} : Finset Idx), (M_set τ D i h_nonempty).Nonempty ∧ is_maximal_in_M_set τ D i h_nonempty x := by
            apply (sublemma_3_2 τ D x h_door h_nonempty hx_not_mem a b ha_mem hb_mem hab h_eq_mini).mp h_dom
          obtain ⟨i, hi_mem, hi_nonempty, hi_max⟩ := h_exists_max
          cases Finset.mem_insert.mp hi_mem with
          | inl hi_eq_a =>
            subst hi_eq_a
            rw [h_Ma_empty] at hi_nonempty
            exact False.elim (Set.not_nonempty_empty hi_nonempty)
          | inr hi_eq_b =>
            have : i = b := Finset.mem_singleton.mp hi_eq_b; subst this
            have h_x_eq_mb : x = m_b := maximal_element_unique τ D i h_nonempty hi_nonempty x hi_max
            left; exact ⟨h_x_eq_mb ▸ rfl, rfl⟩
         | odoor h0 _ j hj_not_mem hj_eq hc_eq =>
           subst hj_eq
           have h_card_eq : C.card = τ.card := h_room.2
           have h_card_D : D.card = τ.card + 1 := h_door.2
           have h_card_insert : (insert j C).card = C.card + 1 := Finset.card_insert_of_notMem hj_not_mem
           rw [hc_eq] at h_card_D
           rw [h_card_insert] at h_card_D
           rw [h_card_eq] at h_card_D
           have hj_in_ab : j ∈ ({a, b} : Finset Idx) :=
             odoor_index_in_pair τ D C a b j h_door h_nonempty ha_mem hb_mem hab h_eq_mini h0 h_card_eq hj_not_mem hc_eq

           cases Finset.mem_insert.mp hj_in_ab with
           | inl hj_eq_a =>
             have hj_eq_a : j = a := hj_eq_a
             subst hj_eq_a
             right
             exact ⟨rfl, (hc_eq ▸ (Finset.erase_insert hj_not_mem).symm)⟩
           | inr hj_eq_b =>
             exfalso
             have h_dom_C : IST.isDominant τ C := h_room.1
             rw [show C = D.erase j by rw[hc_eq]; exact (Finset.erase_insert hj_not_mem).symm] at h_dom_C
             have hj_eq_b : j = b := Finset.mem_singleton.mp hj_eq_b
             subst hj_eq_b
             have h_contra := (sublemma_3_1 τ D h_door h_nonempty j hb_mem).mp h_dom_C
             obtain ⟨_, _, _, _, _, _, _, h_M_empty⟩ := h_contra
             exact (Set.not_nonempty_iff_eq_empty.mpr h_M_empty) h_Mb_nonempty
    · have h_Mb_empty : M_set τ D b h_nonempty = ∅ := Set.not_nonempty_iff_eq_empty.mp h_Mb_nonempty
      use τ, τ, D.erase b, D.erase a
      constructor
      · intro h_pair_eq
        have h_erasure_eq : D.erase b = D.erase a := congr_arg Prod.snd h_pair_eq
        have h_a_in_erase_b : a ∈ D.erase b := Finset.mem_erase.mpr ⟨hab, ha_mem⟩
        rw [h_erasure_eq] at h_a_in_erase_b
        exact (Finset.notMem_erase a D) h_a_in_erase_b
      constructor
      · constructor
        · apply (sublemma_3_1 τ D h_door h_nonempty b hb_mem).mpr
          use a, b, ha_mem, hb_mem, hab, h_eq_mini, (Or.inr rfl), h_Mb_empty
        · rw [Finset.card_erase_of_mem hb_mem, h_door.2]
          simp
      constructor
      · constructor
        · apply (sublemma_3_1 τ D h_door h_nonempty a ha_mem).mpr
          use a, b, ha_mem, hb_mem, hab, h_eq_mini, (Or.inl rfl), h_Ma_empty
        · rw [Finset.card_erase_of_mem ha_mem, h_door.2]
          simp
      constructor
      · apply isDoorof.odoor
        · apply (sublemma_3_1 τ D h_door h_nonempty b hb_mem).mpr
          use a, b, ha_mem, hb_mem, hab, h_eq_mini, (Or.inr rfl), h_Mb_empty
        · exact h_door
        · exact Finset.notMem_erase b D
        · rfl
        · exact (Finset.insert_erase hb_mem).symm
      constructor
      · apply isDoorof.odoor
        · apply (sublemma_3_1 τ D h_door h_nonempty a ha_mem).mpr
          use a, b, ha_mem, hb_mem, hab, h_eq_mini, (Or.inl rfl), h_Ma_empty
        · exact h_door
        · exact Finset.notMem_erase a D
        · rfl
        · exact (Finset.insert_erase ha_mem).symm
      · intros sigma C h_room h_door_rel
        cases h_door_rel with
        | idoor h0 _ x hx_not_mem hx_eq hc_eq =>
          subst hx_eq hc_eq
          have h_dom : IST.isDominant (insert x τ) D := h0
          have h_exists_max : ∃ i ∈ ({a, b} : Finset Idx), (M_set τ D i h_nonempty).Nonempty ∧ is_maximal_in_M_set τ D i h_nonempty x := by
            apply (sublemma_3_2 τ D x h_door h_nonempty hx_not_mem a b ha_mem hb_mem hab h_eq_mini).mp h_dom
          obtain ⟨i, hi_mem, hi_nonempty, _⟩ := h_exists_max
          cases Finset.mem_insert.mp hi_mem with
          | inl hi_eq_a =>
            subst hi_eq_a; rw [h_Ma_empty] at hi_nonempty
            exact absurd hi_nonempty Set.not_nonempty_empty
          | inr hi_eq_b =>
            have : i = b := Finset.mem_singleton.mp hi_eq_b; subst this
            rw [h_Mb_empty] at hi_nonempty
            exact absurd hi_nonempty Set.not_nonempty_empty
        | odoor h0 _ j hj_not_mem hj_eq hc_eq =>
          subst hj_eq
          have h_dom_C : IST.isDominant τ C := h0
          have h_card_eq : C.card = τ.card := h_room.2
          have h_card_D : D.card = τ.card + 1 := h_door.2
          have h_card_insert : (insert j C).card = C.card + 1 := Finset.card_insert_of_notMem hj_not_mem
          rw [hc_eq] at h_card_D
          rw [h_card_insert] at h_card_D
          rw [h_card_eq] at h_card_D
          have hj_in_ab : j ∈ ({a, b} : Finset Idx) :=
            odoor_index_in_pair τ D C a b j h_door h_nonempty ha_mem hb_mem hab h_eq_mini h_dom_C h_card_eq hj_not_mem hc_eq
          cases Finset.mem_insert.mp hj_in_ab with
          | inl hj_eq_a =>
            have hj_eq_a : j = a := hj_eq_a
            subst hj_eq_a
            have h_C_eq_erase : C = D.erase j := by
              rw [hc_eq]
              exact (Finset.erase_insert hj_not_mem).symm
            right
            exact ⟨rfl, h_C_eq_erase⟩
          | inr hj_eq_b =>
            have hj_eq_b : j = b := Finset.mem_singleton.mp hj_eq_b
            subst hj_eq_b
            have h_C_eq_erase : C = D.erase j := by
              rw [hc_eq]
              exact (Finset.erase_insert hj_not_mem).symm
            left
            exact ⟨rfl, h_C_eq_erase⟩

end KeyLemma


noncomputable section Scarf

open Classical




variable (c : T → Idx) (sigma : Finset T) (C : Finset Idx)

def isColorful : Prop := IST.isCell sigma C ∧ sigma.image c   = C

def isNearlyColorful : Prop := IST.isCell sigma C ∧ (C \ sigma.image c).card = 1

def isTypedNC (i : Idx) (sigma : Finset T) (C : Finset Idx): Prop := IST.isCell sigma C ∧ (C \ (sigma.image c)) = {i}


variable {c sigma C}


omit [Inhabited T] [DecidableEq T] in
lemma not_colorful_of_TypedNC (h1 : isTypedNC c i sigma C) : ¬ IST.isColorful c sigma C := by
  intro h
  unfold isTypedNC at h1
  unfold isColorful at h
  have h_diff := h1.2
  have h_ne : sigma.image c ≠ C := by
    intro h_eq
    rw [←h_eq, Finset.sdiff_self] at h_diff
    have h_singleton_nonempty : ({i} : Finset Idx).Nonempty := Finset.singleton_nonempty i
    rw [←h_diff] at h_singleton_nonempty
    exact Finset.not_nonempty_empty h_singleton_nonempty
  exact h_ne h.2

omit [Inhabited T] [DecidableEq T] in
lemma NC_of_TNC (h1 : isTypedNC c i sigma C) : isNearlyColorful c sigma C := by
  have hcell := h1.1
  have heq := h1.2
  constructor
  · exact hcell
  · rw [heq]
    have h_eq : C \ image c sigma = {i} := by
      rw [heq]
    rw [←heq, h_eq]
    exact Finset.card_singleton i
lemma Finset.eq_of_mem_of_card_one {α : Type*} [DecidableEq α] {s : Finset α} {a : α} (h_mem : a ∈ s) (h_card : s.card = 1) : s = {a} :=
  Finset.eq_singleton_iff_unique_mem.mpr ⟨h_mem, fun y hy =>
    let ⟨b, hb⟩ := Finset.card_eq_one.mp h_card
    have h_a_eq_b : a = b := Finset.eq_of_mem_singleton (hb ▸ h_mem)
    have h_y_eq_b : y = b := Finset.eq_of_mem_singleton (hb ▸ hy)
    h_y_eq_b.trans h_a_eq_b.symm⟩

omit [Inhabited T] [DecidableEq T] in
lemma room_of_colorful (h : IST.isColorful c sigma C) : IST.isRoom sigma C := by
  unfold isRoom
  unfold isColorful at h
  constructor
  · exact h.1
  · have h1 : C.card = (sigma.image c).card := by rw [h.2]
    have h2 : (sigma.image c).card ≤ sigma.card := Finset.card_image_le
    have h3 : sigma.card ≤ C.card := card_le_of_domiant h.1
    linarith



def pick_colorful_point (h : IST.isColorful c sigma C): sigma := Classical.choice (sigma_nonempty_of_room (room_of_colorful h)).to_subtype




omit [Inhabited T] [DecidableEq T] in
lemma NC_of_outsidedoor (h : isOutsideDoor sigma C) : isNearlyColorful c sigma C  := by
  cases h with
  | intro hd he =>
    unfold isNearlyColorful
    unfold isCell
    constructor
    · exact hd.1
    · rw [he]
      have h_img : Finset.image c Finset.empty = Finset.empty := Finset.image_empty c
      rw [h_img]
      have h_disj : Disjoint C Finset.empty := Finset.disjoint_empty_right C
      have h_sdiff : C \ Finset.empty = C := Finset.sdiff_eq_self_of_disjoint h_disj
      rw [h_sdiff]
      unfold isDoor at hd
      have h1 := hd.2
      rw [he] at h1
      exact h1


omit [Inhabited T] in
lemma NC_or_C_of_door (h1 : isTypedNC c i τ D) (h2 : isDoorof τ D sigma C) : isTypedNC c i sigma C ∨ isColorful c sigma C := by
  unfold isTypedNC at h1 ⊢
  unfold isColorful
  have h1_cell := h1.left
  have h1_eq := h1.right

  have h_sigma_cell : isCell sigma C := by
    cases h2 with
    | idoor h0 _ _ _ _ _ => exact h0
    | odoor h0 _ _ _ _ _ => exact h0

  have step1_subset : C \ (sigma.image c) ⊆ D \ (τ.image c) := by
    intro y hy
    simp only [Finset.mem_sdiff] at hy ⊢
    obtain ⟨y_in_C, y_notin_img_sigma⟩ := hy
    constructor
    · cases h2
      · rename_i h_D_eq; rw [h_D_eq]; exact y_in_C
      · rename_i h_D_eq; rw [h_D_eq]; exact Finset.mem_insert_of_mem y_in_C
    · cases h2 with
      | idoor h0 hdoor x h_x_notin h_sigma_eq h_D_eq =>
        rw [← h_sigma_eq, Finset.image_insert] at y_notin_img_sigma
        simp only [Finset.mem_insert, not_or] at y_notin_img_sigma
        exact y_notin_img_sigma.2
      | odoor h0 hdoor j h_j_notin h_sigma_eq h_D_eq =>
        rw [← h_sigma_eq] at y_notin_img_sigma
        exact y_notin_img_sigma

  have step2_D_card : (D \ (τ.image c)).card = 1 := by
    have D_sdiff_eq_i : D \ (τ.image c) = {i} := by
      rw [h1_eq]
    rw [D_sdiff_eq_i, Finset.card_singleton]

  have step3_C_card_le : (C \ sigma.image c).card ≤ 1 := by
    rw [← step2_D_card]
    exact Finset.card_le_card step1_subset

  by_cases h : (C \ sigma.image c).card = 0
  · right
    constructor
    · exact h_sigma_cell
    · have h_C_subset_img : C ⊆ sigma.image c := by
        rw [Finset.subset_iff]
        intro x hx
        by_contra hxn
        have : x ∈ C \ sigma.image c := by simp [hx, hxn]
        have : (C \ sigma.image c).Nonempty := ⟨x, this⟩
        have : 0 < (C \ sigma.image c).card := Finset.card_pos.2 this
        linarith [h]

      have h_room: isRoom sigma C := isRoom_of_Door h2
      have h_card_eq : C.card = sigma.card := h_room.2
      have h_img_le_C_card : (sigma.image c).card ≤ C.card := by
        calc (sigma.image c).card
          ≤ sigma.card := Finset.card_image_le
          _ = C.card := h_card_eq.symm
      exact (Finset.eq_of_subset_of_card_le h_C_subset_img h_img_le_C_card).symm

  · left
    constructor
    · exact h_sigma_cell
    · have h_card_one : (C \ sigma.image c).card = 1 := by omega

      have h_subset_singleton : C \ sigma.image c ⊆ {i} := by
        have D_sdiff_eq_i : D \ (τ.image c) = {i} := by
          rw [h1_eq]
        rw [← D_sdiff_eq_i]
        exact step1_subset

      have C_sdiff_eq_i : C \ sigma.image c = {i} :=
        Finset.eq_of_subset_of_card_le h_subset_singleton (by rw [h_card_one, Finset.card_singleton])

      have h_i_notin_img : i ∉ sigma.image c := by
        have h_i_in_sdiff : i ∈ C \ sigma.image c := by rw [C_sdiff_eq_i]; simp
        exact (Finset.mem_sdiff.mp h_i_in_sdiff).2

      exact C_sdiff_eq_i

omit [Inhabited T] in
lemma NCtype_of_door (h1 : isTypedNC c i τ D) (_ : isDoorof τ D sigma C) (_ : isTypedNC c i sigma C) : isTypedNC c i τ D := h1

omit [Inhabited T] in
lemma isTypedNC_of_isNearlyColorful_of_isDoorof_isTypedNC (h_nc : isNearlyColorful c τ D) (h_door : isDoorof τ D sigma C) (h_room_typed : isTypedNC c i sigma C) : isTypedNC c i τ D := by
  constructor
  · exact h_nc.1
  · have h_subset : C \ image c sigma ⊆ D \ image c τ := by
      intro y hy
      simp only [Finset.mem_sdiff] at hy ⊢
      obtain ⟨y_in_C, y_notin_img_sigma⟩ := hy
      constructor
      · cases h_door with
        | idoor h0 _ _ _ _ h_D_eq => rw [h_D_eq]; exact y_in_C
        | odoor h0 _ _ _ _ h_D_eq => rw [h_D_eq]; exact Finset.mem_insert_of_mem y_in_C
      · cases h_door with
        | idoor h0 _ x _ h_sigma_eq _ =>
          rw [← h_sigma_eq, Finset.image_insert] at y_notin_img_sigma
          simp only [Finset.mem_insert, not_or] at y_notin_img_sigma
          exact y_notin_img_sigma.2
        | odoor h0 _ _ _ h_sigma_eq _ =>
          rw [← h_sigma_eq] at y_notin_img_sigma
          exact y_notin_img_sigma
    have h_i_in_diff : i ∈ D \ image c τ := h_subset (h_room_typed.2 ▸ Finset.mem_singleton_self i)
    have h_card_one : (D \ image c τ).card = 1 := h_nc.2
    exact Finset.eq_of_mem_of_card_one h_i_in_diff h_card_one


omit [Inhabited T] [DecidableEq T] in
lemma card_of_NCcell (h : isNearlyColorful c sigma D) : #sigma = #(image c sigma)  ∨  #sigma = #(image c sigma) + 1 := by
  unfold isNearlyColorful at h
  rcases h with ⟨h_cell, h_nc_card⟩
  let img := image c sigma
  have h_card_le_D : sigma.card ≤ D.card := card_le_of_domiant h_cell
  have h_D_card_eq := (Finset.card_sdiff_add_card_inter D img).symm
  rw [h_nc_card] at h_D_card_eq
  have h_inter_le_img : (D ∩ img).card ≤ img.card := card_le_card (Finset.inter_subset_right)
  have h_D_le : D.card ≤ 1 + img.card := by
    linarith [h_D_card_eq, h_inter_le_img]
  have h_img_le_sigma : img.card ≤ sigma.card := card_image_le
  have h_sigma_le_plus_one : sigma.card ≤ img.card + 1 := by
    linarith [h_card_le_D, h_D_le]
  have h_or : sigma.card ≤ img.card ∨ sigma.card = img.card + 1 := by
    apply Nat.le_or_eq_of_le_succ
    exact h_sigma_le_plus_one
  cases h_or with
  | inl h_le =>
    left
    exact le_antisymm h_le h_img_le_sigma
  | inr h_eq =>
    right
    exact h_eq

omit [Inhabited T] [DecidableEq T] in
lemma image_subset_of_NCdoor (h1 : isNearlyColorful c sigma C) (h2 : isDoor sigma C) : image c sigma ⊆ C := by
  unfold isNearlyColorful at h1
  unfold isDoor at h2
  rcases h1 with ⟨h_cell, h_nc_card⟩
  rcases h2 with ⟨_, h_door_card⟩
  let img := image c sigma
  have h_img_le_sigma : img.card ≤ sigma.card := card_image_le
  have h_sigma_le_C : sigma.card ≤ C.card := card_le_of_domiant h_cell
  have h_inter_card : (C ∩ img).card = sigma.card := by
    have h_C_card_eq := (Finset.card_sdiff_add_card_inter C img).symm
    rw [h_nc_card] at h_C_card_eq
    have h_C_eq : C.card = 1 + (C ∩ img).card := by linarith [h_C_card_eq]
    rw [h_door_card] at h_C_eq
    linarith [h_C_eq]
  have h_img_eq_inter : img.card = (C ∩ img).card := by
    have h_le1 : (C ∩ img).card ≤ img.card := card_le_card (Finset.inter_subset_right)
    have h_le2 : img.card ≤ (C ∩ img).card := by
      calc img.card
        ≤ sigma.card := h_img_le_sigma
        _ = (C ∩ img).card := h_inter_card.symm
    exact le_antisymm h_le2 h_le1
  have h_inter_eq_img : C ∩ img = img :=
    Finset.eq_of_subset_of_card_le (Finset.inter_subset_right) (by rw [h_img_eq_inter])
  rwa [Finset.inter_eq_right] at h_inter_eq_img

section ImageErase

variable {T Idx : Type*} [DecidableEq T] [DecidableEq Idx]

lemma image_erase_eq_erase_image_of_unique
  (sigma : Finset T) (c : T → Idx) {z : T}
  (_ : z ∈ sigma)
  (uniq : ∀ ⦃w⦄, w ∈ sigma → c w = c z → w = z) :
  (sigma.erase z).image c = (sigma.image c).erase (c z) := by
  ext i
  constructor
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨w, hw_in_erase, rfl⟩
    rcases Finset.mem_erase.mp hw_in_erase with ⟨hw_ne_z, hw_in_sigma⟩
    have h_ne_color : c w ≠ c z := by
      intro h_eq
      have := uniq hw_in_sigma h_eq
      exact hw_ne_z this
    exact Finset.mem_erase.mpr ⟨h_ne_color, Finset.mem_image.mpr ⟨w, hw_in_sigma, rfl⟩⟩
  · intro hi
    rcases Finset.mem_erase.mp hi with ⟨h_i_ne, hi_img⟩
    rcases Finset.mem_image.mp hi_img with ⟨w, hw_in_sigma, rfl⟩
    have hw_ne_z : w ≠ z := by
      intro h_eq
      apply h_i_ne
      simp [h_eq]
    exact Finset.mem_image.mpr ⟨w, Finset.mem_erase.mpr ⟨hw_ne_z, hw_in_sigma⟩, rfl⟩

end ImageErase
variable (c sigma C) in
abbrev NCdoors := {(τ,D) | isNearlyColorful c τ D ∧ isDoorof τ D sigma C }


omit [DecidableEq T] [Inhabited T] IST in
lemma three_collision_card_bound [DecidableEq T] (sigma : Finset T) (c : T → Idx)
    (a b z : T) (ha_in_sigma : a ∈ sigma) (hb_in_sigma : b ∈ sigma) (hz_in_sigma : z ∈ sigma)
    (hab_ne : a ≠ b) (haz_ne : a ≠ z) (hbz_ne : b ≠ z)
    (hc_eq : c a = c b) (hcz_eq : c b = c z) :
    sigma.card ≥ (sigma.image c).card + 2 := by
  let sigma_rest := sigma \ {a, b, z}
  have h_three_subset_sigma : {a, b, z} ⊆ sigma := by
    intro w hw; simp at hw; rcases hw with (rfl | rfl | rfl);
    · exact ha_in_sigma
    · exact hb_in_sigma
    · exact hz_in_sigma

  have h_partition : sigma = {a, b, z} ∪ sigma_rest :=
    (Finset.union_sdiff_of_subset h_three_subset_sigma).symm

  have h_disjoint : Disjoint ({a, b, z} : Finset T) sigma_rest :=
    Finset.disjoint_sdiff

  have h_card_partition : sigma.card = ({a, b, z} : Finset T).card + sigma_rest.card := by
    rw [h_partition, Finset.card_union_of_disjoint h_disjoint]

  have h_triple_card : ({a, b, z} : Finset T).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨a, b, z, hab_ne, haz_ne, hbz_ne, rfl⟩

  have h_image_bound : (sigma.image c).card ≤ sigma_rest.card + 1 := by
    have h_image_union : sigma.image c = insert (c a) (sigma_rest.image c) := by
      ext i; simp only [Finset.mem_image, Finset.mem_insert]
      constructor
      · rintro ⟨t, ht_in_sigma, rfl⟩
        by_cases h_t_abz : t ∈ ({a, b, z} : Finset T)
        · simp at h_t_abz; rcases h_t_abz with (rfl | rfl | rfl)
          · left; rfl
          · left; exact hc_eq.symm
          · left; exact (hc_eq.trans hcz_eq).symm
        · right; use t; simp [sigma_rest, ht_in_sigma, h_t_abz]
      · rintro (rfl | ⟨t, ht_in_rest, rfl⟩)
        · use a
        · use t; exact ⟨(Finset.mem_sdiff.mp ht_in_rest).1, rfl⟩
    rw [h_image_union]
    linarith [Finset.card_insert_le (c a) (sigma_rest.image c), Finset.card_image_le (f := c) (s := sigma_rest)]

  calc sigma.card
      = 3 + sigma_rest.card           := by rw [h_card_partition, h_triple_card]
    _ = sigma_rest.card + 3           := by ring
    _ = (sigma_rest.card + 1) + 2     := by ring
    _ ≥ (sigma.image c).card + 2      := by linarith [h_image_bound]


omit [DecidableEq T] [Inhabited T] IST in
lemma image_erase_collision_preserves [DecidableEq T] (sigma : Finset T) (c : T → Idx)
    (x y : T) (hx_in_sigma : x ∈ sigma) (hy_in_sigma : y ∈ sigma) (hxy_ne : x ≠ y) (hcxy_eq : c x = c y) :
    (sigma.erase x).image c = sigma.image c ∧ (sigma.erase y).image c = sigma.image c := by
  constructor
  · ext z
    simp only [Finset.mem_image]
    constructor
    · intro ⟨w, hw_in_erased, hw_eq⟩
      have hw_in_sigma : w ∈ sigma := by
        rw [Finset.mem_erase] at hw_in_erased
        exact hw_in_erased.2
      exact ⟨w, hw_in_sigma, hw_eq⟩
    · intro ⟨w, hw_in_sigma, hw_eq⟩
      by_cases h : w = x
      · subst h
        use y
        constructor
        · rw [Finset.mem_erase]
          exact ⟨hxy_ne.symm, hy_in_sigma⟩
        · rw [←hcxy_eq, hw_eq]
      · use w
        exact ⟨Finset.mem_erase.mpr ⟨h, hw_in_sigma⟩, hw_eq⟩
  · ext z
    simp only [Finset.mem_image]
    constructor
    · intro ⟨w, hw_in_erased, hw_eq⟩
      have hw_in_sigma : w ∈ sigma := by
        rw [Finset.mem_erase] at hw_in_erased
        exact hw_in_erased.2
      exact ⟨w, hw_in_sigma, hw_eq⟩
    · intro ⟨w, hw_in_sigma, hw_eq⟩
      by_cases h : w = y
      · subst h
        use x
        constructor
        · rw [Finset.mem_erase]
          exact ⟨hxy_ne, hx_in_sigma⟩
        · rw [hcxy_eq, hw_eq]
      · use w
        exact ⟨Finset.mem_erase.mpr ⟨h, hw_in_sigma⟩, hw_eq⟩


omit [DecidableEq T] [Inhabited T] in
lemma collision_door_valid [DecidableEq T] (sigma : Finset T) (C : Finset Idx) (_ : T → Idx)
    (x : T) (h_cell : isCell sigma C) (hx_in_sigma : x ∈ sigma) (h_card_eq : C.card = sigma.card) :
    isDoorof (sigma.erase x) C sigma C := by
  apply isDoorof.idoor h_cell
  · constructor
    · exact Dominant_of_subset sigma (sigma.erase x) C (Finset.erase_subset x sigma) h_cell
    · rw [h_card_eq]
      rw [Finset.card_erase_of_mem hx_in_sigma]
      exact (Nat.sub_add_cancel (Finset.card_pos.mpr ⟨x, hx_in_sigma⟩)).symm
  · exact Finset.notMem_erase x sigma
  · exact Finset.insert_erase hx_in_sigma
  · rfl


omit [DecidableEq T] [Inhabited T] in
lemma doors_of_NCroom [DecidableEq T] (h_room : isRoom sigma C) (h_nc : isNearlyColorful c sigma C) :
  ∃ door1 door2, door1 ≠ door2 ∧ NCdoors c sigma C = {door1, door2} := by
  have h_cases := card_of_NCcell h_nc
  have h_card_eq : C.card = sigma.card := h_room.2
  have h_cell : isCell sigma C := h_room.1
  let img := image c sigma

  cases h_cases with
  | inl h_eq =>
    have h_inj_on_sigma : Set.InjOn c ↑sigma := (Finset.card_image_iff).mp h_eq.symm
    have h_img_C_card_1 : (img \ C).card = 1 := by
      have h_card_eq' : C.card = img.card := by linarith [h_card_eq, h_eq]
      have h_C_sdiff := Finset.card_sdiff_add_card_inter C img
      rw [h_nc.2, h_card_eq'] at h_C_sdiff
      have h_img_sdiff := Finset.card_sdiff_add_card_inter img C
      rw [Finset.inter_comm] at h_C_sdiff
      linarith [h_C_sdiff, h_img_sdiff]
    obtain ⟨c_y, h_img_C_eq⟩ := Finset.card_eq_one.mp h_img_C_card_1
    have h_c_y_in_img : c_y ∈ img := by
      have : c_y ∈ img \ C := by rw [h_img_C_eq]; simp
      exact (Finset.mem_sdiff.mp this).1
    have h_c_y_notin_C : c_y ∉ C := by
      have : c_y ∈ img \ C := by rw [h_img_C_eq]; simp
      exact (Finset.mem_sdiff.mp this).2
    obtain ⟨y, h_y_in_sigma, h_c_y_eq⟩ := Finset.mem_image.mp h_c_y_in_img
    subst h_c_y_eq
    have h_y_unique : ∀ ⦃z⦄, z ∈ sigma → c z = c y → z = y :=
      λ z hz hcz => h_inj_on_sigma hz h_y_in_sigma hcz
    let door1 := (sigma.erase y, C)
    let door2 := (sigma, insert (c y) C)
    use door1, door2
    constructor
    · intro h_eq_doors; simp [Prod.ext_iff] at h_eq_doors;
      have this := h_eq_doors.1
      have : y ∉ sigma := Finset.erase_eq_self.mp this
      exact this h_y_in_sigma
    · ext ⟨τ, D⟩; constructor
      · intro h
        rcases h with ⟨h_nc_door, h_is_door⟩
        cases h_is_door with
        | idoor h0 h_door x hx_notin_τ h_insert_x h_D_eq_C =>
          subst h_D_eq_C
          have h_nc_card := h_nc_door.2
          have h_x_in_sigma : x ∈ sigma := by rw [←h_insert_x]; exact Finset.mem_insert_self x τ
          have h_τ_eq_erase : τ = sigma.erase x := by rw [←Finset.erase_insert hx_notin_τ, h_insert_x]
          have h_x_unique : ∀ ⦃w⦄, w ∈ sigma → c w = c x → w = x := by
            intro w hw hcw
            exact h_inj_on_sigma hw h_x_in_sigma hcw
          have h_img_erase : (τ.image c) = img.erase (c x) := by
            rw [h_τ_eq_erase]
            exact image_erase_eq_erase_image_of_unique sigma c h_x_in_sigma h_x_unique
          rw [h_img_erase] at h_nc_card
          by_cases h_x_eq_y : x = y
          · subst h_x_eq_y
            simp [h_τ_eq_erase, door1]
          · have h_cx_in_D : c x ∈ D := by
              by_contra h_cx_notin_C
              have h_cx_in_img_diff_D : c x ∈ img \ D := Finset.mem_sdiff.mpr ⟨Finset.mem_image_of_mem c h_x_in_sigma, h_cx_notin_C⟩
              rw [h_img_C_eq, Finset.mem_singleton] at h_cx_in_img_diff_D
              have h_c_eq : c x = c y := by rw [h_cx_in_img_diff_D]
              have x_in_sigma : x ∈ sigma := by
                have : x ∈ insert x τ := Finset.mem_insert_self x τ
                have : x ∈ sigma := by
                  rw [←h_insert_x]
                  exact Finset.mem_insert_self x τ
                exact this
              have := h_y_unique x_in_sigma h_c_eq
              exact h_x_eq_y this
            exfalso
            have h_card_2 : (D \ (img.erase (c x))).card = 2 := by
              have h_eq : D \ (img.erase (c x)) = insert (c x) (D \ img) := by
                ext y
                simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
                constructor
                · intro ⟨hy_D, hy_not_erase⟩
                  simp at hy_not_erase
                  by_cases h : y = c x
                  · left; exact h
                  · right
                    exact ⟨hy_D, hy_not_erase h⟩
                · intro h
                  cases h with
                  | inl h_eq => exact ⟨h_eq ▸ h_cx_in_D, by simp [h_eq]⟩
                  | inr h_in =>
                    exact ⟨h_in.1, by simp; intro h_neq; exact h_in.2⟩
              rw [h_eq, Finset.card_insert_of_notMem]
              · rw [h_nc.2]
              · intro h_mem
                have := (Finset.mem_sdiff.mp h_mem).2
                have h_img_mem : c x ∈ img := Finset.mem_image_of_mem c h_x_in_sigma
                exact this h_img_mem
            rw [h_card_2] at h_nc_card; linarith
           | odoor h0 h_door j hj_notin_C h_τ_eq_sigma h_D_eq_insert =>
            subst h_τ_eq_sigma; subst h_D_eq_insert
            have h_nc_card := h_nc_door.2
            by_cases h_j_eq_cy : j = c y
            · subst h_j_eq_cy; simp; right; rfl
            · exfalso
              have h_j_notin_img : j ∉ img := by
                intro h_j_in_img
                have h_j_in_img_diff_C : j ∈ img \ C := Finset.mem_sdiff.mpr ⟨h_j_in_img, hj_notin_C⟩
                rw [h_img_C_eq, Finset.mem_singleton] at h_j_in_img_diff_C
                exact h_j_eq_cy h_j_in_img_diff_C
              have h_card_2 : ((insert j C) \ img).card = 2 := by
                have h_eq : (insert j C) \ img = (C \ img) ∪ {j} := by
                  ext x
                  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
                  constructor
                  · intro ⟨hx_in, hx_notin⟩
                    cases hx_in with
                    | inl hx_eq_j => right; exact hx_eq_j
                    | inr hx_in_C => left; exact ⟨hx_in_C, hx_notin⟩
                  · intro h
                    cases h with
                    | inl h => exact ⟨Or.inr h.1, h.2⟩
                    | inr h => exact ⟨Or.inl h, by rw [h]; exact h_j_notin_img⟩
                rw [h_eq, Finset.card_union_of_disjoint]
                · rw [h_nc.2, Finset.card_singleton]
                · exact Finset.disjoint_singleton_right.mpr (fun h => hj_notin_C (Finset.mem_sdiff.mp h).1)
              rw [h_card_2] at h_nc_card; linarith
      · intro h
        simp at h
        rcases h with (h_eq1 | h_eq2)
        · have ⟨h_τ_eq, h_D_eq⟩ : τ = sigma.erase y ∧ D = C := Prod.mk.inj h_eq1
          subst h_τ_eq h_D_eq
          constructor
          · unfold isNearlyColorful
            constructor
            · unfold isCell
              exact Dominant_of_subset _ _ D (Finset.erase_subset y sigma) h_cell
            · rw [image_erase_eq_erase_image_of_unique sigma c h_y_in_sigma h_y_unique]
              have h_eq_diff : D \ (image c sigma).erase (c y) = D \ image c sigma := by
                ext z
                constructor
                · intro h
                  simp only [Finset.mem_sdiff, Finset.mem_erase] at h ⊢
                  exact ⟨h.1, fun h_in => h.2 ⟨fun h_eq => h_c_y_notin_C (h_eq ▸ h.1), h_in⟩⟩
                · intro h
                  simp only [Finset.mem_sdiff, Finset.mem_erase] at h ⊢
                  exact ⟨h.1, fun ⟨_, h_in⟩ => h.2 h_in⟩
              rw [h_eq_diff, h_nc.2]
          · apply isDoorof.idoor
            · exact h_cell
            · constructor
              · unfold isCell
                exact Dominant_of_subset _ _ D (Finset.erase_subset y sigma) h_cell
              · rw [Finset.card_erase_of_mem h_y_in_sigma, h_card_eq]
                exact (Nat.sub_add_cancel (Finset.card_pos.mpr ⟨y, h_y_in_sigma⟩)).symm
            · exact Finset.notMem_erase y sigma
            · exact Finset.insert_erase h_y_in_sigma
            · rfl

        · have ⟨h_τ_eq, h_D_eq⟩ : τ = sigma ∧ D = insert (c y) C := Prod.mk.inj h_eq2
          subst h_τ_eq h_D_eq
          constructor
          · unfold isNearlyColorful
            constructor
            · unfold isCell
              unfold isDominant
              intro z
              obtain ⟨i, hi_in_C, hi_dom⟩ := h_cell z
              use i, Finset.mem_insert_of_mem hi_in_C
            · have h_j_in_img : c y ∈ img := Finset.mem_image_of_mem c h_y_in_sigma
              have h_sdiff_insert : (insert (c y) C) \ img = C \ img := by
                rw [Finset.insert_sdiff_of_mem _ h_j_in_img]
              rw [h_sdiff_insert, h_nc.2]
          · apply isDoorof.odoor
            · exact h_cell
            · constructor
              · apply Dominant_of_supset τ C (insert (c y) C)
                · exact Finset.subset_insert (c y) C
                · exact h_cell
              · rw [Finset.card_insert_of_notMem h_c_y_notin_C, h_card_eq]
            · exact h_c_y_notin_C
            · rfl
            · rfl
  | inr h_inj =>
    unfold isNearlyColorful at h_nc
    obtain ⟨h_cell, h_missing_card⟩ := h_nc
    have h_missing_exists : ∃! i₀, i₀ ∈ C ∧ i₀ ∉ sigma.image c := by
      have h_nonempty : (C \ sigma.image c).Nonempty := by
        rw [←Finset.card_pos]
        rw [h_missing_card]
        norm_num
      have h_singleton : ∃ i₀, C \ sigma.image c = {i₀} := by
        exact Finset.card_eq_one.mp h_missing_card
      obtain ⟨i₀, h_eq⟩ := h_singleton
      use i₀
      constructor
      · constructor
        · have h_i₀_in_diff : i₀ ∈ C \ image c sigma := by rw [h_eq]; simp
          exact (Finset.mem_sdiff.mp h_i₀_in_diff).1
        · have h_i₀_in_diff : i₀ ∈ C \ image c sigma := by rw [h_eq]; simp
          exact (Finset.mem_sdiff.mp h_i₀_in_diff).2
      · intro j ⟨h_j_in_C, h_j_notin_img⟩
        have h_j_in_diff : j ∈ C \ sigma.image c := by
          exact Finset.mem_sdiff.mpr ⟨h_j_in_C, h_j_notin_img⟩
        rw [h_eq] at h_j_in_diff
        exact Finset.mem_singleton.mp h_j_in_diff

    obtain ⟨i₀, ⟨h_i₀_in_C, h_i₀_notin_img⟩, h_i₀_unique⟩ := h_missing_exists

    have h_collision_exists : ∃ x y, x ∈ sigma ∧ y ∈ sigma ∧ x ≠ y ∧ c x = c y := by
      by_contra h_no_collision
      push Not at h_no_collision
      have h_inj_on_sigma : Set.InjOn c sigma := by
        intro x h_x y h_y h_eq
        by_contra h_ne
        exact h_no_collision x y h_x h_y h_ne h_eq
      have h_card_eq : sigma.card = (sigma.image c).card := by
        exact (Finset.card_image_of_injOn h_inj_on_sigma).symm
      rw [h_card_eq] at h_inj
      linarith

    obtain ⟨x, y, h_x_in_sigma, h_y_in_sigma, h_xy_ne, h_cxy_eq⟩ := h_collision_exists

    have h_collision_structure : ∃ a b, a ∈ sigma ∧ b ∈ sigma ∧ c a = c b ∧ a ≠ b ∧ Set.InjOn c (sigma \ {a, b}) := by
      obtain ⟨a, b, ha, hb, heq, hne, hinj⟩ := injOn_sdiff sigma c h_inj
      exact ⟨a, b, ha, hb, heq, hne, by convert hinj; simp⟩

    obtain ⟨a, b, ha_in_sigma, hb_in_sigma, hc_eq, hab_ne, h_inj_outside⟩ := h_collision_structure

    have h_collision_pair : (a = x ∧ b = y) ∨ (a = y ∧ b = x) := by
      have h_pair_eq : ({x, y} : Finset T) = {a, b} := by
        by_contra h_ne_pair
        by_cases h_disjoint : Disjoint ({x, y} : Finset T) {a, b}

        · have h_x_notin_ab : x ∉ {a, b} := Finset.disjoint_left.mp h_disjoint (by simp)
          have h_y_notin_ab : y ∉ {a, b} := Finset.disjoint_left.mp h_disjoint (by simp)
          have h_x_in_sdiff : x ∈ sigma \ {a, b} := Finset.mem_sdiff.mpr ⟨h_x_in_sigma, h_x_notin_ab⟩
          have h_y_in_sdiff : y ∈ sigma \ {a, b} := Finset.mem_sdiff.mpr ⟨h_y_in_sigma, h_y_notin_ab⟩
          have h_x_in_set : x ∈ (↑sigma : Set T) \ {a, b} := by
            simp [Set.mem_diff, h_x_in_sigma]
            simp at h_x_notin_ab
            exact h_x_notin_ab
          have h_y_in_set : y ∈ (↑sigma : Set T) \ {a, b} := by
            simp [Set.mem_diff, h_y_in_sigma]
            simp at h_y_notin_ab
            exact h_y_notin_ab
          have h_inj_xy := h_inj_outside h_x_in_set h_y_in_set h_cxy_eq
          exact h_xy_ne h_inj_xy

        · rw [Finset.not_disjoint_iff] at h_disjoint
          obtain ⟨u, hu_in_xy, hu_in_ab⟩ := h_disjoint
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu_in_xy hu_in_ab
          cases hu_in_xy with
          | inl h_u_eq_x =>
            rw [h_u_eq_x] at hu_in_ab
            cases hu_in_ab with
            | inl h_x_eq_a =>
              by_cases h_y_eq_b : y = b
              · rw [h_x_eq_a, h_y_eq_b] at h_ne_pair
                exact h_ne_pair rfl
              · have h_y_ne_a : y ≠ a := by
                  rw [h_x_eq_a] at h_xy_ne
                  exact h_xy_ne.symm
                have h_c_chain : c a = c y := by
                  rw [←h_x_eq_a, h_cxy_eq]
                have h_y_in_complement : y ∈ sigma \ {a, b} := by
                  rw [Finset.mem_sdiff]
                  exact ⟨h_y_in_sigma, by simp [h_y_ne_a, h_y_eq_b]⟩

                have h_y_in_set : y ∈ (↑sigma : Set T) \ {a, b} := by
                  simp [Set.mem_diff, h_y_in_sigma, h_y_ne_a, h_y_eq_b]

                have h_pairs_different : ({a, y} : Finset T) ≠ {a, b} := by
                  intro h_eq
                  have h_y_in : y ∈ ({a, b} : Finset T) := by
                    rw [←h_eq]
                    simp
                  simp at h_y_in
                  cases h_y_in with
                  | inl h_y_eq_a => exact h_y_ne_a h_y_eq_a
                  | inr h_y_eq_b_case => exact h_y_eq_b h_y_eq_b_case

                exfalso

                have h_all_distinct : a ≠ b ∧ a ≠ y ∧ b ≠ y := by
                  exact ⟨hab_ne, h_y_ne_a.symm, Ne.symm h_y_eq_b⟩

                have h_same_color : c a = c b ∧ c b = c y := by
                  exact ⟨hc_eq, by rw [←hc_eq, ←h_c_chain]⟩

                have h_three_in_sigma : a ∈ sigma ∧ b ∈ sigma ∧ y ∈ sigma := by
                  exact ⟨ha_in_sigma, hb_in_sigma, h_y_in_sigma⟩

                have h_card_bound : sigma.card ≥ (sigma.image c).card + 2 :=
                  three_collision_card_bound sigma c a b y ha_in_sigma hb_in_sigma h_y_in_sigma
                    hab_ne h_all_distinct.2.1 h_all_distinct.2.2 hc_eq h_same_color.2

                linarith [h_inj, h_card_bound]

            | inr h_x_eq_b =>
              by_cases h_y_eq_a : y = a
              · rw [h_x_eq_b, h_y_eq_a] at h_ne_pair
                have : ({b, a} : Finset T) = {a, b} := by simp [Finset.pair_comm]
                rw [this] at h_ne_pair
                exact h_ne_pair rfl
              · have h_y_ne_b : y ≠ b := by
                  rw [h_x_eq_b] at h_xy_ne
                  exact h_xy_ne.symm

                have h_c_chain : c b = c y := by
                  rw [←h_x_eq_b, h_cxy_eq]

                have h_y_in_complement : y ∈ sigma \ {a, b} := by
                  rw [Finset.mem_sdiff]
                  exact ⟨h_y_in_sigma, by simp [h_y_eq_a, h_y_ne_b]⟩

                have h_y_in_set : y ∈ (↑sigma : Set T) \ {a, b} := by
                  simp [Set.mem_diff, h_y_in_sigma, h_y_eq_a, h_y_ne_b]

                have h_pairs_different : ({b, y} : Finset T) ≠ {a, b} := by
                  intro h_eq
                  have h_y_in : y ∈ ({a, b} : Finset T) := by
                    rw [←h_eq]
                    simp
                  simp at h_y_in
                  cases h_y_in with
                  | inl h_y_eq_a_case => exact h_y_eq_a h_y_eq_a_case
                  | inr h_y_eq_b_case => exact h_y_ne_b h_y_eq_b_case

                exfalso

                have h_all_distinct : a ≠ b ∧ b ≠ y ∧ a ≠ y := by
                  exact ⟨hab_ne, h_y_ne_b.symm, Ne.symm h_y_eq_a⟩

                have h_same_color : c a = c b ∧ c b = c y := by
                  exact ⟨hc_eq, h_c_chain⟩

                have h_three_in_sigma : a ∈ sigma ∧ b ∈ sigma ∧ y ∈ sigma := by
                  exact ⟨ha_in_sigma, hb_in_sigma, h_y_in_sigma⟩

                have h_card_bound : sigma.card ≥ (sigma.image c).card + 2 :=
                  three_collision_card_bound sigma c a b y ha_in_sigma hb_in_sigma h_y_in_sigma
                    hab_ne h_all_distinct.2.2 h_all_distinct.2.1 hc_eq h_same_color.2

                linarith [h_inj, h_card_bound]

          | inr h_u_eq_y =>
            rw [h_u_eq_y] at hu_in_ab
            cases hu_in_ab with
            | inl h_y_eq_a =>
              by_cases h_x_eq_b : x = b
              · rw [h_y_eq_a, h_x_eq_b] at h_ne_pair
                have : ({a, b} : Finset T) = {b, a} := by simp [Finset.pair_comm]
                rw [←this] at h_ne_pair
                exact h_ne_pair rfl
              · have h_x_ne_a : x ≠ a := by
                  rw [h_y_eq_a] at h_xy_ne
                  exact h_xy_ne
                have h_c_chain : c a = c x := by
                  rw [←h_y_eq_a, h_cxy_eq.symm]
                have h_x_in_complement : x ∈ sigma \ {a, b} := by
                  rw [Finset.mem_sdiff]
                  exact ⟨h_x_in_sigma, by simp [h_x_ne_a, h_x_eq_b]⟩

                have h_x_in_set : x ∈ (↑sigma : Set T) \ {a, b} := by
                  simp [Set.mem_diff, h_x_in_sigma, h_x_ne_a, h_x_eq_b]

                have h_pairs_different : ({a, x} : Finset T) ≠ {a, b} := by
                  intro h_eq
                  have h_x_in : x ∈ ({a, b} : Finset T) := by
                    rw [←h_eq]
                    simp
                  simp at h_x_in
                  cases h_x_in with
                  | inl h_x_eq_a_case => exact h_x_ne_a h_x_eq_a_case
                  | inr h_x_eq_b_case => exact h_x_eq_b h_x_eq_b_case

                exfalso

                have h_all_distinct : a ≠ b ∧ a ≠ x ∧ b ≠ x := by
                  exact ⟨hab_ne, h_x_ne_a.symm, Ne.symm h_x_eq_b⟩

                have h_same_color : c a = c b ∧ c b = c x := by
                  exact ⟨hc_eq, by rw [←hc_eq, ←h_c_chain]⟩

                have h_three_in_sigma : a ∈ sigma ∧ b ∈ sigma ∧ x ∈ sigma := by
                  exact ⟨ha_in_sigma, hb_in_sigma, h_x_in_sigma⟩

                have h_card_bound : sigma.card ≥ (sigma.image c).card + 2 :=
                  three_collision_card_bound sigma c a b x ha_in_sigma hb_in_sigma h_x_in_sigma
                    hab_ne h_all_distinct.2.1 h_all_distinct.2.2 hc_eq h_same_color.2

                linarith [h_inj, h_card_bound]

            | inr h_y_eq_b =>
              by_cases h_x_eq_a : x = a
              · rw [h_y_eq_b, h_x_eq_a] at h_ne_pair
                exact h_ne_pair rfl
              · have h_x_ne_b : x ≠ b := by
                  rw [h_y_eq_b] at h_xy_ne
                  exact h_xy_ne

                have h_c_chain : c b = c x := by
                  rw [←h_y_eq_b, h_cxy_eq.symm]

                have h_x_in_complement : x ∈ sigma \ {a, b} := by
                  rw [Finset.mem_sdiff]
                  exact ⟨h_x_in_sigma, by simp [h_x_eq_a, h_x_ne_b]⟩

                have h_x_in_set : x ∈ (↑sigma : Set T) \ {a, b} := by
                  simp [Set.mem_diff, h_x_in_sigma, h_x_eq_a, h_x_ne_b]

                have h_pairs_different : ({b, x} : Finset T) ≠ {a, b} := by
                  intro h_eq
                  have h_x_in : x ∈ ({a, b} : Finset T) := by
                    rw [←h_eq]
                    simp
                  simp at h_x_in
                  cases h_x_in with
                  | inl h_x_eq_a_case => exact h_x_eq_a h_x_eq_a_case
                  | inr h_x_eq_b_case => exact h_x_ne_b h_x_eq_b_case

                exfalso

                have h_all_distinct : a ≠ b ∧ b ≠ x ∧ a ≠ x := by
                  exact ⟨hab_ne, h_x_ne_b.symm, Ne.symm h_x_eq_a⟩

                have h_same_color : c a = c b ∧ c b = c x := by
                  exact ⟨hc_eq, h_c_chain⟩

                have h_three_in_sigma : a ∈ sigma ∧ b ∈ sigma ∧ x ∈ sigma := by
                  exact ⟨ha_in_sigma, hb_in_sigma, h_x_in_sigma⟩

                have h_card_bound : sigma.card ≥ (sigma.image c).card + 2 :=
                  three_collision_card_bound sigma c a b x ha_in_sigma hb_in_sigma h_x_in_sigma
                    hab_ne h_all_distinct.2.2 h_all_distinct.2.1 hc_eq h_same_color.2

                linarith [h_inj, h_card_bound]

      have h_eq_or_swap : ({x, y} : Finset T) = {a, b} ∨ ({x, y} : Finset T) = {b, a} := by
        left; exact h_pair_eq
      cases h_eq_or_swap with
      | inl h_eq =>
        have : {a, b} = {x, y} := h_eq.symm
        by_cases h : a = x
        · left
          constructor
          · exact h
          · have h_b_in : b ∈ ({x, y} : Finset T) := by rw [← this]; simp
            simp at h_b_in
            cases h_b_in with
            | inl h_b_eq_x => rw [h, h_b_eq_x] at hab_ne; contradiction
            | inr h_b_eq_y => exact h_b_eq_y
        · right
          have h_a_in : a ∈ ({x, y} : Finset T) := by rw [← this]; simp
          simp at h_a_in
          cases h_a_in with
          | inl h_a_eq_x => contradiction
          | inr h_a_eq_y =>
            constructor
            · exact h_a_eq_y
            · have h_b_in : b ∈ ({x, y} : Finset T) := by rw [← this]; simp
              simp at h_b_in
              cases h_b_in with
              | inl h_b_eq_x => exact h_b_eq_x
              | inr h_b_eq_y => rw [h_a_eq_y, h_b_eq_y] at hab_ne; contradiction
      | inr h_eq =>
        have : {b, a} = {x, y} := h_eq.symm
        by_cases h : b = x
        · have h_a_in : a ∈ ({x, y} : Finset T) := by rw [← this]; simp
          simp at h_a_in
          cases h_a_in with
          | inl h_a_eq_x =>
            exfalso
            rw [h_a_eq_x] at hab_ne
            rw [h] at hab_ne
            exact hab_ne rfl
          | inr h_a_eq_y => exact Or.inr ⟨h_a_eq_y, h⟩
        · have h_b_in : b ∈ ({x, y} : Finset T) := by rw [← this]; simp
          simp at h_b_in
          cases h_b_in with
          | inl h_b_eq_x => contradiction
          | inr h_b_eq_y =>
            have h_a_in : a ∈ ({x, y} : Finset T) := by rw [← this]; simp
            simp at h_a_in
            cases h_a_in with
            | inl h_a_eq_x => exact Or.inl ⟨h_a_eq_x, h_b_eq_y⟩
            | inr h_a_eq_y => rw [h_a_eq_y, h_b_eq_y] at hab_ne; contradiction

    let τ₁ := sigma.erase x
    let τ₂ := sigma.erase y
    let door1 := (τ₁, C)
    let door2 := (τ₂, C)

    have h_door1_valid : isDoorof τ₁ C sigma C :=
      collision_door_valid sigma C c x h_cell h_x_in_sigma h_card_eq

    have h_door2_valid : isDoorof τ₂ C sigma C :=
      collision_door_valid sigma C c y h_cell h_y_in_sigma h_card_eq

    have h_imgs_preserved := image_erase_collision_preserves sigma c x y h_x_in_sigma h_y_in_sigma h_xy_ne h_cxy_eq

    have h_door1_nc : isNearlyColorful c τ₁ C := by
      unfold isNearlyColorful
      constructor
      · exact Dominant_of_subset sigma τ₁ C (Finset.erase_subset x sigma) h_cell
      · rw [h_imgs_preserved.1, h_missing_card]

    have h_door2_nc : isNearlyColorful c τ₂ C := by
      unfold isNearlyColorful
      constructor
      · exact Dominant_of_subset sigma τ₂ C (Finset.erase_subset y sigma) h_cell
      · rw [h_imgs_preserved.2, h_missing_card]

    have h_doors_distinct : door1 ≠ door2 := by
      simp [door1, door2, τ₁, τ₂]
      intro h_eq
      have h_y_mem : y ∈ sigma.erase x := by
        rw [Finset.mem_erase]
        exact ⟨h_xy_ne.symm, h_y_in_sigma⟩
      rw [h_eq] at h_y_mem
      have h_y_not_mem : y ∉ sigma.erase y := by
        rw [Finset.mem_erase]
        simp
      exact h_y_not_mem h_y_mem

    have h_exactly_two : NCdoors c sigma C = {door1, door2} := by
      ext ⟨τ, D⟩
      simp [NCdoors]
      constructor
      · intro ⟨h_nc_τD, h_door_τD⟩
        cases h_door_τD with
        | idoor h_cell_sigmaC h_door_τD z h_z_notin_τ h_insert_eq h_D_eq_C =>
          rw [h_D_eq_C]
          have h_τ_eq : τ = sigma.erase z := by
            rw [←Finset.erase_insert h_z_notin_τ, h_insert_eq]
          rw [h_τ_eq]
          have h_z_in_sigma : z ∈ sigma := by
            rw [←h_insert_eq]
            exact Finset.mem_insert_self z τ
          by_cases h_z_cases : z = x ∨ z = y
          · rcases h_z_cases with h_z_eq_x | h_z_eq_y
            · left; simp [door1, τ₁, h_z_eq_x]
            · right; simp [door2, τ₂, h_z_eq_y]
          · exfalso
            push Not at h_z_cases
            have h_card_is_one : (C \ (sigma.erase z).image c).card = 1 := by rw [←h_D_eq_C, ←h_τ_eq]; exact h_nc_τD.2
            have h_card_is_two : (C \ (sigma.erase z).image c).card = 2 := by
              have h_uniq_z : ∀ w ∈ sigma, c w = c z → w = z := by
                intro w hw h_c_eq
                rcases h_collision_pair with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
                · have h_z_ne_ab : z ≠ a ∧ z ≠ b := h_z_cases
                  by_cases hw_ab : w ∈ ({a, b} : Finset T)
                  · exfalso
                    have h_c_z_eq_ca : c z = c a := by
                      simp at hw_ab; rcases hw_ab with rfl | rfl
                      · exact h_c_eq.symm
                      · transitivity c w; exact h_c_eq.symm; exact hc_eq.symm
                    have h_card_ge_img_add_2 : sigma.card ≥ (sigma.image c).card + 2 :=
                      three_collision_card_bound sigma c a b z ha_in_sigma hb_in_sigma h_z_in_sigma
                        hab_ne (Ne.symm h_z_ne_ab.1) (Ne.symm h_z_ne_ab.2) hc_eq (h_c_z_eq_ca ▸ hc_eq.symm)
                    linarith [h_inj, h_card_ge_img_add_2]
                  · have h_w_sdiff : w ∈ sigma \ {a, b} := by simp [hw, hw_ab]
                    have h_z_sdiff : z ∈ sigma \ {a, b} := by simp [h_z_in_sigma, h_z_ne_ab]
                    exact h_inj_outside (by simpa using h_w_sdiff) (by simpa using h_z_sdiff) h_c_eq
                · have h_z_ne_ab : z ≠ a ∧ z ≠ b := h_z_cases.symm
                  by_cases hw_ab : w ∈ ({a, b} : Finset T)
                  · exfalso
                    have h_c_z_eq_ca : c z = c a := by
                      simp at hw_ab; rcases hw_ab with rfl | rfl
                      · exact h_c_eq.symm
                      · transitivity c w; exact h_c_eq.symm; exact hc_eq.symm
                    have h_card_ge_img_add_2 : sigma.card ≥ (sigma.image c).card + 2 :=
                      three_collision_card_bound sigma c a b z ha_in_sigma hb_in_sigma h_z_in_sigma
                        hab_ne (Ne.symm h_z_ne_ab.1) (Ne.symm h_z_ne_ab.2) hc_eq (h_c_z_eq_ca ▸ hc_eq.symm)
                    linarith [h_inj, h_card_ge_img_add_2]
                  · have h_w_sdiff : w ∈ sigma \ {a, b} := by simp [hw, hw_ab]
                    have h_z_sdiff : z ∈ sigma \ {a, b} := by simp [h_z_in_sigma, h_z_ne_ab]
                    exact h_inj_outside (by simpa using h_w_sdiff) (by simpa using h_z_sdiff) h_c_eq

              have h_img_erase : (sigma.erase z).image c = (sigma.image c).erase (c z) :=
                image_erase_eq_erase_image_of_unique sigma c h_z_in_sigma h_uniq_z

              rw [h_img_erase]
              have h_img_subset_C : image c sigma ⊆ C := by
                have h_C_card_img : C.card = (image c sigma).card + 1 := by rw [h_card_eq, h_inj]
                have h_C_card_form : C.card = (C \ image c sigma).card + (C ∩ image c sigma).card := (card_sdiff_add_card_inter C (image c sigma)).symm
                rw [h_missing_card] at h_C_card_form
                have h_img_eq_inter_card : (image c sigma).card = (C ∩ image c sigma).card := by linarith
                have h_inter_eq_img : C ∩ image c sigma = image c sigma :=
                  Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [h_img_eq_inter_card])
                rwa [Finset.inter_eq_right] at h_inter_eq_img

              have h_cz_in_C : c z ∈ C := h_img_subset_C (mem_image_of_mem c h_z_in_sigma)
              have h_cz_not_in_diff : c z ∉ C \ image c sigma := by simp [mem_image_of_mem c h_z_in_sigma]

              have h_eq : C \ (image c sigma).erase (c z) = (C \ image c sigma) ∪ {c z} := by
                ext y
                simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_union, Finset.mem_singleton]
                constructor
                · intro ⟨hy_in_C, hy_cond⟩
                  by_cases h : y ∈ image c sigma
                  · right; by_contra h'; exact hy_cond ⟨h', h⟩
                  · left; exact ⟨hy_in_C, h⟩
                · intro h
                  cases h with
                  | inl h => exact ⟨h.1, fun h' => h.2 h'.2⟩
                  | inr h => rw [h]; exact ⟨h_cz_in_C, fun hp => hp.1 rfl⟩
              rw [h_eq, Finset.card_union_of_disjoint]
              · rw [h_missing_card, Finset.card_singleton]
              · exact Finset.disjoint_singleton_right.mpr h_cz_not_in_diff

            rw [h_card_is_two] at h_card_is_one
            norm_num at h_card_is_one

        | odoor h_cell_sigmaC h_door_τD j h_j_notin_C h_τ_eq_sigma h_D_eq =>
          exfalso
          have h_card_is_one : ((C ∪ {j}) \ (sigma.image c)).card = 1 := by
           have : D \ (τ.image c) = (C ∪ {j}) \ (sigma.image c) := by rw [h_D_eq, ← h_τ_eq_sigma]; rw [Finset.insert_eq, Finset.union_comm]
           rw [← this]
           exact h_nc_τD.2
          have h_img_subset_C : image c sigma ⊆ C := by
            have h_C_card_img : C.card = (image c sigma).card + 1 := by rw [h_card_eq, h_inj]
            have h_C_card_form : C.card = (C \ image c sigma).card + (C ∩ image c sigma).card := (card_sdiff_add_card_inter C (image c sigma)).symm
            rw [h_missing_card] at h_C_card_form
            have h_img_eq_inter_card : (image c sigma).card = (C ∩ image c sigma).card := by linarith
            have h_inter_eq_img : C ∩ image c sigma = image c sigma :=
              Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [h_img_eq_inter_card])
            rwa [Finset.inter_eq_right] at h_inter_eq_img
          have h_j_notin_img : j ∉ image c sigma := fun h => h_j_notin_C (h_img_subset_C h)
          have h_card_is_two : ((C ∪ {j}) \ (sigma.image c)).card = 2 := by
            rw [Finset.union_sdiff_distrib, Finset.card_union_of_disjoint]
            · have h_sdiff_eq : {j} \ image c sigma = {j} :=
                Finset.sdiff_eq_self_of_disjoint (Finset.disjoint_singleton_left.mpr h_j_notin_img)
              rw [h_sdiff_eq, Finset.card_singleton]
              linarith [h_missing_card]
            · rw [Finset.sdiff_eq_self_of_disjoint (Finset.disjoint_singleton_left.mpr h_j_notin_img)]
              rw [Finset.disjoint_singleton_right]
              intro h
              have : j ∈ C := (Finset.mem_sdiff.mp h).1
              exact h_j_notin_C this
          rw [h_card_is_two] at h_card_is_one
          norm_num at h_card_is_one
      · intro h_or
        cases h_or with
        | inl h_eq =>
          have : τ = τ₁ ∧ D = C := Prod.mk.inj h_eq
          rw [this.1, this.2]
          exact ⟨h_door1_nc, h_door1_valid⟩
        | inr h_eq =>
          have : τ = τ₂ ∧ D = C := Prod.mk.inj h_eq
          rw [this.1, this.2]
          exact ⟨h_door2_nc, h_door2_valid⟩

    use door1, door2


variable [Fintype T] [Fintype Idx]

variable (c) in
abbrev colorful := Finset.filter (fun (x : Finset T× Finset Idx) =>  IST.isColorful c x.1 x.2) univ

variable (c) in
abbrev dbcountingset (i : Idx):= Finset.filter (fun x : (Finset T× Finset Idx) × (Finset T× Finset Idx) => isTypedNC c i x.1.1 x.1.2 ∧ isDoorof x.1.1 x.1.2 x.2.1 x.2.2) univ


variable (c) in
lemma dbcount_outside_door' (i : Idx): ∃ x,  filter (fun x => isOutsideDoor x.1.1 x.1.2) (dbcountingset c i) = {x}  :=  by
  classical

  have h_T_nonempty : Nonempty T := ⟨(default : T)⟩
  have h_T_univ_nonempty : (Finset.univ : Finset T).Nonempty := Finset.univ_nonempty_iff.mpr h_T_nonempty
  let x_max_i : T := @Finset.max' T (IST i) Finset.univ h_T_univ_nonempty
  let sigma_u : Finset T := {x_max_i}
  let C_u : Finset Idx := {i}
  let τ_u : Finset T := Finset.empty
  let D_u : Finset Idx := {i}
  let x_unique : (Finset T × Finset Idx) × (Finset T × Finset Idx) := ((τ_u, D_u), (sigma_u, C_u))

  have h_outside_door_τu_Du : isOutsideDoor τ_u D_u := outsidedoor_singleton i
  have h_typed_nc : isTypedNC c i τ_u D_u := by
    constructor
    · exact (NC_of_outsidedoor (c := c) h_outside_door_τu_Du).1
    · simp only [τ_u]
      constructor

  have h_door_relation : isDoorof τ_u D_u sigma_u C_u := by
    apply isDoorof.idoor
    · intro y
      use i
      constructor
      · simp only [C_u, Finset.mem_singleton]
      · intro x hx
        simp only [sigma_u] at hx
        simp only [Finset.mem_singleton] at hx
        rw [hx]
        exact @Finset.le_max' T (IST i) Finset.univ y (Finset.mem_univ y)
    · exact h_outside_door_τu_Du.1
    · simp only [τ_u]
      exact Finset.notMem_empty x_max_i
    · simp only [τ_u, sigma_u]
      rfl
    · rfl

  use x_unique
  ext x_gen
  simp only [mem_filter, mem_univ, mem_singleton]

  constructor
  · intro h_in_filter
    simp at h_in_filter
    obtain ⟨h_in_db, h_outside⟩ := h_in_filter
    obtain ⟨h_typed, h_door⟩ := h_in_db
    obtain ⟨h_is_door, h_empty⟩ := h_outside
    have h_empty_image : (x_gen.1.1).image c = ∅ := by
      rw [h_empty]
      exact Finset.image_empty c
    have h_x_gen_1_2_eq : x_gen.1.2 = {i} := by
      have h_eq := h_typed.2
      rw [h_empty_image] at h_eq
      simp at h_eq
      exact h_eq
    obtain ⟨_, h_D_singleton⟩ := outsidedoor_is_singleton ⟨h_is_door, h_empty⟩
    obtain ⟨j, h_D_eq⟩ := h_D_singleton

    have h_j_eq_i : j = i := by
      have h_eq_j : x_gen.1.2 = {j} := h_D_eq
      rw [h_x_gen_1_2_eq] at h_eq_j
      have : j ∈ {j} := Finset.mem_singleton_self j
      rw [←h_eq_j] at this
      exact Finset.eq_of_mem_singleton this

    cases h_door with
    | idoor h_cell_sigmaC h_door_τD x h_x_notin h_insert_eq h_D_eq_C =>
      have h_sigma_eq : x_gen.2.1 = {x} := by
        rw [←h_insert_eq, h_empty]
        rfl
      have h_x_eq_max : x = x_max_i := by
        have h_dom : ∀ y, y ≤[i] x := by
          intro y
          obtain ⟨j_dom, hj_in, hj_dom⟩ := h_cell_sigmaC y
          rw [←h_D_eq_C, h_x_gen_1_2_eq] at hj_in
          simp at hj_in
          subst hj_in
          apply hj_dom
          rw [h_sigma_eq]
          simp
        have h1 : x ≤[i] x_max_i := @Finset.le_max' T (IST i) Finset.univ x (Finset.mem_univ x)
        have h2 : x_max_i ≤[i] x := h_dom x_max_i
        exact @le_antisymm T (IST i).toPartialOrder x x_max_i h1 h2
      apply Prod.ext
      · apply Prod.ext
        · exact h_empty
        · rw [h_x_gen_1_2_eq]
      · apply Prod.ext
        · rw [h_sigma_eq, h_x_eq_max]
        · rw [←h_D_eq_C, h_x_gen_1_2_eq]

    | odoor h_cell_sigmaC h_door_τD j h_j_notin h_τ_eq h_D_insert =>
      exfalso
      have h_sigma_empty : x_gen.2.1 = ∅ := by
        rw [←h_τ_eq, h_empty]
        rfl
      let h_door_constructed : isDoorof x_gen.1.1 x_gen.1.2 x_gen.2.1 x_gen.2.2 :=
        isDoorof.odoor h_cell_sigmaC ⟨h_is_door.1, h_is_door.2⟩ j h_j_notin h_τ_eq h_D_insert
      have h_room : IST.isRoom x_gen.2.1 x_gen.2.2 := isRoom_of_Door h_door_constructed
      have h_sigma_nonempty : x_gen.2.1.Nonempty := sigma_nonempty_of_room h_room
      rw [h_sigma_empty] at h_sigma_nonempty
      exact Finset.not_nonempty_empty h_sigma_nonempty

  · intro h_eq
    rw [h_eq]
    simp only [true_and]
    constructor
    · constructor
      · exact h_typed_nc
      · exact h_door_relation
    · exact h_outside_door_τu_Du

variable (c)


lemma dbcount_outside_door_odd (i : Idx): Odd (filter (fun x => isOutsideDoor x.1.1 x.1.2) (dbcountingset c i)).card  := by
  have cardone: (filter (fun x => isOutsideDoor x.1.1 x.1.2) (dbcountingset c i)).card = 1 := by
    obtain ⟨x,hx⟩ := dbcount_outside_door' c i
    simp [hx]
  convert odd_one

omit [Inhabited T] in
lemma fiber_size_internal_door (c : T → Idx) (i : Idx) (y : Finset T × Finset Idx)
    (hy_internal : IST.isInternalDoor y.1 y.2) (hy_typed : isTypedNC c i y.1 y.2) :
    let s := filter (fun x => ¬ isOutsideDoor x.1.1 x.1.2) (dbcountingset c i)
    let f := fun (x : (Finset T × Finset Idx) × Finset T × Finset Idx) => x.1
    (filter (fun a => f a = y) s).card = 2 := by
  obtain ⟨sigma₁, sigma₂, C₁, C₂, h_ne, h_room₁, h_room₂, h_door₁, h_door₂, h_unique⟩ :=
    internal_door_two_rooms y.1 y.2 hy_internal
  let s := filter (fun x => ¬ isOutsideDoor x.1.1 x.1.2) (dbcountingset c i)
  let f := fun (x : (Finset T × Finset Idx) × Finset T × Finset Idx) => x.1
  let elem1 : (Finset T × Finset Idx) × Finset T × Finset Idx := (y, (sigma₁, C₁))
  let elem2 : (Finset T × Finset Idx) × Finset T × Finset Idx := (y, (sigma₂, C₂))
  have elem1_in_s : elem1 ∈ s := by
    simp only [elem1, s, mem_filter]
    constructor
    · simp only [mem_univ, true_and]
      exact ⟨hy_typed, h_door₁⟩
    · intro h_outside
      exact (Finset.nonempty_iff_ne_empty.mp hy_internal.2) h_outside.2
  have elem2_in_s : elem2 ∈ s := by
    simp only [elem2, s, mem_filter]
    constructor
    · simp only [mem_univ, true_and]
      exact ⟨hy_typed, h_door₂⟩
    · intro h_outside
      exact (Finset.nonempty_iff_ne_empty.mp hy_internal.2) h_outside.2
  have elems_distinct : elem1 ≠ elem2 := by
    intro h_eq
    injection h_eq with _ h_pair_eq
    exact h_ne h_pair_eq
  have fiber_eq : filter (fun a => f a = y) s = {elem1, elem2} := by
    ext x
    constructor
    · intro hx
      rw [mem_filter] at hx
      obtain ⟨hx_s, hx_eq⟩ := hx
      rw [mem_filter] at hx_s
      obtain ⟨hx_db, _⟩ := hx_s
      rw [mem_filter] at hx_db
      obtain ⟨_, hx_typed_x, hx_door_x⟩ := hx_db
      have h_x_form : x = (y, x.2) := Prod.ext_iff.mpr ⟨hx_eq, rfl⟩
      have h_room_x2 : IST.isRoom x.2.1 x.2.2 := isRoom_of_Door hx_door_x
      have hx_door_y : isDoorof y.1 y.2 x.2.1 x.2.2 :=
        hx_eq ▸ hx_door_x
      obtain h_case1 | h_case2 := h_unique x.2.1 x.2.2 h_room_x2 hx_door_y
      · simp only [mem_insert, mem_singleton]
        left
        rw [h_x_form]
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · exact h_case1.1
          · exact h_case1.2
      · simp only [mem_insert, mem_singleton]
        right
        rw [h_x_form]
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · exact h_case2.1
          · exact h_case2.2
    · intro hx
      simp only [mem_insert, mem_singleton] at hx
      cases hx with
      | inl h =>
        rw [h, mem_filter]
        exact ⟨elem1_in_s, by simp [f, elem1]⟩
      | inr h =>
        rw [h, mem_filter]
        exact ⟨elem2_in_s, by simp [f, elem2]⟩
  apply Eq.trans (congrArg Finset.card fiber_eq)
  exact Finset.card_pair elems_distinct

omit [Inhabited T] in
lemma dbcount_internal_door_even (i : Idx) : Even (filter (fun x => ¬ isOutsideDoor x.1.1 x.1.2) (dbcountingset c i)).card := by
  let s := filter (fun x => ¬ isOutsideDoor x.1.1 x.1.2) (dbcountingset c i)
  let t := filter (fun (x : Finset T × Finset Idx) => IST.isInternalDoor x.1 x.2 ∧ isTypedNC c i x.1 x.2) univ
  let f := fun (x : (Finset T × Finset Idx) × Finset T × Finset Idx) => x.1
  have fs_in_t : ∀ x ∈ s, f x ∈ t := by
    intro x hx
    rw [mem_filter] at hx
    obtain ⟨hx_db, hx_not_outside⟩ := hx
    rw [mem_filter] at hx_db
    obtain ⟨_, hx_typed, hx_door⟩ := hx_db
    rw [mem_filter]
    simp only [mem_univ, true_and]
    constructor
    · unfold isInternalDoor
      constructor
      · cases hx_door with
        | idoor h0 h1 y h_notin h_eq h_D_eq_C => exact h1
        | odoor h0 h1 j h_notin h_eq h_D_eq => exact h1
      · by_contra h_empty
        have h_outside : isOutsideDoor x.1.1 x.1.2 := by
          constructor
          · cases hx_door with
            | idoor h0 h1 y h_notin h_eq h_D_eq_C => exact h1
            | odoor h0 h1 j h_notin h_eq h_D_eq => exact h1
          · exact Finset.not_nonempty_iff_eq_empty.mp h_empty
        exact hx_not_outside h_outside
    · exact hx_typed

  have fiber_size_two : ∀ y ∈ t, (filter (fun a=> f a = y) s).card = 2 := by
    intro y hy
    rw [mem_filter] at hy
    obtain ⟨_, hy_internal, hy_typed⟩ := hy
    exact fiber_size_internal_door c i y hy_internal hy_typed

  have counteq := Finset.card_eq_sum_card_fiberwise fs_in_t
  have sumeq := Finset.sum_const_nat fiber_size_two
  rw [sumeq] at counteq
  rw [counteq]
  simp only [even_two, Even.mul_left]


omit [Fintype T] [Fintype Idx] [Inhabited T] in
variable {c} in
lemma NC_of_NCdoor (h1 : isTypedNC c i τ D)
(h2 : isDoorof τ D sigma C) :
  ¬ isColorful c sigma C → isTypedNC c i sigma C := by
  intro h_not_colorful
  obtain h_typed | h_colorful := NC_or_C_of_door h1 h2
  · exact h_typed
  · contradiction

omit [Inhabited T] in
variable {c} in
lemma firber2_doors_NCroom (h0 : isRoom sigma C) (h1 : isTypedNC c i sigma C) :
  (filter (fun (x : (Finset T× Finset Idx)× Finset T × Finset Idx) => x.2 = (sigma,C)) (dbcountingset c i)).card = 2 := by
    obtain ⟨door1, door2, h_ne, h_doors_eq⟩ := doors_of_NCroom h0 (NC_of_TNC h1)
    have h_filter_eq : filter (fun (x : (Finset T× Finset Idx)× Finset T × Finset Idx) => x.2 = (sigma,C)) (dbcountingset c i) =
                       {(door1, (sigma,C)), (door2, (sigma,C))} := by
      ext x
      constructor
      · intro hx
        rw [mem_filter] at hx
        obtain ⟨h_db, h_eq⟩ := hx
        rw [mem_filter] at h_db
        obtain ⟨_, h_typed, h_door⟩ := h_db
        have h_x_form : x = (x.1, (sigma,C)) := by
          rw [Prod.ext_iff]
          exact ⟨rfl, h_eq⟩
        rw [h_x_form]
        simp
        have h_x1_in_doors : x.1 ∈ NCdoors c sigma C := by
          simp [NCdoors]
          have h_sigma : x.2.1 = sigma := by rw [h_eq]
          have h_C : x.2.2 = C := by rw [h_eq]
          rw [h_sigma, h_C] at h_door
          exact ⟨NC_of_TNC h_typed, h_door⟩
        rw [h_doors_eq] at h_x1_in_doors
        simp at h_x1_in_doors
        exact h_x1_in_doors
      · intro hx
        simp at hx
        cases hx with
        | inl h =>
          rw [h, mem_filter]
          constructor
          · rw [mem_filter]
            have h_door1_in_doors : door1 ∈ NCdoors c sigma C := by
              rw [h_doors_eq]
              exact Set.mem_insert door1 {door2}
            simp [NCdoors] at h_door1_in_doors
            exact ⟨by simp, isTypedNC_of_isNearlyColorful_of_isDoorof_isTypedNC h_door1_in_doors.1 h_door1_in_doors.2 h1, h_door1_in_doors.2⟩
          · rfl
        | inr h =>
          rw [h, mem_filter]
          constructor
          · rw [mem_filter]
            have h_door2_in_doors : door2 ∈ NCdoors c sigma C := by
              rw [h_doors_eq]
              exact Set.mem_insert_of_mem door1 (Set.mem_singleton door2)
            simp [NCdoors] at h_door2_in_doors
            exact ⟨by simp, isTypedNC_of_isNearlyColorful_of_isDoorof_isTypedNC h_door2_in_doors.1 h_door2_in_doors.2 h1, h_door2_in_doors.2⟩
          · rfl
    rw [h_filter_eq]
    simp [h_ne]

omit [Inhabited T] in
lemma dbcount_NCroom (i : Idx) : Even (filter (fun x => ¬isColorful c x.2.1 x.2.2) (dbcountingset c i)).card := by
  let s := filter (fun x => ¬isColorful c x.2.1 x.2.2) (dbcountingset c i)
  let t := filter (fun (x : Finset T × Finset Idx) => IST.isRoom x.1 x.2 ∧ isTypedNC c i x.1 x.2 ) univ
  let f := fun (x : (Finset T × Finset Idx)× Finset T × Finset Idx) => x.2
  have fs_in_t : ∀ x ∈ s, f x ∈ t := by
    intro x hx;
    show x.2 ∈ t
    rw [mem_filter] at hx
    obtain ⟨hx1,hx2⟩ := hx
    rw [mem_filter] at hx1
    rw [mem_filter]
    refine ⟨by simp, isRoom_of_Door hx1.2.2,?_⟩
    apply NC_of_NCdoor hx1.2.1 hx1.2.2 hx2
  have counteq := Finset.card_eq_sum_card_fiberwise fs_in_t
  have fiber_sizetwo :∀ y ∈ t, #(filter (fun a=> f a = y) s) = 2  :=
    by
      intro y hy
      rw [Finset.mem_filter] at hy
      obtain ⟨_,hy1,hy2⟩ := hy
      unfold s
      rw [filter_filter]
      have f2 := firber2_doors_NCroom hy1 hy2
      rw [<-f2]
      congr 1
      apply filter_congr
      intro x hx
      rw [mem_filter] at hx
      obtain ⟨hx1,hx2,hx3⟩ := hx
      unfold f
      constructor
      · simp
      · intro h
        simp_rw [h,and_true]
        exact not_colorful_of_TypedNC hy2
  have sumeq := Finset.sum_const_nat fiber_sizetwo
  rw [sumeq] at counteq
  rw [counteq]
  simp only [even_two, Even.mul_left]

lemma parity_lemma {a b c d : ℕ } (h1 : Odd a) (h2 : Even b) (h3 : Even d) (h4 : a + b = c + d ): Odd c := by
  by_contra h0
  replace h0 := Nat.not_odd_iff_even.1 h0
  have oddab := Even.odd_add h2 h1
  rw [h4] at oddab
  have evencd := Even.add h0 h3
  exact Nat.not_odd_iff_even.2 evencd oddab


theorem _root_.Finset.card_filter_filter_neg {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p]
 : s.card  = (Finset.filter p s).card + (Finset.filter (fun (a : α) => ¬p a) s).card :=
  by
    nth_rw 1 [<-Finset.filter_union_filter_not_eq p s]
    apply Finset.card_union_eq_card_add_card.2 (Finset.disjoint_filter_filter_not _ _ _)

lemma typed_colorful_room_odd  (i : Idx): Odd (Finset.filter (fun (x: (Finset T× Finset Idx) × Finset T × Finset Idx) =>  isColorful c x.2.1 x.2.2) (dbcountingset c i)).card
:= by
  let s:= dbcountingset c i
  have cardeq' := Finset.card_filter_filter_neg s (fun x => isOutsideDoor x.1.1 x.1.2)
  have cardeq := Finset.card_filter_filter_neg s (fun x => isColorful c x.2.1 x.2.2)
  apply parity_lemma (dbcount_outside_door_odd c i) (dbcount_internal_door_even c i) (dbcount_NCroom c i)
  rw [<-cardeq',<-cardeq]

variable [Inhabited Idx]

theorem Scarf : (IST.colorful c).Nonempty := by
  have cardpos := Odd.pos $ typed_colorful_room_odd c default
  replace nonempty:= Finset.card_pos.1 cardpos
  obtain ⟨x,hx⟩ := nonempty
  replace hx := (Finset.mem_filter.1 hx).2
  use x.2
  simp only [mem_filter, mem_univ, hx, and_self]


end Scarf

end IndexedLOrder

end ScarfLib


open Classical

section

instance Pi.Lex.finite {α : Type*} {β : α → Type*} [DecidableEq α] [Finite α]
    [∀ a, Finite (β a)] : Finite (Πₗ a, β a) :=
        (Equiv.finite_iff toLex).1 Pi.finite

end

noncomputable section
open IndexedLOrder

variable (n l : ℕ+) (i : Fin n)

abbrev TT := {x : Πₗ (_ : Fin n), Fin (l+1) | ∑ i, (x i : ℕ)  = l}

instance TT.finite : Finite (TT n l) := by
  rw [Set.coe_eq_subtype]
  exact Subtype.finite

instance TT.inhabited : Inhabited (TT n l) where
  default :=
    ⟨ fun i => if i = 0 then Fin.last l else 0,  by
      simp only [TT, Set.mem_setOf_eq]
      rw [Finset.sum_eq_single (0 : Fin n)]
      · simp
      · intro b _ hb; simp [hb]
      · simp [Fin.val_last] ⟩

instance TT.funlike : FunLike (TT n l) (Fin n) (Fin (l+1)) where
  coe := fun a => a.1
  coe_injective' := by
    intro a b h
    exact Subtype.ext h

variable {n l} in
def TTtostdSimplex (x : TT n l) : stdSimplex ℝ (Fin n) := ⟨fun i => x i / l, by
  rw [stdSimplex]
  constructor
  · intro;simp only[Set.coe_setOf]
    apply div_nonneg <;> simp
  · simp only [Set.coe_setOf];
    rw [<-Finset.sum_div, div_eq_one_iff_eq]
    · exact_mod_cast x.2
    · exact Iff.mpr Nat.cast_ne_zero (PNat.ne_zero l)
  ⟩

instance TT.CoestdSimplex : CoeOut (TT n l) (stdSimplex ℝ (Fin n)) where
  coe := TTtostdSimplex


variable {n l} in
abbrev TT.Ilt (x y : TT n l) :=
  toLex (x i, x.1) < toLex (y i, y.1)

variable {n l} in
instance TT.ILO : IndexedLOrder (Fin n) (TT n l) where
  IST := fun i => LinearOrder.lift' (fun x : TT n l => toLex (x i, x.1)) (by
    intro a b h
    have hp : (a i, a.1) = (b i, b.1) := congrArg ofLex h
    exact Subtype.ext (congrArg Prod.snd hp))

set_option quotPrecheck false
local notation  lhs "<[" i "]" rhs => (IndexedLOrder.IST i).lt lhs rhs
local notation  lhs "≤[" i "]" rhs => (IndexedLOrder.IST i).le lhs rhs

lemma TT.Ilt_def (a b : TT n l) :
  (a <[i] b) ↔ TT.Ilt i a b := by
  rfl

lemma TT.Ilt_keyprop (a b : TT n l) :
  a i < b i → a <[i] b := by
  intro h
  change toLex (a i, a.1) < toLex (b i, b.1)
  rw [Prod.Lex.lt_iff]
  exact Or.inl h

lemma size_bound_key (sigma : Finset (TT n l)) (C : Finset (Fin n)) (h : TT.ILO.isDominant sigma C)
(h2 : sigma.Nonempty):
  l < ∑ k ∈ C, (sigma.image (fun x => (x k : ℕ))).min' (Finset.image_nonempty.mpr h2) + C.card := by
  by_contra h_not
  push Not at h_not
  let m := fun k => (sigma.image (fun x => (x k : ℕ))).min' (Finset.image_nonempty.mpr h2)
  have h_sum_bound : ∑ k ∈ C, m k + C.card ≤ l := h_not
  have h_sum_plus_one : ∑ k ∈ C, (m k + 1) ≤ l := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_one]
    exact h_sum_bound
  have h_exists_point : ∃ M : TT n l, ∀ k ∈ C, m k + 1 ≤ M k := by
    let M' : Fin n → ℕ := fun k => if k ∈ C then m k + 1 else 0
    let S := ∑ k, M' k
    have h_S_le_l : S ≤ l := by
      simp [S, M', h_sum_plus_one]
    let R := l - S
    let M_coords : Fin n → ℕ := fun k => if k = (0 : Fin n) then M' 0 + R else M' k
    have h_M_coords_sum : ∑ k, M_coords k = l := by
      have h1 : S = M' 0 + ∑ k ∈ (Finset.univ : Finset (Fin n)).erase 0, M' k := by
        simp [S]
        rw [← Finset.sum_insert (Finset.notMem_erase 0 Finset.univ)]
        rw [Finset.insert_erase (Finset.mem_univ 0)]
      have : ∑ k, M_coords k = M_coords 0 + ∑ k ∈ (Finset.univ : Finset (Fin n)).erase 0, M_coords k := by
        rw [← Finset.sum_insert (Finset.notMem_erase 0 Finset.univ)]
        rw [Finset.insert_erase (Finset.mem_univ 0)]
      rw [this]
      simp only [M_coords, if_true]
      have sum_eq : ∑ x ∈ Finset.univ.erase 0, (if x = 0 then M' 0 + R else M' x) = ∑ x ∈ Finset.univ.erase 0, M' x := by
        apply Finset.sum_congr rfl
        intro k hk
        simp only [if_neg (Finset.ne_of_mem_erase hk)]
      rw [sum_eq, add_comm (M' 0) R, add_assoc, ← h1]
      simp only [R]
      have hM'0_le_S : M' 0 ≤ S := by
        have : M' 0 ≤ ∑ k, M' k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
        exact this
      omega

    have h_M_coords_bound : ∀ k, M_coords k ≤ l := by
      intro k
      by_cases h_is_zero : k = 0
      · simp [h_is_zero, M_coords, R]
        have hM'0_le_S : M' 0 ≤ S := by
          have : M' 0 ≤ ∑ k, M' k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
          exact this
        omega
      · simp [h_is_zero, M_coords]
        by_cases hk_in_C : k ∈ C
        · simp [M', hk_in_C]; exact Nat.le_trans (Finset.single_le_sum (fun k _ => Nat.zero_le (m k + 1)) hk_in_C) h_sum_plus_one
        · simp [M', hk_in_C]
    let M_val : Fin n → Fin (l + 1) := fun k => ⟨M_coords k, Nat.lt_succ_of_le (h_M_coords_bound k)⟩
    use ⟨M_val, by simp [M_val, h_M_coords_sum]⟩
    intro k hk_in_C
    change m k < M_coords k
    by_cases h_is_zero : k = 0
    · subst k
      dsimp [M_coords, M']
      simp [hk_in_C]
      omega
    · dsimp [M_coords, M']
      simp [h_is_zero, hk_in_C]
  obtain ⟨M, hM⟩ := h_exists_point
  have h_min_less : ∀ k ∈ C, ∃ x_min ∈ sigma, ∀ x ∈ sigma, x_min ≤[k] x := by
    intro k _
    letI : LinearOrder (TT n l) := IndexedLOrder.IST k
    let x_min := sigma.min' h2
    use x_min
    constructor
    · exact Finset.min'_mem sigma h2
    · intro x hx
      exact Finset.min'_le sigma x hx
  have h_contradiction : ∀ k ∈ C, ∃ x_min ∈ sigma, x_min <[k] M := by
    intro k hk_in_C
    letI : LinearOrder (TT n l) := IndexedLOrder.IST k
    let x_min := sigma.min' h2
    use x_min
    constructor
    · exact Finset.min'_mem sigma h2
    · apply TT.Ilt_keyprop
      have h_min_coord : (x_min k : ℕ) = (sigma.image (fun x => (x k : ℕ))).min' (Finset.image_nonempty.mpr h2) := by
        symm
        apply le_antisymm
        · apply Finset.min'_le
          apply Finset.mem_image_of_mem
          exact Finset.min'_mem sigma h2
        · apply Finset.le_min'
          intro y hy
          rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
          have h_x_min_le_x : x_min ≤[k] x := Finset.min'_le sigma x hx
          by_cases h_case : (x_min k : ℕ) ≤ (x k : ℕ)
          · exact h_case
          · exfalso
            push Not at h_case
            have h_x_lt_min : x <[k] x_min := by
              apply TT.Ilt_keyprop
              exact h_case
            exact not_lt.mpr h_x_min_le_x h_x_lt_min
      have h_nat_lt : (x_min k : ℕ) < (M k : ℕ) := by
        rw [h_min_coord]
        exact Nat.lt_of_succ_le (hM k hk_in_C)
      exact h_nat_lt
  have h_not_dominant : ¬ TT.ILO.isDominant sigma C := by
    intro hdom
    rcases hdom M with ⟨k, hk, hall⟩
    rcases h_contradiction k hk with ⟨x, hx, hlt⟩
    exact (@not_le_of_gt (TT n l) (IndexedLOrder.IST k).toPreorder x M hlt) (hall x hx)
  exact h_not_dominant h



theorem size_bound_in (sigma : Finset (TT n l)) (C : Finset (Fin n)) (h : TT.ILO.isDominant sigma C):
    ∀ x ∈ sigma, ∀ y ∈ sigma, ∀ i : Fin n, abs ((x i : ℤ) - (y i : ℤ)) < 2 * (n + 1)
    := by
  by_cases hsigma : sigma.Nonempty
  · intro x hx y hy i
    let m k := (sigma.image (fun z => (z k : ℕ))).min' (Finset.image_nonempty.mpr hsigma)
    let m' i := if h_i : i ∈ C then m i else 0
    have h_le_l_sub_sum : (l : ℕ) - ∑ k ∈ C, m k < C.card := by
      have h_key : l < ∑ k ∈ C, m k + C.card := size_bound_key n l sigma C h hsigma
      have h_sum_le_l : ∑ k ∈ C, m k ≤ l := by
        rcases hsigma with ⟨x, hx⟩
        have h_m_le : ∀ k ∈ C, m k ≤ (x k : ℕ) := fun k _ =>
          Finset.min'_le (sigma.image (fun z => (z k : ℕ))) (x k : ℕ) (Finset.mem_image_of_mem (fun z => (z k : ℕ)) hx)
        calc
          ∑ k ∈ C, m k ≤ ∑ k ∈ C, (x k : ℕ) := Finset.sum_le_sum h_m_le
          _ ≤ ∑ k, (x k : ℕ) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C) (by simp)
          _ = l := x.2
      rw [Nat.sub_lt_iff_lt_add h_sum_le_l, add_comm]
      exact h_key
    have h_bound : ∀ z ∈ sigma, (z i : ℕ) - m' i < C.card := by
      intro z hz
      by_cases hi_in_C : i ∈ C
      · simp [m', hi_in_C]
        have h_mi_le_zi : m i ≤ (z i : ℕ) := by
          apply Finset.min'_le
          apply Finset.mem_image_of_mem
          exact hz
        have h_zi_le_sum : (z i : ℕ) ≤ ∑ k ∈ C, (z k : ℕ) :=
          Finset.single_le_sum (fun k _ => Nat.zero_le (z k : ℕ)) hi_in_C
        have h_sum_z_le_l : ∑ k ∈ C, (z k : ℕ) ≤ l := by
          calc ∑ k ∈ C, (z k : ℕ) ≤ ∑ k, (z k : ℕ) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C) (by simp)
          _ = l := z.2
        have h_diff_bound : (z i : ℕ) - m i ≤ l - ∑ k ∈ C, m k := by
          calc
          (z i : ℕ) - m i ≤ ∑ k ∈ C, ((z k : ℕ) - m k) :=
            Finset.single_le_sum (fun k _ => Nat.zero_le ((z k : ℕ) - m k)) hi_in_C
          _ = (∑ k ∈ C, (z k : ℕ)) - (∑ k ∈ C, m k) := by
            rw [Finset.sum_tsub_distrib]
            intro k hk
            apply Finset.min'_le
            apply Finset.mem_image_of_mem
            exact hz
          _ ≤ l - ∑ k ∈ C, m k := by
            apply Nat.sub_le_sub_right
            calc
              ∑ k ∈ C, (z k : ℕ) ≤ ∑ k, (z k : ℕ) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C) (by simp)
              _ = l := z.2
        exact lt_of_le_of_lt h_diff_bound h_le_l_sub_sum

      · simp [m', hi_in_C]
        have h_sum_le : (z i : ℕ) + ∑ k ∈ C, (z k : ℕ) ≤ l := by
          calc
            (z i : ℕ) + ∑ k ∈ C, (z k : ℕ) = ∑ k ∈ insert i C, (z k : ℕ) := by
              rw [Finset.sum_insert hi_in_C]
            _ ≤ ∑ k, (z k : ℕ) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by simp)
            _ = l := z.2
        have h_le_sub : (z i : ℕ) ≤ l - ∑ k ∈ C, (z k : ℕ) := Nat.le_sub_of_add_le h_sum_le
        have h_m_le_z : ∑ k ∈ C, m k ≤ ∑ k ∈ C, (z k : ℕ) := by
          apply Finset.sum_le_sum
          intro k hk
          apply Finset.min'_le
          apply Finset.mem_image_of_mem
          exact hz
        have h_sub_le_sub : l - ∑ k ∈ C, (z k : ℕ) ≤ l - ∑ k ∈ C, m k :=
          Nat.sub_le_sub_left h_m_le_z l
        exact lt_of_le_of_lt (h_le_sub.trans h_sub_le_sub) h_le_l_sub_sum
    have h_nonneg : ∀ z ∈ sigma, 0 ≤ (z i : ℤ) - (m' i : ℤ) := by
      intro z hz
      by_cases hi_in_C : i ∈ C
      · simp [m', hi_in_C]
        have h_min_le : m i ≤ ↑(z i) := by
          apply Finset.min'_le
          apply Finset.mem_image_of_mem
          exact hz
        exact_mod_cast h_min_le
      · simp [m', hi_in_C]

    have h_abs_lt_2_card : abs ((x i : ℤ) - (y i : ℤ)) < 2 * (C.card : ℤ) := by
      have h_bound_int : ∀ z ∈ sigma, (z i : ℤ) - (m' i : ℤ) < C.card := by
        intro z hz
        have := h_bound z hz
        simp only [m'] at this ⊢
        split_ifs at this ⊢ with h_case
        · have : (z i : ℕ) - m i < C.card := this
          simp
          have h_le : m i ≤ (z i : ℕ) := by
            apply Finset.min'_le
            apply Finset.mem_image_of_mem
            exact hz
          exact (Int.ofNat_sub h_le) ▸ (Int.ofNat_lt.mpr this)
        · simp only [Int.ofNat_zero, sub_zero]
          exact Int.ofNat_lt.mpr this
      calc
        abs ((x i : ℤ) - (y i : ℤ)) = abs (((x i : ℤ) - (m' i : ℤ)) - ((y i : ℤ) - (m' i : ℤ))) := by rw [sub_sub_sub_cancel_right]
        _ ≤ abs ((x i : ℤ) - (m' i : ℤ)) + abs ((y i : ℤ) - (m' i : ℤ)) := abs_sub _ _
        _ = ((x i : ℤ) - (m' i : ℤ)) + ((y i : ℤ) - (m' i : ℤ)) := by
          rw [abs_of_nonneg (h_nonneg x hx), abs_of_nonneg (h_nonneg y hy)]
        _ < (C.card : ℤ) + (C.card : ℤ) := by
          apply add_lt_add (h_bound_int x hx) (h_bound_int y hy)
        _ = 2 * (C.card : ℤ) := by rw [two_mul]
    have h_card_le_n : C.card ≤ n :=
      calc
        C.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ C)
        _ = n := by simp
    apply lt_trans h_abs_lt_2_card
    have : (2 * (C.card : ℤ)) < 2 * (n + 1 : ℤ) := by
      linarith [Int.ofNat_le.mpr h_card_le_n]
    exact this
  · intro x hx y hy i
    exfalso
    exact hsigma ⟨x, hx⟩

theorem size_bound_out (sigma : Finset (TT n l)) (C : Finset (Fin n)) (h : TT.ILO.isDominant sigma C):
    ∀ x ∈ sigma, ∀ i ∉ C, (x i : ℤ) < n + 1
    := by
  by_cases hsigma : sigma.Nonempty
  · intro x hx i hi_not_C
    let m k := (sigma.image (fun z => (z k : ℕ))).min' (Finset.image_nonempty.mpr hsigma)
    have h_le_l_sub_sum : l - ∑ k ∈ C, m k < C.card := by
      have h_sum_le_l : ∑ k ∈ C, m k ≤ l := by
        rcases hsigma with ⟨x, hx⟩
        have h_m_le : ∀ k ∈ C, m k ≤ (x k : ℕ) := fun k _ =>
          Finset.min'_le (sigma.image (fun z => (z k : ℕ))) (x k : ℕ) (Finset.mem_image_of_mem (fun z => (z k : ℕ)) hx)
        calc
          ∑ k ∈ C, m k ≤ ∑ k ∈ C, (x k : ℕ) := Finset.sum_le_sum h_m_le
          _ ≤ ∑ k, (x k : ℕ) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C) (by simp)
          _ = l := x.2
      rw [Nat.sub_lt_iff_lt_add h_sum_le_l, add_comm]
      exact size_bound_key n l sigma C h hsigma
    have h_bound : (x i : ℕ) < C.card := by
      have h_sum_le : (x i : ℕ) + ∑ k ∈ C, (x k : ℕ) ≤ l := by
        calc
          (x i : ℕ) + ∑ k ∈ C, (x k : ℕ) = ∑ k ∈ insert i C, (x k : ℕ) := by
            rw [Finset.sum_insert hi_not_C]
          _ ≤ ∑ k, (x k : ℕ) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by simp)
          _ = l := x.2
      have h_le_sub : (x i : ℕ) ≤ l - ∑ k ∈ C, (x k : ℕ) := Nat.le_sub_of_add_le h_sum_le
      have h_m_le_x : ∑ k ∈ C, m k ≤ ∑ k ∈ C, (x k : ℕ) := by
        apply Finset.sum_le_sum
        intro k _
        apply Finset.min'_le
        apply Finset.mem_image_of_mem
        exact hx
      have h_sub_le_sub : l - ∑ k ∈ C, (x k : ℕ) ≤ l - ∑ k ∈ C, m k :=
        Nat.sub_le_sub_left h_m_le_x l
      exact lt_of_le_of_lt (h_le_sub.trans h_sub_le_sub) h_le_l_sub_sum
    have h_card_le_n : C.card ≤ n := by
      calc
        C.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ C)
        _ = n := by simp [Fintype.card_fin]
    have h_lt_n : (x i : ℤ) < ↑n := by
      apply lt_of_lt_of_le
      · exact Int.ofNat_lt.mpr h_bound
      · exact Int.ofNat_le.mpr h_card_le_n
    linarith
  · intro x hx
    exfalso
    exact hsigma ⟨x, hx⟩

section Brouwer



variable (f : stdSimplex ℝ (Fin n) → stdSimplex ℝ (Fin n))

variable {n l}

instance stdSimplex.upidx (x y : stdSimplex ℝ (Fin n)) : Nonempty { i | x.1 i ≤ y.1 i} := by
  by_contra h
  push Not at h
  have sum_x_eq_1 := x.2.2
  have sum_y_eq_1 := y.2.2
  have sum_lt : Finset.sum Finset.univ y.1 < Finset.sum Finset.univ x.1 := by
    apply Finset.sum_lt_sum_of_nonempty
    . exact Finset.univ_nonempty
    . intro i _
      have : ¬ (x.1 i ≤ y.1 i) := by
        intro hle
        exact h.elim ⟨i, hle⟩
      exact lt_of_not_ge this
  rw [sum_y_eq_1, sum_x_eq_1] at sum_lt
  exact (lt_irrefl 1 sum_lt).elim


noncomputable def stdSimplex.pick (x  y : stdSimplex ℝ (Fin n)) := Classical.choice $ stdSimplex.upidx x y



def Fcolor (x : TT n l) : Fin n := stdSimplex.pick x (f x)

def room_seq (l' : ℕ) :=
  let l : PNat := ⟨l'+1,Nat.zero_lt_succ _⟩
  Classical.choice (TT.ILO.Scarf (@Fcolor n l f)).to_subtype

def room_point_seq (l' : ℕ) := pick_colorful_point
(Finset.mem_filter.1 (room_seq f l').2).2 |>.1



section finiteness


def mk_subseq (f : ℕ → ℕ) (h : ∀ n, n < f n) : ℕ → ℕ
  | 0 => f 0
  | n+1 => f (mk_subseq f h n)

theorem exists_subseq_constant_of_finite_image {s : Finset α} (e : ℕ → α) (he : ∀ n, e n ∈ s ) :
  ∃ a ∈ s, ∃ g : ℕ ↪o ℕ,  (∀ n, e (g n) = a) := by

  have range_subset : Set.range e ⊆ (s : Set α) := Set.range_subset_iff.mpr he
  have range_finite : (Set.range e).Finite := s.finite_toSet.subset range_subset
  let imgs : Finset α := Finset.filter (fun a => ¬(Set.Finite (e ⁻¹' {a}))) s
  have imgs_nonempty : imgs.Nonempty := by
    by_contra h
    simp only [Finset.not_nonempty_iff_eq_empty] at h
    have preimages_all_finite : ∀ a ∈ s, Set.Finite (e ⁻¹' {a}) := by
      intro a ha
      by_contra hnf
      have a_in_imgs : a ∈ imgs := by
        simp only [imgs, Finset.mem_filter, ha, true_and]
        exact hnf
      have : imgs ≠ ∅ := Finset.ne_empty_of_mem a_in_imgs
      contradiction
    have nat_finite : Set.Finite (Set.univ : Set ℕ) := by
      have univ_eq : Set.univ = e ⁻¹' (s : Set α) := by ext n; simp [he]
      rw [univ_eq]
      have : e ⁻¹' (s : Set α) = ⋃ a ∈ s, e ⁻¹' {a} := by
        ext n; simp [ Set.mem_preimage]
      rw [this]
      exact Set.Finite.biUnion s.finite_toSet preimages_all_finite
    exact Set.infinite_univ nat_finite

  obtain ⟨a, a_in_imgs⟩ := imgs_nonempty
  have a_in_s : a ∈ s := (Finset.mem_filter.1 a_in_imgs).1
  have a_infinite_preimage : ¬Set.Finite (e ⁻¹' {a}) := (Finset.mem_filter.1 a_in_imgs).2

  use a, a_in_s
  let preimage := e ⁻¹' {a}
  have preimage_infinite : Set.Infinite preimage := a_infinite_preimage

  have h_nonempty : preimage.Nonempty := by
    by_contra h_empty
    rw [Set.not_nonempty_iff_eq_empty] at h_empty
    rw [h_empty] at preimage_infinite
    exact Set.finite_empty.not_infinite preimage_infinite
  obtain ⟨m₀, hm₀⟩ := h_nonempty
  have h_exists_larger : ∀ k : ℕ, ∃ m ∈ preimage, k < m := by
    intro k
    by_contra h_not
    push Not at h_not
    have : preimage ⊆ {n | n ≤ k} := fun n hn => h_not n hn
    have h_finite : Set.Finite preimage := (Set.finite_le_nat k).subset this
    exact preimage_infinite h_finite
  choose f hf using h_exists_larger
  have f_lt : ∀ n : ℕ, n < f n := fun n => (hf n).2
  have f_in : ∀ n : ℕ, f n ∈ preimage := fun n => (hf n).1
  let g := mk_subseq f f_lt
  have hg_in : ∀ n, g n ∈ preimage := by
    intro n
    induction' n with n ih
    · simp [g, mk_subseq]; exact f_in 0
    · simp [g, mk_subseq]; exact f_in (g n)
  have hg_strict : StrictMono g := by
    intro m n hmn
    induction' hmn with n hmn ih
    · simp [g, mk_subseq]
      exact f_lt (g m)
    · simp [g, mk_subseq]
      exact lt_trans ih (f_lt (g n))
  use OrderEmbedding.ofStrictMono g hg_strict
  intro n
  exact hg_in n

end finiteness

lemma constant_index_set_nonempty : Nonempty {(a, g) :(Finset (Fin n)) × (ℕ ↪o ℕ) | ∀ l', (room_seq f (g l')).1.2 = a } := by
  obtain ⟨a, ha,g,hg⟩ := exists_subseq_constant_of_finite_image (s := Finset.univ)
    (fun x => (room_seq f x).1.2) (by simp)
  use ⟨a,g⟩; simp [hg]



def gpkg :=  Classical.choice $ constant_index_set_nonempty f

abbrev g1 := gpkg f |>.1.2


open Topology
open Filter



lemma dominant_coords_tend_to_zero (f : stdSimplex ℝ (Fin n) → stdSimplex ℝ (Fin n)) (C : Finset (Fin n)) (g : ℕ ↪o ℕ) (h_const : ∀ l', (room_seq f (g l')).1.2 = C) :
  ∀ i ∉ C, Filter.Tendsto (fun l' => ((room_point_seq f (g l')) : stdSimplex ℝ (Fin n)).1 i) Filter.atTop (𝓝 0) := by
  intro i hiC
  have h_tendsto_bound : Filter.Tendsto (fun l' => ((n : ℝ) + 1) / ((g l' : ℝ) + 1)) Filter.atTop (𝓝 0) := by
    have h_denom_tendsto : Filter.Tendsto (fun l' => (g l' : ℝ) + 1) Filter.atTop Filter.atTop := by
      have g_tendsto : Filter.Tendsto (fun l' => g l') Filter.atTop Filter.atTop := by
        apply Filter.tendsto_atTop_atTop.mpr
        intro b
        use b
        intro l' hl'
        exact le_trans hl' (StrictMono.id_le g.strictMono l')
      have cast_tendsto : Filter.Tendsto (fun l' => (g l' : ℝ)) Filter.atTop Filter.atTop :=
        Filter.Tendsto.comp tendsto_natCast_atTop_atTop g_tendsto
      exact Tendsto.atTop_add cast_tendsto (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
    have : Tendsto (fun l' => ((n : ℝ) + 1) / ((g l' : ℝ) + 1)) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds h_denom_tendsto
    exact this
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) h_tendsto_bound
  · intro l'
    exact ((room_point_seq f (g l')) : stdSimplex ℝ (Fin n)).2.1 i
  · intro l'
    let l_pnat : PNat := ⟨g l' + 1, Nat.succ_pos _⟩
    let rs := room_seq f (g l')
    let sigma := rs.1.1
    let C_l := rs.1.2
    have h_C_l : C_l = C := h_const l'
    have hiC_l : i ∉ C_l := h_C_l ▸ hiC
    let x := room_point_seq f (g l')
    let colorful_proof := (Finset.mem_filter.mp rs.2).2
    have hx_mem : x ∈ sigma := (pick_colorful_point colorful_proof).2
    have h_dom : TT.ILO.isDominant sigma C_l := colorful_proof.1
    have h_bound := size_bound_out n l_pnat sigma C_l h_dom x hx_mem i hiC_l
    simp only [TTtostdSimplex, Subtype.coe_mk]
    have h_eq : (↑l_pnat : ℝ) = ↑(g l') + 1 := by simp [l_pnat, PNat.mk_coe]
    rw [h_eq]
    rw [div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < ↑(g l') + 1)]
    have h_bound_real : ((x i : ℕ) : ℝ) < (↑n + 1 : ℝ) := by
      exact_mod_cast Nat.lt_succ_of_le (Int.ofNat_le.mp (Int.le_of_lt_add_one h_bound))
    exact le_of_lt h_bound_real

@[reducible]
def hpkg_aux :
  Nonempty {(z , h) : (stdSimplex ℝ  (Fin n)) × (ℕ → ℕ) | StrictMono h ∧ Filter.Tendsto
    ((fun l' => (room_point_seq f (g1 f l'): stdSimplex ℝ (Fin n))) ∘ h)
    Filter.atTop (𝓝 z) } := by
  let u := fun l' : ℕ => (room_point_seq f (g1 f l') : stdSimplex ℝ (Fin n))
  have h_compact : IsCompact (Set.univ : Set (stdSimplex ℝ (Fin n))) := isCompact_univ
  have h_in_univ : ∀ n, u n ∈ Set.univ := fun _ => Set.mem_univ _
  obtain ⟨z, hz, φ, φ_mono, h_tendsto⟩ := h_compact.tendsto_subseq h_in_univ
  use ⟨z, φ⟩
  exact ⟨φ_mono, h_tendsto⟩

def hpkg := Classical.choice  (hpkg_aux f)



theorem tendsto_diam_to_zero (f : stdSimplex ℝ (Fin n) → stdSimplex ℝ (Fin n)) :
  Tendsto (fun k =>
    Metric.diam
      (((room_seq f (g1 f ((hpkg f).1.2 k))).1.1.image
        (fun x => TTtostdSimplex x) : Finset (stdSimplex ℝ (Fin n))) :
          Set (stdSimplex ℝ (Fin n)))) atTop (𝓝 0) := by
  let l k := g1 f ((hpkg f).1.2 k)
  let sigma k := (room_seq f (l k)).1.1
  let projected_sigma k := (sigma k).image (fun x => TTtostdSimplex x)
  have h_diam_bounded : ∃ (C : ℝ), ∀ k,
      Metric.diam ((projected_sigma k : Finset (stdSimplex ℝ (Fin n))) :
        Set (stdSimplex ℝ (Fin n))) ≤ C / (l k + 1) := by
    use 2 * Real.sqrt (n : ℝ) * ((n : ℝ) + 1)
    intro k
    let l_pnat : PNat := ⟨l k + 1, Nat.succ_pos _⟩
    let rs := room_seq f (l k)
    let C_k := rs.1.2
    have h_dom : TT.ILO.isDominant (sigma k) C_k := (Finset.mem_filter.mp rs.2).2.1
    have h_coord_bound : ∀ x ∈ (sigma k), ∀ y ∈ (sigma k), ∀ i : Fin n,
        abs (((TTtostdSimplex x).1 i : ℝ) - ((TTtostdSimplex y).1 i : ℝ)) < 2 * ((n : ℝ) + 1) / (l k + 1) := by
      intro x hx y hy i
      have h_bound_int := size_bound_in n l_pnat (sigma k) C_k h_dom x hx y hy i
      simp only [TTtostdSimplex]
      rw [← sub_div]
      rw [abs_div]
      have h_pos : (0 : ℝ) < l_pnat := by positivity
      rw [abs_of_pos h_pos]
      have h_eq : (l_pnat : ℝ) = l k + 1 := by simp [l_pnat, PNat.mk_coe]
      rw [h_eq]
      rw [div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < l k + 1)]
      exact_mod_cast h_bound_int
    have h_dist_bound : ∀ x ∈ (sigma k), ∀ y ∈ (sigma k),
        dist (TTtostdSimplex x) (TTtostdSimplex y) ≤ 2 * Real.sqrt (n : ℝ) * ((n : ℝ) + 1) / (l k + 1) := by
      intro x hx y hy
      have h_coord_diff_le : ∀ i, |(TTtostdSimplex x).1 i - (TTtostdSimplex y).1 i| ≤ 2 * (↑n + 1) / (↑(l k) + 1) :=
        fun i => le_of_lt (h_coord_bound x hx y hy i)
      calc dist (TTtostdSimplex x) (TTtostdSimplex y)
        = ‖(TTtostdSimplex x).1 - (TTtostdSimplex y).1‖ := rfl
      _ ≤ 2 * (↑n + 1) / (l k + 1) := by
          rw [pi_norm_le_iff_of_nonneg (by positivity)]
          exact h_coord_diff_le
      _ ≤ 2 * Real.sqrt (n : ℝ) * ((n : ℝ) + 1) / (l k + 1) := by
          rw [div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < l k + 1)]
          have h_assoc : 2 * Real.sqrt (n : ℝ) * ((n : ℝ) + 1) = 2 * (Real.sqrt (n : ℝ) * ((n : ℝ) + 1)) := by ring
          rw [h_assoc]
          have hsqrt : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
            apply Real.one_le_sqrt.mpr
            norm_cast
            exact PNat.one_le n
          have hmul := mul_le_mul_of_nonneg_left hsqrt (by positivity : 0 ≤ 2 * ((n : ℝ) + 1))
          nlinarith
    apply Metric.diam_le_of_forall_dist_le (by positivity)
    intro x hx y hy
    rcases Finset.mem_image.mp hx with ⟨x', hx', rfl⟩
    rcases Finset.mem_image.mp hy with ⟨y', hy', rfl⟩
    exact h_dist_bound x' hx' y' hy'
  rcases h_diam_bounded with ⟨C, hC_bound⟩
  have h_l_tends_to_inf : Tendsto (fun k => (l k : ℝ) + 1) atTop atTop := by
    have h_l_mono : StrictMono l := (g1 f).strictMono.comp (hpkg f).2.1
    have h_l_tends_nat : Tendsto l atTop atTop := h_l_mono.tendsto_atTop
    have h_l_tends_real : Tendsto (fun k => (l k : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp h_l_tends_nat
    exact Tendsto.atTop_add h_l_tends_real tendsto_const_nhds
  have h_C_div_l_tends_to_zero : Tendsto (fun k => C / (l k + 1)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop h_l_tends_to_inf
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds : Tendsto (fun _ => (0:ℝ)) atTop (𝓝 0)) h_C_div_l_tends_to_zero (fun _ => Metric.diam_nonneg) hC_bound

theorem f_coords_ge_z_coords (f : stdSimplex ℝ (Fin n) → stdSimplex ℝ (Fin n)) (hf : Continuous f) :
  ∀ i ∈ (gpkg f).1.1, (f (hpkg f).1.1).1 i ≥ ((hpkg f).1.1).1 i := by
      let z := (hpkg f).1.1
      let C := (gpkg f).1.1
      let φ := (hpkg f).1.2
      have convergence_to_z : Filter.Tendsto ((fun l' => (room_point_seq f (g1 f l'): stdSimplex ℝ (Fin n))) ∘ φ) Filter.atTop (𝓝 z) := by
        exact (hpkg f).2.2
      have constant_color_set : ∀ l', (room_seq f (g1 f l')).1.2 = C := by
        exact (gpkg f).2
      intro idx h_idx_C
      have h_exists_point : ∀ l', ∃ y,
        y ∈ (room_seq f (g1 f l')).1.1 ∧
        (let l_pnat : PNat := ⟨(g1 f) l' + 1, by simp⟩; @Fcolor n l_pnat f y) = idx := by
        intro l'
        let l_pnat : PNat := ⟨(g1 f) l' + 1, by simp⟩
        let rs := room_seq f (g1 f l')
        let sigma := rs.1.1
        let C_l := rs.1.2
        have h_C_l : C_l = C := constant_color_set l'
        let colorful_proof := (Finset.mem_filter.mp rs.2).2
        have h_image_eq : sigma.image (@Fcolor n l_pnat f) = C_l := colorful_proof.2
        have h_idx_in_C_l : idx ∈ C_l := h_C_l ▸ h_idx_C
        have h_idx_in_image : idx ∈ sigma.image (@Fcolor n l_pnat f) := by
          rw [h_image_eq]; exact h_idx_in_C_l
        rw [Finset.mem_image] at h_idx_in_image
        obtain ⟨y, hy_in_sigma, hy_color⟩ := h_idx_in_image
        use y

      let y_seq := fun l' => TTtostdSimplex (h_exists_point l').choose
      have y_seq_spec : ∀ l',
        (h_exists_point l').choose ∈ (room_seq f (g1 f l')).1.1 ∧
        (let l_pnat : PNat := ⟨(g1 f) l' + 1, by simp⟩; @Fcolor n l_pnat f (h_exists_point l').choose) = idx := by
        intro l'
        exact (h_exists_point l').choose_spec

      have h_ineq : ∀ l', (f (y_seq l')).1 idx ≥ (y_seq l').1 idx := by
        intro l'
        have h_spec := y_seq_spec l'
        simp [y_seq] at h_spec ⊢
        let chosen_point := (h_exists_point l').choose
        have h_color : (let l_pnat : PNat := ⟨(g1 f) l' + 1, by simp⟩; @Fcolor n l_pnat f chosen_point) = idx := h_spec.2
        let l_pnat : PNat := ⟨(g1 f) l' + 1, by simp⟩
        unfold Fcolor at h_color
        have h_pick_property : ∃ h : Nonempty {i | (chosen_point : stdSimplex ℝ (Fin n)).1 i ≤ (f (chosen_point : stdSimplex ℝ (Fin n))).1 i},
          @Classical.choice _ h = idx := by
          rw [← h_color]
          use stdSimplex.upidx (chosen_point : stdSimplex ℝ (Fin n)) (f (chosen_point : stdSimplex ℝ (Fin n)))
          rfl
        obtain ⟨h_nonempty, h_choice_eq⟩ := h_pick_property
        have h_mem : idx ∈ {i | (chosen_point : stdSimplex ℝ (Fin n)).1 i ≤ (f (chosen_point : stdSimplex ℝ (Fin n))).1 i} := by
          let choice_prop := Classical.choice h_nonempty
          have : idx = choice_prop.val := h_choice_eq.symm
          rw [this]
          exact choice_prop.property
        exact h_mem

      have y_seq_φ_converges_to_z : Filter.Tendsto (y_seq ∘ φ) Filter.atTop (𝓝 z) := by
        have h_dist_tends_to_zero : Filter.Tendsto (fun k => dist (y_seq (φ k)) ((fun l' => (room_point_seq f (g1 f l') : stdSimplex ℝ (Fin n))) (φ k))) Filter.atTop (𝓝 0) := by
          have h_bound : ∀ k, dist (y_seq (φ k)) ((room_point_seq f (g1 f (φ k)) : stdSimplex ℝ (Fin n))) ≤
                Metric.diam
                  (((room_seq f (g1 f (φ k))).1.1.image
                    (fun x => TTtostdSimplex x) : Finset (stdSimplex ℝ (Fin n))) :
                      Set (stdSimplex ℝ (Fin n))) := by
            intro k
            apply Metric.dist_le_diam_of_mem
            · exact Set.Finite.isBounded
                (((room_seq f (g1 f (φ k))).1.1.image
                  (fun x => TTtostdSimplex x)).finite_toSet)
            · exact Finset.mem_image_of_mem TTtostdSimplex (y_seq_spec (φ k)).1
            · exact Finset.mem_image_of_mem TTtostdSimplex (pick_colorful_point ((Finset.mem_filter.1 (room_seq f (g1 f (φ k))).2).2)).2
          have h_diam_tendsto : Tendsto (fun k =>
              Metric.diam
                (((room_seq f (g1 f (φ k))).1.1.image TTtostdSimplex :
                  Finset (stdSimplex ℝ (Fin n))) : Set (stdSimplex ℝ (Fin n)))) atTop
              (𝓝 0) := by
            exact tendsto_diam_to_zero f
          exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_diam_tendsto
            (Eventually.of_forall (fun _ => dist_nonneg)) (Eventually.of_forall h_bound)
        rw [Metric.tendsto_nhds]
        intro ε hε
        have h1 := (Metric.tendsto_nhds.1 convergence_to_z) (ε / 2) (half_pos hε)
        have h2 := (Metric.tendsto_nhds.1 h_dist_tends_to_zero) (ε / 2) (half_pos hε)
        apply (h1.and h2).mono
        intro k ⟨hk1, hk2⟩
        calc dist (y_seq (φ k)) z
          ≤ dist (y_seq (φ k)) ((room_point_seq f (g1 f (φ k)) : stdSimplex ℝ (Fin n)))
            + dist ((room_point_seq f (g1 f (φ k)) : stdSimplex ℝ (Fin n))) z := dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := add_lt_add (by simp at hk2; exact hk2) hk1
        _ = ε := add_halves ε

      have f_y_seq_φ_converges_to_f_z : Filter.Tendsto (f ∘ y_seq ∘ φ) Filter.atTop (𝓝 (f z)) := by
        exact hf.continuousAt.tendsto.comp y_seq_φ_converges_to_z
      have f_y_seq_φ_coord_converges : Filter.Tendsto (fun l' => (f (y_seq (φ l'))).1 idx) Filter.atTop (𝓝 ((f z).1 idx)) := by
        have h_continuous : Continuous (fun x : stdSimplex ℝ (Fin n) => x.1 idx) :=
          Continuous.comp (continuous_apply idx) continuous_subtype_val
        exact h_continuous.continuousAt.tendsto.comp f_y_seq_φ_converges_to_f_z
      have y_seq_φ_coord_converges : Filter.Tendsto (fun l' => (y_seq (φ l')).1 idx) Filter.atTop (𝓝 (z.1 idx)) := by
        have h_continuous : Continuous (fun x : stdSimplex ℝ (Fin n) => x.1 idx) :=
          Continuous.comp (continuous_apply idx) continuous_subtype_val
        exact h_continuous.continuousAt.tendsto.comp y_seq_φ_converges_to_z

      exact le_of_tendsto_of_tendsto y_seq_φ_coord_converges f_y_seq_φ_coord_converges (Eventually.of_forall (fun l' => h_ineq (φ l')))

theorem Brouwer (hf : Continuous f): ∃ x , f x = x := by
  let z := (hpkg f).1.1
  let C := (gpkg f).1.1
  let φ := (hpkg f).1.2

  use z

  have h_tendsto_diam := tendsto_diam_to_zero f

  have convergence_to_z : Filter.Tendsto ((fun l' => (room_point_seq f (g1 f l'): stdSimplex ℝ (Fin n))) ∘ φ) Filter.atTop (𝓝 z) :=
    (hpkg f).2.2

  have constant_color_set : ∀ l', (room_seq f (g1 f l')).1.2 = C :=
    (gpkg f).2

  have coords_outside_C_zero : ∀ i_1 ∉ C, z.1 i_1 = 0 := by
    intro i_1 hi_not_C
    have tendsto_zero : Filter.Tendsto (fun l' => ((room_point_seq f (g1 f l')) : stdSimplex ℝ (Fin n)).1 i_1) Filter.atTop (𝓝 0) :=
      dominant_coords_tend_to_zero f C (g1 f) constant_color_set i_1 hi_not_C
    have h_tendsto_coord_z : Tendsto (fun k => ((room_point_seq f (g1 f (φ k))) : stdSimplex ℝ (Fin n)).1 i_1) atTop (𝓝 (z.1 i_1)) := by
      have h_continuous : Continuous (fun x : stdSimplex ℝ (Fin n) => x.1 i_1) :=
        Continuous.comp (continuous_apply i_1) continuous_subtype_val
      exact h_continuous.continuousAt.tendsto.comp convergence_to_z
    have tendsto_zero_subseq : Tendsto (fun k => ((room_point_seq f (g1 f (φ k))) : stdSimplex ℝ (Fin n)).1 i_1) atTop (𝓝 0) :=
      (dominant_coords_tend_to_zero f C (g1 f) constant_color_set i_1 hi_not_C).comp (hpkg f).2.1.tendsto_atTop
    exact tendsto_nhds_unique h_tendsto_coord_z tendsto_zero_subseq

  have sum_coords_in_C_eq_one : ∑ i_1 ∈ C, z.1 i_1 = 1 := by
    have total_sum_eq_one : ∑ i, z.1 i = 1 := z.2.2
    have split_sum : ∑ i, z.1 i = ∑ i ∈ C, z.1 i + ∑ i ∈ Cᶜ, z.1 i :=
      (Finset.sum_add_sum_compl C (z.1)).symm
    have compl_sum_zero : ∑ i ∈ Cᶜ, z.1 i = 0 := by
      apply Finset.sum_eq_zero
      intro i_1 hi
      exact coords_outside_C_zero i_1 (Finset.mem_compl.mp hi)
    rw [split_sum, compl_sum_zero, add_zero] at total_sum_eq_one
    exact total_sum_eq_one

  have f_coords_ge_z_coords := f_coords_ge_z_coords f hf

  have sum_f_coords_ge_one : ∑ i_1 ∈ C, (f z).1 i_1 ≥ 1 := by
    calc ∑ i_1 ∈ C, (f z).1 i_1
        ≥ ∑ i_1 ∈ C, z.1 i_1 := Finset.sum_le_sum fun i_1 hi => f_coords_ge_z_coords i_1 hi
      _ = 1 := sum_coords_in_C_eq_one

  have f_coords_outside_C_zero : ∀ i_1 ∉ C, (f z).1 i_1 = 0 := by
    intro i_1 hi_not_C
    have total_sum_f : ∑ i, (f z).1 i = 1 := (f z).2.2
    have sum_f_C_eq_one : ∑ i_2 ∈ C, (f z).1 i_2 = 1 := by
      have : ∑ i_2 ∈ C, (f z).1 i_2 ≤ 1 := by
        calc ∑ i_2 ∈ C, (f z).1 i_2
          ≤ ∑ i, (f z).1 i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C) (fun i_2 _ _ => (f z).2.1 i_2)
          _ = 1 := total_sum_f
      exact le_antisymm this sum_f_coords_ge_one
    have compl_sum_zero : ∑ i_2 ∈ Cᶜ, (f z).1 i_2 = 0 := by
      have split_sum : ∑ i, (f z).1 i = ∑ i ∈ C, (f z).1 i + ∑ i ∈ Cᶜ, (f z).1 i :=
        (Finset.sum_add_sum_compl C ((f z).1)).symm
      rw [total_sum_f, sum_f_C_eq_one] at split_sum
      linarith
    have hi_in_compl : i_1 ∈ Cᶜ := Finset.mem_compl.mpr hi_not_C
    have h_nonneg : (f z).1 i_1 ≥ 0 := (f z).2.1 i_1
    have h_le_sum : (f z).1 i_1 ≤ ∑ j ∈ Cᶜ, (f z).1 j := Finset.single_le_sum (fun j _ => (f z).2.1 j) hi_in_compl
    rw [compl_sum_zero] at h_le_sum
    exact le_antisymm h_le_sum h_nonneg

  have f_coords_eq_z_coords : ∀ i_1 ∈ C, (f z).1 i_1 = z.1 i_1 := by
    intro i_1 hi_C
    have h_sum_f_C_eq_one : ∑ i_2 ∈ C, (f z).1 i_2 = 1 := by
      have total_sum_f : ∑ i, (f z).1 i = 1 := (f z).2.2
      have : ∑ i_2 ∈ C, (f z).1 i_2 ≤ 1 := by
        calc
          ∑ i_2 ∈ C, (f z).1 i_2 ≤ ∑ i, (f z).1 i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C) (fun i_2 _ _ => (f z).2.1 i_2)
          _ = 1 := total_sum_f
      exact le_antisymm this (sum_f_coords_ge_one)
    have h_sum_eq : ∑ i_2 ∈ C, (f z).1 i_2 = ∑ i_2 ∈ C, z.1 i_2 := by
      rw [h_sum_f_C_eq_one, sum_coords_in_C_eq_one]
    exact (((Finset.sum_eq_sum_iff_of_le fun i_2 hi => f_coords_ge_z_coords i_2 hi).mp h_sum_eq.symm) i_1 hi_C).symm

  ext i_1
  by_cases hi : i_1 ∈ C
  · exact f_coords_eq_z_coords i_1 hi
  · exact (f_coords_outside_C_zero i_1 hi).trans (coords_outside_C_zero i_1 hi).symm


end Brouwer

end

lemma continuous_stdSimplex_map {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y) : Continuous (stdSimplex.map (S := ℝ) f) := by
  apply Continuous.subtype_mk
  exact (FunOnFinite.linearMap ℝ ℝ f).continuous_of_finiteDimensional.comp continuous_subtype_val


theorem stdSimplex_exists_isFixedPt_of_continuous {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : stdSimplex ℝ ι → stdSimplex ℝ ι) (hf : Continuous f) :
    ∃ x, Function.IsFixedPt f x := by
  classical
  let k : ℕ+ := ⟨Fintype.card ι, Fintype.card_pos_iff.mpr ‹Nonempty ι›⟩
  let e : ι ≃ Fin k := Fintype.equivFin ι
  let toFin : stdSimplex ℝ ι → stdSimplex ℝ (Fin k) := stdSimplex.map e
  let fromFin : stdSimplex ℝ (Fin k) → stdSimplex ℝ ι := stdSimplex.map e.symm
  let g : stdSimplex ℝ (Fin k) → stdSimplex ℝ (Fin k) := fun y => toFin (f (fromFin y))
  have hg : Continuous g := by
    exact (continuous_stdSimplex_map e).comp (hf.comp (continuous_stdSimplex_map e.symm))
  obtain ⟨y, hy⟩ := Brouwer (n := k) (f := g) hg
  refine ⟨fromFin y, ?_⟩
  have hcongr : fromFin (g y) = fromFin y := congrArg fromFin hy
  have hleft : fromFin (toFin (f (fromFin y))) = f (fromFin y) := by
    dsimp [fromFin, toFin]
    rw [stdSimplex.map_comp_apply]
    convert stdSimplex.map_id_apply (S := ℝ) (f (stdSimplex.map e.symm y)) using 2
    funext i
    simp
  dsimp [g] at hcongr
  rw [hleft] at hcongr
  exact hcongr
end PerronFrobenius



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
