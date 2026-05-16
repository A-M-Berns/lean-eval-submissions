import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic

namespace Submission

open Set

lemma convex_intrinsicInterior_closure_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {c : Set E} (hc : Convex ℝ c) :
    intrinsicInterior ℝ (closure c) ⊆ c := by
  intro x hx
  by_cases hne : c.Nonempty
  · let A : AffineSubspace ℝ E := affineSpan ℝ c
    have hclos_subset_A : closure c ⊆ (A : Set E) := by
      exact closure_minimal (subset_affineSpan ℝ c) A.closed_of_finiteDimensional
    have hspan_closure : affineSpan ℝ (closure c) = A := by
      exact le_antisymm (affineSpan_le.2 hclos_subset_A) (affineSpan_mono ℝ subset_closure)
    have hAne : (A : Set E).Nonempty := by
      obtain ⟨p, hp⟩ := hne
      exact ⟨p, subset_affineSpan ℝ c hp⟩
    haveI : Nonempty A := hAne.to_subtype
    haveI : Nonempty c := hne.to_subtype
    obtain ⟨p, hp⟩ := hAne
    let pA : A := ⟨p, hp⟩
    let e := @AffineIsometryEquiv.constVSub ℝ A.direction A _ _ _ _ _ pA
    let C : Set A := (↑) ⁻¹' c
    let D : Set A.direction := e '' C
    have hDconv : Convex ℝ D := by
      rintro u ⟨y, hyc, rfl⟩ v ⟨z, hzc, rfl⟩ a b ha hb hab
      let w : E := a • (y : E) + b • (z : E)
      have hwc : w ∈ c := hc hyc hzc ha hb hab
      have hwA : w ∈ A := subset_affineSpan ℝ c hwc
      refine ⟨⟨w, hwA⟩, hwc, ?_⟩
      ext
      simp [e, pA, w, sub_eq_add_neg, smul_add]
      calc
        p + (-(b • (z : E)) + -(a • (y : E))) =
            (a • p + b • p) + (-(b • (z : E)) + -(a • (y : E))) := by
          rw [← add_smul, hab, one_smul]
        _ = a • p + -(a • (y : E)) + (b • p + -(b • (z : E))) := by
          abel
    have hDne : D.Nonempty := by
      obtain ⟨z, hz⟩ := hne
      have hzA : z ∈ A := subset_affineSpan ℝ c hz
      exact ⟨e ⟨z, hzA⟩, ⟨⟨z, hzA⟩, hz, rfl⟩⟩
    have hDint : (interior D).Nonempty :=
      (Convex.interior_nonempty_iff_affineSpan_eq_top hDconv).2 ?_
    · rw [intrinsicInterior, hspan_closure] at hx
      simp only [mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hCclosure : closure C = (↑) ⁻¹' closure c := by
        have himg : ((↑) : A → E) '' C = c := by
          ext z
          constructor
          · rintro ⟨zA, hzA, rfl⟩
            exact hzA
          · intro hz
            exact ⟨⟨z, subset_affineSpan ℝ c hz⟩, hz, rfl⟩
        rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, himg]
      have hey : e y ∈ interior (closure D) := by
        have : e y ∈ e '' interior ((↑) ⁻¹' closure c : Set A) := ⟨y, hy, rfl⟩
        rw [← e.coe_toHomeomorph] at this
        rw [e.toHomeomorph.image_interior, ← hCclosure, e.toHomeomorph.image_closure] at this
        simpa [D] using this
      have heyD : e y ∈ interior D := by
        simpa [hDconv.interior_closure_eq_interior_of_nonempty_interior hDint] using hey
      obtain ⟨z, hzC, hzy⟩ : ∃ z ∈ C, e z = e y := by
        simpa [D] using interior_subset heyD
      have : z = y := e.injective hzy
      simpa [C, this] using hzC
    · have hCspan : affineSpan ℝ C = (⊤ : AffineSubspace ℝ A) := by
        simp [A, C, affineSpan_coe_preimage_eq_top (k := ℝ) (A := c)]
      calc
        affineSpan ℝ D = (affineSpan ℝ C).map e.toAffineEquiv.toAffineMap := by
          rw [AffineSubspace.map_span]
          rfl
        _ = (⊤ : AffineSubspace ℝ A).map e.toAffineEquiv.toAffineMap := by
          rw [hCspan]
        _ = ⊤ := by
          exact AffineMap.map_top_of_surjective e.toAffineEquiv.toAffineMap e.surjective
  · rw [not_nonempty_iff_eq_empty] at hne
    simp [hne] at hx

lemma finset_extremePoints_of_mem_convexHull_extremePoints
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} {x : E}
    (hxconv : x ∈ convexHull ℝ (s.extremePoints ℝ)) :
    ∃ t : Finset E,
      (↑t : Set E) ⊆ s.extremePoints ℝ ∧
      t.card ≤ Module.finrank ℝ E + 1 ∧
      x ∈ convexHull ℝ (↑t : Set E) := by
  classical
  let t := Caratheodory.minCardFinsetOfMemConvexHull hxconv
  refine ⟨t, Caratheodory.minCardFinsetOfMemConvexHull_subseteq hxconv, ?_,
    Caratheodory.mem_minCardFinsetOfMemConvexHull hxconv⟩
  have ht_ind : AffineIndependent ℝ ((↑) : t → E) :=
    Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hxconv
  have hcard₁ :
      Fintype.card t ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → E))) + 1 :=
    ht_ind.card_le_finrank_succ
  have hfin :
      Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → E))) ≤ Module.finrank ℝ E := by
    exact Submodule.finrank_le (vectorSpan ℝ (Set.range ((↑) : t → E)))
  simpa using hcard₁.trans (Nat.add_le_add_right hfin 1)

lemma mem_convexHull_extremePoints_of_mem_intrinsicInterior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} {x : E}
    (hscomp : IsCompact s)
    (hsconv : Convex ℝ s)
    (hxint : x ∈ intrinsicInterior ℝ s) :
    x ∈ convexHull ℝ (s.extremePoints ℝ) := by
  let c : Set E := convexHull ℝ (s.extremePoints ℝ)
  have hclosure : closure c = s := by
    simpa [c] using closure_convexHull_extremePoints hscomp hsconv
  exact convex_intrinsicInterior_closure_subset (c := c) (convex_convexHull ℝ _) (by
    simpa [c, hclosure] using hxint)

lemma exists_supporting_functional_of_mem_intrinsicFrontier
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} {x : E}
    (hsconv : Convex ℝ s)
    (hxfr : x ∈ intrinsicFrontier ℝ s) :
    ∃ l : StrongDual ℝ E,
      (∃ v : (affineSpan ℝ s).direction, l (v : E) ≠ 0) ∧
      ∀ y ∈ s, l y ≤ l x := by
  let A : AffineSubspace ℝ E := affineSpan ℝ s
  rw [intrinsicFrontier] at hxfr
  simp only [mem_image] at hxfr
  obtain ⟨xA, hxAfront, rfl⟩ := hxfr
  haveI : Nonempty A := ⟨xA⟩
  let e := @AffineIsometryEquiv.constVSub ℝ A.direction A _ _ _ _ _ xA
  let C : Set A := (↑) ⁻¹' s
  let D : Set A.direction := e '' C
  have hCne : C.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    change xA ∈ frontier C at hxAfront
    rw [h, frontier_empty] at hxAfront
    exact hxAfront
  have hsne : s.Nonempty := by
    obtain ⟨y, hy⟩ := hCne
    exact ⟨y, hy⟩
  haveI : Nonempty s := hsne.to_subtype
  have hDconv : Convex ℝ D := by
    rintro u ⟨y, hyc, rfl⟩ v ⟨z, hzc, rfl⟩ a b ha hb hab
    let w : E := a • (y : E) + b • (z : E)
    have hwc : w ∈ s := hsconv hyc hzc ha hb hab
    have hwA : w ∈ A := subset_affineSpan ℝ s hwc
    refine ⟨⟨w, hwA⟩, hwc, ?_⟩
    ext
    simp [e, w, sub_eq_add_neg, smul_add]
    calc
      (xA : E) + (-(b • (z : E)) + -(a • (y : E))) =
          (a • (xA : E) + b • (xA : E)) + (-(b • (z : E)) + -(a • (y : E))) := by
        rw [← add_smul, hab, one_smul]
      _ = a • (xA : E) + -(a • (y : E)) + (b • (xA : E) + -(b • (z : E))) := by
        abel
  have hDint : (interior D).Nonempty :=
    (Convex.interior_nonempty_iff_affineSpan_eq_top hDconv).2 ?_
  · have hxDfront : e xA ∈ frontier D := by
      have : e xA ∈ e '' frontier C := ⟨xA, hxAfront, rfl⟩
      rw [← e.coe_toHomeomorph] at this
      rw [e.toHomeomorph.image_frontier] at this
      simpa [D] using this
    have hxDnot : e xA ∉ interior D := by
      rw [frontier] at hxDfront
      exact hxDfront.2
    obtain ⟨f, hfne, hfmax⟩ :=
      geometric_hahn_banach_of_nonempty_interior_point hDconv hxDnot hDint
    obtain ⟨g, hg, hgnorm⟩ := Real.exists_extension_norm_eq A.direction f
    let l : StrongDual ℝ E := -g
    refine ⟨l, ?_, ?_⟩
    · have hf_exists : ∃ v : A.direction, f v ≠ 0 := by
        by_contra h
        apply hfne
        ext v
        exact not_not.mp (not_exists.mp h v)
      obtain ⟨v, hv⟩ := hf_exists
      refine ⟨v, ?_⟩
      have hgv : g (v : E) = f v := hg v
      simpa [l, hgv] using hv
    · intro y hy
      let yA : A := ⟨y, subset_affineSpan ℝ s hy⟩
      have hyD : e yA ∈ D := ⟨yA, hy, rfl⟩
      have hle : f (e yA) ≤ f (e xA) := hfmax (e yA) hyD
      have hleg : g ((e yA : A.direction) : E) ≤ g ((e xA : A.direction) : E) := by
        simpa [hg] using hle
      have hgxy : g ((xA : E) - y) ≤ g ((xA : E) - (xA : E)) := by
        simpa [e, yA, sub_eq_add_neg] using hleg
      have hgxy' : g (xA : E) ≤ g y := by
        simpa using hgxy
      simpa [l] using neg_le_neg hgxy'
  · have hCspan : affineSpan ℝ C = (⊤ : AffineSubspace ℝ A) := by
      simp [A, C, affineSpan_coe_preimage_eq_top (k := ℝ) (A := s)]
    calc
      affineSpan ℝ D = (affineSpan ℝ C).map e.toAffineEquiv.toAffineMap := by
        rw [AffineSubspace.map_span]
        rfl
      _ = (⊤ : AffineSubspace ℝ A).map e.toAffineEquiv.toAffineMap := by
        rw [hCspan]
      _ = ⊤ := by
        exact AffineMap.map_top_of_surjective e.toAffineEquiv.toAffineMap e.surjective

lemma finrank_direction_toExposed_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} {x : E} {l : StrongDual ℝ E}
    (hx : x ∈ s)
    (hdir : ∃ v : (affineSpan ℝ s).direction, l (v : E) ≠ 0)
    (hmax : ∀ y ∈ s, l y ≤ l x) :
    Module.finrank ℝ (affineSpan ℝ (l.toExposed s)).direction <
      Module.finrank ℝ (affineSpan ℝ s).direction := by
  let F : Set E := l.toExposed s
  let A : AffineSubspace ℝ E := affineSpan ℝ s
  let H : AffineSubspace ℝ E := AffineSubspace.mk' x (LinearMap.ker (l : E →ₗ[ℝ] ℝ))
  have hF_subset_s : F ⊆ s := by
    intro y hy
    exact hy.1
  have hF_subset_H : F ⊆ H := by
    intro y hy
    have hxy : l x ≤ l y := hy.2 x hx
    have hyx : l y ≤ l x := hmax y hy.1
    have h_eq : l y = l x := le_antisymm hyx hxy
    change y - x ∈ LinearMap.ker (l : E →ₗ[ℝ] ℝ)
    simp [map_sub, h_eq]
  have hdirF_le_A :
      (affineSpan ℝ F).direction ≤ A.direction :=
    AffineSubspace.direction_le (affineSpan_mono ℝ hF_subset_s)
  have hdirF_le_ker :
      (affineSpan ℝ F).direction ≤ LinearMap.ker (l : E →ₗ[ℝ] ℝ) := by
    simpa [H] using
      (AffineSubspace.direction_le (affineSpan_le.2 hF_subset_H) :
        (affineSpan ℝ F).direction ≤ H.direction)
  have hlt : (affineSpan ℝ F).direction < A.direction := by
    refine lt_of_le_of_ne hdirF_le_A ?_
    intro h_eq
    obtain ⟨v, hv⟩ := hdir
    have hvker : (v : E) ∈ LinearMap.ker (l : E →ₗ[ℝ] ℝ) := by
      have hv_mem : (v : E) ∈ (affineSpan ℝ F).direction := by
        rw [h_eq]
        exact v.2
      exact hdirF_le_ker hv_mem
    exact hv (by simpa [LinearMap.mem_ker] using hvker)
  simpa [F, A] using Submodule.finrank_lt_finrank_of_lt hlt

lemma mem_convexHull_extremePoints_of_mem_compact_convex_aux
    (n : ℕ) :
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      {s : Set E} {x : E},
      IsCompact s →
      Convex ℝ s →
      Module.finrank ℝ (affineSpan ℝ s).direction ≤ n →
      x ∈ s →
      x ∈ convexHull ℝ (s.extremePoints ℝ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E _ _ _ s x hscomp hsconv hdim hx
    have hxclosure : x ∈ intrinsicClosure ℝ s := subset_intrinsicClosure hx
    rw [← intrinsicInterior_union_intrinsicFrontier (𝕜 := ℝ) (s := s)] at hxclosure
    rcases hxclosure with hxint | hxfr
    · exact mem_convexHull_extremePoints_of_mem_intrinsicInterior hscomp hsconv hxint
    · obtain ⟨l, hldir, hlmax⟩ :=
        exists_supporting_functional_of_mem_intrinsicFrontier hsconv hxfr
      let F : Set E := l.toExposed s
      have hxF : x ∈ F := ⟨hx, hlmax⟩
      have hFexp : IsExposed ℝ s F := by
        simpa [F] using ContinuousLinearMap.toExposed.isExposed (𝕜 := ℝ) (A := s) (l := l)
      have hFcomp : IsCompact F := by
        simpa [F] using hFexp.isCompact hscomp
      have hFconv : Convex ℝ F := hFexp.convex hsconv
      have hdimFlt :
          Module.finrank ℝ (affineSpan ℝ F).direction <
            Module.finrank ℝ (affineSpan ℝ s).direction := by
        simpa [F] using finrank_direction_toExposed_lt (s := s) (x := x) (l := l) hx hldir hlmax
      have hdimF : Module.finrank ℝ (affineSpan ℝ F).direction ≤ n := hdimFlt.le.trans hdim
      have hxFconv : x ∈ convexHull ℝ (F.extremePoints ℝ) :=
        ih (Module.finrank ℝ (affineSpan ℝ F).direction) (hdimFlt.trans_le hdim)
          hFcomp hFconv (le_rfl) hxF
      exact (convexHull_mono (𝕜 := ℝ) hFexp.isExtreme.extremePoints_subset_extremePoints) hxFconv

theorem mem_convexHull_finset_extremePoints_of_mem_compact_convex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} {x : E}
    (hscomp : IsCompact s)
    (hsconv : Convex ℝ s)
    (hx : x ∈ s) :
    ∃ t : Finset E,
      (↑t : Set E) ⊆ s.extremePoints ℝ ∧
      t.card ≤ Module.finrank ℝ E + 1 ∧
      x ∈ convexHull ℝ (↑t : Set E) := by
  have hdim : Module.finrank ℝ (affineSpan ℝ s).direction ≤ Module.finrank ℝ E := by
    exact Submodule.finrank_le (affineSpan ℝ s).direction
  exact finset_extremePoints_of_mem_convexHull_extremePoints
    (mem_convexHull_extremePoints_of_mem_compact_convex_aux
      (Module.finrank ℝ E) hscomp hsconv hdim hx)

end Submission
