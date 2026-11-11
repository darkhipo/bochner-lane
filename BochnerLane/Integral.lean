/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Integration against an infinite product of probability measures

For a family of probability measures `μ` on `X i`, `Measure.infinitePi μ` is the product measure
on `Π i, X i`.  `Measure.infinitePi_map_restrict` identifies the pushforward of `Measure.infinitePi μ`
along the restriction to a finite set `s` with `Measure.pi` over `s`, and
`MeasureTheory.integral_fintype_prod_eq_prod` factors an integral of a finite product against
`Measure.pi`.  This file composes the two: the Bochner integral of a finite product
`∏ i ∈ s, f i (x i)` against `Measure.infinitePi μ` is the product of the one-dimensional
integrals.

No independence hypothesis appears: independence of the coordinates of `Measure.infinitePi μ` is a
consequence of the product-measure construction, not an assumption.

The `ℝ≥0∞` counterpart of this factorization, and its infinite-index limit, are in
`BochnerLane/Lintegral.lean`.  The remaining step beyond this file is the infinite index for
Bochner-valued `f`: replacing `s : Finset ι` by the full index requires a product limit
`HasProd (fun i => ∫ x, f i x ∂(μ i)) L` together with a.e. multipliability of
`fun i => f i (x i)`, which supplies the dominating function for
`MeasureTheory.tendsto_integral_of_dominated_convergence`.
-/

module

public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.SpecialFunctions.Log.Summable

open MeasureTheory ProbabilityTheory

open scoped ENNReal Topology BigOperators

public section

namespace BochnerLane

variable {ι : Type*} {X : ι → Type*} {mX : ∀ i, MeasurableSpace (X i)}
  {μ : (i : ι) → Measure (X i)} [∀ i, IsProbabilityMeasure (μ i)]

/-- **Finite-prefix Bochner factorization over an infinite product space.**

For a family of probability measures `μ` and a finite set `s` of coordinates, the Bochner integral
of `∏ i ∈ s, f i (x i)` against `Measure.infinitePi μ` is the product of the one-dimensional
integrals `∫ x, f i x ∂(μ i)`.

This composes `Measure.infinitePi_map_restrict` (a statement about measures) with
`MeasureTheory.integral_fintype_prod_eq_prod` (a statement about integrals against `Measure.pi`).
No independence hypothesis is needed: independence of the coordinates of `Measure.infinitePi μ` is
derived from the construction of the product measure. -/
theorem integral_finset_restrict_prod_eq_prod {𝕜 : Type*} [RCLike 𝕜]
    {f : (i : ι) → X i → 𝕜} (s : Finset ι)
    (hf : ∀ i, AEStronglyMeasurable (f i) (μ i)) :
    ∫ x : (i : ι) → X i, ∏ i ∈ s, f i (x i) ∂(Measure.infinitePi μ)
      = ∏ i ∈ s, ∫ x, f i x ∂(μ i) := by
  classical
  have hae : AEStronglyMeasurable (fun y : (i : s) → X i => ∏ i : s, f i (y i))
      (Measure.pi (fun i : s => μ i)) := by
    have h1 : AEStronglyMeasurable
        (fun y : (i : s) → X i => ∏ i ∈ (Finset.univ : Finset s),
          (fun (y : (i : s) → X i) => f i (y i)) y)
        (Measure.pi (fun i : s => μ i)) :=
      Finset.aestronglyMeasurable_fun_prod (Finset.univ : Finset s) (fun i _ =>
        (hf i).comp_quasiMeasurePreserving
          (Measure.quasiMeasurePreserving_eval (α := fun i : s => X (i : ι))
            (μ := fun i : s => μ (i : ι)) i))
    simpa using h1
  have hmap : (Measure.infinitePi μ).map (s.restrict (π := X)) = Measure.pi (fun i : s => μ i) :=
    Measure.infinitePi_map_restrict (μ := μ) (I := s)
  have hae' : AEStronglyMeasurable (fun y : (i : s) → X i => ∏ i : s, f i (y i))
      ((Measure.infinitePi μ).map (s.restrict (π := X))) := by
    rw [hmap]; exact hae
  calc
    ∫ x : (i : ι) → X i, ∏ i ∈ s, f i (x i) ∂(Measure.infinitePi μ)
        = ∫ x : (i : ι) → X i,
            (fun y : (i : s) → X i => ∏ i : s, f i (y i)) (s.restrict (π := X) x)
            ∂(Measure.infinitePi μ) := by
          congr 1
          funext x
          exact (Finset.prod_coe_sort s (fun i => f i (x i))).symm
    _ = ∫ y : (i : s) → X i, ∏ i : s, f i (y i)
            ∂((Measure.infinitePi μ).map (s.restrict (π := X))) := by
          rw [integral_map (by fun_prop) hae']
    _ = ∫ y : (i : s) → X i, ∏ i : s, f i (y i) ∂(Measure.pi (fun i : s => μ i)) := by
          rw [hmap]
    _ = ∏ i : s, ∫ x, f i x ∂(μ i) :=
          integral_fintype_prod_eq_prod (f := fun i : s => f (i : ι))
            (μ := fun i : s => μ (i : ι))
    _ = ∏ i ∈ s, ∫ x, f i x ∂(μ i) :=
          Finset.prod_coe_sort s (fun i : ι => ∫ x, f i x ∂(μ i))

end BochnerLane
