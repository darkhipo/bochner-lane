/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Bochner product-integral identity over an infinite index

`BochnerLane/Integral.lean` proves the finite-prefix Bochner factorization: for a family of
probability measures `μ` and a finite `s`, `∫ ∏ i ∈ s, f i (x i) ∂(Measure.infinitePi μ)` is the
product `∏ i ∈ s, ∫ f i ∂(μ i)`.  The finite partial products over an increasing family of finite
sets therefore converge, along `Filter.atTop` on `Finset ι`, to a limit of which we know two things:
their integrals converge to `HasProd (fun i => ∫ f i) L`'s limit `L`, and (under a.e.
multipliability) the partial products themselves converge a.e. to `∏' i, f i (x i)`.

Exchanging the limit with the integral is exactly the Lebesgue dominated convergence theorem, in
the filter form `MeasureTheory.tendsto_integral_filter_of_dominated_convergence` with
`l = atTop` on `Finset ι` (countably generated as soon as `ι` is countable).  The hypothesis it
needs is a dominating integrable function:

* `g` integrable, with `‖∏ i ∈ s, f i (x i)‖ ≤ g x` for **every** finite `s`, almost everywhere.

The uniformity over `s` is not decoration.  `BochnerLane.tprod_integral_needs_domination`
(`Counterexample.lean`) exhibits `f i = 2 · 1_{x i = true}` on the fair coin: every hypothesis of
the target *without* domination holds — each `f i` is integrable with `∫ f i = 1`, the one
dimensional integrals have product limit `1`, and the coordinates are a.e. multipliable — yet
`∏' i, f i (x i) = 0` a.e., so the integral is `0 ≠ 1`.  Bounding the a.e. product
`∏' i, ‖f i (x i)‖` does **not** suffice in general either: for factors below `1` the finite
partial products *decrease*, so `∏ i ∈ s, ‖f i‖` is not bounded above by the infinite product.
The hypothesis below is therefore stated as a bound on all finite partial products, which is what
dominated convergence actually consumes.
-/

module

public import BochnerLane.Integral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Filter

open scoped ENNReal Topology BigOperators

public section

namespace MeasureTheory

variable {ι : Type*} {X : ι → Type*} {mX : ∀ i, MeasurableSpace (X i)} {μ : (i : ι) → Measure (X i)}

/-- The finite product of a.e.-strongly-measurable functions is a.e.-strongly-measurable on the
infinite product space.  (`ℝ≥0∞`-valued companion: `MeasureTheory.aemeasurable_finset_prod_infinitePi`.) -/
theorem aestronglyMeasurable_finset_prod_infinitePi [∀ i, IsProbabilityMeasure (μ i)]
    {𝕜 : Type*} [CommMonoid 𝕜] [TopologicalSpace 𝕜] [ContinuousMul 𝕜]
    (s : Finset ι) (f : (i : ι) → X i → 𝕜)
    (hf : ∀ i, AEStronglyMeasurable (f i) (μ i)) :
    AEStronglyMeasurable (fun x : (i : ι) → X i => ∏ i ∈ s, f i (x i))
      (Measure.infinitePi μ) := by
  classical
  have hqmp : Measure.QuasiMeasurePreserving (s.restrict (π := X)) (Measure.infinitePi μ)
      (Measure.pi fun i : s => μ i) :=
    ⟨Finset.measurable_restrict s, by rw [Measure.infinitePi_map_restrict]⟩
  have h1 : AEStronglyMeasurable (fun y : (i : s) → X i => ∏ i ∈ (Finset.univ : Finset s),
      (fun (y : (i : s) → X i) => f i (y i)) y) (Measure.pi fun i : s => μ i) :=
    Finset.aestronglyMeasurable_fun_prod (Finset.univ : Finset s) fun i _ =>
      (hf (i : ι)).comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_eval (α := fun i : s => X (i : ι))
          (μ := fun i : s => μ (i : ι)) i)
  have key : (fun y : (i : s) → X i => ∏ i ∈ (Finset.univ : Finset s),
        (fun (y : (i : s) → X i) => f (i : ι) (y i)) y) ∘ (s.restrict (π := X))
      = fun x : (i : ι) → X i => ∏ i ∈ s, f i (x i) := by
    funext x
    exact Finset.prod_coe_sort s fun i => f i (x i)
  simpa only [key] using h1.comp_quasiMeasurePreserving hqmp

end MeasureTheory

namespace BochnerLane

variable {ι : Type*} {X : ι → Type*} {mX : ∀ i, MeasurableSpace (X i)}
  {μ : (i : ι) → Measure (X i)} [∀ i, IsProbabilityMeasure (μ i)]

set_option linter.unusedVariables false in
/-- **The Bochner product-integral identity over an infinite index, dominated form.**

For `ℝ`-valued `f i` whose coordinates are a.e. multipliable and whose one-dimensional Bochner
integrals have product limit `L`, and under an integrable dominating function for the finite
partial products, the Bochner integral of the a.e.-defined infinite product is `L`.

The proof exchanges the limit with the integral by dominated convergence along the (countably
generated) filter `atTop` on `Finset ι`, using the finite-prefix factorization
`integral_finset_restrict_prod_eq_prod` for the integrals of the partial products.

The integrability hypothesis `hfi` belongs to the shape of the target statement (it is what makes
`fun i => ∫ x, f i x ∂(μ i)` the family one means to take a product of) but the proof does not
consume it: the finite-prefix factorization needs only a.e.-strong measurability, and domination
already bounds the partial products.  It is retained rather than dropped so that the theorem is
the same statement as `Targets.lean`'s, with the one hypothesis T2 was missing added. -/
theorem integral_tprod_eq_tprod_integral_of_dominated [Countable ι]
    {f : (i : ι) → X i → ℝ} {L : ℝ}
    (hf : ∀ i, AEStronglyMeasurable (f i) (μ i))
    (hfi : ∀ i, Integrable (f i) (μ i))
    (hmul : ∀ᵐ x ∂(Measure.infinitePi μ), Multipliable fun i => f i (x i))
    (hL : HasProd (fun i => ∫ x, f i x ∂(μ i)) L)
    {g : ((i : ι) → X i) → ℝ} (hg : Integrable g (Measure.infinitePi μ))
    (hdom : ∀ᵐ x ∂(Measure.infinitePi μ), ∀ s : Finset ι, ‖∏ i ∈ s, f i (x i)‖ ≤ g x) :
    ∫ x : (i : ι) → X i, ∏' i, f i (x i) ∂(Measure.infinitePi μ) = L := by
  classical
  have hmeas : ∀ s : Finset ι,
      AEStronglyMeasurable (fun x : (i : ι) → X i => ∏ i ∈ s, f i (x i))
        (Measure.infinitePi μ) :=
    fun s => MeasureTheory.aestronglyMeasurable_finset_prod_infinitePi s f hf
  have hbound : ∀ s : Finset ι, ∀ᵐ x ∂(Measure.infinitePi μ),
      ‖∏ i ∈ s, f i (x i)‖ ≤ g x := fun s => hdom.mono fun x hx => hx s
  have hlim : ∀ᵐ x ∂(Measure.infinitePi μ),
      Tendsto (fun s : Finset ι => ∏ i ∈ s, f i (x i)) atTop (𝓝 (∏' i, f i (x i))) :=
    hmul.mono fun x hx => hx.hasProd
  have hDCT : Tendsto
      (fun s : Finset ι => ∫ x : (i : ι) → X i, ∏ i ∈ s, f i (x i)
        ∂(Measure.infinitePi μ))
      atTop (𝓝 (∫ x : (i : ι) → X i, ∏' i, f i (x i) ∂(Measure.infinitePi μ))) :=
    tendsto_integral_filter_of_dominated_convergence (μ := Measure.infinitePi μ)
      (l := atTop) (bound := g) (F := fun s x => ∏ i ∈ s, f i (x i))
      (f := fun x => ∏' i, f i (x i)) (Eventually.of_forall hmeas)
      (Eventually.of_forall hbound) hg hlim
  rw [funext fun s => integral_finset_restrict_prod_eq_prod (μ := μ) s (f := f) hf] at hDCT
  exact tendsto_nhds_unique hDCT hL

/-- The dominated form in the `∃ L` shape of the target statement `Targets.lean`. -/
theorem exists_integral_tprod_eq_tprod_integral_of_dominated [Countable ι]
    {f : (i : ι) → X i → ℝ}
    (hf : ∀ i, AEStronglyMeasurable (f i) (μ i))
    (hfi : ∀ i, Integrable (f i) (μ i))
    (hmul : ∀ᵐ x ∂(Measure.infinitePi μ), Multipliable fun i => f i (x i))
    (hL : ∃ L, HasProd (fun i => ∫ x, f i x ∂(μ i)) L)
    {g : ((i : ι) → X i) → ℝ} (hg : Integrable g (Measure.infinitePi μ))
    (hdom : ∀ᵐ x ∂(Measure.infinitePi μ), ∀ s : Finset ι, ‖∏ i ∈ s, f i (x i)‖ ≤ g x) :
    ∃ L, HasProd (fun i => ∫ x, f i x ∂(μ i)) L ∧
      ∫ x : (i : ι) → X i, ∏' i, f i (x i) ∂(Measure.infinitePi μ) = L := by
  obtain ⟨L, hL⟩ := hL
  exact ⟨L, hL, integral_tprod_eq_tprod_integral_of_dominated hf hfi hmul hL hg hdom⟩

end BochnerLane
