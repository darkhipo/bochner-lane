/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Target statements: the Bochner product-integral identity past a finite prefix

`BochnerLane/Integral.lean` supplies the finite-prefix Bochner factorization and
`BochnerLane/Lintegral.lean` the full `ℝ≥0∞` layer (finite factorization plus both infinite-index
forms).

**Status of the Bochner infinite index (measured, not asserted).**  The statement `T2` below is the
one this lane set out to prove.  It is **false as written**: a.e. multipliability of
`fun i => f i (x i)` and a product limit for the one-dimensional integrals do not supply uniform
integrability, and the identity fails for `f i = 2 · 1_{x i = true}` on the infinite product of fair
coins (`BochnerLane.tprod_integral_needs_domination`, `BochnerLane/Counterexample.lean`, and
`BochnerLane.target_is_false` below, which is the negation of `T2` at that instance).  There the
hypotheses all hold — each `f i` is integrable with `∫ f i = 1`, so the integrals have product
limit `1`, and the coordinates are a.e. multipliable — while `∏' i, f i (x i) = 0` a.e. and hence
`∫ ∏' i, f i (x i) = 0`: mass escapes at infinity.

The **true** form, proved in `BochnerLane/Infinite.lean`, is `T2` plus a dominating integrable
function bounding every finite partial product:

`BochnerLane.integral_tprod_eq_tprod_integral_of_dominated`:
for `ℝ`-valued `f i`, with `∀ i, AEStronglyMeasurable (f i) (μ i)`, `∀ i, Integrable (f i) (μ i)`,
a.e. `Multipliable fun i => f i (x i)`, `HasProd (fun i => ∫ x, f i x ∂(μ i)) L` and an integrable
`g` with `‖∏ i ∈ s, f i (x i)‖ ≤ g x` for every finite `s` a.e., one has
`∫ x, ∏' i, f i (x i) ∂(Measure.infinitePi μ) = L`.

The domination must be stated over **all** finite partial products.  A bound on the a.e. product
`∏' i, ‖f i (x i)‖` does not replace it: for factors below `1` the finite partial products
*decrease*, so `∏ i ∈ s, ‖f i‖` is bounded below, not above, by the infinite product.

## Measured corrections to the original brief (pin: Lean v4.34.1, Mathlib d13f23b7)

* Independence cannot be dropped from the identity.  For a single measure space `μ` and arbitrary
  integrable `X i : Ω → ℝ` the identity `∫ ∏ᵢ Xᵢ ∂μ = ∏ᵢ ∫Xᵢ ∂μ` fails already at two coordinates
  (`independence_free_form_is_false`, `Counterexample.lean`).  Independence is instead **derived**
  from the product measure `Measure.infinitePi`, which is what the theorems below use.
* The supremum `⨆ s : Finset ι, ∏ i ∈ s, F i (x i)` is the `ℝ≥0∞` infinite product only when every
  factor is at least `1`; otherwise the partial products are not directed and the exchange with the
  integral fails (`sup_form_lintegral_finset_prod_is_false`, `Counterexample.lean`).  Both regimes
  are proved separately in `Lintegral.lean`
  (`MeasureTheory.lintegral_iSup_finset_prod_eq` for factors `≥ 1`,
  `MeasureTheory.lintegral_iInf_finset_prod_eq` for factors `≤ 1`).
* **The Bochner infinite index needs domination, not merely a.e. multipliability** (the correction
  above; `tprod_integral_needs_domination`).
* The product measure is not missing at this pin: `Measure.infinitePi μ` exists for an arbitrary
  index type and a family of probability measures (`Probability/ProductMeasure.lean`).
* The scalar summability-logs step also exists already: `Real.multipliable_of_summable_log`,
  `Real.hasProd_of_hasSum_log` (`Analysis/SpecialFunctions/Log/Summable.lean`).
* `iIndepFun.integral_prod_eq_prod_integral` is `[Fintype ι]`-only at this pin
  (`Probability/Independence/Integration.lean`), so the infinite index is genuinely absent there.
-/

module

public import BochnerLane.Counterexample
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Integral.Pi

open MeasureTheory ProbabilityTheory

open scoped ENNReal Topology BigOperators

public section

namespace BochnerLane

/-- **T2 — infinite-index Bochner product-integral identity (the `HasProd` shape), as published.**

For `ℝ`-valued `f i` on the infinite product space, if the coordinates are a.e. multipliable and
the family of one-dimensional Bochner integrals `i ↦ ∫ x, f i x ∂(μ i)` has a product limit `L`,
then the Bochner integral of the a.e.-defined infinite product equals `L`.

**This statement is false**; see `BochnerLane.target_is_false` and
`BochnerLane.tprod_integral_needs_domination`.  It is retained verbatim as the statement of record
so that the refutation is a refutation of the published claim.  The true form is
`BochnerLane.integral_tprod_eq_tprod_integral_of_dominated` (`BochnerLane/Infinite.lean`), which
adds an integrable dominating function for the finite partial products. -/
def integral_tprod_eq_tprod_integral (ι : Type*) (X : ι → Type*)
    (mX : ∀ i, MeasurableSpace (X i)) (μ : (i : ι) → Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] : Prop :=
  ∀ (f : (i : ι) → X i → ℝ),
    (∀ i, AEStronglyMeasurable (f i) (μ i)) →
      (∀ i, Integrable (f i) (μ i)) →
        (∀ᵐ x ∂(Measure.infinitePi μ), Multipliable fun i => f i (x i)) →
          (∃ L, HasProd (fun i => ∫ x, f i x ∂(μ i)) L) →
            ∃ L, HasProd (fun i => ∫ x, f i x ∂(μ i)) L ∧
              ∫ x : (i : ι) → X i, ∏' i, f i (x i) ∂(Measure.infinitePi μ) = L

/-- **`T2` is false at the infinite product of fair coins.**

The counterexample of `BochnerLane.tprod_integral_needs_domination` satisfies every hypothesis of
`integral_tprod_eq_tprod_integral ℕ (fun _ => Bool) _ (fun _ => fairCoin)` while violating its
conclusion, so the target as published cannot be proved.  The missing hypothesis is domination of
the finite partial products by an integrable function; with it the identity holds
(`BochnerLane.integral_tprod_eq_tprod_integral_of_dominated`). -/
theorem target_is_false :
    ¬ integral_tprod_eq_tprod_integral ℕ (fun _ => Bool) (fun _ => inferInstance)
        (fun _ : ℕ => fairCoin) := by
  intro h
  obtain ⟨f, hfi, hmul, hHas, hInt⟩ := tprod_integral_needs_domination
  obtain ⟨L, hL, hLeq⟩ := h f (fun i => (hfi i).1) hfi hmul ⟨1, hHas⟩
  rw [hL.unique hHas, hInt] at hLeq
  exact zero_ne_one hLeq

end BochnerLane
