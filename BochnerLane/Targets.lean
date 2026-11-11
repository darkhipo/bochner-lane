/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Target statements: the Bochner product-integral identity past a finite prefix

`BochnerLane/Integral.lean` supplies the finite-prefix Bochner factorization and
`BochnerLane/Lintegral.lean` the full `ℝ≥0∞` layer (finite factorization plus both infinite-index
forms).  What remains is the Bochner (`ℝ`-valued) infinite index, stated below.

`T2` is written as a `Prop`-valued `def` on purpose: this **machine-checks the statement** (it
elaborates, is well-typed, has no `sorry`, no `axiom`) while making it explicit that **no proof is
claimed**.  A Mathlib PR would turn it into a `theorem` with a proof.

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
* The product measure is not missing at this pin: `Measure.infinitePi μ` exists for an arbitrary
  index type and a family of probability measures (`Probability/ProductMeasure.lean`).
* The scalar summability-logs step also exists already: `Real.multipliable_of_summable_log`,
  `Real.hasProd_of_hasSum_log` (`Analysis/SpecialFunctions/Log/Summable.lean`).
* `iIndepFun.integral_prod_eq_prod_integral` is `[Fintype ι]`-only at this pin
  (`Probability/Independence/Integration.lean`), so the infinite index is genuinely absent there.
-/

module

public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Integral.Pi

open MeasureTheory ProbabilityTheory

open scoped ENNReal Topology BigOperators

public section

namespace BochnerLane

/-- **T2 — infinite-index Bochner product-integral identity (the `HasProd` shape).**

For `ℝ`-valued `f i` on the infinite product space, if the coordinates are a.e. multipliable and
the family of one-dimensional Bochner integrals `i ↦ ∫ x, f i x ∂(μ i)` has a product limit `L`,
then the Bochner integral of the a.e.-defined infinite product equals `L`.

The `HasProd`/summability hypothesis is exactly what replaces `[Fintype ι]`: it is the condition
under which `∏' i, f i (x i)` is defined and under which the product of the integrals converges.
For positive `f i` it is discharged by `Real.multipliable_of_summable_log`
(`Summable fun i => log (f i (x i))`).

Proof obligations: `integral_finset_restrict_prod_eq_prod` (proved, `Integral.lean`) and
`lintegral_iSup_finset_prod_eq` / `lintegral_iInf_finset_prod_eq` (proved, `Lintegral.lean`), plus
`tendsto_integral_of_dominated_convergence` with the dominating function supplied by
`∏' i, ‖f i (x i)‖` under the a.e.-multipliability condition, or monotone convergence after
splitting `f i = max (f i) 0 - max (-(f i)) 0`. -/
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

end BochnerLane
