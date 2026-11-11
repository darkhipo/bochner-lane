# PR package — carry the product-integral identity past a finite prefix

**Proposed title**

> feat(Probability): the product-integral identity over an infinite product measure

**Branch contents.** Four files, all sorry-free and axiom-clean at Lean `v4.34.1` /
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. Sources under `docs/pr/` (byte-identical copies
of the compiled lane files, sha256 below).

| Package file | Proposed upstream home | Contents |
|---|---|---|
| `Lintegral.lean` | `Mathlib/MeasureTheory/Integral/Pi.lean` (finite index) + `Mathlib/Probability/ProductMeasure.lean`, `section Integral` (infinite index) | `lintegral_fin_nat_prod_eq_prod`, `lintegral_fintype_prod_eq_prod`, `aemeasurable_finset_prod_infinitePi`, `lintegral_finset_restrict_prod_eq_prod`, `lintegral_iSup_finset_prod_eq`, `lintegral_iInf_finset_prod_eq` |
| `Integral.lean` | `Mathlib/Probability/ProductMeasure.lean`, `section Integral` | `integral_finset_restrict_prod_eq_prod` (Bochner, finite prefix) |
| `Infinite.lean` | `Mathlib/Probability/ProductMeasure.lean`, `section Integral` | `aestronglyMeasurable_finset_prod_infinitePi`, `tendsto_integral_indicator_ge_atTop_zero`, `uniformIntegrable_of_ae_dominated`, `integral_tprod_eq_tprod_integral_of_uniformIntegrable` (Bochner, infinite index, Vitali form — the primary exchange), `uniformIntegrable_finset_prod_infinitePi_of_dominated`, `integral_tprod_eq_tprod_integral_of_dominated` (domination form, derived from the Vitali form), and their `∃ L` forms |
| `Counterexample.lean` | `Mathlib/Probability/ProductMeasure.lean` (beside the theorems it delimits) | `independence_free_form_is_false`, `sup_form_lintegral_finset_prod_is_false`, `tprod_integral_needs_domination` |

## What the PR adds, against what exists at this pin

Exists already, and is used rather than reproved:

* `Measure.infinitePi μ` — the product measure over an **arbitrary** index type
  (`Probability/ProductMeasure.lean`), with `IsProjectiveLimit`, the finite-prefix identity
  `Measure.infinitePi_map_restrict : (infinitePi μ).map I.restrict = Measure.pi fun i : I => μ i`,
  and the cylinder mass `infinitePi_pi`.
* `MeasureTheory.lintegral_restrict_infinitePi` and `MeasureTheory.integral_restrict_infinitePi` —
  the pullback of an integral along `Finset.restrict`.
* `MeasureTheory.lintegral_prod_mul` — the two-fold `ℝ≥0∞` case.
* `MeasureTheory.integral_fintype_prod_eq_prod` — the finite-index Bochner case.
* `MeasureTheory.lintegral_iSup_directed` and `MeasureTheory.lintegral_iInf_directed_of_measurable` —
  the directed monotone convergence theorems for `ℝ≥0∞`.
* `MeasureTheory.tendsto_integral_filter_of_dominated_convergence` — dominated convergence along an
  arbitrary countably generated filter, which is what makes the `Finset ι` net usable directly
  (`atTop` on `Finset ι` is countably generated when `ι` is countable).

Added here:

1. **`lintegral_fintype_prod_eq_prod`** (and its `Fin n` form `lintegral_fin_nat_prod_eq_prod`):
   `∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i)`.  Mathlib has the two-fold
   case and the `RCLike`-valued finite case, but not the `ℝ≥0∞` finite case; the induction is over
   `Fin n`, splitting off coordinate `0` with `measurePreserving_piFinSuccAbove` and applying
   `lintegral_prod_mul`.
2. **`lintegral_finset_restrict_prod_eq_prod`**: the same factorization on the *infinite* product
   space for a finite prefix `s`, composing `Measure.infinitePi_map_restrict` with (1).  This is the
   `ℝ≥0∞` companion of `integral_finset_restrict_prod_eq_prod`, and unlike the Bochner case it can
   be phrased with a.e.-measurable (not measurable) factors.
3. **`lintegral_iSup_finset_prod_eq`** — the infinite index for factors `≥ 1`, where the partial
   products are directed and `⨆ s, ∏ i ∈ s, f i (x i)` is the infinite product.
4. **`lintegral_iInf_finset_prod_eq`** — the dual for factors `≤ 1`, which is the regime of the
   genuine `ℝ≥0∞` infinite product: `ENNReal.tprod_eq_iInf_prod` identifies `∏' i, f i` with
   `⨅ s, ∏ i ∈ s, f i`, and directed monotone convergence for infima exchanges it with the
   integral.
5. **`integral_finset_restrict_prod_eq_prod`** — the Bochner finite-prefix factorization for
   `RCLike`-valued `f`, i.e. the finite increment of the identity the PR is named for.
6. **`aestronglyMeasurable_finset_prod_infinitePi`** and
   **`integral_tprod_eq_tprod_integral_of_dominated`** — the Bochner infinite index, i.e. the
   identity itself:
   `∫ x, ∏' i, f i (x i) ∂(Measure.infinitePi μ) = L` under
   `∀ i, AEStronglyMeasurable (f i) (μ i)`, `∀ i, Integrable (f i) (μ i)`,
   `∀ᵐ x, Multipliable fun i => f i (x i)`, `HasProd (fun i => ∫ x, f i x ∂(μ i)) L`, and an
   integrable `g` with `‖∏ i ∈ s, f i (x i)‖ ≤ g x` for every finite `s`, a.e.  The proof is
   dominated convergence along `atTop` on `Finset ι`, with the integrals of the partial products
   computed by (5).  `[Countable ι]` is needed for that filter to be countably generated (and for
   the a.e. limit to be a measurable limit).
7. **`integral_tprod_eq_tprod_integral_of_uniformIntegrable`** — the same identity with the
   *weaker* uniformity hypothesis: uniform integrability of the family of finite partial products
   `fun s : Finset ι => fun x => ∏ i ∈ s, f i (x i)` at `p = 1`, and no dominating function at all.
   Exchanged with Vitali's convergence theorem (`tendsto_Lp_finite_of_tendsto_ae`, `p = 1`, the
   product measure being a probability space) and closed through the filter-generic
   `MeasureTheory.tendsto_integral_of_L1'`.  The `Finset ι` net is met by Vitali's `ℕ`-indexed
   statement through a monotone cofinal sequence of finite sets
   (`Filter.exists_seq_monotone_tendsto_atTop_atTop`, from `[Countable ι]`); both limits are read off
   along that sequence, so no enumeration of `ι` is constructed.
8. **`tendsto_integral_indicator_ge_atTop_zero`, `uniformIntegrable_of_ae_dominated`, and
   `uniformIntegrable_finset_prod_infinitePi_of_dominated`** — the tail lemma Mathlib lacks and its
   consequence.  For `g` integrable, `∫ x, {x | C ≤ g x}.indicator g x ∂μ → 0` along `atTop` on `ℕ`
   (dominated convergence along that filter, `|g|` as bound, after passing to a strongly measurable
   representative — level sets of an a.e.-measurable function need not be measurable, and the
   indicator phrasing avoids the `MeasurableSet` hypothesis `Integrable g` alone cannot supply).
   Consequently a family of a.e.-strongly-measurable functions dominated a.e. by one integrable
   real `g` is uniformly integrable at exponent 1: every tail `eLpNorm` is bounded by the tail of
   `g` through the a.e. pointwise bound `{x | C ≤ ‖F i x‖₊} ⊆ {x | C ≤ g x}`, and
   `uniformIntegrable_of` consumes exactly that.  Specialized to the partial-product family this
   feeds (6)'s domination form, which is thereby *derived from* (7) rather than proved in parallel —
   the package carries one exchange theorem (the Vitali form) plus the machine-checked
   domination ⟹ uniform-integrability implication.
9. **Three refutations**, shipped because they are cheap and because each one delimits a hypothesis:
   * `independence_free_form_is_false` — the identity does not survive dropping the product-measure
     construction (it fails at two coordinates on a single measure space);
   * `sup_form_lintegral_finset_prod_is_false` — `⨆ s : Finset ι, ∏ i ∈ s, f i (x i)` is the
     infinite product only when every factor is `≥ 1`; without it the family is not directed and the
     exchange with the integral fails already for the index `Unit`;
   * `tprod_integral_needs_domination` — the domination hypothesis in (6) is not removable.  On the
     infinite product of fair coins with `f i = 2 · 1_{x i = true}`, every other hypothesis holds
     (each `f i` is integrable with `∫ f i = 1`, the integrals have product limit `1`, the
     coordinates are a.e. multipliable) while `∏' i, f i (x i) = 0` a.e., so the integral is
     `0 ≠ 1`.  The mechanism is the classical failure of uniform integrability: the partial
     products `2ⁿ · 1_{x 0 = … = x (n-1) = true}` all have integral `1`, and their a.e. limit is
     `0`.

## Honest scope

* **The PR does not drop independence.**  Independence of the coordinates of `Measure.infinitePi μ`
  is a consequence of the construction and is spent here — never assumed.  Dropping it outright is
  false (`independence_free_form_is_false`), so any claim of an "independence-free" product-integral
  identity has to name the product-measure construction instead.
* **The `ℝ≥0∞` layer is complete; the Bochner layer carries the identity with one extra
  hypothesis.**  For `ℝ≥0∞` the infinite index is proved in both monotone regimes, with no
  domination needed (`ℝ≥0∞` products are monotone limits, and `lintegral_iSup_directed` /
  `lintegral_iInf_directed_of_measurable` are total on `ℝ≥0∞`).  For Bochner-valued `f` two things
  are genuinely extra, and both are in (6): a.e. multipliability (so that `∏' i, f i (x i)` is
  defined) and a *uniformity* condition on the finite partial products (so that the limit may pass
  through the integral).  Two such conditions are proved, and they are stated differently:
  pointwise domination by an integrable `g` (6), and uniform integrability of the partial-product
  family (7), in which no dominating function appears in the hypotheses at all.  Domination implies
  uniform integrability (the tail integrals are bounded by `∫_{g ≥ C} g → 0`), so (7) is the weaker
  hypothesis of the two — that implication is machine-checked in the package (item 8), not prose.  The
  witnessing counterexample defeats the *bare* target by violating uniform integrability (its tail
  integrals are identically `1`, by the machine-checked cylinder mass `2^{-#s}`), so (7)'s hypothesis
  genuinely excludes it rather than sidestepping it.
* **The domination hypothesis is stated over all finite partial products, not over `∏' i, ‖f i‖`.**
  A bound on the a.e. product `∏' i, ‖f i (x i)‖` would not do: for factors below `1` the finite
  partial products *decrease*, so `∏ i ∈ s, ‖f i‖` is bounded below, not above, by the infinite
  product.  This is the same monotonicity obstruction that forces the two regimes in
  `Lintegral.lean`, seen on the Bochner side.
* **Not claimed:** any unconditional infinite-product theorem for sign-changing Bochner-valued `f`
  with *no* uniformity hypothesis on the partial products — false,
  `tprod_integral_needs_domination`, and the same witness is not uniformly integrable either, so
  even under uniform integrability the bare hypotheses never suffice.  Also not claimed: any
  statement about `ℝ≥0∞` products of factors that cross `1`.  For such families the infinite
  product is legitimately a two-sided limit, and a directed monotone convergence theorem does not
  apply.
* **No new dependencies.**  The package imports only `Probability/ProductMeasure.lean`,
  `MeasureTheory/Integral/Pi.lean`, `MeasureTheory/Integral/Lebesgue/Sub.lean` (for the infimum
  form), `MeasureTheory/Measure/QuasiMeasurePreserving.lean`, `MeasureTheory/Integral/
  DominatedConvergence.lean` (for the Bochner infinite index) and
  `MeasureTheory/Integral/Bochner/SumMeasure.lean` (only in `Counterexample.lean`).

## Style

Mathlib conventions are followed: names mirror the existing `integral_*` lemmas
(`lintegral_fintype_prod_eq_prod` beside `integral_fintype_prod_eq_prod`,
`integral_tprod_eq_tprod_integral_of_dominated` beside the `HasProd` API), docstrings state the
mathematical content and the role of each hypothesis, all proofs are term-or-calc style without
`native_decide`, and nothing outside `MeasureTheory`'s existing namespaces is introduced except the
`BochnerLane` namespace in `Integral.lean`/`Infinite.lean`/`Counterexample.lean`, which would be
folded into `MeasureTheory` upstream.  No dependency on this repository's tooling, receipts, or
naming.

## Verification

* two clean rebuilds of the package: exit `0`, error-stripped logs byte-identical
  (sha256 of the timing-stripped log `8a1e8fa46e7b39745b931fba00c5a66edf6ce8991e5eb8b21814a6ef610579ca`,
  both runs);
* `#print axioms` on all eighteen theorems printed by the lane's `CheckAxioms.lean`:
  `[propext, Classical.choice, Quot.sound]` only;
* `grep -rn "sorry\|admit\|native_decide"` over the sources: no hits.

## Files in this package

| File | sha256 |
|---|---|
| `docs/pr/Lintegral.lean` | `d88b966851ba22ad5152fafffaace49f379d91164f0f2c7282571ff383e0e18e` |
| `docs/pr/Integral.lean` | `ca7667c5618e12e2488d36dadfb84ea00cc5e2996753f86eb850f2c2fbbd1df2` |
| `docs/pr/Infinite.lean` | `c6dae54f7a98c62a6b7d5bb2e9911a79993c27b716cc7514e6fc0d9345022bdf` |
| `docs/pr/Counterexample.lean` | `bcfa8ba11cc74f73c651ada8c2a8aabf7e1590e3440acfca13223302246fe94a` |
