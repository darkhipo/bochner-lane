# PR package — carry the product-integral identity past a finite prefix

**Proposed title**

> feat(Probability): the product-integral identity over an infinite product measure

**Branch contents.** Three files, all sorry-free and axiom-clean at Lean `v4.34.1` /
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. Sources under `docs/pr/` (byte-identical copies
of the compiled lane files, sha256 below).

| Package file | Proposed upstream home | Contents |
|---|---|---|
| `Lintegral.lean` | `Mathlib/MeasureTheory/Integral/Pi.lean` (finite index) + `Mathlib/Probability/ProductMeasure.lean`, `section Integral` (infinite index) | `lintegral_fin_nat_prod_eq_prod`, `lintegral_fintype_prod_eq_prod`, `aemeasurable_finset_prod_infinitePi`, `lintegral_finset_restrict_prod_eq_prod`, `lintegral_iSup_finset_prod_eq`, `lintegral_iInf_finset_prod_eq` |
| `Integral.lean` | `Mathlib/Probability/ProductMeasure.lean`, `section Integral` | `integral_finset_restrict_prod_eq_prod` (Bochner, finite prefix) |
| `Counterexample.lean` | `Mathlib/Probability/ProductMeasure.lean` (beside the theorems it delimits) | `independence_free_form_is_false`, `sup_form_lintegral_finset_prod_is_false` |

`Integral.lean` also names the remaining step in its module docstring; the statement of that step,
for reference, is `BochnerLane.integral_tprod_eq_tprod_integral` in the lane's `Targets.lean`.

## What the PR adds, against what exists at this pin

Exists already, and is used rather than reproved:

* `Measure.infinitePi μ` — the product measure over an **arbitrary** index type
  (`Probability/ProductMeasure.lean`), with `IsProjectiveLimit` and the finite-prefix identity
  `Measure.infinitePi_map_restrict : (infinitePi μ).map I.restrict = Measure.pi fun i : I => μ i`.
* `MeasureTheory.lintegral_restrict_infinitePi` and `MeasureTheory.integral_restrict_infinitePi` —
  the pullback of an integral along `Finset.restrict`.
* `MeasureTheory.lintegral_prod_mul` — the two-fold `ℝ≥0∞` case.
* `MeasureTheory.integral_fintype_prod_eq_prod` — the finite-index Bochner case.
* `MeasureTheory.lintegral_iSup_directed` and `MeasureTheory.lintegral_iInf_directed_of_measurable` —
  the directed monotone convergence theorems for `ℝ≥0∞`.

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
6. **Two refutations**, shipped because they are cheap and because each one delimits a hypothesis:
   * `independence_free_form_is_false` — the identity does not survive dropping the product-measure
     construction (it fails at two coordinates on a single measure space);
   * `sup_form_lintegral_finset_prod_is_false` — `⨆ s : Finset ι, ∏ i ∈ s, f i (x i)` is the
     infinite product only when every factor is `≥ 1`; without it the family is not directed and the
     exchange with the integral fails already for the index `Unit`.

## Honest scope

* **The PR does not drop independence.**  Independence of the coordinates of `Measure.infinitePi μ`
  is a consequence of the construction and is spent here — never assumed.  Dropping it outright is
  false (`independence_free_form_is_false`), so any claim of an "independence-free" product-integral
  identity has to name the product-measure construction instead.
* **The `ℝ≥0∞` layer is finished; the Bochner layer is finite-prefix only.**  For `ℝ≥0∞` the
  infinite index is proved in both monotone regimes.  For Bochner-valued `f` the infinite index is
  *not* claimed: it needs a dominating function, supplied by a.e. multipliability of
  `fun i => ‖f i (x i)‖`, plus `HasProd (fun i => ∫ x, f i x ∂(μ i)) L`.  That statement is
  recorded (as an unproved `Prop`) in the lane's `Targets.lean`, not in the PR.
* **Not claimed:** any unconditional infinite-product theorem for sign-changing Bochner-valued `f`
  without a domination hypothesis, and any statement about `ℝ≥0∞` products of factors that cross
  `1`.  For such families the infinite product is legitimately a two-sided limit, and a directed
  monotone convergence theorem does not apply.
* **No new dependencies.**  The package imports only `Probability/ProductMeasure.lean`,
  `MeasureTheory/Integral/Pi.lean`, `MeasureTheory/Integral/Lebesgue/Sub.lean` (for the infimum
  form) and `MeasureTheory/Measure/QuasiMeasurePreserving.lean`.

## Style

Mathlib conventions are followed: names mirror the existing `integral_*` lemmas
(`lintegral_fintype_prod_eq_prod` beside `integral_fintype_prod_eq_prod`), docstrings state the
mathematical content and the role of each hypothesis, all proofs are term-or-calc style without
`native_decide`, and nothing outside `MeasureTheory`'s existing namespaces is introduced except the
`BochnerLane` namespace in `Integral.lean`/`Counterexample.lean`, which would be folded into
`MeasureTheory` upstream.  No dependency on this repository's tooling, receipts, or naming.

## Verification

* two clean rebuilds of the package: exit `0`, error-stripped logs byte-identical
  (sha256 of the stripped log `9818dd9d353e94569071df1e297132baa3802e937728fa4bb7e1d9f81a64ecb3`, both runs);
* `#print axioms` on all eight theorems: `[propext, Classical.choice, Quot.sound]` only;
* `grep -rn "sorry\|admit\|native_decide"` over the sources: no hits.

## Files in this package

| File | sha256 |
|---|---|
| `docs/pr/Lintegral.lean` | `d88b966851ba22ad5152fafffaace49f379d91164f0f2c7282571ff383e0e18e` |
| `docs/pr/Integral.lean` | `434f08757431dd7b18b95907082cd14bbfc62317557dec1ef70eeda66b1ed541` |
| `docs/pr/Counterexample.lean` | `dc55ea7156f21896f48120f157333d6653b0f143b36f4b234bf43ec1c79e12f8` |
