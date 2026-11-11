# Bochner infinite-product lane — REPORT (gate 4, increment 2)

Lane: `/Volumes/Substrate-1/bigo/bochner-lane` · Pin: Lean `v4.34.1` / Mathlib `d13f23b7`
(campaign pin; built by clonefile from `l25-base-core`).

## 0. Verdict on T1 (the next action from increment 1)

**T1 as stated was false, and the proof attempt is what found it.** The statement in increment 1
was `∫⁻ x, (⨆ s : Finset ι, ∏ i ∈ s, F i (x i)) ∂(infinitePi μ) = ⨆ s, ∏ i ∈ s, ∫⁻ F i ∂μ i`
with the parenthetical claim that "`⨆ s` is the correct `ℝ≥0∞` product". That parenthetical is
wrong: `⨆ s, ∏ i ∈ s, c` for `0 < c < 1` is `1` (the empty prefix), not the infinite product `0`,
and the family `s ↦ ∏ i ∈ s, F i (x i)` is **not directed** unless every factor is `≥ 1`, so the
monotone convergence theorem does not apply. Measured, machine-checked, smallest possible index:

`sup_form_lintegral_finset_prod_is_false` (`BochnerLane/Counterexample.lean`): one coordinate
(`Unit`), fair coin on `Bool`, `F () = 2 · 1_{true}`. Then
`∫⁻ max 1 (F x) ∂coin = 3/2` but `max 1 (∫⁻ F ∂coin) = 1`.

So T1 was split into the two regimes where it is true, and **both are proved**:

| Theorem | Regime | Statement |
|---|---|---|
| `MeasureTheory.lintegral_iSup_finset_prod_eq` | every factor `≥ 1` | `∫⁻ ⨆ s, ∏ i ∈ s, F i (x i) = ⨆ s, ∏ i ∈ s, ∫⁻ F i` |
| `MeasureTheory.lintegral_iInf_finset_prod_eq` | every factor `≤ 1` | `∫⁻ ⨅ s, ∏ i ∈ s, F i (x i) = ⨅ s, ∏ i ∈ s, ∫⁻ F i` |

The infimum form is the one that is literally the `ℝ≥0∞` infinite product
(`ENNReal.tprod_eq_iInf_prod`: `∏' i, F i = ⨅ s, ∏ i ∈ s, F i` for factors `≤ 1`). The supremum
form is the one that covers factors `≥ 1`. No independence hypothesis in either — independence of
the coordinates of `Measure.infinitePi μ` is spent from the construction.

## 1. Lemmas landed this increment (`BochnerLane/Lintegral.lean`)

1. `lintegral_fin_nat_prod_eq_prod` — `ℝ≥0∞` Tonelli in `n` variables over `Measure.pi`
   (induction on `n`, splitting with `measurePreserving_piFinSuccAbove`, `lintegral_prod_mul`).
2. `lintegral_fintype_prod_eq_prod` — the same for a general finite index type
   (`measurePreserving_piCongrLeft`). **This is the piece Mathlib was missing**: it has the two-fold
   case (`lintegral_prod_mul`) and the `RCLike` finite case (`integral_fintype_prod_eq_prod`), and
   the `ℝ≥0∞` finite case existed nowhere.
3. `aemeasurable_finset_prod_infinitePi` — the finite product is a.e.-measurable on the infinite
   product space (via `Finset.restrict` quasi-measure-preserving).
4. `lintegral_finset_restrict_prod_eq_prod` — the finite-prefix factorization on
   `Measure.infinitePi μ`, composing `Measure.infinitePi_map_restrict` with (2). The `ℝ≥0∞`
   companion of increment 1's Bochner lemma, and strictly stronger in its measurability hypothesis
   (`AEMeasurable` rather than `Measurable`).
5. `lintegral_iSup_finset_prod_eq`, `lintegral_iInf_finset_prod_eq` — the two infinite-index forms
   above, by `lintegral_iSup_directed` and `lintegral_iInf_directed_of_measurable`.

All sorry-free, all axiom-clean (receipts in §4).

## 2. Second measured correction (F5)

| # | Prior claim | Measured | Where |
|---|---|---|---|
| F5 | "`⨆ s : Finset ι, ∏ i ∈ s, F i (x i)` is the correct `ℝ≥0∞` product" | only for factors `≥ 1`; general form refuted | `Counterexample.lean`:`sup_form_lintegral_finset_prod_is_false` |

This is the same failure class as F4: a premise that reads as a definitional triviality and is
false. It is recorded as a theorem, not as prose, for the same reason F4 is.

## 3. PR package state

`docs/PR.md` — assembled and self-contained; sources under `docs/pr/` (byte-identical copies, sha256
in the PR doc). Title: *the product-integral identity over an infinite product measure*. Proposed
upstream home: `MeasureTheory/Integral/Pi.lean` (finite index) and
`Probability/ProductMeasure.lean` (`section Integral`, infinite index). Honest scope: the package
carries the identity **past a finite prefix** and does **not** drop independence — it derives it
from the product measure. Files: `Lintegral.lean` (six lemmas), `Integral.lean` (the Bochner
finite-prefix lemma + the named next step), `Counterexample.lean` (both refutations).

## 4. Receipts

- **determinism**: two clean rebuilds of the lane (`rm -rf .lake/build/lib/lean/BochnerLane*`, then
  `lake build`), both exit `0`, error-stripped logs byte-identical
  (sha256 `9818dd9d353e94569071df1e297132baa3802e937728fa4bb7e1d9f81a64ecb3` both runs).
- **axioms**: `#print axioms` on all eight theorems → `[propext, Classical.choice, Quot.sound]`
  only (house triple).
- **purity**: `grep -rn "sorry\|admit\|native_decide"` over `BochnerLane/*.lean` and
  `BochnerLane.lean` → no hits.
- deterministic build of 3140 jobs, `Build completed successfully`.

## 5. Citation ledger (anchors verified via Crossref before citing — unchanged from increment 1)

- Hölzl, J. & Heller, A., *Three Chapters of Measure Theory in Isabelle/HOL*, ITP 2011, Springer —
  DOI `10.1007/978-3-642-22863-6_12`. ✔ title/authors/year confirmed.
- Mikusiński, J., *The Bochner Integral*, Birkhäuser Basel, **1978** —
  DOI `10.1007/978-3-0348-5567-9`. ✔ confirmed (note: 1978, not "1985").
- Durrett, R., *Probability* (5th ed.), Cambridge University Press, **2019** —
  DOI `10.1017/9781108591034`. ✔ confirmed.
- Kahane, J.-P., *Some Random Series of Functions*, **2nd ed.**, Cambridge Studies in Advanced
  Mathematics 5, Cambridge University Press, **1985** — cited by edition. ✔ The
  `10.2307/3618365` review is deliberately **not** used.
- Not reused (known-dead gate anchors): "Hastings 2022", "FKM Prop 2".

## 6. Single next action

Prove **T2** (`BochnerLane.integral_tprod_eq_tprod_integral`, `Targets.lean`): the Bochner
infinite index. Concretely, from the two ingredients now in hand — the finite-prefix Bochner
factorization (`Integral.lean`) and the `ℝ≥0∞` infinite-index forms (`Lintegral.lean`) — split
`f i = (f i)⁺ - (f i)⁻`, apply `lintegral_iSup_finset_prod_eq` / `lintegral_iInf_finset_prod_eq`
to each part under the `HasProd` hypothesis, and close with
`tendsto_integral_of_dominated_convergence` using the dominating function
`∏' i, ‖f i (x i)‖` supplied by a.e.-multipliability. Successor criterion: T2 as a `theorem`,
sorry-free, same receipt trio, and `docs/PR.md` extended with the infinite-index Bochner file.
