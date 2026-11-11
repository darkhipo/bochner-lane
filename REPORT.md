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

## 6. Single next action (increment 2 — executed in increment 3, with a correction)

Prove **T2** (`BochnerLane.integral_tprod_eq_tprod_integral`, `Targets.lean`): the Bochner
infinite index. Concretely, from the two ingredients now in hand — the finite-prefix Bochner
factorization (`Integral.lean`) and the `ℝ≥0∞` infinite-index forms (`Lintegral.lean`) — split
`f i = (f i)⁺ - (f i)⁻`, apply `lintegral_iSup_finset_prod_eq` / `lintegral_iInf_finset_prod_eq`
to each part under the `HasProd` hypothesis, and close with
`tendsto_integral_of_dominated_convergence` using the dominating function
`∏' i, ‖f i (x i)‖` supplied by a.e.-multipliability. Successor criterion: T2 as a `theorem`,
sorry-free, same receipt trio, and `docs/PR.md` extended with the infinite-index Bochner file.

**Outcome (increment 3): T2 as stated is false, and the plan's last clause is where it breaks.**
The dominating function `∏' i, ‖f i (x i)‖` is not a dominating function: for factors below `1`
the finite partial products decrease, so `∏ i ∈ s, ‖f i‖` is bounded *below*, not above, by the
infinite product. Worse, no bound derived from a.e. multipliability can work — see §7.

---

# Increment 3 — the Bochner infinite index

## 7. Verdict on T2

**T2 (`BochnerLane.integral_tprod_eq_tprod_integral`) is FALSE as published.** Machine-checked, not
argued: `BochnerLane.target_is_false` (`Targets.lean`) proves the negation of the published `Prop`
at the infinite product of fair coins, via the explicit counterexample
`BochnerLane.tprod_integral_needs_domination` (`Counterexample.lean`).

The counterexample: `ι = ℕ`, one coordinate type `Bool`, `μ i = fairCoin`, `f i = 2 · 1_{x i = true}`.

| Hypothesis of T2 | Holds? |
|---|---|
| `∀ i, AEStronglyMeasurable (f i) fairCoin` | yes (finite range) |
| `∀ i, Integrable (f i) fairCoin` | yes, `∫ f i = 2 · ½ = 1` |
| `∃ L, HasProd (fun i => ∫ f i) L` | yes, `L = 1` (constant-`1` family) |
| `∀ᵐ x, Multipliable fun i => f i (x i)` | yes — some coordinate is `false` a.e., then every finite product containing it is `0` |
| conclusion `∫ ∏' i, f i (x i) = L` | **no** — `∏' i, f i (x i) = 0` a.e., so the integral is `0 ≠ 1` |

The mechanism is the classical failure of uniform integrability: the partial products
`2ⁿ · 1_{x 0 = … = x (n-1) = true}` have integral `1` for every `n` and converge a.e. to `0`.
A.e. multipliability constrains the *pointwise* limit; it says nothing about the *mass* at infinity.

Two things this correction teaches, both now in the package's docstrings:

1. **The plan's dominating function was the wrong object.** `∏' i, ‖f i (x i)‖` does not bound the
   finite partial products from above (decreasing partial products below `1`), and in the
   counterexample it is `0` while the partial products are `2ⁿ` on a set of measure `2⁻ⁿ`. The
   hypothesis has to be stated as a bound over **all** finite partial products, which is exactly
   what dominated convergence consumes.
2. **`ℝ≥0∞` needed no such hypothesis, and that asymmetry is not an accident.** `ℝ≥0∞` products are
   monotone limits absorbed by `lintegral_iSup_directed` / `lintegral_iInf_directed_of_measurable`;
   Bochner integrals of a signed, non-monotone family need uniform integrability, which
   `ℝ≥0∞`-monotonicity silently supplies and a.e. convergence does not.

## 8. The true form, proved (`BochnerLane/Infinite.lean`, 139 lines)

| Theorem | Statement |
|---|---|
| `MeasureTheory.aestronglyMeasurable_finset_prod_infinitePi` | the finite product `∏ i ∈ s, f i (x i)` is a.e.-strongly-measurable on `Measure.infinitePi μ` (the `𝕜` companion of the `ℝ≥0∞` lemma in `Lintegral.lean`) |
| `BochnerLane.integral_tprod_eq_tprod_integral_of_dominated` | T2's hypotheses **plus** an integrable `g` with `‖∏ i ∈ s, f i (x i)‖ ≤ g x` for all finite `s` a.e. ⟹ `∫ x, ∏' i, f i (x i) ∂(infinitePi μ) = L` |
| `BochnerLane.exists_integral_tprod_eq_tprod_integral_of_dominated` | the same in T2's `∃ L` shape |

Proof: dominated convergence along `atTop` on `Finset ι` (countably generated for countable `ι`, so
`tendsto_integral_filter_of_dominated_convergence` applies to the net directly — no enumeration of
`ι` and no `ℕ`-reindexing), with the integrals of the partial products evaluated by
`integral_finset_restrict_prod_eq_prod`; uniqueness of the limit in `ℝ` closes it.

Honest notes recorded in the file: `[Countable ι]` is genuinely needed (countably generated filter,
and the a.e. limit of a net needs a countable cofinal family to be a.e.-strongly-measurable); the
`Integrable` hypothesis of T2 is *retained but not consumed* by the proof (the finite-prefix
factorization needs only a.e.-strong measurability) — it is kept so the theorem is T2's statement
with one hypothesis added, and the file says so.

## 9. PR package state

Four files under `docs/pr/`, byte-identical copies (sha256 in `docs/PR.md`):
`Lintegral.lean` (unchanged), `Integral.lean` (unchanged), `Infinite.lean` (**new**, the Bochner
infinite index), `Counterexample.lean` (**extended** with `tprod_integral_needs_domination` — three
refutations now, each delimiting one hypothesis). `docs/PR.md` updated: four-file table, item 6 (the
identity), item 7 (three refutations), honest scope rewritten around the domination hypothesis, and
the file/hash table. The lane's `Targets.lean` was rewritten: the published statement is kept
verbatim as the statement of record, `target_is_false` refutes it, and the docstring points at the
proved dominated form.

## 10. Receipts (increment 3)

- **determinism**: two clean rebuilds (`rm -rf .lake/build/lib/lean/BochnerLane*` +
  `.lake/build/ir/BochnerLane*`, then `lake build`), both exit `0`, error-stripped logs
  byte-identical — sha256 `453befdc1fb0fe212844f8e9913795dc133af702f10a784cf3fd4e891c8e7330`, both
  runs; 3141 jobs, `Build completed successfully`.
- **axioms**: `#print axioms` on all thirteen theorems printed by `CheckAxioms.lean` →
  `[propext, Classical.choice, Quot.sound]` only (house triple), including `target_is_false` and
  `tprod_integral_needs_domination`.
- **purity**: `grep -rn "sorry\|admit\|native_decide"` over `BochnerLane/*.lean` and
  `BochnerLane.lean` → no hits.
- **numeric simulation before proof**: the two numbers the counterexample turns on —
  `∫ 2 · 1_{true} d(½·count) = 1`, and `(½)ⁿ → 0` — were checked before writing the Lean, then the
  Lean was checked against them.

## 11. Single next action (increment 4)

Prove the **uniform-integrability form** of the same identity: replace the pointwise domination
hypothesis of `integral_tprod_eq_tprod_integral_of_dominated` by the weakest condition the
counterexample actually violates — with `X_n := ∏ i ∈ range n, f i (x i)`, assume the family
`(X_n)` is uniformly integrable (Vitali) instead of pointwise dominated, and conclude
`∫ ∏' = L`.

What is on the shelf at this pin, measured rather than assumed:
`Mathlib/MeasureTheory/Function/UniformIntegrable.lean` has the `UnifIntegrable`/`UniformIntegrable`
API over a general index type, and `tendsto_Lp_finite_of_tendsto_ae` (line 540) is the Vitali
theorem in the shape "UI + a.e. convergence ⟹ `Lᵖ` convergence" — but it is **`ℕ`-indexed and
`[IsFiniteMeasure μ]`** (the product measure is a probability measure, so the finiteness is free;
the index is not). The `Finset ι` net must therefore be passed through a countable cofinal sequence
(`Filter.exists_seq_tendsto` / `tendsto_iff_seq_tendsto`, both available) or the UI hypothesis must
be stated over `Finset ι`-indexed families directly, and the `L¹ → ∫` bridge
(`‖∫ g‖ ≤ ‖g‖₁`) has to be located. Successor criterion: one new theorem in `Infinite.lean`,
sorry-free, same receipt trio, `docs/PR.md` and the `docs/pr/` copy refreshed, and the counterexample
verified to violate UI (it does: `tprod_integral_needs_domination` is the witness, since a UI family
with integrals `1` cannot converge a.e. to `0`).

---

# Increment 4 — the uniform-integrability (Vitali) form

## 12. Verdict

**Proved.** `BochnerLane.integral_tprod_eq_tprod_integral_of_uniformIntegrable`: same conclusion
`∫ x, ∏' i, f i (x i) ∂(infinitePi μ) = L` from the bare target's hypotheses (a.e.-strong
measurability, integrability, a.e. multipliability, `HasProd` of the one-dimensional integrals)
**plus** uniform integrability of the family of finite partial products

```
hUI : UniformIntegrable (fun s : Finset ι => fun x => ∏ i ∈ s, f i (x i)) 1 (Measure.infinitePi μ)
```

and no dominating function anywhere.  Plus its `∃ L` companion
`exists_integral_tprod_eq_tprod_integral_of_uniformIntegrable`.  Sorry-free, axiom-clean.

The hypothesis is the `Finset ι`-net form, not the `range n` form: it is the same family the
dominated form quantifies over (`∀ s : Finset ι`), so the two theorems differ only in the
uniformity condition.

## 13. What the pin actually had, measured (§11 predicted it; this is the measurement)

| Piece | At this pin | Verdict |
|---|---|---|
| UI of the net ⟹ `L¹` convergence | `tendsto_Lp_finite_of_tendsto_ae` (line 540) is **`ℕ`-indexed** | **missing for nets** |
| `L¹` convergence ⟹ `∫` convergence | `MeasureTheory.tendsto_integral_of_L1'` (line 388) is **filter-generic** (`{l : Filter ι}`) | present |
| UI + a.e. convergence (net) ⟹ limit is integrable | `UniformIntegrable.memLp_of_ae_tendsto` (line 998), general `u` with `[NeBot u] [IsCountablyGenerated u]` | present, and used |
| cofinal `ℕ` sequence in `atTop` on `Finset ι` | `Filter.exists_seq_monotone_tendsto_atTop_atTop`, from `[Countable ι]` | present |
| `[IsFiniteMeasure]` | the product measure is a probability measure | free |

So **exactly one bridge was missing** — the net-shaped Vitali step — and it is not missing in a way
that blocks the theorem: a monotone cofinal sequence `xs : ℕ → Finset ι` converts the net statement
into the `ℕ`-indexed one, and both limits (the `L¹`/integral limit and the `HasProd` limit) are read
off along the same sequence.  `UniformIntegrable.comp` does not exist at this pin, so the restriction
to the sequence is built inline from `UnifIntegrable.comp` plus the `eLpNorm` bound field.

## 14. Proof shape (`BochnerLane/Infinite.lean`: 10-line statement, 50-line proof)

1. `aestronglyMeasurable_finset_prod_infinitePi` gives measurability of every partial product;
   `hmul.mono fun x hx => hx.hasProd` gives a.e. convergence along `atTop` on `Finset ι`.
2. `hUI.memLp_of_ae_tendsto (u := atTop)` — the *net-generic* half of the UI API — makes the limit
   `∏' i, f i (x i)` `MemLp 1`.
3. `exists_seq_monotone_tendsto_atTop_atTop (Finset ι)` gives `xs`; `hUI` restricts to
   `fun n => ∏ i ∈ xs n, f i (x i)`, and a.e. convergence restricts with it.
4. Vitali (`tendsto_Lp_finite_of_tendsto_ae`, `p = 1`) gives `eLpNorm (P_{xs n} - ∏') 1 → 0`.
5. `tendsto_integral_of_L1'` upgrades that to `∫ P_{xs n} → ∫ ∏'`; `integral_finset_restrict_prod_eq_prod`
   rewrites each `∫ P_{xs n}`, and `HasProd` composed with `xs` gives the same sequence converging to
   `L`.  Uniqueness in `ℝ` closes it.

## 15. The witness, and what it does to the UI hypothesis

`tprod_integral_needs_domination` (`Counterexample.lean`) is cited in both docstrings as the
UI-violating witness.  Its partial products are `2^{#s}` on the all-true cylinder, whose measure is
`2^{-#s}` (`infinitePi_cylinder_allTrue`, machine-checked), so for every threshold `C` and every
`#s` with `2^{#s} ≥ C`

    ∫_{‖∏ i ∈ s, f i‖ ≥ C} ‖∏ i ∈ s, f i‖ = 2^{#s} · 2^{-#s} = 1,

and the sup over `s` of the tail integral is `1` for **every** `C` instead of tending to `0`: the
family is not uniformly integrable.  The UI hypothesis therefore excludes exactly the family that
refutes the bare target — it is not a hypothesis that dodges the counterexample, it is the condition
the counterexample violates.  (The arithmetic is prose in the docstrings; the cylinder mass it rests
on is the machine-checked lemma above.  The converse implication — domination ⟹ UI — is recorded as
prose in the same place, explicitly marked as not machine-checked in this package.)

## 16. Receipts (increment 4)

- **determinism**: two clean rebuilds (`rm -rf .lake/build/lib/lean/BochnerLane*` +
  `.lake/build/ir/BochnerLane*`, then `lake build`), both exit `0`, progress lines and their
  `(N.Ns)` timings stripped, remaining logs byte-identical — sha256
  `6a02e815b05b4ff8b98d7db0026d3d260b54ce4e0a9896a4faee699f3d70eb9c`, both runs; 3141 jobs,
  `Build completed successfully`.
- **axioms**: `#print axioms` on all **fifteen** theorems printed by `CheckAxioms.lean` (two new
  entries) → `[propext, Classical.choice, Quot.sound]` only (house triple).
- **purity**: `grep -rn "sorry\|admit\|native_decide"` over `BochnerLane/*.lean` and
  `BochnerLane.lean` → no hits.
- **PR copy refreshed**: `docs/pr/Infinite.lean` is a byte-identical copy of the lane file
  (sha256 `c6d833d37d6187c26503b2779ff316c2e4051676d4d6d3df85cd06a8f441d083`, both paths); the other
  three package files are unchanged from increment 3 and still hash as recorded in `docs/PR.md`.

## 17. Single next action (increment 5)

Machine-check the one implication that is still prose on both sides of the two exchange theorems:
**domination ⟹ uniform integrability**.  Concretely, prove in `Infinite.lean`

    (hg : Integrable g ν) (hdom : ∀ᵐ x ∂ν, ∀ s : Finset ι, ‖∏ i ∈ s, f i (x i)‖ ≤ g x)
      → UniformIntegrable (fun s => fun x => ∏ i ∈ s, f i (x i)) 1 ν

via `uniformIntegrable_of` (tail bound: `{‖P s‖ ≥ C} ⊆ {g ≥ C}`, so the tail `eLpNorm` is at most
`∫⁻_{g ≥ C} g`, which tends to `0` by the absolute continuity of `∫ · g`), then derive
`integral_tprod_eq_tprod_integral_of_dominated` **as a corollary** of the UI form so the package
carries one theorem instead of two.  Named remainder to locate first: the pin's lemma for
`∫_{g ≥ C} g → 0` (`Integrable.tendsto_setIntegral_*` family — the increment-4 grep for
`tendsto_setIntegral_ge_atTop_zero` in `Integral/Bochner/*.lean` and `Integral/*.lean` returned
nothing, so the name must be found before the proof is attempted, not after).
