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

Exchanging the limit with the integral needs a *uniformity* hypothesis, because the index of the
limit is a net and pointwise integrability is not preserved by limits.  This file proves two
exchange theorems, one per uniformity regime:

* `integral_tprod_eq_tprod_integral_of_dominated` — uniformity by a dominating integrable function,
  exchanged with the Lebesgue dominated convergence theorem, in the filter form
  `MeasureTheory.tendsto_integral_filter_of_dominated_convergence` with `l = atTop` on `Finset ι`
  (countably generated as soon as `ι` is countable).  The hypothesis it needs is a dominating
  integrable function:

* `g` integrable, with `‖∏ i ∈ s, f i (x i)‖ ≤ g x` for **every** finite `s`, almost everywhere.

* `integral_tprod_eq_tprod_integral_of_uniformIntegrable` — uniformity by uniform integrability of
  the family of finite partial products, exchanged with Vitali's convergence theorem.  This is the
  hypothesis that dominated convergence cannot express: the family is only required to be
  *equi-absolutely-continuous*, with no single dominating function.

The uniformity over `s` is not decoration, and the two hypotheses are genuinely different.
`BochnerLane.tprod_integral_needs_domination` (`Counterexample.lean`) exhibits
`f i = 2 · 1_{x i = true}` on the fair coin: every hypothesis of the target *without* domination
holds — each `f i` is integrable with `∫ f i = 1`, the one dimensional integrals have product limit
`1`, and the coordinates are a.e. multipliable — yet `∏' i, f i (x i) = 0` a.e., so the integral is
`0 ≠ 1`.  Bounding the a.e. product `∏' i, ‖f i (x i)‖` does **not** suffice in general either: for
factors below `1` the finite partial products *decrease*, so `∏ i ∈ s, ‖f i‖` is not bounded above
by the infinite product.  The hypothesis below is therefore stated as a bound on all finite partial
products, which is what dominated convergence actually consumes.

That witness also shows that the uniform-integrability hypothesis is a real condition on the family,
not a restatement of the bare hypotheses: the counterexample's finite partial products are `2^{#s}`
on the all-true cylinder, whose measure is `2^{-#s}` (`infinitePi_cylinder_allTrue` in
`Counterexample.lean`), so
`∫_{‖∏ i ∈ s, f i‖ ≥ C} ‖∏ i ∈ s, f i‖ = 2^{#s} · 2^{-#s} = 1` for every `#s` with
`2^{#s} ≥ C`.  The supremum over `s` of that tail integral is therefore `1` for *every* threshold
`C` instead of tending to `0`, i.e. the family is **not** uniformly integrable, and the hypothesis
below genuinely excludes the counterexample rather than merely avoiding it.  (That computation is
prose here; the cylinder measure it uses is machine-checked in `Counterexample.lean`.  Domination by
an integrable `g`, conversely, does imply uniform integrability of the dominated family — the tail
integrals are bounded by `∫_{g ≥ C} g → 0` — so the hypothesis below is the *weaker* of the two;
that implication is machine-checked in this file (`BochnerLane.uniformIntegrable_finset_prod_infinitePi_of_dominated`,
via the tail limit `MeasureTheory.tendsto_integral_indicator_ge_atTop_zero`, which `Mathlib`
lacks and this file proves).)
-/

module

public import BochnerLane.Integral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

open MeasureTheory Filter

open scoped ENNReal Topology BigOperators NNReal

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

/-! ### The tail of an integrable function vanishes, and its consequence for uniform integrability

The pin's hoped-for Mathlib lemma `tendsto_setIntegral_ge_atTop_zero` does not exist: grepping
the `MeasureTheory` trees for the tail-integral-tends-to-zero statement
(`tendsto_lintegral_atTop_zero`-class, absolute-continuity-of-integral families, `UnifTight`,
`PeakFunction`) finds no such result — `UnifTight` is small-set tightness, `PeakFunction` is
approximations of identity, and the absolute-continuity statements are about small *sets*, not
large *values*.  This file therefore proves the tail limit itself, by dominated convergence
along `atTop` with bound `|g|` after passing `g` to a strongly measurable representative (level
sets of an a.e.-measurable function are not measurable, so the representative swap is not
decoration).  It is phrased with indicator functions — no `MeasurableSet` hypothesis, which
`Integrable g` alone would not supply — because that is the form in which
`uniformIntegrable_of` consumes tail bounds.  The corollary `uniformIntegrable_of_ae_dominated`
is the machine-checked form of the pin's prose remark that domination implies uniform
integrability. -/

/-- **The tail of an integrable function vanishes.**  For `g` integrable, the integral of `g`
over the set of points where it exceeds `C` — written with indicator functions, so no
`MeasurableSet` hypothesis is needed — tends to `0` as `C → ∞` along `ℕ`. -/
theorem tendsto_integral_indicator_ge_atTop_zero {α : Type*} {mα : MeasurableSpace α}
    {μ : Measure α} {g : α → ℝ} (hg : Integrable g μ) :
    Tendsto (fun C : ℕ => ∫ x, Set.indicator {x | (C : ℝ) ≤ g x} g x ∂μ) atTop (𝓝 0) := by
  classical
  -- pass to a strongly measurable representative; level sets of `g` itself need not be measurable
  obtain ⟨g', hgm, hgeq⟩ := hg.aestronglyMeasurable
  have hg'int : Integrable g' μ := hg.congr hgeq
  -- the integrands are a.e. equal, hence their integrals are
  have hcongr : ∀ C : ℕ, ∫ x, Set.indicator {x | (C : ℝ) ≤ g x} g x ∂μ
      = ∫ x, Set.indicator {x | (C : ℝ) ≤ g' x} g' x ∂μ := fun C =>
    integral_congr_ae (hgeq.mono fun x hx => by
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, hx])
  simp only [hcongr]
  -- now everything is honest: the level sets are measurable
  have hTmeas : ∀ C : ℕ, MeasurableSet {x | (C : ℝ) ≤ g' x} :=
    fun C => stronglyMeasurable_const.measurableSet_le hgm
  have h := tendsto_integral_filter_of_dominated_convergence
    (bound := fun x => |g' x|)
    (F := fun (C : ℕ) x => Set.indicator {x | (C : ℝ) ≤ g' x} g' x)
    (f := fun _ => (0 : ℝ)) (Eventually.of_forall fun C =>
      (hgm.indicator (hTmeas C)).aestronglyMeasurable)
    (Eventually.of_forall fun C => Eventually.of_forall fun x => by
      by_cases h : (C : ℝ) ≤ g' x
      · simp [h]
      · simp [h])
    hg'int.abs
    (Eventually.of_forall fun x => by
      obtain ⟨n, hn⟩ := exists_nat_gt (g' x)
      exact (tendsto_const_nhds (x := (0 : ℝ))).congr' (by
        filter_upwards [Filter.eventually_ge_atTop n] with m hm
        have hC : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        simp [not_le.2 (lt_of_lt_of_le hn hC)]))
  simpa using h

/-- A family of a.e.-strongly-measurable functions dominated a.e. by one integrable real
function is uniformly integrable at exponent `1` — the machine-checked form of the remark that
domination implies uniform integrability: every tail `eLpNorm` is bounded by the tail of `g`,
which vanishes by `tendsto_integral_indicator_ge_atTop_zero`. -/
theorem uniformIntegrable_of_ae_dominated {ι' : Type*} {α : Type*} {mα : MeasurableSpace α}
    {E : Type*} [NormedAddCommGroup E] {μ : Measure α} [IsFiniteMeasure μ] {F : ι' → α → E}
    {g : α → ℝ} (hFmeas : ∀ i, AEStronglyMeasurable (F i) μ) (hg : Integrable g μ)
    (hdom : ∀ i, ∀ᵐ x ∂μ, ‖F i x‖ ≤ g x) : UniformIntegrable F 1 μ := by
  classical
  -- enorm respects domination by a nonnegative real
  have hmono {a : E} {b : ℝ} (hab : ‖a‖ ≤ b) (hb : 0 ≤ b) : ‖a‖ₑ ≤ ‖b‖ₑ := by
    rw [← ofReal_norm a, Real.enorm_eq_ofReal hb]
    exact ENNReal.ofReal_le_ofReal hab
  -- measurable representative of `g`, and the family's common `L¹` mass
  obtain ⟨g', hgm, hgeq⟩ := hg.aestronglyMeasurable
  have hg'int : Integrable g' μ := hg.congr hgeq
  have hbnd : ∀ i, eLpNorm (F i) 1 μ ≤ ENNReal.ofReal (∫ x, |g' x| ∂μ) := by
    intro i
    calc eLpNorm (F i) 1 μ ≤ eLpNorm g' 1 μ :=
          eLpNorm_mono_enorm_ae (hFmeas i) (by
            filter_upwards [hdom i, hgeq] with x hx hxg
            rw [← hxg]
            exact hmono hx (le_trans (norm_nonneg _) hx))
      _ ≤ ENNReal.ofReal (∫ x, |g' x| ∂μ) := by
          rw [eLpNorm_one_eq_lintegral_enorm hgm.aestronglyMeasurable]
          exact le_of_eq ((lintegral_congr_ae (Eventually.of_forall fun x =>
            Real.enorm_eq_ofReal_abs (g' x))).trans
            (ofReal_integral_eq_lintegral_ofReal hg'int.abs (Eventually.of_forall
              fun x => abs_nonneg (g' x))).symm)
  refine uniformIntegrable_of le_rfl ENNReal.one_ne_top hFmeas fun ε hε => ?_
  rcases eq_or_ne ε ⊤ with htop | htop
  · exact ⟨0, fun i => by simp [htop]⟩
  have hεr : (0 : ℝ) < ε.toReal := by
    simpa using (ENNReal.toReal_lt_toReal (by simp) htop).mpr hε
  obtain ⟨C, hC⟩ : ∃ C : ℕ, ∫ x, Set.indicator {x | (C : ℝ) ≤ g' x} g' x ∂μ ≤ ε.toReal := by
    have hex := ((tendsto_integral_indicator_ge_atTop_zero hg'int).eventually
      (eventually_lt_nhds hεr)).exists
    exact ⟨hex.choose, le_of_lt hex.choose_spec⟩
  refine ⟨(C : ℝ≥0), fun i => ?_⟩
  -- per family member: representative, honest level sets, a.e. congruence of indicators
  obtain ⟨Gi, hGm, hGeq⟩ := hFmeas i
  have hCnat : (((C : ℝ≥0) : ℝ) : ℝ) = (C : ℝ) := by norm_cast
  set S' : Set α := {x | (C : ℝ≥0) ≤ ‖Gi x‖₊} with hS'def
  set T' : Set α := {x | (C : ℝ) ≤ g' x} with hT'def
  have hS'meas : MeasurableSet S' := stronglyMeasurable_const.measurableSet_le hGm.nnnorm
  have hT'meas : MeasurableSet T' := stronglyMeasurable_const.measurableSet_le hgm
  have hTailMeas : AEStronglyMeasurable (T'.indicator g') μ :=
    (hgm.indicator hT'meas).aestronglyMeasurable
  have hint' : Integrable (T'.indicator g') μ := by
    refine hg'int.abs.mono' hTailMeas ?_
    filter_upwards with x
    by_cases hx : x ∈ T' <;> simp [hx]
  calc eLpNorm ({x | (C : ℝ≥0) ≤ ‖F i x‖₊}.indicator (F i)) 1 μ
      = eLpNorm (S'.indicator Gi) 1 μ := by
        refine eLpNorm_congr_ae (hGeq.mono fun x hx => ?_)
        simp only [hS'def, Set.indicator_apply, Set.mem_ofPred_eq, hx]
    _ ≤ eLpNorm (T'.indicator g') 1 μ := by
        refine eLpNorm_mono_enorm_ae ((hGm.indicator hS'meas).aestronglyMeasurable) ?_
        filter_upwards [hdom i, hGeq, hgeq] with x hx hxF hxg
        have hnorm : ‖Gi x‖ = ‖F i x‖ := by rw [hxF]
        by_cases hsm : x ∈ S'
        · have hxg' : (C : ℝ) ≤ g' x := by
            have hsm' : (((C : ℝ≥0) : ℝ) : ℝ) ≤ (((‖Gi x‖₊ : ℝ≥0) : ℝ) : ℝ) := hsm
            rw [hCnat] at hsm'
            calc (C : ℝ) ≤ ‖Gi x‖ := hsm'
              _ = ‖F i x‖ := hnorm
              _ ≤ g x := hx
              _ = g' x := hxg
          rw [Set.indicator_of_mem hsm, Set.indicator_of_mem (show x ∈ T' by
            rw [hT'def, Set.mem_ofPred_eq]; exact hxg')]
          exact hmono (by rw [hnorm, ← hxg]; exact hx)
            (le_trans (by exact Nat.cast_nonneg C) hxg')
        · rw [Set.indicator_of_notMem hsm]
          simp [enorm_zero]
    _ = ENNReal.ofReal (∫ x, T'.indicator g' x ∂μ) := by
        have hnn : (0 : α → ℝ) ≤ᵐ[μ] T'.indicator g' := by
          filter_upwards with x
          by_cases hx : x ∈ T'
          · rw [Set.indicator_of_mem hx]
            have hxT : (C : ℝ) ≤ g' x := by
              rw [hT'def, Set.mem_ofPred_eq] at hx
              exact hx
            exact le_trans (by exact Nat.cast_nonneg C) hxT
          · rw [Set.indicator_of_notMem hx]
            exact le_refl 0
        rw [eLpNorm_one_eq_lintegral_enorm hTailMeas,
          ofReal_integral_eq_lintegral_ofReal hint' hnn]
        refine lintegral_congr_ae (Eventually.of_forall fun x => ?_)
        by_cases hx : x ∈ T'
        · have hxT : (C : ℝ) ≤ g' x := by
            rw [hT'def, Set.mem_ofPred_eq] at hx
            exact hx
          show ‖T'.indicator g' x‖ₑ = ENNReal.ofReal (T'.indicator g' x)
          rw [Set.indicator_of_mem hx, Real.enorm_eq_ofReal_abs,
            abs_of_nonneg (le_trans (by exact Nat.cast_nonneg C) hxT)]
        · show ‖T'.indicator g' x‖ₑ = ENNReal.ofReal (T'.indicator g' x)
          rw [Set.indicator_of_notMem hx]
          simp
    _ ≤ ε := ENNReal.ofReal_le_of_le_toReal hC

end MeasureTheory

namespace BochnerLane

variable {ι : Type*} {X : ι → Type*} {mX : ∀ i, MeasurableSpace (X i)}
  {μ : (i : ι) → Measure (X i)} [∀ i, IsProbabilityMeasure (μ i)]

set_option linter.unusedVariables false in
/-- **The Bochner product-integral identity over an infinite index, uniform-integrability form.**

Same statement as `integral_tprod_eq_tprod_integral_of_dominated`, with the dominating integrable
function replaced by uniform integrability of the family of finite partial products
`fun s : Finset ι => fun x => ∏ i ∈ s, f i (x i)` — equi-absolute-continuity of that family's
integrals, with no single dominating function anywhere in the hypotheses.

The exchange runs through Vitali's convergence theorem rather than dominated convergence, and the
two uniformity hypotheses are not interchangeable.  `tprod_integral_needs_domination` shows the
bare target fails for a family whose partial products are *not* uniformly integrable (their tail
integrals are identically `1`), so this hypothesis excludes the counterexample rather than merely
avoiding it.  Conversely, domination by an integrable `g` implies uniform integrability of the
dominated family (`uniformIntegrable_finset_prod_infinitePi_of_dominated`, machine-checked below
via the tail lemma `MeasureTheory.tendsto_integral_indicator_ge_atTop_zero`), so this theorem is
the primary exchange result of the file: the dominated form is recovered from it as a
convenience wrapper.

Vitali's theorem at this pin (`tendsto_Lp_finite_of_tendsto_ae`) is stated for `ℕ`-indexed
sequences, while the limit index here is the `Finset ι` net.  The nets are reconciled by choosing a
monotone cofinal sequence of finite sets (`Filter.exists_seq_monotone_tendsto_atTop_atTop`, available
because `ι` is countable) and reading off both limits along it; the `L¹ → ∫` step is
`MeasureTheory.tendsto_integral_of_L1'`, which is filter-generic. -/
theorem integral_tprod_eq_tprod_integral_of_uniformIntegrable [Countable ι]
    {f : (i : ι) → X i → ℝ} {L : ℝ}
    (hf : ∀ i, AEStronglyMeasurable (f i) (μ i))
    (hfi : ∀ i, Integrable (f i) (μ i))
    (hmul : ∀ᵐ x ∂(Measure.infinitePi μ), Multipliable fun i => f i (x i))
    (hL : HasProd (fun i => ∫ x, f i x ∂(μ i)) L)
    (hUI : UniformIntegrable
      (fun s : Finset ι => fun x : (i : ι) → X i => ∏ i ∈ s, f i (x i)) 1
      (Measure.infinitePi μ)) :
    ∫ x : (i : ι) → X i, ∏' i, f i (x i) ∂(Measure.infinitePi μ) = L := by
  classical
  have hmeas : ∀ s : Finset ι,
      AEStronglyMeasurable (fun x : (i : ι) → X i => ∏ i ∈ s, f i (x i))
        (Measure.infinitePi μ) :=
    fun s => MeasureTheory.aestronglyMeasurable_finset_prod_infinitePi s f hf
  -- a.e. convergence of the finite partial products along the net `atTop` on `Finset ι`
  have hae : ∀ᵐ x ∂(Measure.infinitePi μ),
      Tendsto (fun s : Finset ι => ∏ i ∈ s, f i (x i)) atTop (𝓝 (∏' i, f i (x i))) :=
    hmul.mono fun x hx => hx.hasProd
  -- uniform integrability makes the a.e. limit integrable
  have hGint : MemLp (fun x : (i : ι) → X i => ∏' i, f i (x i)) 1 (Measure.infinitePi μ) :=
    hUI.memLp_of_ae_tendsto (u := atTop) hae
  -- a monotone cofinal sequence of finite sets, to meet Vitali's `ℕ`-indexed statement
  obtain ⟨xs, -, hxs⟩ := exists_seq_monotone_tendsto_atTop_atTop (Finset ι)
  have hUIseq : UniformIntegrable
      (fun n : ℕ => fun x : (i : ι) → X i => ∏ i ∈ xs n, f i (x i)) 1
      (Measure.infinitePi μ) := by
    obtain ⟨C, hC⟩ := hUI.2
    exact ⟨hUI.1.comp xs, C, fun n => hC (xs n)⟩
  have haeseq : ∀ᵐ x ∂(Measure.infinitePi μ),
      Tendsto (fun n : ℕ => ∏ i ∈ xs n, f i (x i)) atTop (𝓝 (∏' i, f i (x i))) :=
    hae.mono fun x hx => hx.comp hxs
  -- Vitali: convergence in `L¹`
  have hLp : Tendsto (fun n : ℕ => eLpNorm
      ((fun x : (i : ι) → X i => ∏ i ∈ xs n, f i (x i)) - fun x => ∏' i, f i (x i)) 1
      (Measure.infinitePi μ)) atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendsto_ae (p := 1) le_rfl ENNReal.one_ne_top
      (fun n => hmeas (xs n)) hGint hUIseq.1 haeseq
  have hInt : ∀ᶠ n : ℕ in atTop,
      Integrable (fun x : (i : ι) → X i => ∏ i ∈ xs n, f i (x i))
        (Measure.infinitePi μ) :=
    Eventually.of_forall fun n => memLp_one_iff_integrable.mp (hUIseq.memLp n)
  -- `L¹` convergence upgrades to convergence of the integrals
  have hbridge : Tendsto
      (fun n : ℕ => ∫ x : (i : ι) → X i, ∏ i ∈ xs n, f i (x i)
        ∂(Measure.infinitePi μ)) atTop
      (𝓝 (∫ x : (i : ι) → X i, ∏' i, f i (x i) ∂(Measure.infinitePi μ))) :=
    tendsto_integral_of_L1' (fun x : (i : ι) → X i => ∏' i, f i (x i)) hInt hLp
  have hfac : ∀ n : ℕ, ∫ x : (i : ι) → X i, ∏ i ∈ xs n, f i (x i)
      ∂(Measure.infinitePi μ) = ∏ i ∈ xs n, ∫ x, f i x ∂(μ i) :=
    fun n => integral_finset_restrict_prod_eq_prod (μ := μ) (xs n) hf
  -- the finite-prefix factorization carries `HasProd` to the same sequence of integrals
  have hseq : Tendsto (fun n : ℕ => ∏ i ∈ xs n, ∫ x, f i x ∂(μ i)) atTop (𝓝 L) := by
    have hprod : Tendsto (fun s : Finset ι => ∏ i ∈ s, ∫ x, f i x ∂(μ i)) atTop (𝓝 L) := hL
    exact hprod.comp hxs
  have hseq' : Tendsto (fun n : ℕ => ∏ i ∈ xs n, ∫ x, f i x ∂(μ i)) atTop
      (𝓝 (∫ x : (i : ι) → X i, ∏' i, f i (x i) ∂(Measure.infinitePi μ))) :=
    hbridge.congr' (Eventually.of_forall fun n => by rw [hfac n])
  exact tendsto_nhds_unique hseq' hseq

/-- The uniform-integrability form in the `∃ L` shape of the target statement `Targets.lean`. -/
theorem exists_integral_tprod_eq_tprod_integral_of_uniformIntegrable [Countable ι]
    {f : (i : ι) → X i → ℝ}
    (hf : ∀ i, AEStronglyMeasurable (f i) (μ i))
    (hfi : ∀ i, Integrable (f i) (μ i))
    (hmul : ∀ᵐ x ∂(Measure.infinitePi μ), Multipliable fun i => f i (x i))
    (hL : ∃ L, HasProd (fun i => ∫ x, f i x ∂(μ i)) L)
    (hUI : UniformIntegrable
      (fun s : Finset ι => fun x : (i : ι) → X i => ∏ i ∈ s, f i (x i)) 1
      (Measure.infinitePi μ)) :
    ∃ L, HasProd (fun i => ∫ x, f i x ∂(μ i)) L ∧
      ∫ x : (i : ι) → X i, ∏' i, f i (x i) ∂(Measure.infinitePi μ) = L := by
  obtain ⟨L, hL⟩ := hL
  exact ⟨L, hL, integral_tprod_eq_tprod_integral_of_uniformIntegrable hf hfi hmul hL hUI⟩

set_option linter.unusedVariables false in
/-- The machine-checked form of the remark that domination implies uniform integrability, for
the family of finite partial products: an integrable dominating function `g` makes the family
`fun s x => ∏ i ∈ s, f i (x i)` uniformly integrable at exponent `1`.  Each tail `eLpNorm` is
bounded by `∫ [g ≥ C] g` through the a.e. pointwise bound
`{x | C ≤ ‖∏ i ∈ s, f i‖} ⊆ {x | C ≤ g}`, and that tail vanishes by
`MeasureTheory.tendsto_integral_indicator_ge_atTop_zero` — the tail lemma `Mathlib` lacks. -/
theorem uniformIntegrable_finset_prod_infinitePi_of_dominated
    {f : (i : ι) → X i → ℝ}
    (hf : ∀ i, AEStronglyMeasurable (f i) (μ i))
    {g : ((i : ι) → X i) → ℝ} (hg : Integrable g (Measure.infinitePi μ))
    (hdom : ∀ᵐ x ∂(Measure.infinitePi μ), ∀ s : Finset ι, ‖∏ i ∈ s, f i (x i)‖ ≤ g x) :
    UniformIntegrable (fun s : Finset ι => fun x : (i : ι) → X i => ∏ i ∈ s, f i (x i)) 1
      (Measure.infinitePi μ) :=
  MeasureTheory.uniformIntegrable_of_ae_dominated
    (fun s => MeasureTheory.aestronglyMeasurable_finset_prod_infinitePi s f hf) hg
    (fun s => hdom.mono fun x hx => hx s)

/-- **The Bochner product-integral identity over an infinite index, dominated form.**

For `ℝ`-valued `f i` whose coordinates are a.e. multipliable and whose one-dimensional Bochner
integrals have product limit `L`, and under an integrable dominating function for the finite
partial products, the Bochner integral of the a.e.-defined infinite product is `L`.

Convenience wrapper: the exchange runs through the uniform-integrability form
(`integral_tprod_eq_tprod_integral_of_uniformIntegrable`), fed by
`uniformIntegrable_finset_prod_infinitePi_of_dominated` — domination by an integrable `g` is
the stronger uniformity hypothesis, and the implication is proved, not assumed.

The integrability hypothesis `hfi` belongs to the shape of the target statement (it is what makes
`fun i => ∫ x, f i x ∂(μ i)` the family one means to take a product of) but the proof does not
consume it.  It is retained rather than dropped so that the theorem is the same statement as
`Targets.lean`'s, with the one hypothesis T2 was missing added. -/
theorem integral_tprod_eq_tprod_integral_of_dominated [Countable ι]
    {f : (i : ι) → X i → ℝ} {L : ℝ}
    (hf : ∀ i, AEStronglyMeasurable (f i) (μ i))
    (hfi : ∀ i, Integrable (f i) (μ i))
    (hmul : ∀ᵐ x ∂(Measure.infinitePi μ), Multipliable fun i => f i (x i))
    (hL : HasProd (fun i => ∫ x, f i x ∂(μ i)) L)
    {g : ((i : ι) → X i) → ℝ} (hg : Integrable g (Measure.infinitePi μ))
    (hdom : ∀ᵐ x ∂(Measure.infinitePi μ), ∀ s : Finset ι, ‖∏ i ∈ s, f i (x i)‖ ≤ g x) :
    ∫ x : (i : ι) → X i, ∏' i, f i (x i) ∂(Measure.infinitePi μ) = L :=
  integral_tprod_eq_tprod_integral_of_uniformIntegrable hf hfi hmul hL
    (uniformIntegrable_finset_prod_infinitePi_of_dominated hf hg hdom)

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
