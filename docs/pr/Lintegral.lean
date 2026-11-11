/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Integrating finite products against a product measure

This file supplies the `ℝ≥0∞` layer of the product-integral identity: for a family of measures
`μ i` on `X i` and `ℝ≥0∞`-valued `F i`, a finite product `∏ i ∈ s, F i (x i)` integrates against
`Measure.pi μ` (and against `Measure.infinitePi μ`) to the product of the one-dimensional
integrals.

Mathlib has the two-fold case (`MeasureTheory.lintegral_prod_mul`) and, for `Measure.infinitePi`,
the pullback `MeasureTheory.lintegral_restrict_infinitePi`; nothing composed them over a general
`Finset`.  `MeasureTheory.lintegral_fintype_prod_eq_prod` is that composition, and
`MeasureTheory.lintegral_iSup_finset_prod_eq` passes to the directed supremum over finite
prefixes, which is the `ℝ≥0∞` form of the infinite product when every factor is `≥ 1`, while
`MeasureTheory.lintegral_iInf_finset_prod_eq` is the dual for factors `≤ 1` — the regime in which
`ENNReal.tprod_eq_iInf_prod` identifies the finite-prefix infimum with the infinite product.
Without a monotonicity hypothesis on one of those two sides the exchange is false
(`BochnerLane.sup_form_lintegral_finset_prod_is_false`).
-/

module

public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

open MeasureTheory

open scoped ENNReal Topology BigOperators

public section

namespace MeasureTheory

variable {ι : Type*} {X : ι → Type*} {mX : ∀ i, MeasurableSpace (X i)} {μ : (i : ι) → Measure (X i)}

/-! ### Finite index -/

set_option backward.isDefEq.respectTransparency false in
/-- A version of **Tonelli's theorem** in `n` variables for `ℝ≥0∞`-valued functions, for a
natural number `n`. -/
theorem lintegral_fin_nat_prod_eq_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : Fin n) → E i → ℝ≥0∞) (hf : ∀ i, AEMeasurable (f i) (μ i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hmeas : AEMeasurable (fun y : (i : Fin n) → E (Fin.succ i) =>
        ∏ i : Fin n, f (Fin.succ i) (y i)) (Measure.pi fun i : Fin n => μ i.succ) := by
      refine Finset.aemeasurable_fun_prod _ fun i _ => ?_
      exact (hf (Fin.succ i)).comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_eval (μ := fun i : Fin n => μ i.succ) i)
    calc
      ∫⁻ x : (i : Fin (n + 1)) → E i, ∏ i, f i (x i) ∂(Measure.pi μ)
          = ∫⁻ x : E 0 × ((i : Fin n) → E (Fin.succ i)),
              f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
              ∂((μ 0).prod (Measure.pi fun i : Fin n => μ i.succ)) := by
            rw [← (measurePreserving_piFinSuccAbove μ 0).symm.lintegral_comp_emb
              (MeasurableEquiv.measurableEmbedding _)]
            simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
              Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
              Fin.zero_succAbove, cast_eq, Fin.cons_zero]
      _ = (∫⁻ x, f 0 x ∂(μ 0)) *
            ∫⁻ y, ∏ i : Fin n, f (Fin.succ i) (y i) ∂(Measure.pi fun i : Fin n => μ i.succ) :=
          lintegral_prod_mul (f := f 0)
            (g := fun y : (i : Fin n) → E (Fin.succ i) => ∏ i, f (Fin.succ i) (y i))
            (hf 0) hmeas
      _ = (∫⁻ x, f 0 x ∂(μ 0)) * ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂(μ i.succ) := by
            rw [ih (fun i : Fin n => f (Fin.succ i)) fun i => hf (Fin.succ i)]
      _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]

/-- A version of **Tonelli's theorem** for `ℝ≥0∞`-valued functions with the variables indexed by a
general finite type. -/
theorem lintegral_fintype_prod_eq_prod {ι : Type*} [Fintype ι] {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : ι) → E i → ℝ≥0∞) (hf : ∀ i, AEMeasurable (f i) (μ i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft (fun i => μ i) e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_nat_prod_eq_prod (fun i => f (e i)) fun i => hf (e i)

/-! ### Infinite index, finite prefixes -/

section InfinitePi

variable [∀ i, IsProbabilityMeasure (μ i)]

/-- The finite product of a.e.-measurable functions is a.e.-measurable on the infinite product
space. -/
theorem aemeasurable_finset_prod_infinitePi (s : Finset ι) (F : (i : ι) → X i → ℝ≥0∞)
    (hF : ∀ i, AEMeasurable (F i) (μ i)) :
    AEMeasurable (fun x : (i : ι) → X i => ∏ i ∈ s, F i (x i)) (Measure.infinitePi μ) := by
  classical
  have hqmp : Measure.QuasiMeasurePreserving (s.restrict (π := X)) (Measure.infinitePi μ)
      (Measure.pi fun i : s => μ i) :=
    ⟨Finset.measurable_restrict s, by rw [Measure.infinitePi_map_restrict]⟩
  have h1 : AEMeasurable (fun y : (i : s) → X i => ∏ i ∈ (Finset.univ : Finset s),
      (fun (y : (i : s) → X i) => F i (y i)) y) (Measure.pi fun i : s => μ i) :=
    Finset.aemeasurable_fun_prod (Finset.univ : Finset s) fun i _ =>
      (hF (i : ι)).comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_eval (α := fun i : s => X (i : ι))
          (μ := fun i : s => μ (i : ι)) i)
  have key : (fun y : (i : s) → X i => ∏ i ∈ (Finset.univ : Finset s),
        (fun (y : (i : s) → X i) => F (i : ι) (y i)) y) ∘ (s.restrict (π := X))
      = fun x : (i : ι) → X i => ∏ i ∈ s, F i (x i) := by
    funext x
    exact Finset.prod_coe_sort s fun i => F i (x i)
  simpa only [key] using h1.comp_quasiMeasurePreserving hqmp

/-- **Finite-prefix factorization over an infinite product space.**  For a family of probability
measures `μ` and a finite `s`, the integral of `∏ i ∈ s, F i (x i)` against `Measure.infinitePi μ`
is the product of the one-dimensional integrals.  No independence hypothesis is needed:
independence of the coordinates of `Measure.infinitePi μ` is a consequence of the construction. -/
theorem lintegral_finset_restrict_prod_eq_prod (s : Finset ι) (F : (i : ι) → X i → ℝ≥0∞)
    (hF : ∀ i, AEMeasurable (F i) (μ i)) :
    ∫⁻ x : (i : ι) → X i, ∏ i ∈ s, F i (x i) ∂(Measure.infinitePi μ)
      = ∏ i ∈ s, ∫⁻ x, F i x ∂(μ i) := by
  classical
  have hmap : (Measure.infinitePi μ).map (s.restrict (π := X))
      = Measure.pi fun i : s => μ i :=
    Measure.infinitePi_map_restrict (μ := μ) (I := s)
  have hae : AEMeasurable (fun y : (i : s) → X i => ∏ i : s, F i (y i))
      ((Measure.infinitePi μ).map (s.restrict (π := X))) := by
    rw [hmap]
    have h1 : AEMeasurable (fun y : (i : s) → X i => ∏ i ∈ (Finset.univ : Finset s),
        (fun (y : (i : s) → X i) => F i (y i)) y) (Measure.pi fun i : s => μ i) :=
      Finset.aemeasurable_fun_prod (Finset.univ : Finset s) fun i _ =>
        (hF (i : ι)).comp_quasiMeasurePreserving
          (Measure.quasiMeasurePreserving_eval (α := fun i : s => X (i : ι))
            (μ := fun i : s => μ (i : ι)) i)
    simpa using h1
  calc
    ∫⁻ x : (i : ι) → X i, ∏ i ∈ s, F i (x i) ∂(Measure.infinitePi μ)
        = ∫⁻ x : (i : ι) → X i,
            (fun y : (i : s) → X i => ∏ i : s, F i (y i)) (s.restrict (π := X) x)
            ∂(Measure.infinitePi μ) := by
          congr 1
          funext x
          exact (Finset.prod_coe_sort s fun i => F i (x i)).symm
    _ = ∫⁻ y : (i : s) → X i, ∏ i : s, F i (y i)
            ∂((Measure.infinitePi μ).map (s.restrict (π := X))) := by
          rw [lintegral_map' hae (Finset.measurable_restrict s).aemeasurable]
    _ = ∫⁻ y : (i : s) → X i, ∏ i : s, F i (y i) ∂(Measure.pi fun i : s => μ i) := by
          rw [hmap]
    _ = ∏ i : s, ∫⁻ x, F i x ∂(μ i) :=
          lintegral_fintype_prod_eq_prod (fun i : s => F (i : ι)) fun i => hF (i : ι)
    _ = ∏ i ∈ s, ∫⁻ x, F i x ∂(μ i) :=
          Finset.prod_coe_sort s fun i : ι => ∫⁻ x, F i x ∂(μ i)

/-! ### The infinite index -/

/-- **The `ℝ≥0∞` product-integral identity over an infinite index, directed-supremum form.**

If every factor is at least `1`, the finite partial products `∏ i ∈ s, F i (x i)` increase with `s`,
so they are a directed family and `⨆ s, ∏ i ∈ s, F i (x i)` is the infinite product of the factors
at `x`.  Monotone convergence for directed families exchanges the integral with the supremum, and
each partial product integrates by `MeasureTheory.lintegral_finset_restrict_prod_eq_prod`.

No independence hypothesis: independence of the coordinates of `Measure.infinitePi μ` is derived
from the product-measure construction, not assumed. -/
theorem lintegral_iSup_finset_prod_eq [Countable ι] (F : (i : ι) → X i → ℝ≥0∞)
    (hF : ∀ i, AEMeasurable (F i) (μ i)) (h1 : ∀ i x, 1 ≤ F i x) :
    ∫⁻ x : (i : ι) → X i, (⨆ s : Finset ι, ∏ i ∈ s, F i (x i)) ∂(Measure.infinitePi μ)
      = ⨆ s : Finset ι, ∏ i ∈ s, ∫⁻ x, F i x ∂(μ i) := by
  classical
  have hm : ∀ s : Finset ι,
      AEMeasurable (fun x : (i : ι) → X i => ∏ i ∈ s, F i (x i)) (Measure.infinitePi μ) :=
    fun s => aemeasurable_finset_prod_infinitePi s F hF
  have hdir : Directed (· ≤ ·) fun s : Finset ι => fun x : (i : ι) → X i => ∏ i ∈ s, F i (x i) := by
    intro s t
    refine ⟨s ∪ t, fun x => ?_, fun x => ?_⟩
    · exact Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_union_left)
        fun i _ _ => h1 i (x i)
    · exact Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_union_right)
        fun i _ _ => h1 i (x i)
  calc
    ∫⁻ x : (i : ι) → X i, (⨆ s : Finset ι, ∏ i ∈ s, F i (x i)) ∂(Measure.infinitePi μ)
        = ⨆ s : Finset ι, ∫⁻ x : (i : ι) → X i, ∏ i ∈ s, F i (x i) ∂(Measure.infinitePi μ) :=
          lintegral_iSup_directed hm hdir
    _ = ⨆ s : Finset ι, ∏ i ∈ s, ∫⁻ x, F i x ∂(μ i) :=
          iSup_congr fun s => lintegral_finset_restrict_prod_eq_prod s F hF

/-- **The `ℝ≥0∞` product-integral identity over an infinite index, directed-infimum form.**

This is the dual of `MeasureTheory.lintegral_iSup_finset_prod_eq` and is the form taken by the
genuine infinite product of factors `≤ 1`: finite partial products *decrease* with `s`, and
`ENNReal.tprod_eq_iInf_prod` identifies `∏' i, F i (x i)` with `⨅ s, ∏ i ∈ s, F i (x i)`.  The
monotone convergence theorem for directed infima (`MeasureTheory.lintegral_iInf_directed_of_measurable`,
which needs an everywhere-measurable family with finite integrals) then exchanges the integral with
the infimum. -/
theorem lintegral_iInf_finset_prod_eq [Countable ι] (F : (i : ι) → X i → ℝ≥0∞)
    (hF : ∀ i, Measurable (F i)) (h1 : ∀ i x, F i x ≤ 1) :
    ∫⁻ x : (i : ι) → X i, (⨅ s : Finset ι, ∏ i ∈ s, F i (x i)) ∂(Measure.infinitePi μ)
      = ⨅ s : Finset ι, ∏ i ∈ s, ∫⁻ x, F i x ∂(μ i) := by
  classical
  have hm : ∀ s : Finset ι,
      Measurable (fun x : (i : ι) → X i => ∏ i ∈ s, F i (x i)) := by
    intro s
    exact Finset.measurable_fun_prod s fun i _ =>
      (hF i).comp (measurable_pi_apply i)
  have hint : ∀ s : Finset ι, ∫⁻ x : (i : ι) → X i, ∏ i ∈ s, F i (x i)
      ∂(Measure.infinitePi μ) ≠ ∞ := by
    intro s
    refine ne_of_lt (lt_of_le_of_lt ?_ ENNReal.one_lt_top)
    calc ∫⁻ x : (i : ι) → X i, ∏ i ∈ s, F i (x i) ∂(Measure.infinitePi μ)
        ≤ ∫⁻ _x : (i : ι) → X i, (1 : ℝ≥0∞) ∂(Measure.infinitePi μ) :=
          lintegral_mono fun x => Finset.prod_le_one fun i _ => h1 i (x i)
      _ = 1 := by simp
  have hμ : Measure.infinitePi μ ≠ 0 := by
    have h1 : (Measure.infinitePi μ) Set.univ = 1 := measure_univ
    intro h
    rw [h] at h1
    exact one_ne_zero h1.symm
  have hdir : Directed (· ≥ ·) fun s : Finset ι => fun x : (i : ι) → X i => ∏ i ∈ s, F i (x i) := by
    intro s t
    refine ⟨s ∪ t, fun x => ?_, fun x => ?_⟩
    · exact Finset.prod_le_prod_of_subset_of_le_one (Finset.subset_union_left)
        fun i _ _ => h1 i (x i)
    · exact Finset.prod_le_prod_of_subset_of_le_one (Finset.subset_union_right)
        fun i _ _ => h1 i (x i)
  calc
    ∫⁻ x : (i : ι) → X i, (⨅ s : Finset ι, ∏ i ∈ s, F i (x i)) ∂(Measure.infinitePi μ)
        = ⨅ s : Finset ι, ∫⁻ x : (i : ι) → X i, ∏ i ∈ s, F i (x i) ∂(Measure.infinitePi μ) :=
          lintegral_iInf_directed_of_measurable (μ := Measure.infinitePi μ) hμ hm hint hdir
    _ = ⨅ s : Finset ι, ∏ i ∈ s, ∫⁻ x, F i x ∂(μ i) :=
          iInf_congr fun s =>
            lintegral_finset_restrict_prod_eq_prod s F fun i => (hF i).aemeasurable

end InfinitePi

end MeasureTheory
