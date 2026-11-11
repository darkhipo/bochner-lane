/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Two readings of "the infinite product of `ℝ≥0∞`-valued functions", and why one is false

This file machine-checks two limitations of the `ℝ≥0∞` product-integral identity, so that they are
recorded as theorems rather than asserted in prose.

* `independence_free_form_is_false` — the product-integral identity does **not** survive dropping
  the product-measure construction: for one measure space and arbitrary integrable `X i`, it fails
  already at two coordinates.

* `sup_form_lintegral_finset_prod_is_false` — the supremum `⨆ s : Finset ι, ∏ i ∈ s, F i (x i)` is
  the infinite product only when every factor is at least `1`.  Without that hypothesis the family
  of finite partial products is not directed, so the integral cannot be exchanged with the
  supremum; the identity fails on the smallest possible index, `Unit`.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Probability.ProductMeasure

open MeasureTheory Filter

open scoped ENNReal Topology BigOperators

public section

namespace BochnerLane

/-- **Without independence, the product-integral identity fails.**

On `Fin 2` with counting measure, take `g = ![1, 2]`.  Then
`∫ g * g ∂count = 1² + 2² = 5` while `(∫ g ∂count) * (∫ g ∂count) = (1 + 2)² = 9`.

So `∫ ∏ᵢ Xᵢ = ∏ᵢ ∫ Xᵢ` needs either independence, or a product-measure construction that
derives it (`Measure.infinitePi`) — it cannot be obtained by replacing independence with
summability conditions on a *single* measure space. -/
theorem independence_free_form_is_false :
    ∃ g : Fin 2 → ℝ,
      ∫ b : Fin 2, g b * g b ∂(Measure.count : Measure (Fin 2))
        ≠ (∫ b : Fin 2, g b ∂(Measure.count : Measure (Fin 2)))
            * (∫ b : Fin 2, g b ∂(Measure.count : Measure (Fin 2))) := by
  refine ⟨![1, 2], ?_⟩
  simp only [integral_count, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-! ### The supremum over finite prefixes is not the infinite product in general -/

/-- The fair coin measure on `Bool`. -/
noncomputable def fairCoin : Measure Bool := (2 : ℝ≥0∞)⁻¹ • (Measure.count : Measure Bool)

lemma fairCoin_univ : fairCoin Set.univ = 1 := by
  rw [fairCoin, Measure.smul_apply, smul_eq_mul, ← Finset.coe_univ, Measure.count_apply_finset]
  simp only [Finset.card_univ, Fintype.card_bool, Nat.cast_ofNat]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

instance : IsProbabilityMeasure fairCoin := ⟨fairCoin_univ⟩

/-- For a single coordinate, the supremum of the finite partial products over `Finset Unit`
is `max 1 (f ())`: the empty prefix contributes `1`, and every factor below `1` only lowers the
product. -/
lemma iSup_finset_prod_unit (f : Unit → ℝ≥0∞) :
    (⨆ s : Finset Unit, ∏ i ∈ s, f i) = max 1 (f ()) := by
  refine le_antisymm (iSup_le ?_) (max_le ?_ ?_)
  · intro s
    rcases Finset.eq_empty_or_nonempty s with rfl | ⟨i, hi⟩
    · simp
    · have hs : s = Finset.univ := by
        refine Finset.eq_univ_of_forall fun j => ?_
        simpa [Subsingleton.elim j i] using hi
      rw [hs]
      simp
  · exact le_iSup_of_le ∅ (by simp)
  · exact le_iSup_of_le Finset.univ (by simp)

/-- The coin integral of the two-valued function used below. -/
lemma fairCoin_lintegral_indicator :
    ∫⁻ b : Bool, (if b then (2 : ℝ≥0∞) else 0) ∂fairCoin = 1 := by
  rw [fairCoin, lintegral_smul_measure, smul_eq_mul, lintegral_count, tsum_fintype,
    Fintype.sum_bool]
  simp only [Bool.false_eq_true, ite_true, ite_false, add_zero]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

/-- The coin integral of its own maximum with `1`. -/
lemma fairCoin_lintegral_max :
    ∫⁻ b : Bool, max 1 (if b then (2 : ℝ≥0∞) else 0) ∂fairCoin = (2 : ℝ≥0∞)⁻¹ * 3 := by
  rw [fairCoin, lintegral_smul_measure, smul_eq_mul, lintegral_count, tsum_fintype,
    Fintype.sum_bool]
  simp only [Bool.false_eq_true, ite_true, ite_false, max_eq_left, zero_le,
    max_eq_right (by norm_num : (1 : ℝ≥0∞) ≤ 2)]
  rw [show (2 : ℝ≥0∞) + 1 = 3 by norm_num]

lemma two_inv_mul_three_ne_one : (2 : ℝ≥0∞)⁻¹ * 3 ≠ 1 := by
  intro h
  have h2 : (2 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ * 3) = 2 * 1 := by rw [h]
  rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul] at h2
  norm_num at h2

/-- **The supremum form of the product-integral identity is false as stated.**

With one coordinate (`Unit`) carrying the fair coin and `F () = 2 · 1_{true}`, the left-hand side
is `∫ max 1 (F x) ∂coin = 3/2` while the right-hand side is `max 1 (∫ F ∂coin) = 1`.  The
hypothesis that every factor is at least `1` in
`MeasureTheory.lintegral_iSup_finset_prod_eq` is therefore not removable: without it the family of
partial products is not directed, and `⨆ s, ∏ i ∈ s, F i (x i)` is not the infinite product. -/
theorem sup_form_lintegral_finset_prod_is_false :
    ∃ F : Unit → Bool → ℝ≥0∞,
      ∫⁻ x : Unit → Bool, (⨆ s : Finset Unit, ∏ i ∈ s, F i (x i))
          ∂(Measure.infinitePi fun _ : Unit => fairCoin)
        ≠ ⨆ s : Finset Unit, ∏ i ∈ s, ∫⁻ x : Bool, F i x ∂fairCoin := by
  classical
  refine ⟨fun _ b => if b then (2 : ℝ≥0∞) else 0, ?_⟩
  have hL : ∫⁻ x : Unit → Bool,
        (⨆ s : Finset Unit, ∏ i ∈ s, (fun _ b => if b then (2 : ℝ≥0∞) else 0) i (x i))
        ∂(Measure.infinitePi fun _ : Unit => fairCoin) = (2 : ℝ≥0∞)⁻¹ * 3 := by
    rw [Measure.infinitePi_eq_pi]
    rw [← (measurePreserving_piUnique (fun _ : Unit => fairCoin)).symm.lintegral_comp_emb
      (MeasurableEquiv.measurableEmbedding _) (f := fun x : Unit → Bool =>
        ⨆ s : Finset Unit, ∏ i ∈ s, (fun _ b => if b then (2 : ℝ≥0∞) else 0) i (x i))]
    trans ∫⁻ a : Bool, max 1 (if a then (2 : ℝ≥0∞) else 0) ∂fairCoin
    · refine lintegral_congr fun a => ?_
      rw [iSup_finset_prod_unit]
      simp
    · exact fairCoin_lintegral_max
  have hR : (⨆ s : Finset Unit, ∏ i ∈ s,
        ∫⁻ x : Bool, (fun _ b => if b then (2 : ℝ≥0∞) else 0) i x ∂fairCoin) = 1 := by
    rw [iSup_finset_prod_unit]
    simp only [fairCoin_lintegral_indicator, max_eq_left, le_refl]
  rw [hL, hR]
  exact two_inv_mul_three_ne_one

/-! ### The Bochner infinite index does not survive without domination

`BochnerLane/Infinite.lean` proves the Bochner identity under one extra hypothesis: an integrable
function bounding all finite partial products.  This section shows that the hypothesis is not
removable — the remaining hypotheses (a.e. multipliability, and a product limit for the
one-dimensional integrals) do not suffice, even with every factor integrable on a probability
space.

The mechanism is the classical failure of uniform integrability.  With one coordinate type
`Bool` and the fair coin, the function `2 · 1_{true}` has integral `1`, so the partial products
over `{0, …, n-1}` all have integral `1`; but the set on which *every* coordinate is `true` has
measure zero, so the product is `0` almost everywhere and its integral is `0`.  Mass escapes at
infinity, exactly as for the martingale `2ⁿ · 1_{first n all true}`. -/

/-- The one-coordinate function `2 · 1_{true}` on the fair coin. -/
private noncomputable def coinDouble : Bool → ℝ := fun b => if b then 2 else 0

private lemma integrable_coinDouble : Integrable (coinDouble : Bool → ℝ) fairCoin := by
  refine Integrable.of_bound ?_ 2 ?_
  · measurability
  · filter_upwards with b
    cases b <;> norm_num [coinDouble]

private lemma integral_coinDouble : ∫ b : Bool, coinDouble b ∂fairCoin = 1 := by
  rw [fairCoin, integral_smul_measure, smul_eq_mul]
  simp only [integral_count, Fintype.sum_bool, coinDouble, Bool.false_eq_true, ite_true,
    ite_false, add_zero]
  norm_num

/-- The fair coin of a singleton. -/
private lemma fairCoin_singleton : fairCoin {true} = (2 : ℝ≥0∞)⁻¹ := by
  rw [fairCoin, Measure.smul_apply, smul_eq_mul, ← Finset.coe_singleton,
    Measure.count_apply_finset]
  simp

/-- The coordinates of `Measure.infinitePi` that are `true` on a finite set form a cylinder whose
measure is the corresponding finite product of coin flips. -/
private lemma infinitePi_cylinder_allTrue (n : ℕ) :
    (Measure.infinitePi fun _ : ℕ => fairCoin)
        (Set.pi (Finset.range n) fun _ : ℕ => ({true} : Set Bool))
      = (2 : ℝ≥0∞)⁻¹ ^ n := by
  rw [Measure.infinitePi_pi (fun _ : ℕ => fairCoin) (fun i _ => measurableSet_singleton true),
    Finset.prod_const, Finset.card_range, fairCoin_singleton]

/-- Almost every point of the infinite product of fair coins has a coordinate that is `false`:
the set of points that are `true` in every coordinate is contained in cylinders of measure
`2⁻ⁿ` for every `n`. -/
private lemma infinitePi_allTrue_eq_zero :
    (Measure.infinitePi fun _ : ℕ => fairCoin) {x : ℕ → Bool | ∀ i, x i = true} = 0 := by
  have hmono : ∀ n : ℕ,
      (Measure.infinitePi fun _ : ℕ => fairCoin) {x : ℕ → Bool | ∀ i, x i = true}
        ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
    intro n
    refine (measure_mono ?_).trans_eq (infinitePi_cylinder_allTrue n)
    intro x hx i _
    exact hx i
  refine le_antisymm ?_ zero_le
  refine ge_of_tendsto
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (2 : ℝ≥0∞)⁻¹ < 1)) ?_
  exact Eventually.of_forall hmono

/-- If a point has a `false` coordinate, the product of the coordinate functions converges to `0`:
every finite set containing that coordinate contributes the factor `0`. -/
private lemma hasProd_coinDouble_of_false {x : ℕ → Bool} (hx : ∃ i, x i = false) :
    HasProd (fun i : ℕ => coinDouble (x i)) 0 := by
  obtain ⟨i, hi⟩ := hx
  have hz : (fun s : Finset ℕ => ∏ j ∈ s, coinDouble (x j)) =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [Filter.eventually_atTop.2 ⟨{i}, fun s hs => hs⟩] with s hs
    exact Finset.prod_eq_zero (Finset.mem_of_subset hs (Finset.mem_singleton_self i))
      (by simp [coinDouble, hi])
  exact Tendsto.congr' hz.symm tendsto_const_nhds

/-- **The a.e.-multipliability hypothesis does not supply a dominating function.**

Take the infinite product of fair coins and the coordinate functions `f i = 2 · 1_{x i = true}`.
Every hypothesis of the Bochner product-integral identity other than domination holds:

* each `f i` is integrable with `∫ f i = 1`, so `HasProd (fun i => ∫ f i) 1`;
* the coordinates are a.e. multipliable — some coordinate is `false` a.e., and then the product
  is `0` (a coordinate equal to `0` makes every finite product containing it vanish).

Yet `∏' i, f i (x i) = 0` almost everywhere, so `∫ ∏' i, f i (x i) = 0 ≠ 1`.  The identity fails,
and the missing ingredient is uniform integrability — which is what the dominating function in
`BochnerLane.integral_tprod_eq_tprod_integral_of_dominated` supplies. -/
theorem tprod_integral_needs_domination :
    ∃ f : ℕ → Bool → ℝ,
      (∀ i, Integrable (f i) fairCoin) ∧
        (∀ᵐ x ∂(Measure.infinitePi fun _ : ℕ => fairCoin), Multipliable fun i => f i (x i)) ∧
          HasProd (fun i => ∫ x, f i x ∂fairCoin) 1 ∧
            (∫ x : ℕ → Bool, ∏' i, f i (x i)
              ∂(Measure.infinitePi fun _ : ℕ => fairCoin)) = 0 := by
  classical
  refine ⟨fun _ => coinDouble, fun _ => integrable_coinDouble, ?_, ?_, ?_⟩
  · have hae : ∀ᵐ x ∂(Measure.infinitePi fun _ : ℕ => fairCoin),
        x ∉ {x : ℕ → Bool | ∀ i, x i = true} :=
      compl_mem_ae_iff.2 infinitePi_allTrue_eq_zero
    filter_upwards [hae] with x hx
    push Not at hx
    obtain ⟨i, hi⟩ := hx
    exact ⟨0, hasProd_coinDouble_of_false ⟨i, by cases h : x i <;> simp_all⟩⟩
  · have hfun : (fun i : ℕ => ∫ x, (fun _ => coinDouble) i x ∂fairCoin) = fun _ => 1 :=
      funext fun _ => integral_coinDouble
    rw [hfun]
    exact hasProd_one
  · have hzero : (fun x : ℕ → Bool => ∏' i, coinDouble (x i))
        =ᵐ[Measure.infinitePi fun _ : ℕ => fairCoin] fun _ => 0 := by
      have hae : ∀ᵐ x ∂(Measure.infinitePi fun _ : ℕ => fairCoin),
          x ∉ {x : ℕ → Bool | ∀ i, x i = true} :=
        compl_mem_ae_iff.2 infinitePi_allTrue_eq_zero
      filter_upwards [hae] with x hx
      push Not at hx
      obtain ⟨i, hi⟩ := hx
      exact (hasProd_coinDouble_of_false ⟨i, by cases h : x i <;> simp_all⟩).tprod_eq
    rw [integral_congr_ae hzero]
    simp

end BochnerLane
