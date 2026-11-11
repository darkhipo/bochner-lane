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

open MeasureTheory

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

end BochnerLane
