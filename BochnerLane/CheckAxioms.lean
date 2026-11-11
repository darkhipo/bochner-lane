import BochnerLane.Lintegral
import BochnerLane.Integral
import BochnerLane.Infinite
import BochnerLane.Counterexample
import BochnerLane.Targets

-- the `ℝ≥0∞` layer: finite factorization
#print axioms MeasureTheory.lintegral_fin_nat_prod_eq_prod
#print axioms MeasureTheory.lintegral_fintype_prod_eq_prod
#print axioms MeasureTheory.lintegral_finset_restrict_prod_eq_prod
-- the infinite index, both regimes
#print axioms MeasureTheory.lintegral_iSup_finset_prod_eq
#print axioms MeasureTheory.lintegral_iInf_finset_prod_eq
-- the Bochner finite prefix
#print axioms BochnerLane.integral_finset_restrict_prod_eq_prod
-- the Bochner infinite index, dominated form (the corrected target)
#print axioms MeasureTheory.aestronglyMeasurable_finset_prod_infinitePi
#print axioms BochnerLane.integral_tprod_eq_tprod_integral_of_dominated
#print axioms BochnerLane.exists_integral_tprod_eq_tprod_integral_of_dominated
-- the Bochner infinite index, uniform-integrability (Vitali) form
#print axioms BochnerLane.integral_tprod_eq_tprod_integral_of_uniformIntegrable
#print axioms BochnerLane.exists_integral_tprod_eq_tprod_integral_of_uniformIntegrable
-- the three refutations
#print axioms BochnerLane.independence_free_form_is_false
#print axioms BochnerLane.sup_form_lintegral_finset_prod_is_false
#print axioms BochnerLane.tprod_integral_needs_domination
#print axioms BochnerLane.target_is_false
