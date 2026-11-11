import BochnerLane.Lintegral
import BochnerLane.Integral
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
-- the two refutations
#print axioms BochnerLane.independence_free_form_is_false
#print axioms BochnerLane.sup_form_lintegral_finset_prod_is_false
