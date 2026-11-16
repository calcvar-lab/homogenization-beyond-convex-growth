import Homogenization

/-! Prints the axioms used by the main theorems. Expected output for each of them:
`[propext, Classical.choice, Quot.sound]`. Run with `lake env lean scripts/CheckAxioms.lean`. -/

#print axioms Homogenization.main_Ggrowth_final_unconditional
#print axioms Homogenization.citedAHM14_holds
#print axioms Homogenization.citedVitaliEnvelope_holds
#print axioms Homogenization.localLowerBound
#print axioms Homogenization.th_product_iii_unconditional
#print axioms Homogenization.properDomainWv_sep_iv
#print axioms Homogenization.properDomainWSharpExample_pd_iv
#print axioms Homogenization.sepConcrete_sep_iv
