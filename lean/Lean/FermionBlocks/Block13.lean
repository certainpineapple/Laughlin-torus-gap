import FermionM3Data
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open scoped ComplexOrder
namespace TorusLean.FermionM3

theorem reconstruction13 :
    OAI.Laughlin.Certificate.MatrixCompute.compressed 13 errorTable13 gramTable13 = matrixTable13 := by decide +kernel

theorem factorAcceptance13 :
    TorusLean.M2.rationalPSDCheck matrixTable13 factorTable13 pivotTable13 = true := by decide +kernel

theorem reconstructedPositive13 :
    (TorusLean.M2.complexify (OAI.Laughlin.Certificate.MatrixCompute.compressed 13 errorTable13 gramTable13)).PosSemidef := by
  rw [reconstruction13]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ factorAcceptance13

theorem officialErrorTable13 :
    errorTable13 = OAI.Laughlin.Certificate.candidateY_13 := by decide +kernel

theorem officialGramTable13 :
    gramTable13 = OAI.Laughlin.Certificate.candidateZ_13 := by decide +kernel

#print axioms reconstruction13

#print axioms factorAcceptance13

#print axioms reconstructedPositive13

#print axioms officialErrorTable13

#print axioms officialGramTable13

end TorusLean.FermionM3
