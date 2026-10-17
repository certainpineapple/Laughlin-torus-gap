import FermionM3Data
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open scoped ComplexOrder
namespace TorusLean.FermionM3

theorem reconstruction11 :
    OAI.Laughlin.Certificate.MatrixCompute.compressed 11 errorTable11 gramTable11 = matrixTable11 := by decide +kernel

theorem factorAcceptance11 :
    TorusLean.M2.rationalPSDCheck matrixTable11 factorTable11 pivotTable11 = true := by decide +kernel

theorem reconstructedPositive11 :
    (TorusLean.M2.complexify (OAI.Laughlin.Certificate.MatrixCompute.compressed 11 errorTable11 gramTable11)).PosSemidef := by
  rw [reconstruction11]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ factorAcceptance11

theorem officialErrorTable11 :
    errorTable11 = OAI.Laughlin.Certificate.candidateY_11 := by decide +kernel

theorem officialGramTable11 :
    gramTable11 = OAI.Laughlin.Certificate.candidateZ_11 := by decide +kernel

#print axioms reconstruction11

#print axioms factorAcceptance11

#print axioms reconstructedPositive11

#print axioms officialErrorTable11

#print axioms officialGramTable11

end TorusLean.FermionM3
