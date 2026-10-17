import FermionM3Data
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open scoped ComplexOrder
namespace TorusLean.FermionM3

theorem reconstruction10 :
    OAI.Laughlin.Certificate.MatrixCompute.compressed 10 errorTable10 gramTable10 = matrixTable10 := by decide +kernel

theorem factorAcceptance10 :
    TorusLean.M2.rationalPSDCheck matrixTable10 factorTable10 pivotTable10 = true := by decide +kernel

theorem reconstructedPositive10 :
    (TorusLean.M2.complexify (OAI.Laughlin.Certificate.MatrixCompute.compressed 10 errorTable10 gramTable10)).PosSemidef := by
  rw [reconstruction10]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ factorAcceptance10

theorem officialErrorTable10 :
    errorTable10 = OAI.Laughlin.Certificate.candidateY_10 := by decide +kernel

theorem officialGramTable10 :
    gramTable10 = OAI.Laughlin.Certificate.candidateZ_10 := by decide +kernel

#print axioms reconstruction10

#print axioms factorAcceptance10

#print axioms reconstructedPositive10

#print axioms officialErrorTable10

#print axioms officialGramTable10

end TorusLean.FermionM3
