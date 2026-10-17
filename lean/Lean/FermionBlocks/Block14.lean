import FermionM3Data
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open scoped ComplexOrder
namespace TorusLean.FermionM3

theorem reconstruction14 :
    OAI.Laughlin.Certificate.MatrixCompute.compressed 14 errorTable14 gramTable14 = matrixTable14 := by decide +kernel

theorem factorAcceptance14 :
    TorusLean.M2.rationalPSDCheck matrixTable14 factorTable14 pivotTable14 = true := by decide +kernel

theorem reconstructedPositive14 :
    (TorusLean.M2.complexify (OAI.Laughlin.Certificate.MatrixCompute.compressed 14 errorTable14 gramTable14)).PosSemidef := by
  rw [reconstruction14]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ factorAcceptance14

theorem officialErrorTable14 :
    errorTable14 = OAI.Laughlin.Certificate.candidateY_14 := by decide +kernel

theorem officialGramTable14 :
    gramTable14 = OAI.Laughlin.Certificate.candidateZ_14 := by decide +kernel

#print axioms reconstruction14

#print axioms factorAcceptance14

#print axioms reconstructedPositive14

#print axioms officialErrorTable14

#print axioms officialGramTable14

end TorusLean.FermionM3
