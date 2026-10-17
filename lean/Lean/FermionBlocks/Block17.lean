import FermionM3Data
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open scoped ComplexOrder
namespace TorusLean.FermionM3

theorem reconstruction17 :
    OAI.Laughlin.Certificate.MatrixCompute.compressed 17 errorTable17 gramTable17 = matrixTable17 := by decide +kernel

theorem factorAcceptance17 :
    TorusLean.M2.rationalPSDCheck matrixTable17 factorTable17 pivotTable17 = true := by decide +kernel

theorem reconstructedPositive17 :
    (TorusLean.M2.complexify (OAI.Laughlin.Certificate.MatrixCompute.compressed 17 errorTable17 gramTable17)).PosSemidef := by
  rw [reconstruction17]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ factorAcceptance17

theorem officialErrorTable17 :
    errorTable17 = OAI.Laughlin.Certificate.candidateY_17 := by decide +kernel

theorem officialGramTable17 :
    gramTable17 = OAI.Laughlin.Certificate.candidateZ_17 := by decide +kernel

#print axioms reconstruction17

#print axioms factorAcceptance17

#print axioms reconstructedPositive17

#print axioms officialErrorTable17

#print axioms officialGramTable17

end TorusLean.FermionM3
