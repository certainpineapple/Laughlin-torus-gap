import FermionM3Data
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open scoped ComplexOrder
namespace TorusLean.FermionM3

theorem reconstruction09 :
    OAI.Laughlin.Certificate.MatrixCompute.compressed 9 errorTable09 gramTable09 = matrixTable09 := by decide +kernel

theorem factorAcceptance09 :
    TorusLean.M2.rationalPSDCheck matrixTable09 factorTable09 pivotTable09 = true := by decide +kernel

theorem reconstructedPositive09 :
    (TorusLean.M2.complexify (OAI.Laughlin.Certificate.MatrixCompute.compressed 9 errorTable09 gramTable09)).PosSemidef := by
  rw [reconstruction09]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ factorAcceptance09

theorem officialErrorTable09 :
    errorTable09 = OAI.Laughlin.Certificate.candidateY_9 := by decide +kernel

theorem officialGramTable09 :
    gramTable09 = OAI.Laughlin.Certificate.candidateZ_9 := by decide +kernel

#print axioms reconstruction09

#print axioms factorAcceptance09

#print axioms reconstructedPositive09

#print axioms officialErrorTable09

#print axioms officialGramTable09

end TorusLean.FermionM3
