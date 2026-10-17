import FermionM3Data
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open scoped ComplexOrder
namespace TorusLean.FermionM3

theorem reconstruction12 :
    OAI.Laughlin.Certificate.MatrixCompute.compressed 12 errorTable12 gramTable12 = matrixTable12 := by decide +kernel

theorem factorAcceptance12 :
    TorusLean.M2.rationalPSDCheck matrixTable12 factorTable12 pivotTable12 = true := by decide +kernel

theorem reconstructedPositive12 :
    (TorusLean.M2.complexify (OAI.Laughlin.Certificate.MatrixCompute.compressed 12 errorTable12 gramTable12)).PosSemidef := by
  rw [reconstruction12]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ factorAcceptance12

theorem officialErrorTable12 :
    errorTable12 = OAI.Laughlin.Certificate.candidateY_12 := by decide +kernel

theorem officialGramTable12 :
    gramTable12 = OAI.Laughlin.Certificate.candidateZ_12 := by decide +kernel

#print axioms reconstruction12

#print axioms factorAcceptance12

#print axioms reconstructedPositive12

#print axioms officialErrorTable12

#print axioms officialGramTable12

end TorusLean.FermionM3
