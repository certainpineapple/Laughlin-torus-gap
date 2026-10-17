import FermionM3Data
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open scoped ComplexOrder
namespace TorusLean.FermionM3

theorem reconstruction22 :
    OAI.Laughlin.Certificate.MatrixCompute.compressed 22 errorTable22 gramTable22 = matrixTable22 := by decide +kernel

theorem factorAcceptance22 :
    TorusLean.M2.rationalPSDCheck matrixTable22 factorTable22 pivotTable22 = true := by decide +kernel

theorem reconstructedPositive22 :
    (TorusLean.M2.complexify (OAI.Laughlin.Certificate.MatrixCompute.compressed 22 errorTable22 gramTable22)).PosSemidef := by
  rw [reconstruction22]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ factorAcceptance22

theorem officialErrorTable22 :
    errorTable22 = OAI.Laughlin.Certificate.candidateY_22 := by decide +kernel

theorem officialGramTable22 :
    gramTable22 = OAI.Laughlin.Certificate.candidateZ_22 := by decide +kernel

#print axioms reconstruction22

#print axioms factorAcceptance22

#print axioms reconstructedPositive22

#print axioms officialErrorTable22

#print axioms officialGramTable22

end TorusLean.FermionM3
