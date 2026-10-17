import FermionM3Data
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open scoped ComplexOrder
namespace TorusLean.FermionM3

theorem reconstruction21 :
    OAI.Laughlin.Certificate.MatrixCompute.compressed 21 errorTable21 gramTable21 = matrixTable21 := by decide +kernel

theorem factorAcceptance21 :
    TorusLean.M2.rationalPSDCheck matrixTable21 factorTable21 pivotTable21 = true := by decide +kernel

theorem reconstructedPositive21 :
    (TorusLean.M2.complexify (OAI.Laughlin.Certificate.MatrixCompute.compressed 21 errorTable21 gramTable21)).PosSemidef := by
  rw [reconstruction21]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ factorAcceptance21

theorem officialErrorTable21 :
    errorTable21 = OAI.Laughlin.Certificate.candidateY_21 := by decide +kernel

theorem officialGramTable21 :
    gramTable21 = OAI.Laughlin.Certificate.candidateZ_21 := by decide +kernel

#print axioms reconstruction21

#print axioms factorAcceptance21

#print axioms reconstructedPositive21

#print axioms officialErrorTable21

#print axioms officialGramTable21

end TorusLean.FermionM3
