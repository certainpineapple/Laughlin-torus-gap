import FermionM3Data
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open scoped ComplexOrder
namespace TorusLean.FermionM3

theorem reconstruction16 :
    OAI.Laughlin.Certificate.MatrixCompute.compressed 16 errorTable16 gramTable16 = matrixTable16 := by decide +kernel

theorem factorAcceptance16 :
    TorusLean.M2.rationalPSDCheck matrixTable16 factorTable16 pivotTable16 = true := by decide +kernel

theorem reconstructedPositive16 :
    (TorusLean.M2.complexify (OAI.Laughlin.Certificate.MatrixCompute.compressed 16 errorTable16 gramTable16)).PosSemidef := by
  rw [reconstruction16]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ factorAcceptance16

theorem officialErrorTable16 :
    errorTable16 = OAI.Laughlin.Certificate.candidateY_16 := by decide +kernel

theorem officialGramTable16 :
    gramTable16 = OAI.Laughlin.Certificate.candidateZ_16 := by decide +kernel

#print axioms reconstruction16

#print axioms factorAcceptance16

#print axioms reconstructedPositive16

#print axioms officialErrorTable16

#print axioms officialGramTable16

end TorusLean.FermionM3
