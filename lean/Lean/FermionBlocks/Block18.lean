import FermionM3Data
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open scoped ComplexOrder
namespace TorusLean.FermionM3

theorem reconstruction18 :
    OAI.Laughlin.Certificate.MatrixCompute.compressed 18 errorTable18 gramTable18 = matrixTable18 := by decide +kernel

theorem factorAcceptance18 :
    TorusLean.M2.rationalPSDCheck matrixTable18 factorTable18 pivotTable18 = true := by decide +kernel

theorem reconstructedPositive18 :
    (TorusLean.M2.complexify (OAI.Laughlin.Certificate.MatrixCompute.compressed 18 errorTable18 gramTable18)).PosSemidef := by
  rw [reconstruction18]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ factorAcceptance18

theorem officialErrorTable18 :
    errorTable18 = OAI.Laughlin.Certificate.candidateY_18 := by decide +kernel

theorem officialGramTable18 :
    gramTable18 = OAI.Laughlin.Certificate.candidateZ_18 := by decide +kernel

#print axioms reconstruction18

#print axioms factorAcceptance18

#print axioms reconstructedPositive18

#print axioms officialErrorTable18

#print axioms officialGramTable18

end TorusLean.FermionM3
