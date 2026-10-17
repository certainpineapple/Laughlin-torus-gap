import FermionM3Data
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open scoped ComplexOrder
namespace TorusLean.FermionM3

theorem reconstruction23 :
    OAI.Laughlin.Certificate.MatrixCompute.compressed 23 errorTable23 gramTable23 = matrixTable23 := by decide +kernel

theorem factorAcceptance23 :
    TorusLean.M2.rationalPSDCheck matrixTable23 factorTable23 pivotTable23 = true := by decide +kernel

theorem reconstructedPositive23 :
    (TorusLean.M2.complexify (OAI.Laughlin.Certificate.MatrixCompute.compressed 23 errorTable23 gramTable23)).PosSemidef := by
  rw [reconstruction23]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ factorAcceptance23

theorem officialErrorTable23 :
    errorTable23 = OAI.Laughlin.Certificate.candidateY_23 := by decide +kernel

theorem officialGramTable23 :
    gramTable23 = OAI.Laughlin.Certificate.candidateZ_23 := by decide +kernel

#print axioms reconstruction23

#print axioms factorAcceptance23

#print axioms reconstructedPositive23

#print axioms officialErrorTable23

#print axioms officialGramTable23

end TorusLean.FermionM3
