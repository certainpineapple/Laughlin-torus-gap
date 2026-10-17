import FermionM3Data
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open scoped ComplexOrder
namespace TorusLean.FermionM3

theorem reconstruction20 :
    OAI.Laughlin.Certificate.MatrixCompute.compressed 20 errorTable20 gramTable20 = matrixTable20 := by decide +kernel

theorem factorAcceptance20 :
    TorusLean.M2.rationalPSDCheck matrixTable20 factorTable20 pivotTable20 = true := by decide +kernel

theorem reconstructedPositive20 :
    (TorusLean.M2.complexify (OAI.Laughlin.Certificate.MatrixCompute.compressed 20 errorTable20 gramTable20)).PosSemidef := by
  rw [reconstruction20]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ factorAcceptance20

theorem officialErrorTable20 :
    errorTable20 = OAI.Laughlin.Certificate.candidateY_20 := by decide +kernel

theorem officialGramTable20 :
    gramTable20 = OAI.Laughlin.Certificate.candidateZ_20 := by decide +kernel

#print axioms reconstruction20

#print axioms factorAcceptance20

#print axioms reconstructedPositive20

#print axioms officialErrorTable20

#print axioms officialGramTable20

end TorusLean.FermionM3
