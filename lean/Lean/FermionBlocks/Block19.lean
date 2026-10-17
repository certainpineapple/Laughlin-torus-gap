import FermionM3Data
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open scoped ComplexOrder
namespace TorusLean.FermionM3

theorem reconstruction19 :
    OAI.Laughlin.Certificate.MatrixCompute.compressed 19 errorTable19 gramTable19 = matrixTable19 := by decide +kernel

theorem factorAcceptance19 :
    TorusLean.M2.rationalPSDCheck matrixTable19 factorTable19 pivotTable19 = true := by decide +kernel

theorem reconstructedPositive19 :
    (TorusLean.M2.complexify (OAI.Laughlin.Certificate.MatrixCompute.compressed 19 errorTable19 gramTable19)).PosSemidef := by
  rw [reconstruction19]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ factorAcceptance19

theorem officialErrorTable19 :
    errorTable19 = OAI.Laughlin.Certificate.candidateY_19 := by decide +kernel

theorem officialGramTable19 :
    gramTable19 = OAI.Laughlin.Certificate.candidateZ_19 := by decide +kernel

#print axioms reconstruction19

#print axioms factorAcceptance19

#print axioms reconstructedPositive19

#print axioms officialErrorTable19

#print axioms officialGramTable19

end TorusLean.FermionM3
