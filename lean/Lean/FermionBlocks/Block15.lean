import FermionM3Data
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open scoped ComplexOrder
namespace TorusLean.FermionM3

theorem reconstruction15 :
    OAI.Laughlin.Certificate.MatrixCompute.compressed 15 errorTable15 gramTable15 = matrixTable15 := by decide +kernel

theorem factorAcceptance15 :
    TorusLean.M2.rationalPSDCheck matrixTable15 factorTable15 pivotTable15 = true := by decide +kernel

theorem reconstructedPositive15 :
    (TorusLean.M2.complexify (OAI.Laughlin.Certificate.MatrixCompute.compressed 15 errorTable15 gramTable15)).PosSemidef := by
  rw [reconstruction15]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ factorAcceptance15

theorem officialErrorTable15 :
    errorTable15 = OAI.Laughlin.Certificate.candidateY_15 := by decide +kernel

theorem officialGramTable15 :
    gramTable15 = OAI.Laughlin.Certificate.candidateZ_15 := by decide +kernel

#print axioms reconstruction15

#print axioms factorAcceptance15

#print axioms reconstructedPositive15

#print axioms officialErrorTable15

#print axioms officialGramTable15

end TorusLean.FermionM3
