import FermionM3Data
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open scoped ComplexOrder
namespace TorusLean.FermionM3

theorem reconstruction02 :
    OAI.Laughlin.Certificate.MatrixCompute.compressed 2 errorTable02 gramTable02 = matrixTable02 := by decide +kernel

theorem factorAcceptance02 :
    TorusLean.M2.rationalPSDCheck matrixTable02 factorTable02 pivotTable02 = true := by decide +kernel

theorem reconstructedPositive02 :
    (TorusLean.M2.complexify (OAI.Laughlin.Certificate.MatrixCompute.compressed 2 errorTable02 gramTable02)).PosSemidef := by
  rw [reconstruction02]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ factorAcceptance02

#print axioms reconstruction02

#print axioms factorAcceptance02

#print axioms reconstructedPositive02

end TorusLean.FermionM3
