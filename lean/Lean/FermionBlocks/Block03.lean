import FermionM3Data
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open scoped ComplexOrder
namespace TorusLean.FermionM3

theorem reconstruction03 :
    OAI.Laughlin.Certificate.MatrixCompute.compressed 3 errorTable03 gramTable03 = matrixTable03 := by decide +kernel

theorem factorAcceptance03 :
    TorusLean.M2.rationalPSDCheck matrixTable03 factorTable03 pivotTable03 = true := by decide +kernel

theorem reconstructedPositive03 :
    (TorusLean.M2.complexify (OAI.Laughlin.Certificate.MatrixCompute.compressed 3 errorTable03 gramTable03)).PosSemidef := by
  rw [reconstruction03]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ factorAcceptance03

#print axioms reconstruction03

#print axioms factorAcceptance03

#print axioms reconstructedPositive03

end TorusLean.FermionM3
