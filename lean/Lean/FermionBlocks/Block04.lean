import FermionM3Data
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open scoped ComplexOrder
namespace TorusLean.FermionM3

theorem reconstruction04 :
    OAI.Laughlin.Certificate.MatrixCompute.compressed 4 errorTable04 gramTable04 = matrixTable04 := by decide +kernel

theorem factorAcceptance04 :
    TorusLean.M2.rationalPSDCheck matrixTable04 factorTable04 pivotTable04 = true := by decide +kernel

theorem reconstructedPositive04 :
    (TorusLean.M2.complexify (OAI.Laughlin.Certificate.MatrixCompute.compressed 4 errorTable04 gramTable04)).PosSemidef := by
  rw [reconstruction04]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ factorAcceptance04

#print axioms reconstruction04

#print axioms factorAcceptance04

#print axioms reconstructedPositive04

end TorusLean.FermionM3
