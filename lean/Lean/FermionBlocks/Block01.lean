import FermionM3Data
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open scoped ComplexOrder
namespace TorusLean.FermionM3

theorem reconstruction01 :
    OAI.Laughlin.Certificate.MatrixCompute.compressed 1 errorTable01 gramTable01 = matrixTable01 := by decide +kernel

theorem factorAcceptance01 :
    TorusLean.M2.rationalPSDCheck matrixTable01 factorTable01 pivotTable01 = true := by decide +kernel

theorem reconstructedPositive01 :
    (TorusLean.M2.complexify (OAI.Laughlin.Certificate.MatrixCompute.compressed 1 errorTable01 gramTable01)).PosSemidef := by
  rw [reconstruction01]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ factorAcceptance01

#print axioms reconstruction01

#print axioms factorAcceptance01

#print axioms reconstructedPositive01

end TorusLean.FermionM3
