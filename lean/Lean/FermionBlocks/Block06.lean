import FermionM3Data
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open scoped ComplexOrder
namespace TorusLean.FermionM3

theorem reconstruction06 :
    OAI.Laughlin.Certificate.MatrixCompute.compressed 6 errorTable06 gramTable06 = matrixTable06 := by decide +kernel

theorem factorAcceptance06 :
    TorusLean.M2.rationalPSDCheck matrixTable06 factorTable06 pivotTable06 = true := by decide +kernel

theorem reconstructedPositive06 :
    (TorusLean.M2.complexify (OAI.Laughlin.Certificate.MatrixCompute.compressed 6 errorTable06 gramTable06)).PosSemidef := by
  rw [reconstruction06]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ factorAcceptance06

#print axioms reconstruction06

#print axioms factorAcceptance06

#print axioms reconstructedPositive06

end TorusLean.FermionM3
