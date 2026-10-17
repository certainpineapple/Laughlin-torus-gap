import FermionM3Data
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open scoped ComplexOrder
namespace TorusLean.FermionM3

theorem reconstruction08 :
    OAI.Laughlin.Certificate.MatrixCompute.compressed 8 errorTable08 gramTable08 = matrixTable08 := by decide +kernel

theorem factorAcceptance08 :
    TorusLean.M2.rationalPSDCheck matrixTable08 factorTable08 pivotTable08 = true := by decide +kernel

theorem reconstructedPositive08 :
    (TorusLean.M2.complexify (OAI.Laughlin.Certificate.MatrixCompute.compressed 8 errorTable08 gramTable08)).PosSemidef := by
  rw [reconstruction08]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ factorAcceptance08

#print axioms reconstruction08

#print axioms factorAcceptance08

#print axioms reconstructedPositive08

end TorusLean.FermionM3
