import FermionM3Data
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open scoped ComplexOrder
namespace TorusLean.FermionM3

theorem reconstruction07 :
    OAI.Laughlin.Certificate.MatrixCompute.compressed 7 errorTable07 gramTable07 = matrixTable07 := by decide +kernel

theorem factorAcceptance07 :
    TorusLean.M2.rationalPSDCheck matrixTable07 factorTable07 pivotTable07 = true := by decide +kernel

theorem reconstructedPositive07 :
    (TorusLean.M2.complexify (OAI.Laughlin.Certificate.MatrixCompute.compressed 7 errorTable07 gramTable07)).PosSemidef := by
  rw [reconstruction07]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ factorAcceptance07

#print axioms reconstruction07

#print axioms factorAcceptance07

#print axioms reconstructedPositive07

end TorusLean.FermionM3
