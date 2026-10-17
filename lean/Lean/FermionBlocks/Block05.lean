import FermionM3Data
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open scoped ComplexOrder
namespace TorusLean.FermionM3

theorem reconstruction05 :
    OAI.Laughlin.Certificate.MatrixCompute.compressed 5 errorTable05 gramTable05 = matrixTable05 := by decide +kernel

theorem factorAcceptance05 :
    TorusLean.M2.rationalPSDCheck matrixTable05 factorTable05 pivotTable05 = true := by decide +kernel

theorem reconstructedPositive05 :
    (TorusLean.M2.complexify (OAI.Laughlin.Certificate.MatrixCompute.compressed 5 errorTable05 gramTable05)).PosSemidef := by
  rw [reconstruction05]
  exact TorusLean.M2.rationalPSDCheck_sound _ _ _ factorAcceptance05

#print axioms reconstruction05

#print axioms factorAcceptance05

#print axioms reconstructedPositive05

end TorusLean.FermionM3
