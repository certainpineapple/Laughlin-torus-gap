import torus.shared.BosonFiniteCertificateNatFourDescendants408P8Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

private theorem f408desc8_left_row3_columns0 :
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 0=f408desc8IntegerLeftProductShared 3 0) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 1=f408desc8IntegerLeftProductShared 3 1) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 2=f408desc8IntegerLeftProductShared 3 2) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 3=f408desc8IntegerLeftProductShared 3 3) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 4=f408desc8IntegerLeftProductShared 3 4) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 5=f408desc8IntegerLeftProductShared 3 5) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 6=f408desc8IntegerLeftProductShared 3 6) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 7=f408desc8IntegerLeftProductShared 3 7) := by
  decide +kernel

#print axioms f408desc8_left_row3_columns0

private theorem f408desc8_left_row3_columns1 :
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 8=f408desc8IntegerLeftProductShared 3 8) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 9=f408desc8IntegerLeftProductShared 3 9) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 10=f408desc8IntegerLeftProductShared 3 10) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 11=f408desc8IntegerLeftProductShared 3 11) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 12=f408desc8IntegerLeftProductShared 3 12) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 13=f408desc8IntegerLeftProductShared 3 13) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 14=f408desc8IntegerLeftProductShared 3 14) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 15=f408desc8IntegerLeftProductShared 3 15) := by
  decide +kernel

#print axioms f408desc8_left_row3_columns1

private theorem f408desc8_left_row3_columns2 :
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 16=f408desc8IntegerLeftProductShared 3 16) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 17=f408desc8IntegerLeftProductShared 3 17) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 18=f408desc8IntegerLeftProductShared 3 18) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 19=f408desc8IntegerLeftProductShared 3 19) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 20=f408desc8IntegerLeftProductShared 3 20) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 21=f408desc8IntegerLeftProductShared 3 21) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 22=f408desc8IntegerLeftProductShared 3 22) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 23=f408desc8IntegerLeftProductShared 3 23) := by
  decide +kernel

#print axioms f408desc8_left_row3_columns2

private theorem f408desc8_left_row3_columns3 :
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 24=f408desc8IntegerLeftProductShared 3 24) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 25=f408desc8IntegerLeftProductShared 3 25) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 26=f408desc8IntegerLeftProductShared 3 26) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 27=f408desc8IntegerLeftProductShared 3 27) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 28=f408desc8IntegerLeftProductShared 3 28) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 29=f408desc8IntegerLeftProductShared 3 29) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 30=f408desc8IntegerLeftProductShared 3 30) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 31=f408desc8IntegerLeftProductShared 3 31) := by
  decide +kernel

#print axioms f408desc8_left_row3_columns3

theorem f408desc8_integer_left_row3_half0 (b : Fin 32) :
    (f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 ⟨b.val+0, by have hb := b.isLt; omega⟩ =
      f408desc8IntegerLeftProductShared 3 ⟨b.val+0, by have hb := b.isLt; omega⟩ := by
  fin_cases b
  · exact f408desc8_left_row3_columns0.1
  · exact f408desc8_left_row3_columns0.2.1
  · exact f408desc8_left_row3_columns0.2.2.1
  · exact f408desc8_left_row3_columns0.2.2.2.1
  · exact f408desc8_left_row3_columns0.2.2.2.2.1
  · exact f408desc8_left_row3_columns0.2.2.2.2.2.1
  · exact f408desc8_left_row3_columns0.2.2.2.2.2.2.1
  · exact f408desc8_left_row3_columns0.2.2.2.2.2.2.2
  · exact f408desc8_left_row3_columns1.1
  · exact f408desc8_left_row3_columns1.2.1
  · exact f408desc8_left_row3_columns1.2.2.1
  · exact f408desc8_left_row3_columns1.2.2.2.1
  · exact f408desc8_left_row3_columns1.2.2.2.2.1
  · exact f408desc8_left_row3_columns1.2.2.2.2.2.1
  · exact f408desc8_left_row3_columns1.2.2.2.2.2.2.1
  · exact f408desc8_left_row3_columns1.2.2.2.2.2.2.2
  · exact f408desc8_left_row3_columns2.1
  · exact f408desc8_left_row3_columns2.2.1
  · exact f408desc8_left_row3_columns2.2.2.1
  · exact f408desc8_left_row3_columns2.2.2.2.1
  · exact f408desc8_left_row3_columns2.2.2.2.2.1
  · exact f408desc8_left_row3_columns2.2.2.2.2.2.1
  · exact f408desc8_left_row3_columns2.2.2.2.2.2.2.1
  · exact f408desc8_left_row3_columns2.2.2.2.2.2.2.2
  · exact f408desc8_left_row3_columns3.1
  · exact f408desc8_left_row3_columns3.2.1
  · exact f408desc8_left_row3_columns3.2.2.1
  · exact f408desc8_left_row3_columns3.2.2.2.1
  · exact f408desc8_left_row3_columns3.2.2.2.2.1
  · exact f408desc8_left_row3_columns3.2.2.2.2.2.1
  · exact f408desc8_left_row3_columns3.2.2.2.2.2.2.1
  · exact f408desc8_left_row3_columns3.2.2.2.2.2.2.2

#print axioms f408desc8_integer_left_row3_half0

end TorusLean.BosonFiniteCertificate
