import torus.shared.BosonFiniteCertificateNatFourDescendants408P8Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

private theorem f408desc8_left_row3_columns4 :
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 32=f408desc8IntegerLeftProductShared 3 32) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 33=f408desc8IntegerLeftProductShared 3 33) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 34=f408desc8IntegerLeftProductShared 3 34) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 35=f408desc8IntegerLeftProductShared 3 35) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 36=f408desc8IntegerLeftProductShared 3 36) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 37=f408desc8IntegerLeftProductShared 3 37) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 38=f408desc8IntegerLeftProductShared 3 38) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 39=f408desc8IntegerLeftProductShared 3 39) := by
  decide +kernel

#print axioms f408desc8_left_row3_columns4

private theorem f408desc8_left_row3_columns5 :
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 40=f408desc8IntegerLeftProductShared 3 40) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 41=f408desc8IntegerLeftProductShared 3 41) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 42=f408desc8IntegerLeftProductShared 3 42) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 43=f408desc8IntegerLeftProductShared 3 43) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 44=f408desc8IntegerLeftProductShared 3 44) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 45=f408desc8IntegerLeftProductShared 3 45) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 46=f408desc8IntegerLeftProductShared 3 46) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 47=f408desc8IntegerLeftProductShared 3 47) := by
  decide +kernel

#print axioms f408desc8_left_row3_columns5

private theorem f408desc8_left_row3_columns6 :
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 48=f408desc8IntegerLeftProductShared 3 48) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 49=f408desc8IntegerLeftProductShared 3 49) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 50=f408desc8IntegerLeftProductShared 3 50) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 51=f408desc8IntegerLeftProductShared 3 51) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 52=f408desc8IntegerLeftProductShared 3 52) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 53=f408desc8IntegerLeftProductShared 3 53) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 54=f408desc8IntegerLeftProductShared 3 54) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 55=f408desc8IntegerLeftProductShared 3 55) := by
  decide +kernel

#print axioms f408desc8_left_row3_columns6

private theorem f408desc8_left_row3_columns7 :
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 56=f408desc8IntegerLeftProductShared 3 56) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 57=f408desc8IntegerLeftProductShared 3 57) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 58=f408desc8IntegerLeftProductShared 3 58) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 59=f408desc8IntegerLeftProductShared 3 59) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 60=f408desc8IntegerLeftProductShared 3 60) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 61=f408desc8IntegerLeftProductShared 3 61) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 62=f408desc8IntegerLeftProductShared 3 62) ∧
    ((f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 63=f408desc8IntegerLeftProductShared 3 63) := by
  decide +kernel

#print axioms f408desc8_left_row3_columns7

theorem f408desc8_integer_left_row3_half1 (b : Fin 32) :
    (f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 ⟨b.val+32, by have hb := b.isLt; omega⟩ =
      f408desc8IntegerLeftProductShared 3 ⟨b.val+32, by have hb := b.isLt; omega⟩ := by
  fin_cases b
  · exact f408desc8_left_row3_columns4.1
  · exact f408desc8_left_row3_columns4.2.1
  · exact f408desc8_left_row3_columns4.2.2.1
  · exact f408desc8_left_row3_columns4.2.2.2.1
  · exact f408desc8_left_row3_columns4.2.2.2.2.1
  · exact f408desc8_left_row3_columns4.2.2.2.2.2.1
  · exact f408desc8_left_row3_columns4.2.2.2.2.2.2.1
  · exact f408desc8_left_row3_columns4.2.2.2.2.2.2.2
  · exact f408desc8_left_row3_columns5.1
  · exact f408desc8_left_row3_columns5.2.1
  · exact f408desc8_left_row3_columns5.2.2.1
  · exact f408desc8_left_row3_columns5.2.2.2.1
  · exact f408desc8_left_row3_columns5.2.2.2.2.1
  · exact f408desc8_left_row3_columns5.2.2.2.2.2.1
  · exact f408desc8_left_row3_columns5.2.2.2.2.2.2.1
  · exact f408desc8_left_row3_columns5.2.2.2.2.2.2.2
  · exact f408desc8_left_row3_columns6.1
  · exact f408desc8_left_row3_columns6.2.1
  · exact f408desc8_left_row3_columns6.2.2.1
  · exact f408desc8_left_row3_columns6.2.2.2.1
  · exact f408desc8_left_row3_columns6.2.2.2.2.1
  · exact f408desc8_left_row3_columns6.2.2.2.2.2.1
  · exact f408desc8_left_row3_columns6.2.2.2.2.2.2.1
  · exact f408desc8_left_row3_columns6.2.2.2.2.2.2.2
  · exact f408desc8_left_row3_columns7.1
  · exact f408desc8_left_row3_columns7.2.1
  · exact f408desc8_left_row3_columns7.2.2.1
  · exact f408desc8_left_row3_columns7.2.2.2.1
  · exact f408desc8_left_row3_columns7.2.2.2.2.1
  · exact f408desc8_left_row3_columns7.2.2.2.2.2.1
  · exact f408desc8_left_row3_columns7.2.2.2.2.2.2.1
  · exact f408desc8_left_row3_columns7.2.2.2.2.2.2.2

#print axioms f408desc8_integer_left_row3_half1

end TorusLean.BosonFiniteCertificate
