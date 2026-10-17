import torus.shared.BosonFiniteCertificateNatFourDescendants408P8LeftRow3Half0
import torus.shared.BosonFiniteCertificateNatFourDescendants408P8LeftRow3Half1

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

theorem f408desc8_integer_left_row3 (b : Fin 64) :
    (f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger) 3 b = f408desc8IntegerLeftProductShared 3 b := by
  fin_cases b
  · exact f408desc8_integer_left_row3_half0 0
  · exact f408desc8_integer_left_row3_half0 1
  · exact f408desc8_integer_left_row3_half0 2
  · exact f408desc8_integer_left_row3_half0 3
  · exact f408desc8_integer_left_row3_half0 4
  · exact f408desc8_integer_left_row3_half0 5
  · exact f408desc8_integer_left_row3_half0 6
  · exact f408desc8_integer_left_row3_half0 7
  · exact f408desc8_integer_left_row3_half0 8
  · exact f408desc8_integer_left_row3_half0 9
  · exact f408desc8_integer_left_row3_half0 10
  · exact f408desc8_integer_left_row3_half0 11
  · exact f408desc8_integer_left_row3_half0 12
  · exact f408desc8_integer_left_row3_half0 13
  · exact f408desc8_integer_left_row3_half0 14
  · exact f408desc8_integer_left_row3_half0 15
  · exact f408desc8_integer_left_row3_half0 16
  · exact f408desc8_integer_left_row3_half0 17
  · exact f408desc8_integer_left_row3_half0 18
  · exact f408desc8_integer_left_row3_half0 19
  · exact f408desc8_integer_left_row3_half0 20
  · exact f408desc8_integer_left_row3_half0 21
  · exact f408desc8_integer_left_row3_half0 22
  · exact f408desc8_integer_left_row3_half0 23
  · exact f408desc8_integer_left_row3_half0 24
  · exact f408desc8_integer_left_row3_half0 25
  · exact f408desc8_integer_left_row3_half0 26
  · exact f408desc8_integer_left_row3_half0 27
  · exact f408desc8_integer_left_row3_half0 28
  · exact f408desc8_integer_left_row3_half0 29
  · exact f408desc8_integer_left_row3_half0 30
  · exact f408desc8_integer_left_row3_half0 31
  · exact f408desc8_integer_left_row3_half1 0
  · exact f408desc8_integer_left_row3_half1 1
  · exact f408desc8_integer_left_row3_half1 2
  · exact f408desc8_integer_left_row3_half1 3
  · exact f408desc8_integer_left_row3_half1 4
  · exact f408desc8_integer_left_row3_half1 5
  · exact f408desc8_integer_left_row3_half1 6
  · exact f408desc8_integer_left_row3_half1 7
  · exact f408desc8_integer_left_row3_half1 8
  · exact f408desc8_integer_left_row3_half1 9
  · exact f408desc8_integer_left_row3_half1 10
  · exact f408desc8_integer_left_row3_half1 11
  · exact f408desc8_integer_left_row3_half1 12
  · exact f408desc8_integer_left_row3_half1 13
  · exact f408desc8_integer_left_row3_half1 14
  · exact f408desc8_integer_left_row3_half1 15
  · exact f408desc8_integer_left_row3_half1 16
  · exact f408desc8_integer_left_row3_half1 17
  · exact f408desc8_integer_left_row3_half1 18
  · exact f408desc8_integer_left_row3_half1 19
  · exact f408desc8_integer_left_row3_half1 20
  · exact f408desc8_integer_left_row3_half1 21
  · exact f408desc8_integer_left_row3_half1 22
  · exact f408desc8_integer_left_row3_half1 23
  · exact f408desc8_integer_left_row3_half1 24
  · exact f408desc8_integer_left_row3_half1 25
  · exact f408desc8_integer_left_row3_half1 26
  · exact f408desc8_integer_left_row3_half1 27
  · exact f408desc8_integer_left_row3_half1 28
  · exact f408desc8_integer_left_row3_half1 29
  · exact f408desc8_integer_left_row3_half1 30
  · exact f408desc8_integer_left_row3_half1 31

#print axioms f408desc8_integer_left_row3

end TorusLean.BosonFiniteCertificate
