import torus.shared.BosonFiniteCertificateNatFourDescendants410P5LeftRow0
import torus.shared.BosonFiniteCertificateNatFourDescendants410P5LeftRow1
import torus.shared.BosonFiniteCertificateNatFourDescendants410P5LeftRow2
import torus.shared.BosonFiniteCertificateNatFourDescendants410P5LeftRow3
import torus.shared.BosonFiniteCertificateNatFourDescendants410P5LeftRow4
import torus.shared.BosonFiniteCertificateNatFourDescendants410P5DRows
import torus.shared.BosonFiniteCertificateNatFourDescendants410P5YRows
import torus.shared.BosonFiniteCertificateNatFourDescendants410P5FRows

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f410desc5_compression_check :
    f410desc5ᵀ*f415rawM4Form*f410desc5=f410desc5Form := by
  have hD : natFourIntegerMatrix 1260 f410desc5IntegerCoordinatesShared=f410desc5 := by
    ext a b
    exact f410desc5_bounded_decode a b
  have hV : f410desc5IntegerCoordinatesSharedᵀ*f415rawInteger=f410desc5IntegerLeftProductShared := by
    ext a b
    fin_cases a
    · exact f410desc5_integer_left_row0 b
    · exact f410desc5_integer_left_row1 b
    · exact f410desc5_integer_left_row2 b
    · exact f410desc5_integer_left_row3 b
    · exact f410desc5_integer_left_row4 b
  have hY : f410desc5IntegerLeftProductShared*f410desc5IntegerCoordinatesShared=f410desc5IntegerFormShared := by
    ext a b
    exact f410desc5_bounded_product a b
  have hF : natFourIntegerMatrix (1260*1000000000000000000000000*1260) f410desc5IntegerFormShared=f410desc5Form := by
    ext a b
    exact f410desc5_bounded_form_decode a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1260
    f415rawInteger f410desc5IntegerCoordinatesShared f410desc5IntegerLeftProductShared f410desc5IntegerFormShared
    f415rawM4Form f410desc5 f410desc5Form f415_raw_integer_check hD hV hY hF

#print axioms f410desc5_compression_check

end TorusLean.BosonFiniteCertificate
