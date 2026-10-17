import torus.shared.BosonFiniteCertificateNatFourDescendants410P6LeftRow0
import torus.shared.BosonFiniteCertificateNatFourDescendants410P6LeftRow1
import torus.shared.BosonFiniteCertificateNatFourDescendants410P6LeftRow2
import torus.shared.BosonFiniteCertificateNatFourDescendants410P6LeftRow3
import torus.shared.BosonFiniteCertificateNatFourDescendants410P6LeftRow4
import torus.shared.BosonFiniteCertificateNatFourDescendants410P6DRows
import torus.shared.BosonFiniteCertificateNatFourDescendants410P6YRows
import torus.shared.BosonFiniteCertificateNatFourDescendants410P6FRows

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f410desc6_compression_check :
    f410desc6ᵀ*f416rawM4Form*f410desc6=f410desc6Form := by
  have hD : natFourIntegerMatrix 1260 f410desc6IntegerCoordinatesShared=f410desc6 := by
    ext a b
    exact f410desc6_bounded_decode a b
  have hV : f410desc6IntegerCoordinatesSharedᵀ*f416rawInteger=f410desc6IntegerLeftProductShared := by
    ext a b
    fin_cases a
    · exact f410desc6_integer_left_row0 b
    · exact f410desc6_integer_left_row1 b
    · exact f410desc6_integer_left_row2 b
    · exact f410desc6_integer_left_row3 b
    · exact f410desc6_integer_left_row4 b
  have hY : f410desc6IntegerLeftProductShared*f410desc6IntegerCoordinatesShared=f410desc6IntegerFormShared := by
    ext a b
    exact f410desc6_bounded_product a b
  have hF : natFourIntegerMatrix (1260*1000000000000000000000000*1260) f410desc6IntegerFormShared=f410desc6Form := by
    ext a b
    exact f410desc6_bounded_form_decode a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1260
    f416rawInteger f410desc6IntegerCoordinatesShared f410desc6IntegerLeftProductShared f410desc6IntegerFormShared
    f416rawM4Form f410desc6 f410desc6Form f416_raw_integer_check hD hV hY hF

#print axioms f410desc6_compression_check

end TorusLean.BosonFiniteCertificate
