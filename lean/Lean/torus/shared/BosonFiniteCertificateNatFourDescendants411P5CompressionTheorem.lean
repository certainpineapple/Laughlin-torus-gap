import torus.shared.BosonFiniteCertificateNatFourDescendants411P5VRow0
import torus.shared.BosonFiniteCertificateNatFourDescendants411P5VRow1
import torus.shared.BosonFiniteCertificateNatFourDescendants411P5VRow2
import torus.shared.BosonFiniteCertificateNatFourDescendants411P5VRow3
import torus.shared.BosonFiniteCertificateNatFourDescendants411P5DRows
import torus.shared.BosonFiniteCertificateNatFourDescendants411P5YRows
import torus.shared.BosonFiniteCertificateNatFourDescendants411P5FRows

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f411desc5_compression_check :
    f411desc5ᵀ*f416rawM4Form*f411desc5=f411desc5Form := by
  have hD : natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared=f411desc5 := by
    ext a b
    exact f411desc5_bounded_decode a b
  have hV : f411desc5IntegerCoordinatesSharedᵀ*f416rawInteger=f411desc5IntegerLeftProductShared := by
    ext a b
    fin_cases a
    · exact f411desc5_bounded_v_row0 b
    · exact f411desc5_bounded_v_row1 b
    · exact f411desc5_bounded_v_row2 b
    · exact f411desc5_bounded_v_row3 b
  have hY : f411desc5IntegerLeftProductShared*f411desc5IntegerCoordinatesShared=f411desc5IntegerFormShared := by
    ext a b
    exact f411desc5_bounded_product a b
  have hF : natFourIntegerMatrix (2520*1000000000000000000000000*2520) f411desc5IntegerFormShared=f411desc5Form := by
    ext a b
    exact f411desc5_bounded_form_decode a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 2520
    f416rawInteger f411desc5IntegerCoordinatesShared f411desc5IntegerLeftProductShared f411desc5IntegerFormShared
    f416rawM4Form f411desc5 f411desc5Form f416_raw_integer_check hD hV hY hF

#print axioms f411desc5_compression_check

end TorusLean.BosonFiniteCertificate
