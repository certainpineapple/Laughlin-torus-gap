import torus.shared.BosonFiniteCertificateNatFourDescendants411P0VRow0
import torus.shared.BosonFiniteCertificateNatFourDescendants411P0VRow1
import torus.shared.BosonFiniteCertificateNatFourDescendants411P0VRow2
import torus.shared.BosonFiniteCertificateNatFourDescendants411P0VRow3
import torus.shared.BosonFiniteCertificateNatFourDescendants411P0DRows
import torus.shared.BosonFiniteCertificateNatFourDescendants411P0YRows
import torus.shared.BosonFiniteCertificateNatFourDescendants411P0FRows

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f411desc0_compression_check :
    f411desc0ᵀ*f411rawM4Form*f411desc0=f411desc0Form := by
  have hD : natFourIntegerMatrix 2520 f411desc0IntegerCoordinatesShared=f411desc0 := by
    ext a b
    exact f411desc0_bounded_decode a b
  have hV : f411desc0IntegerCoordinatesSharedᵀ*f411rawInteger=f411desc0IntegerLeftProductShared := by
    ext a b
    fin_cases a
    · exact f411desc0_bounded_v_row0 b
    · exact f411desc0_bounded_v_row1 b
    · exact f411desc0_bounded_v_row2 b
    · exact f411desc0_bounded_v_row3 b
  have hY : f411desc0IntegerLeftProductShared*f411desc0IntegerCoordinatesShared=f411desc0IntegerFormShared := by
    ext a b
    exact f411desc0_bounded_product a b
  have hF : natFourIntegerMatrix (2520*1000000000000000000000000*2520) f411desc0IntegerFormShared=f411desc0Form := by
    ext a b
    exact f411desc0_bounded_form_decode a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 2520
    f411rawInteger f411desc0IntegerCoordinatesShared f411desc0IntegerLeftProductShared f411desc0IntegerFormShared
    f411rawM4Form f411desc0 f411desc0Form f411_raw_integer_check hD hV hY hF

#print axioms f411desc0_compression_check

end TorusLean.BosonFiniteCertificate
