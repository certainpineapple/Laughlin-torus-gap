import torus.shared.BosonFiniteCertificateNatFourDescendants415P0VRow0
import torus.shared.BosonFiniteCertificateNatFourDescendants415P0VRow1
import torus.shared.BosonFiniteCertificateNatFourDescendants415P0VRow2
import torus.shared.BosonFiniteCertificateNatFourDescendants415P0VRow3
import torus.shared.BosonFiniteCertificateNatFourDescendants415P0VRow4
import torus.shared.BosonFiniteCertificateNatFourDescendants415P0VRow5
import torus.shared.BosonFiniteCertificateNatFourDescendants415P0VRow6
import torus.shared.BosonFiniteCertificateNatFourDescendants415P0DRows
import torus.shared.BosonFiniteCertificateNatFourDescendants415P0YRows
import torus.shared.BosonFiniteCertificateNatFourDescendants415P0FRows

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f415desc0_compression_check :
    f415desc0ᵀ*f415rawM4Form*f415desc0=f415desc0Form := by
  have hD : natFourIntegerMatrix 360360 f415desc0IntegerCoordinatesShared=f415desc0 := by
    ext a b
    exact f415desc0_bounded_decode a b
  have hV : f415desc0IntegerCoordinatesSharedᵀ*f415rawInteger=f415desc0IntegerLeftProductShared := by
    ext a b
    fin_cases a
    · exact f415desc0_bounded_v_row0 b
    · exact f415desc0_bounded_v_row1 b
    · exact f415desc0_bounded_v_row2 b
    · exact f415desc0_bounded_v_row3 b
    · exact f415desc0_bounded_v_row4 b
    · exact f415desc0_bounded_v_row5 b
    · exact f415desc0_bounded_v_row6 b
  have hY : f415desc0IntegerLeftProductShared*f415desc0IntegerCoordinatesShared=f415desc0IntegerFormShared := by
    ext a b
    exact f415desc0_bounded_product a b
  have hF : natFourIntegerMatrix (360360*1000000000000000000000000*360360) f415desc0IntegerFormShared=f415desc0Form := by
    ext a b
    exact f415desc0_bounded_form_decode a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 360360
    f415rawInteger f415desc0IntegerCoordinatesShared f415desc0IntegerLeftProductShared f415desc0IntegerFormShared
    f415rawM4Form f415desc0 f415desc0Form f415_raw_integer_check hD hV hY hF

#print axioms f415desc0_compression_check

end TorusLean.BosonFiniteCertificate
