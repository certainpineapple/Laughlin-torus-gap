import torus.shared.BosonFiniteCertificateNatFourDescendants415P1VRow0
import torus.shared.BosonFiniteCertificateNatFourDescendants415P1VRow1
import torus.shared.BosonFiniteCertificateNatFourDescendants415P1VRow2
import torus.shared.BosonFiniteCertificateNatFourDescendants415P1VRow3
import torus.shared.BosonFiniteCertificateNatFourDescendants415P1VRow4
import torus.shared.BosonFiniteCertificateNatFourDescendants415P1VRow5
import torus.shared.BosonFiniteCertificateNatFourDescendants415P1VRow6
import torus.shared.BosonFiniteCertificateNatFourDescendants415P1DRows
import torus.shared.BosonFiniteCertificateNatFourDescendants415P1YRows
import torus.shared.BosonFiniteCertificateNatFourDescendants415P1FRows

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f415desc1_compression_check :
    f415desc1ᵀ*f416rawM4Form*f415desc1=f415desc1Form := by
  have hD : natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared=f415desc1 := by
    ext a b
    exact f415desc1_bounded_decode a b
  have hV : f415desc1IntegerCoordinatesSharedᵀ*f416rawInteger=f415desc1IntegerLeftProductShared := by
    ext a b
    fin_cases a
    · exact f415desc1_bounded_v_row0 b
    · exact f415desc1_bounded_v_row1 b
    · exact f415desc1_bounded_v_row2 b
    · exact f415desc1_bounded_v_row3 b
    · exact f415desc1_bounded_v_row4 b
    · exact f415desc1_bounded_v_row5 b
    · exact f415desc1_bounded_v_row6 b
  have hY : f415desc1IntegerLeftProductShared*f415desc1IntegerCoordinatesShared=f415desc1IntegerFormShared := by
    ext a b
    exact f415desc1_bounded_product a b
  have hF : natFourIntegerMatrix (360360*1000000000000000000000000*360360) f415desc1IntegerFormShared=f415desc1Form := by
    ext a b
    exact f415desc1_bounded_form_decode a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 360360
    f416rawInteger f415desc1IntegerCoordinatesShared f415desc1IntegerLeftProductShared f415desc1IntegerFormShared
    f416rawM4Form f415desc1 f415desc1Form f416_raw_integer_check hD hV hY hF

#print axioms f415desc1_compression_check

end TorusLean.BosonFiniteCertificate
