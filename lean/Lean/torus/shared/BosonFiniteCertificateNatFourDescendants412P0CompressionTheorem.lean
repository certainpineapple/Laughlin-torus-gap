import torus.shared.BosonFiniteCertificateNatFourDescendants412P0VRow0
import torus.shared.BosonFiniteCertificateNatFourDescendants412P0VRow1
import torus.shared.BosonFiniteCertificateNatFourDescendants412P0VRow2
import torus.shared.BosonFiniteCertificateNatFourDescendants412P0VRow3
import torus.shared.BosonFiniteCertificateNatFourDescendants412P0VRow4
import torus.shared.BosonFiniteCertificateNatFourDescendants412P0VRow5
import torus.shared.BosonFiniteCertificateNatFourDescendants412P0VRow6
import torus.shared.BosonFiniteCertificateNatFourDescendants412P0DRows
import torus.shared.BosonFiniteCertificateNatFourDescendants412P0YRows
import torus.shared.BosonFiniteCertificateNatFourDescendants412P0FRows

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f412desc0_compression_check :
    f412desc0ᵀ*f412rawM4Form*f412desc0=f412desc0Form := by
  have hD : natFourIntegerMatrix 6930 f412desc0IntegerCoordinatesShared=f412desc0 := by
    ext a b
    exact f412desc0_bounded_decode a b
  have hV : f412desc0IntegerCoordinatesSharedᵀ*f412rawInteger=f412desc0IntegerLeftProductShared := by
    ext a b
    fin_cases a
    · exact f412desc0_bounded_v_row0 b
    · exact f412desc0_bounded_v_row1 b
    · exact f412desc0_bounded_v_row2 b
    · exact f412desc0_bounded_v_row3 b
    · exact f412desc0_bounded_v_row4 b
    · exact f412desc0_bounded_v_row5 b
    · exact f412desc0_bounded_v_row6 b
  have hY : f412desc0IntegerLeftProductShared*f412desc0IntegerCoordinatesShared=f412desc0IntegerFormShared := by
    ext a b
    exact f412desc0_bounded_product a b
  have hF : natFourIntegerMatrix (6930*1000000000000000000000000*6930) f412desc0IntegerFormShared=f412desc0Form := by
    ext a b
    exact f412desc0_bounded_form_decode a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 6930
    f412rawInteger f412desc0IntegerCoordinatesShared f412desc0IntegerLeftProductShared f412desc0IntegerFormShared
    f412rawM4Form f412desc0 f412desc0Form f412_raw_integer_check hD hV hY hF

#print axioms f412desc0_compression_check

end TorusLean.BosonFiniteCertificate
