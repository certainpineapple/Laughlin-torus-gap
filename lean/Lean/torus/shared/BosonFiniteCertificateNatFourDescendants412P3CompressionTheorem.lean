import torus.shared.BosonFiniteCertificateNatFourDescendants412P3VRow0
import torus.shared.BosonFiniteCertificateNatFourDescendants412P3VRow1
import torus.shared.BosonFiniteCertificateNatFourDescendants412P3VRow2
import torus.shared.BosonFiniteCertificateNatFourDescendants412P3VRow3
import torus.shared.BosonFiniteCertificateNatFourDescendants412P3VRow4
import torus.shared.BosonFiniteCertificateNatFourDescendants412P3VRow5
import torus.shared.BosonFiniteCertificateNatFourDescendants412P3VRow6
import torus.shared.BosonFiniteCertificateNatFourDescendants412P3DRows
import torus.shared.BosonFiniteCertificateNatFourDescendants412P3YRows
import torus.shared.BosonFiniteCertificateNatFourDescendants412P3FRows

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f412desc3_compression_check :
    f412desc3ᵀ*f415rawM4Form*f412desc3=f412desc3Form := by
  have hD : natFourIntegerMatrix 6930 f412desc3IntegerCoordinatesShared=f412desc3 := by
    ext a b
    exact f412desc3_bounded_decode a b
  have hV : f412desc3IntegerCoordinatesSharedᵀ*f415rawInteger=f412desc3IntegerLeftProductShared := by
    ext a b
    fin_cases a
    · exact f412desc3_bounded_v_row0 b
    · exact f412desc3_bounded_v_row1 b
    · exact f412desc3_bounded_v_row2 b
    · exact f412desc3_bounded_v_row3 b
    · exact f412desc3_bounded_v_row4 b
    · exact f412desc3_bounded_v_row5 b
    · exact f412desc3_bounded_v_row6 b
  have hY : f412desc3IntegerLeftProductShared*f412desc3IntegerCoordinatesShared=f412desc3IntegerFormShared := by
    ext a b
    exact f412desc3_bounded_product a b
  have hF : natFourIntegerMatrix (6930*1000000000000000000000000*6930) f412desc3IntegerFormShared=f412desc3Form := by
    ext a b
    exact f412desc3_bounded_form_decode a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 6930
    f415rawInteger f412desc3IntegerCoordinatesShared f412desc3IntegerLeftProductShared f412desc3IntegerFormShared
    f415rawM4Form f412desc3 f412desc3Form f415_raw_integer_check hD hV hY hF

#print axioms f412desc3_compression_check

end TorusLean.BosonFiniteCertificate
