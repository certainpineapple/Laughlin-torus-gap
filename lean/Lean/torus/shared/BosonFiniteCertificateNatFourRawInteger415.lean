import torus.shared.BosonFiniteCertificateNatFourRawInteger415Rows0
import torus.shared.BosonFiniteCertificateNatFourRawInteger415Rows1
import torus.shared.BosonFiniteCertificateNatFourRawInteger415Rows2
import torus.shared.BosonFiniteCertificateNatFourRawInteger415Rows3
import torus.shared.BosonFiniteCertificateNatFourRawInteger415Rows4
import torus.shared.BosonFiniteCertificateNatFourRawInteger415Rows5
import torus.shared.BosonFiniteCertificateNatFourRawInteger415Rows6
import torus.shared.BosonFiniteCertificateNatFourRawInteger415Rows7
import torus.shared.BosonFiniteCertificateNatFourRawInteger415Rows8
import torus.shared.BosonFiniteCertificateNatFourRawInteger415Rows9
import torus.shared.BosonFiniteCertificateNatFourRawInteger415Rows10
import torus.shared.BosonFiniteCertificateNatFourRawInteger415Rows11
import torus.shared.BosonFiniteCertificateNatFourRawInteger415Rows12
import torus.shared.BosonFiniteCertificateNatFourRawInteger415Rows13

/-! A common-denominator integer witness for an independently source-verified
raw M4 matrix. The exact rational-table equality below is checked separately. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.BosonFiniteCertificate
open Matrix

theorem f415_raw_integer_check :
    natFourIntegerMatrix 1000000000000000000000000 f415rawInteger=f415rawM4Form := by
  ext a b
  fin_cases a
  · exact f415_raw_integer_rows_block0.1 b
  · exact f415_raw_integer_rows_block0.2.1 b
  · exact f415_raw_integer_rows_block0.2.2.1 b
  · exact f415_raw_integer_rows_block0.2.2.2 b
  · exact f415_raw_integer_rows_block1.1 b
  · exact f415_raw_integer_rows_block1.2.1 b
  · exact f415_raw_integer_rows_block1.2.2.1 b
  · exact f415_raw_integer_rows_block1.2.2.2 b
  · exact f415_raw_integer_rows_block2.1 b
  · exact f415_raw_integer_rows_block2.2.1 b
  · exact f415_raw_integer_rows_block2.2.2.1 b
  · exact f415_raw_integer_rows_block2.2.2.2 b
  · exact f415_raw_integer_rows_block3.1 b
  · exact f415_raw_integer_rows_block3.2.1 b
  · exact f415_raw_integer_rows_block3.2.2.1 b
  · exact f415_raw_integer_rows_block3.2.2.2 b
  · exact f415_raw_integer_rows_block4.1 b
  · exact f415_raw_integer_rows_block4.2.1 b
  · exact f415_raw_integer_rows_block4.2.2.1 b
  · exact f415_raw_integer_rows_block4.2.2.2 b
  · exact f415_raw_integer_rows_block5.1 b
  · exact f415_raw_integer_rows_block5.2.1 b
  · exact f415_raw_integer_rows_block5.2.2.1 b
  · exact f415_raw_integer_rows_block5.2.2.2 b
  · exact f415_raw_integer_rows_block6.1 b
  · exact f415_raw_integer_rows_block6.2.1 b
  · exact f415_raw_integer_rows_block6.2.2.1 b
  · exact f415_raw_integer_rows_block6.2.2.2 b
  · exact f415_raw_integer_rows_block7.1 b
  · exact f415_raw_integer_rows_block7.2.1 b
  · exact f415_raw_integer_rows_block7.2.2.1 b
  · exact f415_raw_integer_rows_block7.2.2.2 b
  · exact f415_raw_integer_rows_block8.1 b
  · exact f415_raw_integer_rows_block8.2.1 b
  · exact f415_raw_integer_rows_block8.2.2.1 b
  · exact f415_raw_integer_rows_block8.2.2.2 b
  · exact f415_raw_integer_rows_block9.1 b
  · exact f415_raw_integer_rows_block9.2.1 b
  · exact f415_raw_integer_rows_block9.2.2.1 b
  · exact f415_raw_integer_rows_block9.2.2.2 b
  · exact f415_raw_integer_rows_block10.1 b
  · exact f415_raw_integer_rows_block10.2.1 b
  · exact f415_raw_integer_rows_block10.2.2.1 b
  · exact f415_raw_integer_rows_block10.2.2.2 b
  · exact f415_raw_integer_rows_block11.1 b
  · exact f415_raw_integer_rows_block11.2.1 b
  · exact f415_raw_integer_rows_block11.2.2.1 b
  · exact f415_raw_integer_rows_block11.2.2.2 b
  · exact f415_raw_integer_rows_block12.1 b
  · exact f415_raw_integer_rows_block12.2.1 b
  · exact f415_raw_integer_rows_block12.2.2.1 b
  · exact f415_raw_integer_rows_block12.2.2.2 b
  · exact f415_raw_integer_rows_block13.1 b
  · exact f415_raw_integer_rows_block13.2 b

#print axioms f415_raw_integer_check
end TorusLean.BosonFiniteCertificate
