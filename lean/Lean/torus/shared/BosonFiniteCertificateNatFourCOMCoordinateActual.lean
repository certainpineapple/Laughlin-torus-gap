import torus.shared.BosonFiniteCertificateNatFourCOMCoordinateActualD00
import torus.shared.BosonFiniteCertificateNatFourCOMCoordinateActualD01
import torus.shared.BosonFiniteCertificateNatFourCOMCoordinateActualD02
import torus.shared.BosonFiniteCertificateNatFourCOMCoordinateActualD03
import torus.shared.BosonFiniteCertificateNatFourCOMCoordinateActualD04
import torus.shared.BosonFiniteCertificateNatFourCOMCoordinateActualD05
import torus.shared.BosonFiniteCertificateNatFourCOMCoordinateActualD06
import torus.shared.BosonFiniteCertificateNatFourCOMCoordinateActualD07
import torus.shared.BosonFiniteCertificateNatFourCOMCoordinateActualD08
import torus.shared.BosonFiniteCertificateNatFourCOMCoordinateActualD09
import torus.shared.BosonFiniteCertificateNatFourCOMCoordinateActualD10
import torus.shared.BosonFiniteCertificateNatFourCOMCoordinateActualD11
import torus.shared.BosonFiniteCertificateNatFourCOMCoordinateActualD12
import torus.shared.BosonFiniteCertificateNatFourCOMCoordinateActualD13
import torus.shared.BosonFiniteCertificateNatFourCOMCoordinateActualD14
import torus.shared.BosonFiniteCertificateNatFourCOMCoordinateActualD15
import torus.shared.BosonFiniteCertificateNatFourCOMCoordinateActualD16

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open TorusLean.Shared.BosonFiniteCertificateWords
open Matrix
open scoped BigOperators

theorem natFourCOMFiberCoordinates_actual_column (D : Fin 17) (d : Fin (D.val+1))
    (a : Fin (natFourRelativeDimensionAt D d)) :
    ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[D.val-d.val])
      (natFourRelativeColumn (natFourRelativeDegreeAt D d) a)=
      natFourWordBlock (natFourOccupationBasis D)
        (fun i => complexify (natFourCOMFiberCoordinates D d) i a) := by
  fin_cases D
  · exact natFourCOMFiberCoordinates_actual_column_D00 d a
  · exact natFourCOMFiberCoordinates_actual_column_D01 d a
  · exact natFourCOMFiberCoordinates_actual_column_D02 d a
  · exact natFourCOMFiberCoordinates_actual_column_D03 d a
  · exact natFourCOMFiberCoordinates_actual_column_D04 d a
  · exact natFourCOMFiberCoordinates_actual_column_D05 d a
  · exact natFourCOMFiberCoordinates_actual_column_D06 d a
  · exact natFourCOMFiberCoordinates_actual_column_D07 d a
  · exact natFourCOMFiberCoordinates_actual_column_D08 d a
  · exact natFourCOMFiberCoordinates_actual_column_D09 d a
  · exact natFourCOMFiberCoordinates_actual_column_D10 d a
  · exact natFourCOMFiberCoordinates_actual_column_D11 d a
  · exact natFourCOMFiberCoordinates_actual_column_D12 d a
  · exact natFourCOMFiberCoordinates_actual_column_D13 d a
  · exact natFourCOMFiberCoordinates_actual_column_D14 d a
  · exact natFourCOMFiberCoordinates_actual_column_D15 d a
  · exact natFourCOMFiberCoordinates_actual_column_D16 d a

#print axioms natFourCOMFiberCoordinates_actual_column
end TorusLean.BosonFiniteCertificate
