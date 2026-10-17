import torus.shared.BosonFiniteCertificateNatFourCOMCoordinateData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open TorusLean.Shared.BosonFiniteCertificateWords
open Matrix
open scoped BigOperators

theorem natFourOccupationBasis_enumeration (D : Fin 17) :
    List.ofFn (natFourOccupationBasis D)=natFourBasis D.val := by
  fin_cases D
  · exact f400_basis_enumeration
  · exact f401_basis_enumeration
  · exact f402_basis_enumeration
  · exact f403_basis_enumeration
  · exact f404_basis_enumeration
  · exact f405_basis_enumeration
  · exact f406_basis_enumeration
  · exact f407_basis_enumeration
  · exact f408_basis_enumeration
  · exact f409_basis_enumeration
  · exact f410_basis_enumeration
  · exact f411_basis_enumeration
  · exact f412_basis_enumeration
  · exact f413_basis_enumeration
  · exact f414_basis_enumeration
  · exact f415_basis_enumeration
  · exact f416_basis_enumeration

#print axioms natFourOccupationBasis_enumeration
end TorusLean.BosonFiniteCertificate
