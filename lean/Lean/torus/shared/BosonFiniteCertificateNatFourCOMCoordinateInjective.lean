import torus.shared.BosonFiniteCertificateNatFourCOMCoordinateEnumeration

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open TorusLean.Shared.BosonFiniteCertificateWords
open Matrix
open scoped BigOperators

theorem natFourOccupationBasis_injective (D : Fin 17) :
    Function.Injective (fun a => wordOccupation (natFourOccupationBasis D a)) := by
  fin_cases D
  · exact f400_occupation_injective
  · exact f401_occupation_injective
  · exact f402_occupation_injective
  · exact f403_occupation_injective
  · exact f404_occupation_injective
  · exact f405_occupation_injective
  · exact f406_occupation_injective
  · exact f407_occupation_injective
  · exact f408_occupation_injective
  · exact f409_occupation_injective
  · exact f410_occupation_injective
  · exact f411_occupation_injective
  · exact f412_occupation_injective
  · exact f413_occupation_injective
  · exact f414_occupation_injective
  · exact f415_occupation_injective
  · exact f416_occupation_injective

#print axioms natFourOccupationBasis_injective
end TorusLean.BosonFiniteCertificate
