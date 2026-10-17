import torus.shared.BosonFiniteCertificateNatFourCOMOriginalSourceData

/-! The unchanged original complete-COM rank coefficient, separated from the
source-form proof so its exact finite fiber algebra can be checked independently. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix

/-- Complete-degree rank coefficient. Both inverse Grams surround the
independently verified original raw form in the actual complete COM family. -/
def natFourOriginalCOMRankCoefficient (D : Fin 17) :
    Matrix (Fin (natFourOccupationDimension D)) (Fin (natFourOccupationDimension D)) ℂ :=
  natFourCOMSourceRankCoefficient D (natFourOriginalRawFormMatrix D)

end TorusLean.BosonFiniteCertificate
