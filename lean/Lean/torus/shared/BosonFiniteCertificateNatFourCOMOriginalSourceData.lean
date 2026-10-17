import torus.shared.BosonFiniteCertificateNatFourCOMSourceForm
import torus.shared.BosonFiniteCertificateNatFourRaw400
import torus.shared.BosonFiniteCertificateNatFourRaw401
import torus.shared.BosonFiniteCertificateNatFourRaw402
import torus.shared.BosonFiniteCertificateNatFourRaw403
import torus.shared.BosonFiniteCertificateNatFourRaw404
import torus.shared.BosonFiniteCertificateNatFourRaw405
import torus.shared.BosonFiniteCertificateNatFourRaw406
import torus.shared.BosonFiniteCertificateNatFourRaw407
import torus.shared.BosonFiniteCertificateNatFourRaw408
import torus.shared.BosonFiniteCertificateNatFourRaw409
import torus.shared.BosonFiniteCertificateNatFourRaw410
import torus.shared.BosonFiniteCertificateNatFourRaw411
import torus.shared.BosonFiniteCertificateNatFourRaw412
import torus.shared.BosonFiniteCertificateNatFourRaw413
import torus.shared.BosonFiniteCertificateNatFourRaw414
import torus.shared.BosonFiniteCertificateNatFourRaw415
import torus.shared.BosonFiniteCertificateNatFourRaw416

/-! All seventeen separately checked original M4 form matrices enter the
whole-N4, all-COM-level rank expansion. This is an identity of the original
normal-ordered source, not a definition of a candidate matrix operator. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

def natFourOriginalRawFormMatrix (D : Fin 17) :
    Matrix (Fin (natFourOccupationDimension D)) (Fin (natFourOccupationDimension D)) ℚ := by
  refine Fin.cases ?_ ?_ D
  · exact f400rawM4Form
  · intro D
    refine Fin.cases ?_ ?_ D
    · exact f401rawM4Form
    · intro D
      refine Fin.cases ?_ ?_ D
      · exact f402rawM4Form
      · intro D
        refine Fin.cases ?_ ?_ D
        · exact f403rawM4Form
        · intro D
          refine Fin.cases ?_ ?_ D
          · exact f404rawM4Form
          · intro D
            refine Fin.cases ?_ ?_ D
            · exact f405rawM4Form
            · intro D
              refine Fin.cases ?_ ?_ D
              · exact f406rawM4Form
              · intro D
                refine Fin.cases ?_ ?_ D
                · exact f407rawM4Form
                · intro D
                  refine Fin.cases ?_ ?_ D
                  · exact f408rawM4Form
                  · intro D
                    refine Fin.cases ?_ ?_ D
                    · exact f409rawM4Form
                    · intro D
                      refine Fin.cases ?_ ?_ D
                      · exact f410rawM4Form
                      · intro D
                        refine Fin.cases ?_ ?_ D
                        · exact f411rawM4Form
                        · intro D
                          refine Fin.cases ?_ ?_ D
                          · exact f412rawM4Form
                          · intro D
                            refine Fin.cases ?_ ?_ D
                            · exact f413rawM4Form
                            · intro D
                              refine Fin.cases ?_ ?_ D
                              · exact f414rawM4Form
                              · intro D
                                refine Fin.cases ?_ ?_ D
                                · exact f415rawM4Form
                                · intro D
                                  refine Fin.cases ?_ ?_ D
                                  · exact f416rawM4Form
                                  · intro D
                                    exact Fin.elim0 D

end TorusLean.BosonFiniteCertificate
