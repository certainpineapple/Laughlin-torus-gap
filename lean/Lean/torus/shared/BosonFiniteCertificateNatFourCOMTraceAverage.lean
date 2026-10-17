import torus.shared.BosonFiniteCertificateNatFourCOMSourceFiber
import torus.shared.BosonFiniteCertificateNatFourRelativeMatrices
import torus.shared.BosonFiniteCertificateNatFourDescendants400
import torus.shared.BosonFiniteCertificateNatFourDescendants401
import torus.shared.BosonFiniteCertificateNatFourDescendants402
import torus.shared.BosonFiniteCertificateNatFourDescendants403
import torus.shared.BosonFiniteCertificateNatFourDescendants404
import torus.shared.BosonFiniteCertificateNatFourDescendants405
import torus.shared.BosonFiniteCertificateNatFourDescendants406
import torus.shared.BosonFiniteCertificateNatFourDescendants407
import torus.shared.BosonFiniteCertificateNatFourDescendants408
import torus.shared.BosonFiniteCertificateNatFourDescendants409
import torus.shared.BosonFiniteCertificateNatFourDescendants410
import torus.shared.BosonFiniteCertificateNatFourDescendants411
import torus.shared.BosonFiniteCertificateNatFourDescendants412
import torus.shared.BosonFiniteCertificateNatFourDescendants413
import torus.shared.BosonFiniteCertificateNatFourDescendants414
import torus.shared.BosonFiniteCertificateNatFourDescendants415
import torus.shared.BosonFiniteCertificateNatFourDescendants416

/-! The complete COM coefficient is contracted with the physical trace
weight. Every descendant form is the original independently checked one,
and the final average is the original b4ddaverage, with its 2/4 factor once. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open TorusLean.Shared.BosonFiniteCertificateRealization
open Matrix
open scoped BigOperators

def natFourDescendantTotalDegree (d : Fin 17) (n : Fin (17-d.val)) : Fin 17 :=
  ⟨d.val+n.val,by have hd := d.isLt; have hn := n.isLt; omega⟩

def natFourDescendantRelativeDegree (d : Fin 17) (n : Fin (17-d.val)) :
    Fin ((natFourDescendantTotalDegree d n).val+1) :=
  ⟨d.val,by simp only [natFourDescendantTotalDegree]; omega⟩

def natFourOriginalDescendantForm (d : Fin 17) (n : Fin (17-d.val)) :
    Matrix (Fin (natFourRelativeDimension d)) (Fin (natFourRelativeDimension d)) ℚ := by
  revert n
  refine Fin.cases ?_ ?_ d
  · intro n
    refine Fin.cases ?_ ?_ n
    · exact f400desc0Form
    · intro n
      refine Fin.cases ?_ ?_ n
      · exact f400desc1Form
      · intro n
        refine Fin.cases ?_ ?_ n
        · exact f400desc2Form
        · intro n
          refine Fin.cases ?_ ?_ n
          · exact f400desc3Form
          · intro n
            refine Fin.cases ?_ ?_ n
            · exact f400desc4Form
            · intro n
              refine Fin.cases ?_ ?_ n
              · exact f400desc5Form
              · intro n
                refine Fin.cases ?_ ?_ n
                · exact f400desc6Form
                · intro n
                  refine Fin.cases ?_ ?_ n
                  · exact f400desc7Form
                  · intro n
                    refine Fin.cases ?_ ?_ n
                    · exact f400desc8Form
                    · intro n
                      refine Fin.cases ?_ ?_ n
                      · exact f400desc9Form
                      · intro n
                        refine Fin.cases ?_ ?_ n
                        · exact f400desc10Form
                        · intro n
                          refine Fin.cases ?_ ?_ n
                          · exact f400desc11Form
                          · intro n
                            refine Fin.cases ?_ ?_ n
                            · exact f400desc12Form
                            · intro n
                              refine Fin.cases ?_ ?_ n
                              · exact f400desc13Form
                              · intro n
                                refine Fin.cases ?_ ?_ n
                                · exact f400desc14Form
                                · intro n
                                  refine Fin.cases ?_ ?_ n
                                  · exact f400desc15Form
                                  · intro n
                                    refine Fin.cases ?_ ?_ n
                                    · exact f400desc16Form
                                    · intro n
                                      exact Fin.elim0 n
  · intro d
    refine Fin.cases ?_ ?_ d
    · intro n
      refine Fin.cases ?_ ?_ n
      · exact f401desc0Form
      · intro n
        refine Fin.cases ?_ ?_ n
        · exact f401desc1Form
        · intro n
          refine Fin.cases ?_ ?_ n
          · exact f401desc2Form
          · intro n
            refine Fin.cases ?_ ?_ n
            · exact f401desc3Form
            · intro n
              refine Fin.cases ?_ ?_ n
              · exact f401desc4Form
              · intro n
                refine Fin.cases ?_ ?_ n
                · exact f401desc5Form
                · intro n
                  refine Fin.cases ?_ ?_ n
                  · exact f401desc6Form
                  · intro n
                    refine Fin.cases ?_ ?_ n
                    · exact f401desc7Form
                    · intro n
                      refine Fin.cases ?_ ?_ n
                      · exact f401desc8Form
                      · intro n
                        refine Fin.cases ?_ ?_ n
                        · exact f401desc9Form
                        · intro n
                          refine Fin.cases ?_ ?_ n
                          · exact f401desc10Form
                          · intro n
                            refine Fin.cases ?_ ?_ n
                            · exact f401desc11Form
                            · intro n
                              refine Fin.cases ?_ ?_ n
                              · exact f401desc12Form
                              · intro n
                                refine Fin.cases ?_ ?_ n
                                · exact f401desc13Form
                                · intro n
                                  refine Fin.cases ?_ ?_ n
                                  · exact f401desc14Form
                                  · intro n
                                    refine Fin.cases ?_ ?_ n
                                    · exact f401desc15Form
                                    · intro n
                                      exact Fin.elim0 n
    · intro d
      refine Fin.cases ?_ ?_ d
      · intro n
        refine Fin.cases ?_ ?_ n
        · exact f402desc0Form
        · intro n
          refine Fin.cases ?_ ?_ n
          · exact f402desc1Form
          · intro n
            refine Fin.cases ?_ ?_ n
            · exact f402desc2Form
            · intro n
              refine Fin.cases ?_ ?_ n
              · exact f402desc3Form
              · intro n
                refine Fin.cases ?_ ?_ n
                · exact f402desc4Form
                · intro n
                  refine Fin.cases ?_ ?_ n
                  · exact f402desc5Form
                  · intro n
                    refine Fin.cases ?_ ?_ n
                    · exact f402desc6Form
                    · intro n
                      refine Fin.cases ?_ ?_ n
                      · exact f402desc7Form
                      · intro n
                        refine Fin.cases ?_ ?_ n
                        · exact f402desc8Form
                        · intro n
                          refine Fin.cases ?_ ?_ n
                          · exact f402desc9Form
                          · intro n
                            refine Fin.cases ?_ ?_ n
                            · exact f402desc10Form
                            · intro n
                              refine Fin.cases ?_ ?_ n
                              · exact f402desc11Form
                              · intro n
                                refine Fin.cases ?_ ?_ n
                                · exact f402desc12Form
                                · intro n
                                  refine Fin.cases ?_ ?_ n
                                  · exact f402desc13Form
                                  · intro n
                                    refine Fin.cases ?_ ?_ n
                                    · exact f402desc14Form
                                    · intro n
                                      exact Fin.elim0 n
      · intro d
        refine Fin.cases ?_ ?_ d
        · intro n
          refine Fin.cases ?_ ?_ n
          · exact f403desc0Form
          · intro n
            refine Fin.cases ?_ ?_ n
            · exact f403desc1Form
            · intro n
              refine Fin.cases ?_ ?_ n
              · exact f403desc2Form
              · intro n
                refine Fin.cases ?_ ?_ n
                · exact f403desc3Form
                · intro n
                  refine Fin.cases ?_ ?_ n
                  · exact f403desc4Form
                  · intro n
                    refine Fin.cases ?_ ?_ n
                    · exact f403desc5Form
                    · intro n
                      refine Fin.cases ?_ ?_ n
                      · exact f403desc6Form
                      · intro n
                        refine Fin.cases ?_ ?_ n
                        · exact f403desc7Form
                        · intro n
                          refine Fin.cases ?_ ?_ n
                          · exact f403desc8Form
                          · intro n
                            refine Fin.cases ?_ ?_ n
                            · exact f403desc9Form
                            · intro n
                              refine Fin.cases ?_ ?_ n
                              · exact f403desc10Form
                              · intro n
                                refine Fin.cases ?_ ?_ n
                                · exact f403desc11Form
                                · intro n
                                  refine Fin.cases ?_ ?_ n
                                  · exact f403desc12Form
                                  · intro n
                                    refine Fin.cases ?_ ?_ n
                                    · exact f403desc13Form
                                    · intro n
                                      exact Fin.elim0 n
        · intro d
          refine Fin.cases ?_ ?_ d
          · intro n
            refine Fin.cases ?_ ?_ n
            · exact f404desc0Form
            · intro n
              refine Fin.cases ?_ ?_ n
              · exact f404desc1Form
              · intro n
                refine Fin.cases ?_ ?_ n
                · exact f404desc2Form
                · intro n
                  refine Fin.cases ?_ ?_ n
                  · exact f404desc3Form
                  · intro n
                    refine Fin.cases ?_ ?_ n
                    · exact f404desc4Form
                    · intro n
                      refine Fin.cases ?_ ?_ n
                      · exact f404desc5Form
                      · intro n
                        refine Fin.cases ?_ ?_ n
                        · exact f404desc6Form
                        · intro n
                          refine Fin.cases ?_ ?_ n
                          · exact f404desc7Form
                          · intro n
                            refine Fin.cases ?_ ?_ n
                            · exact f404desc8Form
                            · intro n
                              refine Fin.cases ?_ ?_ n
                              · exact f404desc9Form
                              · intro n
                                refine Fin.cases ?_ ?_ n
                                · exact f404desc10Form
                                · intro n
                                  refine Fin.cases ?_ ?_ n
                                  · exact f404desc11Form
                                  · intro n
                                    refine Fin.cases ?_ ?_ n
                                    · exact f404desc12Form
                                    · intro n
                                      exact Fin.elim0 n
          · intro d
            refine Fin.cases ?_ ?_ d
            · intro n
              refine Fin.cases ?_ ?_ n
              · exact f405desc0Form
              · intro n
                refine Fin.cases ?_ ?_ n
                · exact f405desc1Form
                · intro n
                  refine Fin.cases ?_ ?_ n
                  · exact f405desc2Form
                  · intro n
                    refine Fin.cases ?_ ?_ n
                    · exact f405desc3Form
                    · intro n
                      refine Fin.cases ?_ ?_ n
                      · exact f405desc4Form
                      · intro n
                        refine Fin.cases ?_ ?_ n
                        · exact f405desc5Form
                        · intro n
                          refine Fin.cases ?_ ?_ n
                          · exact f405desc6Form
                          · intro n
                            refine Fin.cases ?_ ?_ n
                            · exact f405desc7Form
                            · intro n
                              refine Fin.cases ?_ ?_ n
                              · exact f405desc8Form
                              · intro n
                                refine Fin.cases ?_ ?_ n
                                · exact f405desc9Form
                                · intro n
                                  refine Fin.cases ?_ ?_ n
                                  · exact f405desc10Form
                                  · intro n
                                    refine Fin.cases ?_ ?_ n
                                    · exact f405desc11Form
                                    · intro n
                                      exact Fin.elim0 n
            · intro d
              refine Fin.cases ?_ ?_ d
              · intro n
                refine Fin.cases ?_ ?_ n
                · exact f406desc0Form
                · intro n
                  refine Fin.cases ?_ ?_ n
                  · exact f406desc1Form
                  · intro n
                    refine Fin.cases ?_ ?_ n
                    · exact f406desc2Form
                    · intro n
                      refine Fin.cases ?_ ?_ n
                      · exact f406desc3Form
                      · intro n
                        refine Fin.cases ?_ ?_ n
                        · exact f406desc4Form
                        · intro n
                          refine Fin.cases ?_ ?_ n
                          · exact f406desc5Form
                          · intro n
                            refine Fin.cases ?_ ?_ n
                            · exact f406desc6Form
                            · intro n
                              refine Fin.cases ?_ ?_ n
                              · exact f406desc7Form
                              · intro n
                                refine Fin.cases ?_ ?_ n
                                · exact f406desc8Form
                                · intro n
                                  refine Fin.cases ?_ ?_ n
                                  · exact f406desc9Form
                                  · intro n
                                    refine Fin.cases ?_ ?_ n
                                    · exact f406desc10Form
                                    · intro n
                                      exact Fin.elim0 n
              · intro d
                refine Fin.cases ?_ ?_ d
                · intro n
                  refine Fin.cases ?_ ?_ n
                  · exact f407desc0Form
                  · intro n
                    refine Fin.cases ?_ ?_ n
                    · exact f407desc1Form
                    · intro n
                      refine Fin.cases ?_ ?_ n
                      · exact f407desc2Form
                      · intro n
                        refine Fin.cases ?_ ?_ n
                        · exact f407desc3Form
                        · intro n
                          refine Fin.cases ?_ ?_ n
                          · exact f407desc4Form
                          · intro n
                            refine Fin.cases ?_ ?_ n
                            · exact f407desc5Form
                            · intro n
                              refine Fin.cases ?_ ?_ n
                              · exact f407desc6Form
                              · intro n
                                refine Fin.cases ?_ ?_ n
                                · exact f407desc7Form
                                · intro n
                                  refine Fin.cases ?_ ?_ n
                                  · exact f407desc8Form
                                  · intro n
                                    refine Fin.cases ?_ ?_ n
                                    · exact f407desc9Form
                                    · intro n
                                      exact Fin.elim0 n
                · intro d
                  refine Fin.cases ?_ ?_ d
                  · intro n
                    refine Fin.cases ?_ ?_ n
                    · exact f408desc0Form
                    · intro n
                      refine Fin.cases ?_ ?_ n
                      · exact f408desc1Form
                      · intro n
                        refine Fin.cases ?_ ?_ n
                        · exact f408desc2Form
                        · intro n
                          refine Fin.cases ?_ ?_ n
                          · exact f408desc3Form
                          · intro n
                            refine Fin.cases ?_ ?_ n
                            · exact f408desc4Form
                            · intro n
                              refine Fin.cases ?_ ?_ n
                              · exact f408desc5Form
                              · intro n
                                refine Fin.cases ?_ ?_ n
                                · exact f408desc6Form
                                · intro n
                                  refine Fin.cases ?_ ?_ n
                                  · exact f408desc7Form
                                  · intro n
                                    refine Fin.cases ?_ ?_ n
                                    · exact f408desc8Form
                                    · intro n
                                      exact Fin.elim0 n
                  · intro d
                    refine Fin.cases ?_ ?_ d
                    · intro n
                      refine Fin.cases ?_ ?_ n
                      · exact f409desc0Form
                      · intro n
                        refine Fin.cases ?_ ?_ n
                        · exact f409desc1Form
                        · intro n
                          refine Fin.cases ?_ ?_ n
                          · exact f409desc2Form
                          · intro n
                            refine Fin.cases ?_ ?_ n
                            · exact f409desc3Form
                            · intro n
                              refine Fin.cases ?_ ?_ n
                              · exact f409desc4Form
                              · intro n
                                refine Fin.cases ?_ ?_ n
                                · exact f409desc5Form
                                · intro n
                                  refine Fin.cases ?_ ?_ n
                                  · exact f409desc6Form
                                  · intro n
                                    refine Fin.cases ?_ ?_ n
                                    · exact f409desc7Form
                                    · intro n
                                      exact Fin.elim0 n
                    · intro d
                      refine Fin.cases ?_ ?_ d
                      · intro n
                        refine Fin.cases ?_ ?_ n
                        · exact f410desc0Form
                        · intro n
                          refine Fin.cases ?_ ?_ n
                          · exact f410desc1Form
                          · intro n
                            refine Fin.cases ?_ ?_ n
                            · exact f410desc2Form
                            · intro n
                              refine Fin.cases ?_ ?_ n
                              · exact f410desc3Form
                              · intro n
                                refine Fin.cases ?_ ?_ n
                                · exact f410desc4Form
                                · intro n
                                  refine Fin.cases ?_ ?_ n
                                  · exact f410desc5Form
                                  · intro n
                                    refine Fin.cases ?_ ?_ n
                                    · exact f410desc6Form
                                    · intro n
                                      exact Fin.elim0 n
                      · intro d
                        refine Fin.cases ?_ ?_ d
                        · intro n
                          refine Fin.cases ?_ ?_ n
                          · exact f411desc0Form
                          · intro n
                            refine Fin.cases ?_ ?_ n
                            · exact f411desc1Form
                            · intro n
                              refine Fin.cases ?_ ?_ n
                              · exact f411desc2Form
                              · intro n
                                refine Fin.cases ?_ ?_ n
                                · exact f411desc3Form
                                · intro n
                                  refine Fin.cases ?_ ?_ n
                                  · exact f411desc4Form
                                  · intro n
                                    refine Fin.cases ?_ ?_ n
                                    · exact f411desc5Form
                                    · intro n
                                      exact Fin.elim0 n
                        · intro d
                          refine Fin.cases ?_ ?_ d
                          · intro n
                            refine Fin.cases ?_ ?_ n
                            · exact f412desc0Form
                            · intro n
                              refine Fin.cases ?_ ?_ n
                              · exact f412desc1Form
                              · intro n
                                refine Fin.cases ?_ ?_ n
                                · exact f412desc2Form
                                · intro n
                                  refine Fin.cases ?_ ?_ n
                                  · exact f412desc3Form
                                  · intro n
                                    refine Fin.cases ?_ ?_ n
                                    · exact f412desc4Form
                                    · intro n
                                      exact Fin.elim0 n
                          · intro d
                            refine Fin.cases ?_ ?_ d
                            · intro n
                              refine Fin.cases ?_ ?_ n
                              · exact f413desc0Form
                              · intro n
                                refine Fin.cases ?_ ?_ n
                                · exact f413desc1Form
                                · intro n
                                  refine Fin.cases ?_ ?_ n
                                  · exact f413desc2Form
                                  · intro n
                                    refine Fin.cases ?_ ?_ n
                                    · exact f413desc3Form
                                    · intro n
                                      exact Fin.elim0 n
                            · intro d
                              refine Fin.cases ?_ ?_ d
                              · intro n
                                refine Fin.cases ?_ ?_ n
                                · exact f414desc0Form
                                · intro n
                                  refine Fin.cases ?_ ?_ n
                                  · exact f414desc1Form
                                  · intro n
                                    refine Fin.cases ?_ ?_ n
                                    · exact f414desc2Form
                                    · intro n
                                      exact Fin.elim0 n
                              · intro d
                                refine Fin.cases ?_ ?_ d
                                · intro n
                                  refine Fin.cases ?_ ?_ n
                                  · exact f415desc0Form
                                  · intro n
                                    refine Fin.cases ?_ ?_ n
                                    · exact f415desc1Form
                                    · intro n
                                      exact Fin.elim0 n
                                · intro d
                                  refine Fin.cases ?_ ?_ d
                                  · intro n
                                    refine Fin.cases ?_ ?_ n
                                    · exact f416desc0Form
                                    · intro n
                                      exact Fin.elim0 n
                                  · intro d
                                    exact Fin.elim0 d

def natFourOriginalDescendantCoefficient (d : Fin 17) (n : Fin (17-d.val)) :
    Matrix (Fin (natFourRelativeDimension d)) (Fin (natFourRelativeDimension d)) ℂ :=
  natFourOriginalCOMCoefficientFiber (natFourDescendantTotalDegree d n)
    (natFourDescendantRelativeDegree d n)

theorem natFourOriginalDescendantForm_source (d : Fin 17) (n : Fin (17-d.val)) :
    natFourOriginalCOMFiberForm (natFourDescendantTotalDegree d n)
      (natFourDescendantRelativeDegree d n)=natFourOriginalDescendantForm d n := by
  fin_cases d
  · fin_cases n
    · exact f400desc0_compression_check
    · exact f400desc1_compression_check
    · exact f400desc2_compression_check
    · exact f400desc3_compression_check
    · exact f400desc4_compression_check
    · exact f400desc5_compression_check
    · exact f400desc6_compression_check
    · exact f400desc7_compression_check
    · exact f400desc8_compression_check
    · exact f400desc9_compression_check
    · exact f400desc10_compression_check
    · exact f400desc11_compression_check
    · exact f400desc12_compression_check
    · exact f400desc13_compression_check
    · exact f400desc14_compression_check
    · exact f400desc15_compression_check
    · exact f400desc16_compression_check
  · fin_cases n
    · exact f401desc0_compression_check
    · exact f401desc1_compression_check
    · exact f401desc2_compression_check
    · exact f401desc3_compression_check
    · exact f401desc4_compression_check
    · exact f401desc5_compression_check
    · exact f401desc6_compression_check
    · exact f401desc7_compression_check
    · exact f401desc8_compression_check
    · exact f401desc9_compression_check
    · exact f401desc10_compression_check
    · exact f401desc11_compression_check
    · exact f401desc12_compression_check
    · exact f401desc13_compression_check
    · exact f401desc14_compression_check
    · exact f401desc15_compression_check
  · fin_cases n
    · exact f402desc0_compression_check
    · exact f402desc1_compression_check
    · exact f402desc2_compression_check
    · exact f402desc3_compression_check
    · exact f402desc4_compression_check
    · exact f402desc5_compression_check
    · exact f402desc6_compression_check
    · exact f402desc7_compression_check
    · exact f402desc8_compression_check
    · exact f402desc9_compression_check
    · exact f402desc10_compression_check
    · exact f402desc11_compression_check
    · exact f402desc12_compression_check
    · exact f402desc13_compression_check
    · exact f402desc14_compression_check
  · fin_cases n
    · exact f403desc0_compression_check
    · exact f403desc1_compression_check
    · exact f403desc2_compression_check
    · exact f403desc3_compression_check
    · exact f403desc4_compression_check
    · exact f403desc5_compression_check
    · exact f403desc6_compression_check
    · exact f403desc7_compression_check
    · exact f403desc8_compression_check
    · exact f403desc9_compression_check
    · exact f403desc10_compression_check
    · exact f403desc11_compression_check
    · exact f403desc12_compression_check
    · exact f403desc13_compression_check
  · fin_cases n
    · exact f404desc0_compression_check
    · exact f404desc1_compression_check
    · exact f404desc2_compression_check
    · exact f404desc3_compression_check
    · exact f404desc4_compression_check
    · exact f404desc5_compression_check
    · exact f404desc6_compression_check
    · exact f404desc7_compression_check
    · exact f404desc8_compression_check
    · exact f404desc9_compression_check
    · exact f404desc10_compression_check
    · exact f404desc11_compression_check
    · exact f404desc12_compression_check
  · fin_cases n
    · exact f405desc0_compression_check
    · exact f405desc1_compression_check
    · exact f405desc2_compression_check
    · exact f405desc3_compression_check
    · exact f405desc4_compression_check
    · exact f405desc5_compression_check
    · exact f405desc6_compression_check
    · exact f405desc7_compression_check
    · exact f405desc8_compression_check
    · exact f405desc9_compression_check
    · exact f405desc10_compression_check
    · exact f405desc11_compression_check
  · fin_cases n
    · exact f406desc0_compression_check
    · exact f406desc1_compression_check
    · exact f406desc2_compression_check
    · exact f406desc3_compression_check
    · exact f406desc4_compression_check
    · exact f406desc5_compression_check
    · exact f406desc6_compression_check
    · exact f406desc7_compression_check
    · exact f406desc8_compression_check
    · exact f406desc9_compression_check
    · exact f406desc10_compression_check
  · fin_cases n
    · exact f407desc0_compression_check
    · exact f407desc1_compression_check
    · exact f407desc2_compression_check
    · exact f407desc3_compression_check
    · exact f407desc4_compression_check
    · exact f407desc5_compression_check
    · exact f407desc6_compression_check
    · exact f407desc7_compression_check
    · exact f407desc8_compression_check
    · exact f407desc9_compression_check
  · fin_cases n
    · exact f408desc0_compression_check
    · exact f408desc1_compression_check
    · exact f408desc2_compression_check
    · exact f408desc3_compression_check
    · exact f408desc4_compression_check
    · exact f408desc5_compression_check
    · exact f408desc6_compression_check
    · exact f408desc7_compression_check
    · exact f408desc8_compression_check
  · fin_cases n
    · exact f409desc0_compression_check
    · exact f409desc1_compression_check
    · exact f409desc2_compression_check
    · exact f409desc3_compression_check
    · exact f409desc4_compression_check
    · exact f409desc5_compression_check
    · exact f409desc6_compression_check
    · exact f409desc7_compression_check
  · fin_cases n
    · exact f410desc0_compression_check
    · exact f410desc1_compression_check
    · exact f410desc2_compression_check
    · exact f410desc3_compression_check
    · exact f410desc4_compression_check
    · exact f410desc5_compression_check
    · exact f410desc6_compression_check
  · fin_cases n
    · exact f411desc0_compression_check
    · exact f411desc1_compression_check
    · exact f411desc2_compression_check
    · exact f411desc3_compression_check
    · exact f411desc4_compression_check
    · exact f411desc5_compression_check
  · fin_cases n
    · exact f412desc0_compression_check
    · exact f412desc1_compression_check
    · exact f412desc2_compression_check
    · exact f412desc3_compression_check
    · exact f412desc4_compression_check
  · fin_cases n
    · exact f413desc0_compression_check
    · exact f413desc1_compression_check
    · exact f413desc2_compression_check
    · exact f413desc3_compression_check
  · fin_cases n
    · exact f414desc0_compression_check
    · exact f414desc1_compression_check
    · exact f414desc2_compression_check
  · fin_cases n
    · exact f415desc0_compression_check
    · exact f415desc1_compression_check
  · fin_cases n
    · exact f416desc0_compression_check

theorem natFourOriginalDescendantForm_average (d : Fin 17) :
    (∑ n : Fin (17-d.val), natFourOriginalCOMWeight n.val • natFourOriginalDescendantForm d n)=
      natFourRelativeCOMMatrix d := by
  fin_cases d
  · have h (n : Fin 17) : natFourOriginalDescendantForm 0 n=f400descForms n.val := by
      fin_cases n <;> rfl
    calc
      _ = (∑ n : Fin 17, natFourOriginalCOMWeight n.val • f400descForms n.val) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact congrArg (fun F => natFourOriginalCOMWeight n.val • F) (h n)
      _ = _ := by
        change (∑ n : Fin 17, natFourOriginalCOMWeight n.val • f400descForms n.val) = b400average
        exact (Fin.sum_univ_eq_sum_range
          (fun n : ℕ => natFourOriginalCOMWeight n • f400descForms n) 17).trans
            f400_COM_average_check
  · have h (n : Fin 16) : natFourOriginalDescendantForm 1 n=f401descForms n.val := by
      fin_cases n <;> rfl
    calc
      _ = (∑ n : Fin 16, natFourOriginalCOMWeight n.val • f401descForms n.val) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact congrArg (fun F => natFourOriginalCOMWeight n.val • F) (h n)
      _ = _ := by
        change (∑ n : Fin 16, natFourOriginalCOMWeight n.val • f401descForms n.val) = b401average
        exact (Fin.sum_univ_eq_sum_range
          (fun n : ℕ => natFourOriginalCOMWeight n • f401descForms n) 16).trans
            f401_COM_average_check
  · have h (n : Fin 15) : natFourOriginalDescendantForm 2 n=f402descForms n.val := by
      fin_cases n <;> rfl
    calc
      _ = (∑ n : Fin 15, natFourOriginalCOMWeight n.val • f402descForms n.val) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact congrArg (fun F => natFourOriginalCOMWeight n.val • F) (h n)
      _ = _ := by
        change (∑ n : Fin 15, natFourOriginalCOMWeight n.val • f402descForms n.val) = b402average
        exact (Fin.sum_univ_eq_sum_range
          (fun n : ℕ => natFourOriginalCOMWeight n • f402descForms n) 15).trans
            f402_COM_average_check
  · have h (n : Fin 14) : natFourOriginalDescendantForm 3 n=f403descForms n.val := by
      fin_cases n <;> rfl
    calc
      _ = (∑ n : Fin 14, natFourOriginalCOMWeight n.val • f403descForms n.val) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact congrArg (fun F => natFourOriginalCOMWeight n.val • F) (h n)
      _ = _ := by
        change (∑ n : Fin 14, natFourOriginalCOMWeight n.val • f403descForms n.val) = b403average
        exact (Fin.sum_univ_eq_sum_range
          (fun n : ℕ => natFourOriginalCOMWeight n • f403descForms n) 14).trans
            f403_COM_average_check
  · have h (n : Fin 13) : natFourOriginalDescendantForm 4 n=f404descForms n.val := by
      fin_cases n <;> rfl
    calc
      _ = (∑ n : Fin 13, natFourOriginalCOMWeight n.val • f404descForms n.val) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact congrArg (fun F => natFourOriginalCOMWeight n.val • F) (h n)
      _ = _ := by
        change (∑ n : Fin 13, natFourOriginalCOMWeight n.val • f404descForms n.val) = b404average
        exact (Fin.sum_univ_eq_sum_range
          (fun n : ℕ => natFourOriginalCOMWeight n • f404descForms n) 13).trans
            f404_COM_average_check
  · have h (n : Fin 12) : natFourOriginalDescendantForm 5 n=f405descForms n.val := by
      fin_cases n <;> rfl
    calc
      _ = (∑ n : Fin 12, natFourOriginalCOMWeight n.val • f405descForms n.val) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact congrArg (fun F => natFourOriginalCOMWeight n.val • F) (h n)
      _ = _ := by
        change (∑ n : Fin 12, natFourOriginalCOMWeight n.val • f405descForms n.val) = b405average
        exact (Fin.sum_univ_eq_sum_range
          (fun n : ℕ => natFourOriginalCOMWeight n • f405descForms n) 12).trans
            f405_COM_average_check
  · have h (n : Fin 11) : natFourOriginalDescendantForm 6 n=f406descForms n.val := by
      fin_cases n <;> rfl
    calc
      _ = (∑ n : Fin 11, natFourOriginalCOMWeight n.val • f406descForms n.val) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact congrArg (fun F => natFourOriginalCOMWeight n.val • F) (h n)
      _ = _ := by
        change (∑ n : Fin 11, natFourOriginalCOMWeight n.val • f406descForms n.val) = b406average
        exact (Fin.sum_univ_eq_sum_range
          (fun n : ℕ => natFourOriginalCOMWeight n • f406descForms n) 11).trans
            f406_COM_average_check
  · have h (n : Fin 10) : natFourOriginalDescendantForm 7 n=f407descForms n.val := by
      fin_cases n <;> rfl
    calc
      _ = (∑ n : Fin 10, natFourOriginalCOMWeight n.val • f407descForms n.val) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact congrArg (fun F => natFourOriginalCOMWeight n.val • F) (h n)
      _ = _ := by
        change (∑ n : Fin 10, natFourOriginalCOMWeight n.val • f407descForms n.val) = b407average
        exact (Fin.sum_univ_eq_sum_range
          (fun n : ℕ => natFourOriginalCOMWeight n • f407descForms n) 10).trans
            f407_COM_average_check
  · have h (n : Fin 9) : natFourOriginalDescendantForm 8 n=f408descForms n.val := by
      fin_cases n <;> rfl
    calc
      _ = (∑ n : Fin 9, natFourOriginalCOMWeight n.val • f408descForms n.val) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact congrArg (fun F => natFourOriginalCOMWeight n.val • F) (h n)
      _ = _ := by
        change (∑ n : Fin 9, natFourOriginalCOMWeight n.val • f408descForms n.val) = b408average
        exact (Fin.sum_univ_eq_sum_range
          (fun n : ℕ => natFourOriginalCOMWeight n • f408descForms n) 9).trans
            f408_COM_average_check
  · have h (n : Fin 8) : natFourOriginalDescendantForm 9 n=f409descForms n.val := by
      fin_cases n <;> rfl
    calc
      _ = (∑ n : Fin 8, natFourOriginalCOMWeight n.val • f409descForms n.val) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact congrArg (fun F => natFourOriginalCOMWeight n.val • F) (h n)
      _ = _ := by
        change (∑ n : Fin 8, natFourOriginalCOMWeight n.val • f409descForms n.val) = b409average
        exact (Fin.sum_univ_eq_sum_range
          (fun n : ℕ => natFourOriginalCOMWeight n • f409descForms n) 8).trans
            f409_COM_average_check
  · have h (n : Fin 7) : natFourOriginalDescendantForm 10 n=f410descForms n.val := by
      fin_cases n <;> rfl
    calc
      _ = (∑ n : Fin 7, natFourOriginalCOMWeight n.val • f410descForms n.val) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact congrArg (fun F => natFourOriginalCOMWeight n.val • F) (h n)
      _ = _ := by
        change (∑ n : Fin 7, natFourOriginalCOMWeight n.val • f410descForms n.val) = b410average
        exact (Fin.sum_univ_eq_sum_range
          (fun n : ℕ => natFourOriginalCOMWeight n • f410descForms n) 7).trans
            f410_COM_average_check
  · have h (n : Fin 6) : natFourOriginalDescendantForm 11 n=f411descForms n.val := by
      fin_cases n <;> rfl
    calc
      _ = (∑ n : Fin 6, natFourOriginalCOMWeight n.val • f411descForms n.val) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact congrArg (fun F => natFourOriginalCOMWeight n.val • F) (h n)
      _ = _ := by
        change (∑ n : Fin 6, natFourOriginalCOMWeight n.val • f411descForms n.val) = b411average
        exact (Fin.sum_univ_eq_sum_range
          (fun n : ℕ => natFourOriginalCOMWeight n • f411descForms n) 6).trans
            f411_COM_average_check
  · have h (n : Fin 5) : natFourOriginalDescendantForm 12 n=f412descForms n.val := by
      fin_cases n <;> rfl
    calc
      _ = (∑ n : Fin 5, natFourOriginalCOMWeight n.val • f412descForms n.val) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact congrArg (fun F => natFourOriginalCOMWeight n.val • F) (h n)
      _ = _ := by
        change (∑ n : Fin 5, natFourOriginalCOMWeight n.val • f412descForms n.val) = b412average
        exact (Fin.sum_univ_eq_sum_range
          (fun n : ℕ => natFourOriginalCOMWeight n • f412descForms n) 5).trans
            f412_COM_average_check
  · have h (n : Fin 4) : natFourOriginalDescendantForm 13 n=f413descForms n.val := by
      fin_cases n <;> rfl
    calc
      _ = (∑ n : Fin 4, natFourOriginalCOMWeight n.val • f413descForms n.val) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact congrArg (fun F => natFourOriginalCOMWeight n.val • F) (h n)
      _ = _ := by
        change (∑ n : Fin 4, natFourOriginalCOMWeight n.val • f413descForms n.val) = b413average
        exact (Fin.sum_univ_eq_sum_range
          (fun n : ℕ => natFourOriginalCOMWeight n • f413descForms n) 4).trans
            f413_COM_average_check
  · have h (n : Fin 3) : natFourOriginalDescendantForm 14 n=f414descForms n.val := by
      fin_cases n <;> rfl
    calc
      _ = (∑ n : Fin 3, natFourOriginalCOMWeight n.val • f414descForms n.val) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact congrArg (fun F => natFourOriginalCOMWeight n.val • F) (h n)
      _ = _ := by
        change (∑ n : Fin 3, natFourOriginalCOMWeight n.val • f414descForms n.val) = b414average
        exact (Fin.sum_univ_eq_sum_range
          (fun n : ℕ => natFourOriginalCOMWeight n • f414descForms n) 3).trans
            f414_COM_average_check
  · have h (n : Fin 2) : natFourOriginalDescendantForm 15 n=f415descForms n.val := by
      fin_cases n <;> rfl
    calc
      _ = (∑ n : Fin 2, natFourOriginalCOMWeight n.val • f415descForms n.val) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact congrArg (fun F => natFourOriginalCOMWeight n.val • F) (h n)
      _ = _ := by
        change (∑ n : Fin 2, natFourOriginalCOMWeight n.val • f415descForms n.val) = b415average
        exact (Fin.sum_univ_eq_sum_range
          (fun n : ℕ => natFourOriginalCOMWeight n • f415descForms n) 2).trans
            f415_COM_average_check
  · have h (n : Fin 1) : natFourOriginalDescendantForm 16 n=f416descForms n.val := by
      fin_cases n ; rfl
    calc
      _ = (∑ n : Fin 1, natFourOriginalCOMWeight n.val • f416descForms n.val) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact congrArg (fun F => natFourOriginalCOMWeight n.val • F) (h n)
      _ = _ := by
        change (∑ n : Fin 1, natFourOriginalCOMWeight n.val • f416descForms n.val) = b416average
        exact (Fin.sum_univ_eq_sum_range
          (fun n : ℕ => natFourOriginalCOMWeight n • f416descForms n) 1).trans
            f416_COM_average_check

theorem natFourOriginalDescendantCoefficient_eq (d : Fin 17) (n : Fin (17-d.val)) :
    natFourOriginalDescendantCoefficient d n=
      ((natFourCOMWeight n.val)⁻¹*(natFourCOMWeight n.val)⁻¹) •
        inverseGramCoefficient (complexify (natFourRelativeGramInverse d))
          (complexify (natFourOriginalDescendantForm d n)) := by
  rw [natFourOriginalDescendantCoefficient,natFourOriginalCOMCoefficientFiber_eq,
    natFourOriginalDescendantForm_source]
  simp only [natFourDescendantTotalDegree,natFourDescendantRelativeDegree,
    natFourRelativeDegreeAt,Nat.add_sub_cancel_left,Fin.eta]
  rfl

/-- The exact finite coefficient identity consumed after physical COM trace.
The lhs has all n=0..16-d fibers and the unnormalized trace's w/2. -/
theorem natFourOriginalCOM_trace_rank_coefficient (d : Fin 17) :
    (∑ n : Fin (17-d.val), (natFourCOMWeight n.val/2) •
      natFourOriginalDescendantCoefficient d n)=natFourRelativeM4RankCoefficient d := by
  apply natFour_COM_trace_coefficient_sum
    (complexify (natFourRelativeGramInverse d))
    (fun n => complexify (natFourOriginalDescendantForm d n))
    (natFourOriginalDescendantCoefficient d) (complexify (natFourRelativeCOMMatrix d))
  · exact natFourOriginalDescendantCoefficient_eq d
  · have h := congrArg complexify (natFourOriginalDescendantForm_average d)
    simpa only [natFour_complexify_sum,complexify_smul_rat] using h

#print axioms natFourOriginalDescendantForm_source
#print axioms natFourOriginalDescendantForm_average
#print axioms natFourOriginalDescendantCoefficient_eq
#print axioms natFourOriginalCOM_trace_rank_coefficient
end TorusLean.BosonFiniteCertificate
