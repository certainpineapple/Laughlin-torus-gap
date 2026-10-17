import torus.shared.BosonFiniteCertificateNatFourCOMRelativeFamily
import torus.shared.BosonFiniteCertificateNatFourCOMBlockGram
import Mathlib.Data.Fintype.EquivFin
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates400
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates401
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates402
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates403
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates404
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates405
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates406
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates407
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates408
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates409
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates410
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates411
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates412
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates413
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates414
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates415
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates416

/-! The complete four-particle COM coordinate change uses precisely the
already proved descendant columns. No independently solved full-size inverse
or new numerical coordinates enter. An arbitrary finite equivalence only
labels the complete dependent family, including every empty fiber. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open TorusLean.Shared.BosonFiniteCertificateWords
open Matrix
open scoped BigOperators

def natFourOccupationDimension : Fin 17 → ℕ := ![1,1,2,3,5,6,9,11,15,18,23,27,34,39,47,54,64]

def natFourOccupationBasis (D : Fin 17) : Fin (natFourOccupationDimension D) → List ℕ := by
  refine Fin.cases ?_ ?_ D
  · exact f400basis
  · intro D
    refine Fin.cases ?_ ?_ D
    · exact f401basis
    · intro D
      refine Fin.cases ?_ ?_ D
      · exact f402basis
      · intro D
        refine Fin.cases ?_ ?_ D
        · exact f403basis
        · intro D
          refine Fin.cases ?_ ?_ D
          · exact f404basis
          · intro D
            refine Fin.cases ?_ ?_ D
            · exact f405basis
            · intro D
              refine Fin.cases ?_ ?_ D
              · exact f406basis
              · intro D
                refine Fin.cases ?_ ?_ D
                · exact f407basis
                · intro D
                  refine Fin.cases ?_ ?_ D
                  · exact f408basis
                  · intro D
                    refine Fin.cases ?_ ?_ D
                    · exact f409basis
                    · intro D
                      refine Fin.cases ?_ ?_ D
                      · exact f410basis
                      · intro D
                        refine Fin.cases ?_ ?_ D
                        · exact f411basis
                        · intro D
                          refine Fin.cases ?_ ?_ D
                          · exact f412basis
                          · intro D
                            refine Fin.cases ?_ ?_ D
                            · exact f413basis
                            · intro D
                              refine Fin.cases ?_ ?_ D
                              · exact f414basis
                              · intro D
                                refine Fin.cases ?_ ?_ D
                                · exact f415basis
                                · intro D
                                  refine Fin.cases ?_ ?_ D
                                  · exact f416basis
                                  · intro D
                                    exact Fin.elim0 D

def natFourRelativeDegreeAt (D : Fin 17) (d : Fin (D.val+1)) : Fin 17 :=
  ⟨d.val,by have hD := D.isLt; have hd := d.isLt; omega⟩

def natFourRelativeDimensionAt (D : Fin 17) (d : Fin (D.val+1)) : ℕ :=
  natFourRelativeDimension (natFourRelativeDegreeAt D d)

def natFourCOMFiberCoordinates (D : Fin 17) (d : Fin (D.val+1)) :
    Matrix (Fin (natFourOccupationDimension D)) (Fin (natFourRelativeDimensionAt D d)) ℚ := by
  revert d
  refine Fin.cases ?_ ?_ D
  · intro d
    refine Fin.cases ?_ ?_ d
    · exact f400desc0
    · intro d
      exact Fin.elim0 d
  · intro D
    refine Fin.cases ?_ ?_ D
    · intro d
      refine Fin.cases ?_ ?_ d
      · exact f400desc1
      · intro d
        refine Fin.cases ?_ ?_ d
        · exact f401desc0
        · intro d
          exact Fin.elim0 d
    · intro D
      refine Fin.cases ?_ ?_ D
      · intro d
        refine Fin.cases ?_ ?_ d
        · exact f400desc2
        · intro d
          refine Fin.cases ?_ ?_ d
          · exact f401desc1
          · intro d
            refine Fin.cases ?_ ?_ d
            · exact f402desc0
            · intro d
              exact Fin.elim0 d
      · intro D
        refine Fin.cases ?_ ?_ D
        · intro d
          refine Fin.cases ?_ ?_ d
          · exact f400desc3
          · intro d
            refine Fin.cases ?_ ?_ d
            · exact f401desc2
            · intro d
              refine Fin.cases ?_ ?_ d
              · exact f402desc1
              · intro d
                refine Fin.cases ?_ ?_ d
                · exact f403desc0
                · intro d
                  exact Fin.elim0 d
        · intro D
          refine Fin.cases ?_ ?_ D
          · intro d
            refine Fin.cases ?_ ?_ d
            · exact f400desc4
            · intro d
              refine Fin.cases ?_ ?_ d
              · exact f401desc3
              · intro d
                refine Fin.cases ?_ ?_ d
                · exact f402desc2
                · intro d
                  refine Fin.cases ?_ ?_ d
                  · exact f403desc1
                  · intro d
                    refine Fin.cases ?_ ?_ d
                    · exact f404desc0
                    · intro d
                      exact Fin.elim0 d
          · intro D
            refine Fin.cases ?_ ?_ D
            · intro d
              refine Fin.cases ?_ ?_ d
              · exact f400desc5
              · intro d
                refine Fin.cases ?_ ?_ d
                · exact f401desc4
                · intro d
                  refine Fin.cases ?_ ?_ d
                  · exact f402desc3
                  · intro d
                    refine Fin.cases ?_ ?_ d
                    · exact f403desc2
                    · intro d
                      refine Fin.cases ?_ ?_ d
                      · exact f404desc1
                      · intro d
                        refine Fin.cases ?_ ?_ d
                        · exact f405desc0
                        · intro d
                          exact Fin.elim0 d
            · intro D
              refine Fin.cases ?_ ?_ D
              · intro d
                refine Fin.cases ?_ ?_ d
                · exact f400desc6
                · intro d
                  refine Fin.cases ?_ ?_ d
                  · exact f401desc5
                  · intro d
                    refine Fin.cases ?_ ?_ d
                    · exact f402desc4
                    · intro d
                      refine Fin.cases ?_ ?_ d
                      · exact f403desc3
                      · intro d
                        refine Fin.cases ?_ ?_ d
                        · exact f404desc2
                        · intro d
                          refine Fin.cases ?_ ?_ d
                          · exact f405desc1
                          · intro d
                            refine Fin.cases ?_ ?_ d
                            · exact f406desc0
                            · intro d
                              exact Fin.elim0 d
              · intro D
                refine Fin.cases ?_ ?_ D
                · intro d
                  refine Fin.cases ?_ ?_ d
                  · exact f400desc7
                  · intro d
                    refine Fin.cases ?_ ?_ d
                    · exact f401desc6
                    · intro d
                      refine Fin.cases ?_ ?_ d
                      · exact f402desc5
                      · intro d
                        refine Fin.cases ?_ ?_ d
                        · exact f403desc4
                        · intro d
                          refine Fin.cases ?_ ?_ d
                          · exact f404desc3
                          · intro d
                            refine Fin.cases ?_ ?_ d
                            · exact f405desc2
                            · intro d
                              refine Fin.cases ?_ ?_ d
                              · exact f406desc1
                              · intro d
                                refine Fin.cases ?_ ?_ d
                                · exact f407desc0
                                · intro d
                                  exact Fin.elim0 d
                · intro D
                  refine Fin.cases ?_ ?_ D
                  · intro d
                    refine Fin.cases ?_ ?_ d
                    · exact f400desc8
                    · intro d
                      refine Fin.cases ?_ ?_ d
                      · exact f401desc7
                      · intro d
                        refine Fin.cases ?_ ?_ d
                        · exact f402desc6
                        · intro d
                          refine Fin.cases ?_ ?_ d
                          · exact f403desc5
                          · intro d
                            refine Fin.cases ?_ ?_ d
                            · exact f404desc4
                            · intro d
                              refine Fin.cases ?_ ?_ d
                              · exact f405desc3
                              · intro d
                                refine Fin.cases ?_ ?_ d
                                · exact f406desc2
                                · intro d
                                  refine Fin.cases ?_ ?_ d
                                  · exact f407desc1
                                  · intro d
                                    refine Fin.cases ?_ ?_ d
                                    · exact f408desc0
                                    · intro d
                                      exact Fin.elim0 d
                  · intro D
                    refine Fin.cases ?_ ?_ D
                    · intro d
                      refine Fin.cases ?_ ?_ d
                      · exact f400desc9
                      · intro d
                        refine Fin.cases ?_ ?_ d
                        · exact f401desc8
                        · intro d
                          refine Fin.cases ?_ ?_ d
                          · exact f402desc7
                          · intro d
                            refine Fin.cases ?_ ?_ d
                            · exact f403desc6
                            · intro d
                              refine Fin.cases ?_ ?_ d
                              · exact f404desc5
                              · intro d
                                refine Fin.cases ?_ ?_ d
                                · exact f405desc4
                                · intro d
                                  refine Fin.cases ?_ ?_ d
                                  · exact f406desc3
                                  · intro d
                                    refine Fin.cases ?_ ?_ d
                                    · exact f407desc2
                                    · intro d
                                      refine Fin.cases ?_ ?_ d
                                      · exact f408desc1
                                      · intro d
                                        refine Fin.cases ?_ ?_ d
                                        · exact f409desc0
                                        · intro d
                                          exact Fin.elim0 d
                    · intro D
                      refine Fin.cases ?_ ?_ D
                      · intro d
                        refine Fin.cases ?_ ?_ d
                        · exact f400desc10
                        · intro d
                          refine Fin.cases ?_ ?_ d
                          · exact f401desc9
                          · intro d
                            refine Fin.cases ?_ ?_ d
                            · exact f402desc8
                            · intro d
                              refine Fin.cases ?_ ?_ d
                              · exact f403desc7
                              · intro d
                                refine Fin.cases ?_ ?_ d
                                · exact f404desc6
                                · intro d
                                  refine Fin.cases ?_ ?_ d
                                  · exact f405desc5
                                  · intro d
                                    refine Fin.cases ?_ ?_ d
                                    · exact f406desc4
                                    · intro d
                                      refine Fin.cases ?_ ?_ d
                                      · exact f407desc3
                                      · intro d
                                        refine Fin.cases ?_ ?_ d
                                        · exact f408desc2
                                        · intro d
                                          refine Fin.cases ?_ ?_ d
                                          · exact f409desc1
                                          · intro d
                                            refine Fin.cases ?_ ?_ d
                                            · exact f410desc0
                                            · intro d
                                              exact Fin.elim0 d
                      · intro D
                        refine Fin.cases ?_ ?_ D
                        · intro d
                          refine Fin.cases ?_ ?_ d
                          · exact f400desc11
                          · intro d
                            refine Fin.cases ?_ ?_ d
                            · exact f401desc10
                            · intro d
                              refine Fin.cases ?_ ?_ d
                              · exact f402desc9
                              · intro d
                                refine Fin.cases ?_ ?_ d
                                · exact f403desc8
                                · intro d
                                  refine Fin.cases ?_ ?_ d
                                  · exact f404desc7
                                  · intro d
                                    refine Fin.cases ?_ ?_ d
                                    · exact f405desc6
                                    · intro d
                                      refine Fin.cases ?_ ?_ d
                                      · exact f406desc5
                                      · intro d
                                        refine Fin.cases ?_ ?_ d
                                        · exact f407desc4
                                        · intro d
                                          refine Fin.cases ?_ ?_ d
                                          · exact f408desc3
                                          · intro d
                                            refine Fin.cases ?_ ?_ d
                                            · exact f409desc2
                                            · intro d
                                              refine Fin.cases ?_ ?_ d
                                              · exact f410desc1
                                              · intro d
                                                refine Fin.cases ?_ ?_ d
                                                · exact f411desc0
                                                · intro d
                                                  exact Fin.elim0 d
                        · intro D
                          refine Fin.cases ?_ ?_ D
                          · intro d
                            refine Fin.cases ?_ ?_ d
                            · exact f400desc12
                            · intro d
                              refine Fin.cases ?_ ?_ d
                              · exact f401desc11
                              · intro d
                                refine Fin.cases ?_ ?_ d
                                · exact f402desc10
                                · intro d
                                  refine Fin.cases ?_ ?_ d
                                  · exact f403desc9
                                  · intro d
                                    refine Fin.cases ?_ ?_ d
                                    · exact f404desc8
                                    · intro d
                                      refine Fin.cases ?_ ?_ d
                                      · exact f405desc7
                                      · intro d
                                        refine Fin.cases ?_ ?_ d
                                        · exact f406desc6
                                        · intro d
                                          refine Fin.cases ?_ ?_ d
                                          · exact f407desc5
                                          · intro d
                                            refine Fin.cases ?_ ?_ d
                                            · exact f408desc4
                                            · intro d
                                              refine Fin.cases ?_ ?_ d
                                              · exact f409desc3
                                              · intro d
                                                refine Fin.cases ?_ ?_ d
                                                · exact f410desc2
                                                · intro d
                                                  refine Fin.cases ?_ ?_ d
                                                  · exact f411desc1
                                                  · intro d
                                                    refine Fin.cases ?_ ?_ d
                                                    · exact f412desc0
                                                    · intro d
                                                      exact Fin.elim0 d
                          · intro D
                            refine Fin.cases ?_ ?_ D
                            · intro d
                              refine Fin.cases ?_ ?_ d
                              · exact f400desc13
                              · intro d
                                refine Fin.cases ?_ ?_ d
                                · exact f401desc12
                                · intro d
                                  refine Fin.cases ?_ ?_ d
                                  · exact f402desc11
                                  · intro d
                                    refine Fin.cases ?_ ?_ d
                                    · exact f403desc10
                                    · intro d
                                      refine Fin.cases ?_ ?_ d
                                      · exact f404desc9
                                      · intro d
                                        refine Fin.cases ?_ ?_ d
                                        · exact f405desc8
                                        · intro d
                                          refine Fin.cases ?_ ?_ d
                                          · exact f406desc7
                                          · intro d
                                            refine Fin.cases ?_ ?_ d
                                            · exact f407desc6
                                            · intro d
                                              refine Fin.cases ?_ ?_ d
                                              · exact f408desc5
                                              · intro d
                                                refine Fin.cases ?_ ?_ d
                                                · exact f409desc4
                                                · intro d
                                                  refine Fin.cases ?_ ?_ d
                                                  · exact f410desc3
                                                  · intro d
                                                    refine Fin.cases ?_ ?_ d
                                                    · exact f411desc2
                                                    · intro d
                                                      refine Fin.cases ?_ ?_ d
                                                      · exact f412desc1
                                                      · intro d
                                                        refine Fin.cases ?_ ?_ d
                                                        · exact f413desc0
                                                        · intro d
                                                          exact Fin.elim0 d
                            · intro D
                              refine Fin.cases ?_ ?_ D
                              · intro d
                                refine Fin.cases ?_ ?_ d
                                · exact f400desc14
                                · intro d
                                  refine Fin.cases ?_ ?_ d
                                  · exact f401desc13
                                  · intro d
                                    refine Fin.cases ?_ ?_ d
                                    · exact f402desc12
                                    · intro d
                                      refine Fin.cases ?_ ?_ d
                                      · exact f403desc11
                                      · intro d
                                        refine Fin.cases ?_ ?_ d
                                        · exact f404desc10
                                        · intro d
                                          refine Fin.cases ?_ ?_ d
                                          · exact f405desc9
                                          · intro d
                                            refine Fin.cases ?_ ?_ d
                                            · exact f406desc8
                                            · intro d
                                              refine Fin.cases ?_ ?_ d
                                              · exact f407desc7
                                              · intro d
                                                refine Fin.cases ?_ ?_ d
                                                · exact f408desc6
                                                · intro d
                                                  refine Fin.cases ?_ ?_ d
                                                  · exact f409desc5
                                                  · intro d
                                                    refine Fin.cases ?_ ?_ d
                                                    · exact f410desc4
                                                    · intro d
                                                      refine Fin.cases ?_ ?_ d
                                                      · exact f411desc3
                                                      · intro d
                                                        refine Fin.cases ?_ ?_ d
                                                        · exact f412desc2
                                                        · intro d
                                                          refine Fin.cases ?_ ?_ d
                                                          · exact f413desc1
                                                          · intro d
                                                            refine Fin.cases ?_ ?_ d
                                                            · exact f414desc0
                                                            · intro d
                                                              exact Fin.elim0 d
                              · intro D
                                refine Fin.cases ?_ ?_ D
                                · intro d
                                  refine Fin.cases ?_ ?_ d
                                  · exact f400desc15
                                  · intro d
                                    refine Fin.cases ?_ ?_ d
                                    · exact f401desc14
                                    · intro d
                                      refine Fin.cases ?_ ?_ d
                                      · exact f402desc13
                                      · intro d
                                        refine Fin.cases ?_ ?_ d
                                        · exact f403desc12
                                        · intro d
                                          refine Fin.cases ?_ ?_ d
                                          · exact f404desc11
                                          · intro d
                                            refine Fin.cases ?_ ?_ d
                                            · exact f405desc10
                                            · intro d
                                              refine Fin.cases ?_ ?_ d
                                              · exact f406desc9
                                              · intro d
                                                refine Fin.cases ?_ ?_ d
                                                · exact f407desc8
                                                · intro d
                                                  refine Fin.cases ?_ ?_ d
                                                  · exact f408desc7
                                                  · intro d
                                                    refine Fin.cases ?_ ?_ d
                                                    · exact f409desc6
                                                    · intro d
                                                      refine Fin.cases ?_ ?_ d
                                                      · exact f410desc5
                                                      · intro d
                                                        refine Fin.cases ?_ ?_ d
                                                        · exact f411desc4
                                                        · intro d
                                                          refine Fin.cases ?_ ?_ d
                                                          · exact f412desc3
                                                          · intro d
                                                            refine Fin.cases ?_ ?_ d
                                                            · exact f413desc2
                                                            · intro d
                                                              refine Fin.cases ?_ ?_ d
                                                              · exact f414desc1
                                                              · intro d
                                                                refine Fin.cases ?_ ?_ d
                                                                · exact f415desc0
                                                                · intro d
                                                                  exact Fin.elim0 d
                                · intro D
                                  refine Fin.cases ?_ ?_ D
                                  · intro d
                                    refine Fin.cases ?_ ?_ d
                                    · exact f400desc16
                                    · intro d
                                      refine Fin.cases ?_ ?_ d
                                      · exact f401desc15
                                      · intro d
                                        refine Fin.cases ?_ ?_ d
                                        · exact f402desc14
                                        · intro d
                                          refine Fin.cases ?_ ?_ d
                                          · exact f403desc13
                                          · intro d
                                            refine Fin.cases ?_ ?_ d
                                            · exact f404desc12
                                            · intro d
                                              refine Fin.cases ?_ ?_ d
                                              · exact f405desc11
                                              · intro d
                                                refine Fin.cases ?_ ?_ d
                                                · exact f406desc10
                                                · intro d
                                                  refine Fin.cases ?_ ?_ d
                                                  · exact f407desc9
                                                  · intro d
                                                    refine Fin.cases ?_ ?_ d
                                                    · exact f408desc8
                                                    · intro d
                                                      refine Fin.cases ?_ ?_ d
                                                      · exact f409desc7
                                                      · intro d
                                                        refine Fin.cases ?_ ?_ d
                                                        · exact f410desc6
                                                        · intro d
                                                          refine Fin.cases ?_ ?_ d
                                                          · exact f411desc5
                                                          · intro d
                                                            refine Fin.cases ?_ ?_ d
                                                            · exact f412desc4
                                                            · intro d
                                                              refine Fin.cases ?_ ?_ d
                                                              · exact f413desc3
                                                              · intro d
                                                                refine Fin.cases ?_ ?_ d
                                                                · exact f414desc2
                                                                · intro d
                                                                  refine Fin.cases ?_ ?_ d
                                                                  · exact f415desc1
                                                                  · intro d
                                                                    refine Fin.cases ?_ ?_ d
                                                                    · exact f416desc0
                                                                    · intro d
                                                                      exact Fin.elim0 d
                                  · intro D
                                    exact Fin.elim0 D

end TorusLean.BosonFiniteCertificate
