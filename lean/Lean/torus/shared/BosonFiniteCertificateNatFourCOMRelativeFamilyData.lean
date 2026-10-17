import torus.shared.BosonFiniteCertificateNatFourRelativeGram400
import torus.shared.BosonFiniteCertificateNatFourRelative400
import torus.shared.BosonFiniteCertificateNatFourRelativeGram401
import torus.shared.BosonFiniteCertificateNatFourRelative401
import torus.shared.BosonFiniteCertificateNatFourRelativeGram402
import torus.shared.BosonFiniteCertificateNatFourRelative402
import torus.shared.BosonFiniteCertificateNatFourRelativeGram403
import torus.shared.BosonFiniteCertificateNatFourRelative403
import torus.shared.BosonFiniteCertificateNatFourRelativeGram404
import torus.shared.BosonFiniteCertificateNatFourRelative404
import torus.shared.BosonFiniteCertificateNatFourRelativeGram405
import torus.shared.BosonFiniteCertificateNatFourRelative405
import torus.shared.BosonFiniteCertificateNatFourRelativeGram406
import torus.shared.BosonFiniteCertificateNatFourRelative406
import torus.shared.BosonFiniteCertificateNatFourRelativeGram407
import torus.shared.BosonFiniteCertificateNatFourRelative407
import torus.shared.BosonFiniteCertificateNatFourRelativeGram408
import torus.shared.BosonFiniteCertificateNatFourRelative408
import torus.shared.BosonFiniteCertificateNatFourRelativeGram409
import torus.shared.BosonFiniteCertificateNatFourRelative409
import torus.shared.BosonFiniteCertificateNatFourRelativeGram410
import torus.shared.BosonFiniteCertificateNatFourRelative410
import torus.shared.BosonFiniteCertificateNatFourRelativeGram411
import torus.shared.BosonFiniteCertificateNatFourRelative411
import torus.shared.BosonFiniteCertificateNatFourRelativeGram412
import torus.shared.BosonFiniteCertificateNatFourRelative412
import torus.shared.BosonFiniteCertificateNatFourRelativeGram413
import torus.shared.BosonFiniteCertificateNatFourRelative413
import torus.shared.BosonFiniteCertificateNatFourRelativeGram414
import torus.shared.BosonFiniteCertificateNatFourRelative414
import torus.shared.BosonFiniteCertificateNatFourRelativeGram415
import torus.shared.BosonFiniteCertificateNatFourRelative415
import torus.shared.BosonFiniteCertificateNatFourRelativeGram416
import torus.shared.BosonFiniteCertificateNatFourRelative416
import torus.shared.BosonFiniteCertificateNatFourBasisHomogeneous

/-! The original seventeen relative families, preserving the empty degree-one
fiber. All family properties are consequences of the genuine Nat word/lowering
actions and the separately verified original relative matrices. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

def natFourRelativeDimension : Fin 17 → ℕ := ![1,0,1,1,2,1,3,2,4,3,5,4,7,5,8,7,10]

#check natFourRelativeDimension

def natFourRelativeColumn (d : Fin 17) : Fin (natFourRelativeDimension d) → Core ℕ ℂ := by
  refine Fin.cases ?_ ?_ d
  · exact f400relativeFamily
  · intro d
    refine Fin.cases ?_ ?_ d
    · exact f401relativeFamily
    · intro d
      refine Fin.cases ?_ ?_ d
      · exact f402relativeFamily
      · intro d
        refine Fin.cases ?_ ?_ d
        · exact f403relativeFamily
        · intro d
          refine Fin.cases ?_ ?_ d
          · exact f404relativeFamily
          · intro d
            refine Fin.cases ?_ ?_ d
            · exact f405relativeFamily
            · intro d
              refine Fin.cases ?_ ?_ d
              · exact f406relativeFamily
              · intro d
                refine Fin.cases ?_ ?_ d
                · exact f407relativeFamily
                · intro d
                  refine Fin.cases ?_ ?_ d
                  · exact f408relativeFamily
                  · intro d
                    refine Fin.cases ?_ ?_ d
                    · exact f409relativeFamily
                    · intro d
                      refine Fin.cases ?_ ?_ d
                      · exact f410relativeFamily
                      · intro d
                        refine Fin.cases ?_ ?_ d
                        · exact f411relativeFamily
                        · intro d
                          refine Fin.cases ?_ ?_ d
                          · exact f412relativeFamily
                          · intro d
                            refine Fin.cases ?_ ?_ d
                            · exact f413relativeFamily
                            · intro d
                              refine Fin.cases ?_ ?_ d
                              · exact f414relativeFamily
                              · intro d
                                refine Fin.cases ?_ ?_ d
                                · exact f415relativeFamily
                                · intro d
                                  refine Fin.cases ?_ ?_ d
                                  · exact f416relativeFamily
                                  · intro d
                                    exact Fin.elim0 d

#check natFourRelativeColumn

def natFourRelativeGram (d : Fin 17) : Matrix (Fin (natFourRelativeDimension d)) (Fin (natFourRelativeDimension d)) ℚ := by
  refine Fin.cases ?_ ?_ d
  · exact f400relativeGram
  · intro d
    refine Fin.cases ?_ ?_ d
    · exact f401relativeGram
    · intro d
      refine Fin.cases ?_ ?_ d
      · exact f402relativeGram
      · intro d
        refine Fin.cases ?_ ?_ d
        · exact f403relativeGram
        · intro d
          refine Fin.cases ?_ ?_ d
          · exact f404relativeGram
          · intro d
            refine Fin.cases ?_ ?_ d
            · exact f405relativeGram
            · intro d
              refine Fin.cases ?_ ?_ d
              · exact f406relativeGram
              · intro d
                refine Fin.cases ?_ ?_ d
                · exact f407relativeGram
                · intro d
                  refine Fin.cases ?_ ?_ d
                  · exact f408relativeGram
                  · intro d
                    refine Fin.cases ?_ ?_ d
                    · exact f409relativeGram
                    · intro d
                      refine Fin.cases ?_ ?_ d
                      · exact f410relativeGram
                      · intro d
                        refine Fin.cases ?_ ?_ d
                        · exact f411relativeGram
                        · intro d
                          refine Fin.cases ?_ ?_ d
                          · exact f412relativeGram
                          · intro d
                            refine Fin.cases ?_ ?_ d
                            · exact f413relativeGram
                            · intro d
                              refine Fin.cases ?_ ?_ d
                              · exact f414relativeGram
                              · intro d
                                refine Fin.cases ?_ ?_ d
                                · exact f415relativeGram
                                · intro d
                                  refine Fin.cases ?_ ?_ d
                                  · exact f416relativeGram
                                  · intro d
                                    exact Fin.elim0 d

#check natFourRelativeGram

def natFourRelativeGramInverse (d : Fin 17) : Matrix (Fin (natFourRelativeDimension d)) (Fin (natFourRelativeDimension d)) ℚ := by
  refine Fin.cases ?_ ?_ d
  · exact f400relativeGramInverse
  · intro d
    refine Fin.cases ?_ ?_ d
    · exact f401relativeGramInverse
    · intro d
      refine Fin.cases ?_ ?_ d
      · exact f402relativeGramInverse
      · intro d
        refine Fin.cases ?_ ?_ d
        · exact f403relativeGramInverse
        · intro d
          refine Fin.cases ?_ ?_ d
          · exact f404relativeGramInverse
          · intro d
            refine Fin.cases ?_ ?_ d
            · exact f405relativeGramInverse
            · intro d
              refine Fin.cases ?_ ?_ d
              · exact f406relativeGramInverse
              · intro d
                refine Fin.cases ?_ ?_ d
                · exact f407relativeGramInverse
                · intro d
                  refine Fin.cases ?_ ?_ d
                  · exact f408relativeGramInverse
                  · intro d
                    refine Fin.cases ?_ ?_ d
                    · exact f409relativeGramInverse
                    · intro d
                      refine Fin.cases ?_ ?_ d
                      · exact f410relativeGramInverse
                      · intro d
                        refine Fin.cases ?_ ?_ d
                        · exact f411relativeGramInverse
                        · intro d
                          refine Fin.cases ?_ ?_ d
                          · exact f412relativeGramInverse
                          · intro d
                            refine Fin.cases ?_ ?_ d
                            · exact f413relativeGramInverse
                            · intro d
                              refine Fin.cases ?_ ?_ d
                              · exact f414relativeGramInverse
                              · intro d
                                refine Fin.cases ?_ ?_ d
                                · exact f415relativeGramInverse
                                · intro d
                                  refine Fin.cases ?_ ?_ d
                                  · exact f416relativeGramInverse
                                  · intro d
                                    exact Fin.elim0 d

#check natFourRelativeGramInverse

end TorusLean.BosonFiniteCertificate
