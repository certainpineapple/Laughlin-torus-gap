import torus.shared.BosonFiniteCertificateNatFourHS416HCompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f416_HCompression_hF_rows_0 (a : Fin 10) (hlo : 0 ≤ a.val) (hhi : a.val < 10) (b : Fin 10) :
    (natFourIntegerMatrix (180180*8*180180) f416HCompressionResult) a b=(b416h) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix (180180*8*180180) f416HCompressionResult) 0 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416h) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix (180180*8*180180) f416HCompressionResult) 1 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416h) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix (180180*8*180180) f416HCompressionResult) 2 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416h) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix (180180*8*180180) f416HCompressionResult) 3 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416h) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix (180180*8*180180) f416HCompressionResult) 4 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416h) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix (180180*8*180180) f416HCompressionResult) 5 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416h) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix (180180*8*180180) f416HCompressionResult) 6 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416h) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix (180180*8*180180) f416HCompressionResult) 7 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416h) 7 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix (180180*8*180180) f416HCompressionResult) 8 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416h) 8 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix (180180*8*180180) f416HCompressionResult) 9 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416h) 9 j) (by decide +kernel)
    exact h 0 b

#print axioms f416_HCompression_hF_rows_0
end TorusLean.BosonFiniteCertificate
