import torus.shared.BosonFiniteCertificateNatFourDescendants416CompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f416_DescCompression_hF_rows_0 (a : Fin 10) (hlo : 0 ≤ a.val) (hhi : a.val < 10) (b : Fin 10) :
    (natFourIntegerMatrix (180180*1000000000000000000000000*180180) f416DescCompressionResult) a b=(f416desc0Form) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix (180180*1000000000000000000000000*180180) f416DescCompressionResult) 0 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0Form) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix (180180*1000000000000000000000000*180180) f416DescCompressionResult) 1 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0Form) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix (180180*1000000000000000000000000*180180) f416DescCompressionResult) 2 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0Form) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix (180180*1000000000000000000000000*180180) f416DescCompressionResult) 3 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0Form) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix (180180*1000000000000000000000000*180180) f416DescCompressionResult) 4 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0Form) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix (180180*1000000000000000000000000*180180) f416DescCompressionResult) 5 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0Form) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix (180180*1000000000000000000000000*180180) f416DescCompressionResult) 6 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0Form) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix (180180*1000000000000000000000000*180180) f416DescCompressionResult) 7 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0Form) 7 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix (180180*1000000000000000000000000*180180) f416DescCompressionResult) 8 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0Form) 8 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix (180180*1000000000000000000000000*180180) f416DescCompressionResult) 9 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0Form) 9 j) (by decide +kernel)
    exact h 0 b

#print axioms f416_DescCompression_hF_rows_0
end TorusLean.BosonFiniteCertificate
