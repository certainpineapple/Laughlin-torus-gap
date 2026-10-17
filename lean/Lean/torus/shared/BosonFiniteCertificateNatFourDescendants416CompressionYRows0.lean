import torus.shared.BosonFiniteCertificateNatFourDescendants416CompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f416_DescCompression_hY_rows_0 (a : Fin 10) (hlo : 0 ≤ a.val) (hhi : a.val < 5) (b : Fin 10) :
    (f416DescCompressionLeftProduct*f416DescCompressionCoordinates) a b=(f416DescCompressionResult) a b := by
  fin_cases a
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (f416DescCompressionLeftProduct*f416DescCompressionCoordinates) 0 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416DescCompressionResult) 0 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (f416DescCompressionLeftProduct*f416DescCompressionCoordinates) 1 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416DescCompressionResult) 1 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (f416DescCompressionLeftProduct*f416DescCompressionCoordinates) 2 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416DescCompressionResult) 2 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (f416DescCompressionLeftProduct*f416DescCompressionCoordinates) 3 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416DescCompressionResult) 3 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (f416DescCompressionLeftProduct*f416DescCompressionCoordinates) 4 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416DescCompressionResult) 4 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · change (5 : ℕ) < 5 at hhi
    omega
  · change (6 : ℕ) < 5 at hhi
    omega
  · change (7 : ℕ) < 5 at hhi
    omega
  · change (8 : ℕ) < 5 at hhi
    omega
  · change (9 : ℕ) < 5 at hhi
    omega

#print axioms f416_DescCompression_hY_rows_0
end TorusLean.BosonFiniteCertificate
