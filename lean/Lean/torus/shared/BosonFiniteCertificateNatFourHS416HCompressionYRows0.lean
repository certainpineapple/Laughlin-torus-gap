import torus.shared.BosonFiniteCertificateNatFourHS416HCompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f416_HCompression_hY_rows_0 (a : Fin 10) (hlo : 0 ≤ a.val) (hhi : a.val < 5) (b : Fin 10) :
    (f416HCompressionLeftProduct*f416HCompressionCoordinates) a b=(f416HCompressionResult) a b := by
  fin_cases a
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (f416HCompressionLeftProduct*f416HCompressionCoordinates) 0 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416HCompressionResult) 0 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (f416HCompressionLeftProduct*f416HCompressionCoordinates) 1 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416HCompressionResult) 1 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (f416HCompressionLeftProduct*f416HCompressionCoordinates) 2 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416HCompressionResult) 2 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (f416HCompressionLeftProduct*f416HCompressionCoordinates) 3 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416HCompressionResult) 3 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (f416HCompressionLeftProduct*f416HCompressionCoordinates) 4 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416HCompressionResult) 4 j) (by decide +kernel)
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

#print axioms f416_HCompression_hY_rows_0
end TorusLean.BosonFiniteCertificate
