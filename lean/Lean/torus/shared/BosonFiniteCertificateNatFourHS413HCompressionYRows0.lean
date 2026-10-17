import torus.shared.BosonFiniteCertificateNatFourHS413HCompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f413_HCompression_hY_rows_0 (a : Fin 5) (hlo : 0 ≤ a.val) (hhi : a.val < 5) (b : Fin 5) :
    (f413HCompressionLeftProduct*f413HCompressionCoordinates) a b=(f413HCompressionResult) a b := by
  fin_cases a
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (f413HCompressionLeftProduct*f413HCompressionCoordinates) 0 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413HCompressionResult) 0 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (f413HCompressionLeftProduct*f413HCompressionCoordinates) 1 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413HCompressionResult) 1 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (f413HCompressionLeftProduct*f413HCompressionCoordinates) 2 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413HCompressionResult) 2 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (f413HCompressionLeftProduct*f413HCompressionCoordinates) 3 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413HCompressionResult) 3 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (f413HCompressionLeftProduct*f413HCompressionCoordinates) 4 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413HCompressionResult) 4 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b

#print axioms f413_HCompression_hY_rows_0
end TorusLean.BosonFiniteCertificate
