import torus.shared.BosonFiniteCertificateNatFourHS413HCompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f413_HCompression_hV_rows_0 (a : Fin 5) (hlo : 0 ≤ a.val) (hhi : a.val < 2) (b : Fin 39) :
    (f413HCompressionCoordinatesᵀ*f413HCompressionInteger) a b=(f413HCompressionLeftProduct) a b := by
  fin_cases a
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (f413HCompressionCoordinatesᵀ*f413HCompressionInteger) 0 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413HCompressionLeftProduct) 0 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (f413HCompressionCoordinatesᵀ*f413HCompressionInteger) 1 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413HCompressionLeftProduct) 1 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · change (2 : ℕ) < 2 at hhi
    omega
  · change (3 : ℕ) < 2 at hhi
    omega
  · change (4 : ℕ) < 2 at hhi
    omega

#print axioms f413_HCompression_hV_rows_0
end TorusLean.BosonFiniteCertificate
