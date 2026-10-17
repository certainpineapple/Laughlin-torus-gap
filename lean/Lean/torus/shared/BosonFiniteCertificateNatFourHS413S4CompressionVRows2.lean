import torus.shared.BosonFiniteCertificateNatFourHS413S4CompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f413_S4Compression_hV_rows_2 (a : Fin 5) (hlo : 4 ≤ a.val) (hhi : a.val < 5) (b : Fin 39) :
    (f413S4CompressionCoordinatesᵀ*f413S4CompressionInteger) a b=(f413S4CompressionLeftProduct) a b := by
  fin_cases a
  · change 4 ≤ (0 : ℕ) at hlo
    omega
  · change 4 ≤ (1 : ℕ) at hlo
    omega
  · change 4 ≤ (2 : ℕ) at hlo
    omega
  · change 4 ≤ (3 : ℕ) at hlo
    omega
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (f413S4CompressionCoordinatesᵀ*f413S4CompressionInteger) 4 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413S4CompressionLeftProduct) 4 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b

#print axioms f413_S4Compression_hV_rows_2
end TorusLean.BosonFiniteCertificate
