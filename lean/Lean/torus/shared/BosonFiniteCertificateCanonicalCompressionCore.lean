import torus.shared.BosonFiniteCertificateCanonicalM3
import torus.shared.BosonFiniteCertificateCanonical
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix
open scoped BigOperators ComplexOrder
open TorusLean.M2
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.BosonThreeBodyLift
open TorusLean.Shared.BosonFiniteCertificateRealization

theorem complexify_smul_rat {m n : ℕ} (q : ℚ) (A : Matrix (Fin m) (Fin n) ℚ) :
    complexify (q • A) = (q : ℂ) • complexify A := by
  ext a b
  simp [complexify]

theorem complexify_sub_rect {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℚ) :
    complexify (A-B) = complexify A - complexify B := by
  ext a b
  simp [complexify]
end TorusLean.BosonFiniteCertificate
