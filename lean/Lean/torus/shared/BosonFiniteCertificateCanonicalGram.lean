import torus.shared.BosonFiniteCertificateCore
import torus.shared.BosonFiniteCertificateRealization
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.M2
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.BosonThreeBodyLift
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open TorusLean.Shared.BosonFiniteCertificateRealization

theorem complexify_mul_rect {m n r : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (B : Matrix (Fin n) (Fin r) ℚ) : complexify (A * B) = complexify A * complexify B := by
  dsimp only [complexify]
  exact Matrix.map_mul

theorem complexify_transpose_rect {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    complexify Aᵀ = (complexify A)ᴴ := by
  ext i j
  simp [complexify, Matrix.conjTranspose_apply]

theorem complexify_diagonal_rat {n : ℕ} (d : Fin n → ℚ) :
    complexify (Matrix.diagonal d) = Matrix.diagonal (fun a => (d a : ℂ)) := by
  ext i j
  by_cases h : i=j <;> simp [complexify, Matrix.diagonal, h]

theorem complexify_one_rat {n : ℕ} : complexify (1 : Matrix (Fin n) (Fin n) ℚ) = 1 := by
  ext i j
  by_cases h : i=j <;> simp [complexify, Matrix.one_apply, h]

#print axioms complexify_mul_rect
#print axioms complexify_transpose_rect
#print axioms complexify_diagonal_rat
#print axioms complexify_one_rat
end TorusLean.BosonFiniteCertificate
