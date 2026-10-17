import torus.shared.BosonFiniteCertificateNatFourRelativeGramCore
import torus.shared.BosonFiniteCertificateNatFourIntegerMatrix

/-! Common-denominator integer verification of the true diagonal occupation
Gram compression. Only arithmetic evaluation is factored; U, G, and F remain
independent inputs and the source Gram equality remains a proof obligation. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TorusLean.BosonFiniteCertificate
open Matrix
open scoped BigOperators

theorem natFour_integer_weighted_compression_check {n r : ℕ} (den : ℕ)
    (g : Fin n → ℕ) (W : Matrix (Fin n) (Fin r) ℤ)
    (Y : Matrix (Fin r) (Fin r) ℤ) (U : Matrix (Fin n) (Fin r) ℚ)
    (F : Matrix (Fin r) (Fin r) ℚ)
    (hU : natFourIntegerMatrix den W=U)
    (hY : ∀ i j, (∑ a, W a i*(g a : ℤ)*W a j)=Y i j)
    (hF : natFourIntegerMatrix (den*den) Y=F) :
    Uᵀ*Matrix.diagonal (fun a => (g a : ℚ))*U=F := by
  rw [←hU,←hF]
  ext i j
  rw [natFour_diagonal_compression_entry]
  simp only [natFourIntegerMatrix]
  rw [←hY i j]
  simp only [Int.cast_sum,Int.cast_mul,Int.cast_natCast,Nat.cast_mul]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [div_eq_mul_inv,mul_inv]
  ring

#print axioms natFour_integer_weighted_compression_check
end TorusLean.BosonFiniteCertificate
