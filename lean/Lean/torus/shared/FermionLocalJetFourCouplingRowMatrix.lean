import torus.shared.FermionLocalJetFourCouplingWedge
import torus.shared.FermionLocalJetRows

/-! The literal ordered seven-row coefficient matrix E_D from equation F-E.
The degree is computed from the original row support before any coupling.
This file proves the real symmetry of that exact matrix; it does not assert
positivity on the copy space or replace the physical Gram-sandwiched certificate. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open scoped BigOperators ComplexConjugate

/-- Original T=p+j+k with k=q+l-t_rho. The two row entries remain ordered. -/
def certificateFourTotal (rho : CertificateRow) (a b : CertificateEntry rho) : ℕ :=
  (certificateEntryData rho a).1 + (certificateEntryData rho a).2.1 +
    certificateJetIndex rho b

theorem certificateFourTotal_exchange (rho : CertificateRow) (a b : CertificateEntry rho) :
    certificateFourTotal rho a b = certificateFourTotal rho b a := by
  have ha := (certificate_row_support rho a).2.2.1
  have hb := (certificate_row_support rho b).2.2.1
  unfold certificateFourTotal certificateJetIndex
  omega

/-- The original support gives T<=7+8+8=23 without dropping a row entry. -/
theorem certificateFourTotal_le (rho : CertificateRow) (a b : CertificateEntry rho) :
    certificateFourTotal rho a b ≤ 23 := by
  have ha := certificate_row_support rho a
  have hb := certificate_row_support rho b
  unfold certificateFourTotal
  omega

theorem paperS45_star (r D T p j k : ℕ) :
    star (paperS45 r D T p j k) = paperS45 r D T p j k := by
  unfold paperS45
  split_ifs
  · simp only [star_mul,s45_star,Complex.star_def,Complex.conj_ofReal]
    ring
  · exact star_zero _

/-- Genuine antisymmetric extension in the spectator indices, including
diagonal and all out-of-range coefficients of the original polynomial. -/
theorem paperS45_exchange_odd (r D T p j k : ℕ) (hr : Odd r) :
    paperS45 r D T p k j = -paperS45 r D T p j k := by
  have ht : p+k+j=T ↔ p+j+k=T := by omega
  unfold paperS45
  simp only [ht,show k+j=j+k by omega]
  split_ifs
  · by_cases hrn : r≤j+k
    · have he := s45_reflection r (j+k) j hrn (by omega)
      have hk : j+k-j=k := by omega
      rw [hk,hr.neg_one_pow] at he
      rw [he]
      ring
    · have he : j+k<r := by omega
      rw [s45_outside r (j+k) k (Or.inl he),s45_outside r (j+k) j (Or.inl he)]
      simp
  · simp

/-- Literal F-E. The explicit T>=D restriction and both signed S factors
are retained; no coefficient is read from a precomputed matrix table. -/
def certificateFourMatrix (D r s : ℕ) : ℂ :=
  -(∑ rho : CertificateRow, ∑ a : CertificateEntry rho, ∑ b : CertificateEntry rho,
    if D≤certificateFourTotal rho a b then
      (certificateAlpha rho a : ℂ) * (certificateAlpha rho b : ℂ) *
        paperS45 r D (certificateFourTotal rho a b)
          (certificateEntryData rho a).1 (certificateEntryData rho a).2.1 (certificateJetIndex rho b) *
        paperS45 s D (certificateFourTotal rho a b)
          (certificateEntryData rho b).1 (certificateEntryData rho b).2.1 (certificateJetIndex rho a)
    else 0)

/-- Exchanging the original ordered entry pair proves real symmetry. -/
theorem certificateFourMatrix_symmetric (D r s : ℕ) :
    certificateFourMatrix D r s = certificateFourMatrix D s r := by
  unfold certificateFourMatrix
  apply congrArg (fun z : ℂ => -z)
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [certificateFourTotal_exchange rho b a]
  split_ifs <;> ring

theorem certificateFourMatrix_star (D r s : ℕ) :
    star (certificateFourMatrix D r s) = certificateFourMatrix D r s := by
  simp only [certificateFourMatrix,star_neg,star_sum]
  apply congrArg (fun z : ℂ => -z)
  apply Finset.sum_congr rfl
  intro rho hrho
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs
  · simp only [star_mul,paperS45_star,Complex.star_def,Complex.conj_ofReal]
    ring
  · exact star_zero _

/-- Hermitian orientation for the later physical quadratic-form transfer. -/
theorem certificateFourMatrix_hermitian (D r s : ℕ) :
    star (certificateFourMatrix D s r) = certificateFourMatrix D r s := by
  rw [certificateFourMatrix_star,certificateFourMatrix_symmetric]

#print axioms certificateFourTotal_exchange
#print axioms certificateFourTotal_le
#print axioms paperS45_star
#print axioms paperS45_exchange_odd
#print axioms certificateFourMatrix_symmetric
#print axioms certificateFourMatrix_star
#print axioms certificateFourMatrix_hermitian
end TorusLean.Shared.FermionLocalJet.FourCoupling
