import torus.shared.FermionLocalJetFourCouplingWordNormalization
import torus.shared.FermionCertificateThreePolynomial
import Mathlib.Algebra.BigOperators.Fin

/-! A directly executable binomial convolution for the ORIGINAL polynomial
coefficient. The target U formula remains untouched in integerSlaterNumerator;
finite list equality will compare both independent definitions. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open scoped BigOperators
namespace SlaterListCandidate

def coefficientList (z T p : ℕ) : ℤ :=
  ((List.finRange (z+1)).map (fun h =>
    if h.val≤p ∧ p-h.val≤T-z then
      (-1 : ℤ)^(z-h.val) * (z.choose h.val : ℤ) * ((T-z).choose (p-h.val) : ℤ)
    else 0)).sum

theorem coefficientList_sum (z T p : ℕ) :
    coefficientList z T p =
      ∑ h ∈ Finset.range (z+1), if h≤p ∧ p-h≤T-z then
        (-1 : ℤ)^(z-h) * (z.choose h : ℤ) * ((T-z).choose (p-h) : ℤ)
      else 0 := by
  rw [Finset.sum_range,Fin.sum_univ_def]
  rfl

/-- Exact equality over Z, obtained from a proved coefficient expansion and
the injective characteristic-zero cast. No numerical equality is assumed. -/
theorem integerS45Coefficient_eq_list (z T p : ℕ) (hz : z≤T) (hp : p≤T) :
    integerS45Coefficient z T p=coefficientList z T p := by
  apply Int.cast_injective (α := ℂ)
  rw [integerS45Coefficient_cast,coefficientList_sum]
  have hc := ThreeCoupling.twoLinearPowers_coeff (1 : ℂ) (-1) 1 1
    z (T-z) p (T-p) (by omega)
  simp only [one_smul,neg_one_smul,← sub_eq_add_neg,one_pow,mul_one] at hc
  rw [hc]
  push_cast
  apply Finset.sum_congr rfl
  intro h hh
  split_ifs <;> ring

def pairCoefficientList (D T r p j k a : ℕ) : ℤ :=
  if a<p+1-a ∧ r≤j+k then
    coefficientList r (j+k) j * coefficientList (D-r) (T-r) p *
      ((a : ℤ)-((p+1-a : ℕ) : ℤ)) *
      (p.factorial : ℤ) * (j.factorial : ℤ) * (k.factorial : ℤ)
  else 0

theorem integerPairSpectatorCoefficient_eq_list (D T r p j k a : ℕ)
    (hrD : r≤D) (hDT : D≤T) (hT : p+j+k=T) :
    integerPairSpectatorCoefficient D T r p j k a=pairCoefficientList D T r p j k a := by
  unfold integerPairSpectatorCoefficient pairCoefficientList
  split_ifs with h
  · rw [integerS45Coefficient_eq_list r (j+k) j h.2 (by omega),
      integerS45Coefficient_eq_list (D-r) (T-r) p (by omega) (by omega)]
  · rfl

end SlaterListCandidate
end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.coefficientList_sum
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.integerS45Coefficient_eq_list
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.integerPairSpectatorCoefficient_eq_list
