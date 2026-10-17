import torus.shared.FermionLocalJetFourCouplingIntegerCoefficients
import torus.shared.FermionLocalJetFourCouplingWordPresentation

/-! Source-level factorial normalization of the original full-T words.
After one common nonzero scalar, every original ordered word coefficient is
an integer. The integer coefficients remain the coefficients of the actual
rotation polynomials, not separately postulated certificate arrays. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.BosonFiniteCertificate
open TorusLean.Shared.ThermalCoherentFermionCOMWords
open TorusLean.Shared.FermionRelativeFrame
open scoped BigOperators

def factorialFourWord (a b j k : ℕ) : WordCoefficients 4 :=
  (factorialRootNat a * factorialRootNat b * factorialRootNat j * factorialRootNat k)⁻¹ •
    Finsupp.single ![a,b,j,k] 1

def fourSourceScale (D T r : ℕ) : ℂ :=
  (Real.sqrt (2:ℝ):ℂ) /
    (factorialRootNat r * factorialRootNat (D-r) * factorialRootNat (T-D) *
      (Real.sqrt (2:ℝ):ℂ)^(T+(T-r)))

def integerPairSpectatorCoefficient (D T r p j k a : ℕ) : ℤ :=
  if a<p+1-a ∧ r≤j+k then
    integerS45Coefficient r (j+k) j * integerS45Coefficient (D-r) (T-r) p *
      ((a:ℤ)-((p+1-a:ℕ):ℤ)) *
      (p.factorial:ℤ) * (j.factorial:ℤ) * (k.factorial:ℤ)
  else 0

def integerDescendantWords (D T r : ℕ) : WordCoefficients 4 :=
  ∑ q : HalfInputIndex T, ∑ a : Fin (q.val.1.val+2),
    (integerPairSpectatorCoefficient D T r q.val.1.val q.val.2.val
      (T-q.val.1.val-q.val.2.val) a.val : ℂ) •
    factorialFourWord a.val (q.val.1.val+1-a.val) q.val.2.val
      (T-q.val.1.val-q.val.2.val)

private theorem factorialRoot_square' (n : ℕ) :
    (factorialRootNat n)^2=(n.factorial:ℂ) := by
  unfold factorialRootNat
  exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg n.factorial)

theorem fourSourceScale_ne_zero (D T r : ℕ) : fourSourceScale D T r ≠ 0 := by
  have h2 : (Real.sqrt (2:ℝ):ℂ)≠0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<2)
  unfold fourSourceScale
  exact div_ne_zero h2 (mul_ne_zero
    (mul_ne_zero (mul_ne_zero (factorialRootNat_ne_zero r)
      (factorialRootNat_ne_zero (D-r))) (factorialRootNat_ne_zero (T-D)))
    (pow_ne_zero _ h2))

/-- One original signed pair/spectator coefficient, before any exterior
sorting. Equality holds in the free ordered-word space itself. -/
theorem pairSpectator_word_normalization (D T r p j k a : ℕ)
    (hrD : r≤D) (hDT : D≤T) (hT : p+j+k=T) (ha : a<p+2) :
    paperS45 r D T p j k •
      ((pairLeftCoefficient p a:ℂ) • Finsupp.single ![a,p+1-a,j,k] 1) =
    fourSourceScale D T r •
      ((integerPairSpectatorCoefficient D T r p j k a:ℂ) •
        factorialFourWord a (p+1-a) j k) := by
  classical
  by_cases hab : a<p+1-a
  · by_cases hrjk : r≤j+k
    · have ha' : a+(p+1-a)=p+1 := by omega
      have h2 : (Real.sqrt (2:ℝ):ℂ)≠0 := by
        exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<2)
      have hpow : p+(j+k+T-r)=T+(T-r) := by omega
      rw [paperS45_integer_roots r D T p j k hrD hDT hT hrjk]
      simp only [pairLeftCoefficient,hab,if_true,Complex.ofReal_mul,
        Complex.ofReal_sub,Complex.ofReal_natCast,
        paperPairWeight_factorial_roots,integerPairSpectatorCoefficient,hrjk,
        and_self,factorialFourWord,smul_smul,fourSourceScale]
      congr 1
      push_cast
      have hpw : (Real.sqrt (2:ℝ):ℂ)^p *
          (Real.sqrt (2:ℝ):ℂ)^(j+k+T-r) =
            (Real.sqrt (2:ℝ):ℂ)^(T+(T-r)) := by rw [← pow_add,hpow]
      rw [← hpw]
      field_simp [factorialRootNat_ne_zero,h2]
      ring_nf
      simp only [factorialRoot_square']
      ring
    · have hs : s45 r (j+k) j=0 := s45_outside r (j+k) j (Or.inl (by omega))
      simp [paperS45,hrD,hDT,hT,hs,integerPairSpectatorCoefficient,hrjk]
  · simp [pairLeftCoefficient,hab,integerPairSpectatorCoefficient]

/-- Entire independently defined original full-T source, with one common
factorial scale and every original ordered coefficient retained. -/
theorem descendantWords_integer_normalization (D T r : ℕ)
    (hrD : r≤D) (hDT : D≤T) :
    descendantWords D T r = fourSourceScale D T r • integerDescendantWords D T r := by
  classical
  simp only [descendantWords,fourInputWords,integerDescendantWords,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro a ha
  apply pairSpectator_word_normalization D T r q.val.1.val q.val.2.val
    (T-q.val.1.val-q.val.2.val) a.val hrD hDT
  · have hp := q.val.1.isLt
    have hj := q.val.2.isLt
    omega
  · exact a.isLt

#print axioms fourSourceScale_ne_zero
#print axioms pairSpectator_word_normalization
#print axioms descendantWords_integer_normalization
end TorusLean.Shared.FermionLocalJet.FourCoupling
