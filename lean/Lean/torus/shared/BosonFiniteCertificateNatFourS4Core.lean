import torus.shared.BosonFiniteCertificateNatFourWords
import torus.shared.BosonFiniteCertificateNatPairHamiltonianAdjoint

/-! The independent genuine double-pair four-body source on Nat orbitals.
Each pair is the original differential pair with its genuine adjoint creator.
The coefficient is the product of the two planar pair weights, including both
factors 1/2. No finite certificate matrix occurs in these definitions. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation

def natFourPairWeight (p q : ℕ) : ℚ :=
  ((p.factorial : ℚ)/2^(p+1))*((q.factorial : ℚ)/2^(q+1))

theorem natFourPairWeight_normalization (p q : ℕ) :
    natFourPairWeight p q = (p.factorial : ℚ)*q.factorial/2^(p+q+2) := by
  unfold natFourPairWeight
  rw [div_mul_div_comm,← pow_add]
  congr 2
  omega

def canonicalNatFourDoublePair (p q : ℕ) : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ :=
  (canonicalPairNat q).comp (canonicalPairNat p)

def canonicalNatFourDoubleCreator (p q : ℕ) : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ :=
  (canonicalPairCreatorNat p).comp (canonicalPairCreatorNat q)

theorem canonicalNatFourDoubleCreator_adjoint (p q : ℕ) (f g : Core ℕ ℂ) :
    natOccupationInner (canonicalNatFourDoubleCreator p q f) g =
      natOccupationInner f (canonicalNatFourDoublePair p q g) := by
  simp only [canonicalNatFourDoubleCreator,canonicalNatFourDoublePair,LinearMap.comp_apply,
    canonicalPairCreatorNat_adjoint]

theorem canonicalNatFourDoubleCreator_right_adjoint (p q : ℕ) (f g : Core ℕ ℂ) :
    natOccupationInner f (canonicalNatFourDoubleCreator p q g) =
      natOccupationInner (canonicalNatFourDoublePair p q f) g := by
  have h := congrArg star (canonicalNatFourDoubleCreator_adjoint p q g f)
  simpa only [natOccupationInner_conj_symm] using h

/-- Every ordered pair of pair degrees with total at most D, once each. -/
def natFourPairSlots (D : ℕ) : List (ℕ × ℕ) :=
  (List.range (D+1)).flatMap fun d => (List.range (d+1)).map fun p => (p,d-p)

def canonicalNatFourS4Cutoff (D : ℕ) : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ :=
  ((natFourPairSlots D).map fun pq => (natFourPairWeight pq.1 pq.2 : ℂ) •
    (canonicalNatFourDoubleCreator pq.1 pq.2).comp
      (canonicalNatFourDoublePair pq.1 pq.2)).sum

/-- Cross-form of the actual independently defined double-pair operator. -/
theorem canonicalNatFourS4Cutoff_form (D : ℕ) (f g : Core ℕ ℂ) :
    natOccupationInner f (canonicalNatFourS4Cutoff D g) =
      ((natFourPairSlots D).map fun pq => (natFourPairWeight pq.1 pq.2 : ℂ) *
        natOccupationInner (canonicalNatFourDoublePair pq.1 pq.2 f)
          (canonicalNatFourDoublePair pq.1 pq.2 g)).sum := by
  simp only [canonicalNatFourS4Cutoff,nat_linear_list_sum_apply,
    natOccupationInner_list_sum_right]
  apply congrArg List.sum
  apply List.map_congr_left
  intro pq hpq
  simp only [LinearMap.smul_apply,LinearMap.comp_apply,natOccupationInner_smul_right,
    canonicalNatFourDoubleCreator_right_adjoint]

/-- The full source uses each monomial's actual degree, not a matrix truncation.
Cutoff stability is a further theorem; the weighted restriction below follows
from this true finite-support linear construction. -/
def canonicalNatFourS4 : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ :=
  (Finsupp.lsum ℂ (fun n : ℕ →₀ ℕ =>
    (canonicalNatFourS4Cutoff (Finsupp.weight id n)).comp (MvPolynomial.monomial n))).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

theorem canonicalNatFourS4_monomial (n : ℕ →₀ ℕ) (c : ℂ) :
    canonicalNatFourS4 (MvPolynomial.monomial n c) =
      canonicalNatFourS4Cutoff (Finsupp.weight id n) (MvPolynomial.monomial n c) := by
  change (Finsupp.lsum ℂ (fun m : ℕ →₀ ℕ =>
    (canonicalNatFourS4Cutoff (Finsupp.weight id m)).comp (MvPolynomial.monomial m)))
      (Finsupp.single n c) = _
  rw [Finsupp.lsum_single]
  rfl

theorem canonicalNatFourS4_eq_cutoff_weighted (d : ℕ) (f : Core ℕ ℂ)
    (hd : f.IsWeightedHomogeneous id d) :
    canonicalNatFourS4 f=canonicalNatFourS4Cutoff d f := by
  rw [← MvPolynomial.support_sum_monomial_coeff f]
  rw [map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [canonicalNatFourS4_monomial,hd (MvPolynomial.mem_support_iff.mp hn)]

#print axioms natFourPairWeight_normalization
#print axioms canonicalNatFourDoubleCreator_adjoint
#print axioms canonicalNatFourDoubleCreator_right_adjoint
#print axioms canonicalNatFourS4Cutoff_form
#print axioms canonicalNatFourS4_monomial
#print axioms canonicalNatFourS4_eq_cutoff_weighted
end TorusLean.BosonFiniteCertificate
