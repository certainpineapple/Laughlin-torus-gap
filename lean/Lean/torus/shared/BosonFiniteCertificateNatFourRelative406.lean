import torus.shared.BosonFiniteCertificateNatFourRelativeCore
import torus.shared.BosonFiniteCertificateNatFourBasis406
import torus.shared.BosonFiniteCertificate406
import torus.shared.BosonFiniteCertificateNatFourBasis405

/-! Degree-6 actual Nat COM lowering and complete relative kernel.
All basis actions are independently checked in rational polynomials before
transporting the frozen split witness to the real source operator. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open Matrix
open scoped BigOperators

theorem f406_rational_lower_check : ∀ a : Fin 9,
    natFourRationalLowerWord (f406basis a) =
      ∑ b : Fin 6, b406lower b a • (wordPolynomial (f405basis b) : Core ℕ ℚ) := by
  intro a
  fin_cases a <;>
    norm_num [natFourRationalLowerWord,natFourLoweredWords,f406basis,f405basis,
      b406lower,Fin.sum_univ_succ,wordPolynomial,Algebra.smul_def] <;> (try simp only [map_ofNat]) <;> ring

theorem f406_actual_lower_word (a : Fin 9) :
    canonicalCOMLowerNat (scaledWord factorialRootNat (f406basis a)) =
      ∑ b : Fin 6, (b406lower b a : ℂ) • scaledWord factorialRootNat (f405basis b) :=
  natFour_lower_action_of_rational_check (f406basis a) f405basis
    (fun b => b406lower b a) (f406_rational_lower_check a)

theorem f406_actual_lower_block (v : Fin 9 → ℂ) :
    canonicalCOMLowerNat (natFourWordBlock f406basis v) =
      natFourWordBlock f405basis (complexify b406lower *ᵥ v) :=
  natFourWordBlock_rect_action f406basis f405basis canonicalCOMLowerNat
    (complexify b406lower) f406_actual_lower_word v

theorem f406_actual_relative_kernel (v : Fin 9 → ℂ) :
    canonicalCOMLowerNat (natFourWordBlock f406basis v)=0 ↔
      ∃ x : Fin 3 → ℂ, complexify b406relative *ᵥ x=v :=
  natFour_lower_kernel_from_split f406basis f405basis
    f405_occupation_injective
    b406lower b406relative b406free b406split
    b406_relative_annihilated b406_relative_complete f406_actual_lower_block v

theorem f406_actual_relative_complete (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id 6) :
    canonicalCOMLowerNat f=0 ↔
      ∃ x : Fin 3 → ℂ, natFourWordBlock f406basis (complexify b406relative *ᵥ x)=f :=
  natFour_relative_homogeneous_complete 6 f406basis f405basis
    f406_basis_enumeration f406_occupation_injective
    f405_occupation_injective
    b406lower b406relative b406free b406split
    b406_relative_annihilated b406_relative_complete f406_actual_lower_block f hN hd

#print axioms f406_rational_lower_check
#print axioms f406_actual_lower_word
#print axioms f406_actual_lower_block
#print axioms f406_actual_relative_kernel
#print axioms f406_actual_relative_complete
end TorusLean.BosonFiniteCertificate
