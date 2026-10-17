import torus.shared.BosonFiniteCertificateNatFourRelativeCore
import torus.shared.BosonFiniteCertificateNatFourBasis400
import torus.shared.BosonFiniteCertificate400

/-! Degree-0 actual Nat COM lowering and complete relative kernel.
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

def f400emptyBasis : Fin 0 → List ℕ := Fin.elim0

theorem f400_empty_occupation_injective :
    Function.Injective (fun a : Fin 0 => wordOccupation (f400emptyBasis a)) := by
  intro a
  exact Fin.elim0 a

theorem f400_rational_lower_check : ∀ a : Fin 1,
    natFourRationalLowerWord (f400basis a) =
      ∑ b : Fin 0, b400lower b a • (wordPolynomial (f400emptyBasis b) : Core ℕ ℚ) := by
  intro a
  fin_cases a <;>
    norm_num [natFourRationalLowerWord,natFourLoweredWords,f400basis,f400emptyBasis,
      b400lower,Fin.sum_univ_succ,wordPolynomial,Algebra.smul_def] <;> ring

theorem f400_actual_lower_word (a : Fin 1) :
    canonicalCOMLowerNat (scaledWord factorialRootNat (f400basis a)) =
      ∑ b : Fin 0, (b400lower b a : ℂ) • scaledWord factorialRootNat (f400emptyBasis b) :=
  natFour_lower_action_of_rational_check (f400basis a) f400emptyBasis
    (fun b => b400lower b a) (f400_rational_lower_check a)

theorem f400_actual_lower_block (v : Fin 1 → ℂ) :
    canonicalCOMLowerNat (natFourWordBlock f400basis v) =
      natFourWordBlock f400emptyBasis (complexify b400lower *ᵥ v) :=
  natFourWordBlock_rect_action f400basis f400emptyBasis canonicalCOMLowerNat
    (complexify b400lower) f400_actual_lower_word v

theorem f400_actual_relative_kernel (v : Fin 1 → ℂ) :
    canonicalCOMLowerNat (natFourWordBlock f400basis v)=0 ↔
      ∃ x : Fin 1 → ℂ, complexify b400relative *ᵥ x=v :=
  natFour_lower_kernel_from_split f400basis f400emptyBasis
    f400_empty_occupation_injective
    b400lower b400relative b400free b400split
    b400_relative_annihilated b400_relative_complete f400_actual_lower_block v

theorem f400_actual_relative_complete (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id 0) :
    canonicalCOMLowerNat f=0 ↔
      ∃ x : Fin 1 → ℂ, natFourWordBlock f400basis (complexify b400relative *ᵥ x)=f :=
  natFour_relative_homogeneous_complete 0 f400basis f400emptyBasis
    f400_basis_enumeration f400_occupation_injective
    f400_empty_occupation_injective
    b400lower b400relative b400free b400split
    b400_relative_annihilated b400_relative_complete f400_actual_lower_block f hN hd

#print axioms f400_rational_lower_check
#print axioms f400_actual_lower_word
#print axioms f400_actual_lower_block
#print axioms f400_actual_relative_kernel
#print axioms f400_actual_relative_complete
#print axioms f400_empty_occupation_injective
end TorusLean.BosonFiniteCertificate
