import torus.shared.BosonFiniteCertificateNatFourWords

/-!
# The original frozen zero-contraction four-body normal tensor

The source is equation (B-row-four), expanded in the rational paper variables
x_j = sqrt(j!) a_j^dagger, partial_j = a_j / sqrt(j!). A spectator column
(p,j) has i=p+j-t. Pair labels are ordered, including both orders when unequal.
The coefficient of creators [a,p-a,j,i'] and annihilators [i,j',b,p'-b]
is y_(p,j) y_(p',j') i! / (j! a! (p-a)!).

Every original row and every column pair is retained, even zero and repeated
rows. The operator is this genuine finite sum of all-Nat differential words,
not a Riesz operator defined from a target matrix. No COM factor or finite
comparison is inserted here. COM 2/4 and the S4 normalization belong to their
own subsequent identities. The derivation of this displayed zero-contraction
formula from the complete physical row square is not asserted by this file.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open scoped BigOperators

/-- Original denominator, before any contraction or COM averaging. -/
def natFourDecodedRowEntry (c : ℤ) : ℚ := (c : ℚ) / 1000000000000

/-- The factorial ratio is the physical adjoint coefficient in the paper
variables; it is not an extra normalization of the four-particle lift. -/
def natFourOriginalCoefficient (t p j a : ℕ) (c c' : ℤ) : ℚ :=
  natFourDecodedRowEntry c * natFourDecodedRowEntry c' *
    ((p+j-t).factorial : ℚ) / ((j.factorial : ℚ) * a.factorial * (p-a).factorial)

/-- One literal term in the original zero-contraction formula. -/
def natFourOriginalTerm (t p j p' j' a b : ℕ) (c c' : ℤ) : NatFourNormalTerm where
  coefficient := natFourOriginalCoefficient t p j a c c'
  creators := [a,p-a,j,p'+j'-t]
  annihilators := [p+j-t,j',b,p'-b]

/-- Two pure-pair / spectator columns. Only two spectator columns have a
zero-contraction four-body contribution. The channel ordering is unchanged. -/
def natFourColumnPairTerms (t : ℕ)
    (left right : Option (ℕ × ℕ) × ℤ) : List NatFourNormalTerm :=
  match left.1, right.1 with
  | some (p,j), some (p',j') =>
      (List.range (p+1)).flatMap fun a =>
        (List.range (p'+1)).map fun b =>
          natFourOriginalTerm t p j p' j' a b left.2 right.2
  | _, _ => []

/-- All pairs of original columns, including their signed frozen integers. -/
def natFourOriginalRowTerms (t : ℕ) (row : List ℤ) : List NatFourNormalTerm :=
  ((columns t).zip row).flatMap fun left =>
    ((columns t).zip row).flatMap fun right => natFourColumnPairTerms t left right

/-- The original row indices are preserved rather than replaced by a chosen
nonzero-row basis. In particular the original 26 zero rows are still present. -/
def natFourOriginalRows : List (ℕ × List ℤ) :=
  (List.range 4).flatMap fun t => (frozenRows t).map fun row => (t,row)

theorem natFourOriginalRows_count : natFourOriginalRows.length = 138 := by
  decide +kernel

/-- Original source tensor. The only data are frozenRows, columns, and the
literal normal-order coefficient above. No b400--b416 certificate enters. -/
def natFourOriginalTerms : List NatFourNormalTerm :=
  natFourOriginalRows.flatMap fun entry => natFourOriginalRowTerms entry.1 entry.2

def paperNatFourOriginalOperator : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ :=
  paperNatFourTerms natFourOriginalTerms

def canonicalNatFourOriginalOperator : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ :=
  canonicalNatFourTerms natFourOriginalTerms

def natFourOriginalWordForm (s u : List ℕ) : ℚ :=
  natFourTermsForm natFourOriginalTerms s u

theorem canonicalNatFourOriginalOperator_conjugate :
    canonicalNatFourOriginalOperator =
      conjugateOperator factorialRootNat factorialRootNat_ne_zero paperNatFourOriginalOperator :=
  canonicalNatFourTerms_conjugate natFourOriginalTerms

/-- Source-to-operator identity for arbitrary Nat-labelled words. The true
falling factorial and physical occupation metric occur on the right. -/
theorem canonicalNatFourOriginalOperator_word_form (s u : List ℕ) :
    natOccupationInner (scaledWord factorialRootNat s)
      (canonicalNatFourOriginalOperator (scaledWord factorialRootNat u)) =
      (natFourOriginalWordForm s u : ℂ) :=
  canonicalNatFourTerms_form natFourOriginalTerms s u

/-- Arbitrary finite word family, without claiming that it exhausts a sector. -/
def natFourWordBlock {ι : Type*} [Fintype ι] (basis : ι → List ℕ) (x : ι → ℂ) : Core ℕ ℂ :=
  ∑ a, x a • scaledWord factorialRootNat (basis a)

/-- Generic finite synthesis is proved before substituting the large frozen
tensor, avoiding a kernel reduction through millions of literal source terms. -/
theorem canonicalNatFourTerms_block_form {ι : Type*} [Fintype ι]
    (terms : List NatFourNormalTerm) (basis : ι → List ℕ) (x y : ι → ℂ) :
    natOccupationInner (natFourWordBlock basis x)
      (canonicalNatFourTerms terms (natFourWordBlock basis y)) =
      ∑ a, ∑ b, star (x a) *
        (natFourTermsForm terms (basis a) (basis b) : ℂ) * y b := by
  classical
  unfold natFourWordBlock
  rw [map_sum, natOccupationInner_sum_left]
  apply Finset.sum_congr rfl
  intro a _
  rw [natOccupationInner_smul_left, natOccupationInner_sum_right, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [map_smul, natOccupationInner_smul_right,
    canonicalNatFourTerms_form]
  ring

/-- Exact full cross-form on any finite word family. Completeness and COM
compression are deliberately not assumptions of this source identity. -/
theorem canonicalNatFourOriginalOperator_block_form {ι : Type*} [Fintype ι]
    (basis : ι → List ℕ) (x y : ι → ℂ) :
    natOccupationInner (natFourWordBlock basis x)
      (canonicalNatFourOriginalOperator (natFourWordBlock basis y)) =
      ∑ a, ∑ b, star (x a) *
        (natFourOriginalWordForm (basis a) (basis b) : ℂ) * y b :=
  canonicalNatFourTerms_block_form natFourOriginalTerms basis x y

#print axioms natFourOriginalRows_count
#print axioms canonicalNatFourOriginalOperator_conjugate
#print axioms canonicalNatFourOriginalOperator_word_form
#print axioms canonicalNatFourTerms_block_form
#print axioms canonicalNatFourOriginalOperator_block_form
end TorusLean.BosonFiniteCertificate
