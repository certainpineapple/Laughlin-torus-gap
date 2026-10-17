import torus.shared.FermionLocalJetFourCouplingIntegerWords
import OAI.Analysis.Laughlin.FourBody.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-! Original increasing four-orbital Slater presentation. The integer check
below compares the original S45/pair word with the original six signed terms
of F-L, in the actual alternating word quotient. No Gram or source equality
is postulated. The generic check interface is discharged degree by degree. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.BosonFiniteCertificate
open TorusLean.Shared.ThermalCoherentFermionCOMWords
open TorusLean.Shared.ThermalCoherentFermionJetWord
open scoped BigOperators ComplexConjugate

abbrev SlaterIndex (D : ℕ) := Fin (OAI.Laughlin.Certificate.quadruples D).length

def slaterTuple (D : ℕ) (A : SlaterIndex D) : ℕ × ℕ × ℕ × ℕ :=
  (OAI.Laughlin.Certificate.quadruples D)[A.val]

def slaterLabels (D : ℕ) (A : SlaterIndex D) : Fin 4 → ℕ :=
  ![(slaterTuple D A).1,(slaterTuple D A).2.1,
    (slaterTuple D A).2.2.1,(slaterTuple D A).2.2.2]

def formalSlater (D : ℕ) (A : SlaterIndex D) : FormalExterior :=
  formalExteriorWord 4 (slaterLabels D A)

/-- The six original signs +,-,+,+,-,+, with the same V and factorials as F-L. -/
def integerSlaterNumerator (D r : ℕ) (A : ℕ × ℕ × ℕ × ℕ) : ℤ :=
  let (a,b,c,d) := A
  let term := fun (x y j k : ℕ) => ((x:ℤ)-(y:ℤ)) *
    ((x+y-1).factorial:ℤ) * (j.factorial:ℤ) * (k.factorial:ℤ) *
    OAI.Laughlin.Certificate.V r D D (x+y-1) j k
  term a b c d - term a c b d + term a d b c + term b c a d -
    term b d a c + term c d a b

def integerSlaterWords (D r : ℕ) : IntegerFourWords :=
  ∑ A : SlaterIndex D, Finsupp.single (slaterLabels D A)
    (integerSlaterNumerator D r (slaterTuple D A))

def copyInverseRoot (D : ℕ) (r : OddMode D) : ℂ :=
  (factorialRootNat r.val.val * factorialRootNat (D-r.val.val))⁻¹

def slaterRoot (D : ℕ) (A : SlaterIndex D) : ℂ :=
  ∏ j : Fin 4, factorialRootNat (slaterLabels D A j)

/-- Literal manuscript L divided by the original copy and Slater factorial
roots. The raw exterior image is never declared isometric. -/
def originalSlaterMatrix (D : ℕ) : Matrix (SlaterIndex D) (OddMode D) ℂ :=
  fun A r => copyInverseRoot D r *
    (OAI.Laughlin.Certificate.L D r.val.val (slaterTuple D A):ℂ) / slaterRoot D A

 theorem fourSourceScale_highest (D : ℕ) (r : OddMode D) :
    fourSourceScale D D r.val.val =
      copyInverseRoot D r / (2:ℂ)^(D-(r.val.val+1)/2) := by
  have hrD : r.val.val≤D := Nat.le_of_lt_succ r.val.isLt
  obtain ⟨k,hk⟩ := r.property
  have hex : D+(D-r.val.val)=2*(D-(r.val.val+1)/2)+1 := by omega
  have h2 : (Real.sqrt (2:ℝ):ℂ)≠0 := by norm_num
  have hs : (Real.sqrt (2:ℝ):ℂ)^2=2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  simp only [fourSourceScale,Nat.sub_self,factorialRootNat,Nat.factorial_zero,
    Nat.cast_one,Real.sqrt_one,Complex.ofReal_one,mul_one]
  change (Real.sqrt (2:ℝ):ℂ) /
    (factorialRootNat r.val.val * factorialRootNat (D-r.val.val) *
      (Real.sqrt (2:ℝ):ℂ)^(D+(D-r.val.val))) = _
  rw [hex,pow_add,pow_one,pow_mul,hs]
  unfold copyInverseRoot
  field_simp [factorialRootNat_ne_zero,h2] <;> ring

 theorem original_L_integer_numerator (D : ℕ) (r : OddMode D)
    (A : ℕ × ℕ × ℕ × ℕ) :
    (OAI.Laughlin.Certificate.L D r.val.val A:ℂ) =
      (integerSlaterNumerator D r.val.val A:ℂ) /
        (2:ℂ)^(D-(r.val.val+1)/2) := by
  have hrD : r.val.val≤D := Nat.le_of_lt_succ r.val.isLt
  obtain ⟨k,hk⟩ := r.property
  have hex : ((1:ℤ)-2*(D:ℤ)+(r.val.val:ℤ))/2 =
      -((D-(r.val.val+1)/2:ℕ):ℤ) := by omega
  rcases A with ⟨a,b,c,d⟩
  simp only [OAI.Laughlin.Certificate.L,integerSlaterNumerator,hex]
  push_cast
  simp only [zpow_neg,zpow_natCast]
  ring

 theorem original_coupled_slater_of_integer_check (D : ℕ)
    (hcheck : ∀ r : OddMode D, alternateIntegerFourWords
      (integerSourceWords D D r.val.val) =
        alternateIntegerFourWords (integerSlaterWords D r.val.val))
    (r : OddMode D) :
    formalCoupledColumn D r =
      ∑ A : SlaterIndex D, originalSlaterMatrix D A r • formalSlater D A := by
  rw [← realize_highestCoupledWords,highestCoupledWords,
    descendantWords_integer_source D D r.val.val
      (Nat.le_of_lt_succ r.val.isLt) (Nat.le_refl D),map_smul,
    integer_alternating_check_sound _ _ (hcheck r)]
  simp only [integerSlaterWords,map_sum,Finset.smul_sum,
    normalizeIntegerFourWords,Finsupp.linearCombination_single,
    realize,map_zsmul,map_smul,Finsupp.linearCombination_single,one_smul]
  apply Finset.sum_congr rfl
  intro A hA
  rw [fourSourceScale_highest]
  simp only [originalSlaterMatrix,formalSlater,slaterRoot,
    original_L_integer_numerator,← Int.cast_smul_eq_zsmul ℂ,smul_smul]
  congr 1
  ring

 theorem slaterIndex_sum {K : Type*} [AddCommMonoid K] (D : ℕ)
    (f : (ℕ × ℕ × ℕ × ℕ) → K) :
    (∑ A : SlaterIndex D, f (slaterTuple D A)) =
      ((OAI.Laughlin.Certificate.quadruples D).map f).sum := by
  rw [← List.sum_ofFn]
  exact congrArg List.sum (List.ofFn_getElem_eq_map _ f)

#print axioms fourSourceScale_highest
#print axioms original_L_integer_numerator
#print axioms original_coupled_slater_of_integer_check
#print axioms slaterIndex_sum
end TorusLean.Shared.FermionLocalJet.FourCoupling
