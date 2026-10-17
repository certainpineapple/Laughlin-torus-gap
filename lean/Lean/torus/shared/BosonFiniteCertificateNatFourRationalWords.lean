import torus.shared.BosonFiniteCertificateNatFourCOMWords

/-! Exact rational word checks transport to the independently defined true
Nat COM operators via coefficient casting and factorial substitution. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open scoped BigOperators

def natFourRationalLowerWord (s : List ℕ) : Core ℕ ℚ :=
  ((natFourLoweredWords s).map fun cw =>
    (cw.1 : ℚ) • (wordPolynomial cw.2 : Core ℕ ℚ)).sum

def natFourRationalRaiseWord (s : List ℕ) : Core ℕ ℚ :=
  ((raisedWordsNat s).map fun w => (wordPolynomial w : Core ℕ ℚ)).sum

def natFourRationalWordCast : Core ℕ ℚ →+* Core ℕ ℂ :=
  MvPolynomial.map (Rat.castHom ℂ)

theorem natFourRationalWordCast_word (s : List ℕ) :
    natFourRationalWordCast (wordPolynomial s) = (wordPolynomial s : Core ℕ ℂ) := by
  induction s with
  | nil => simp only [wordPolynomial_nil,map_one]
  | cons j s ih =>
    simp only [wordPolynomial_cons,map_mul,natFourRationalWordCast,MvPolynomial.map_X] at ih ⊢
    rw [ih]

theorem natFourRationalWordCast_smul (c : ℚ) (p : Core ℕ ℚ) :
    natFourRationalWordCast (c • p) = (c : ℂ) • natFourRationalWordCast p := by
  simp only [Algebra.smul_def,map_mul,natFourRationalWordCast,MvPolynomial.algebraMap_eq,
    MvPolynomial.map_C,Rat.coe_castHom]

theorem natFourRationalWordCast_lower (s : List ℕ) :
    natFourRationalWordCast (natFourRationalLowerWord s) =
      paperNatFourCOMLower (wordPolynomial s) := by
  rw [paperNatFourCOMLower_word]
  simp only [natFourRationalLowerWord,map_list_sum,List.map_map,Function.comp_def,
    natFourRationalWordCast_smul,natFourRationalWordCast_word,Rat.cast_natCast]

theorem natFourRationalWordCast_raise (s : List ℕ) :
    natFourRationalWordCast (natFourRationalRaiseWord s) =
      paperCOMRaiseNat (wordPolynomial s) := by
  rw [paperCOMRaiseNat_word]
  simp only [natFourRationalRaiseWord,map_list_sum,List.map_map,Function.comp_def,
    natFourRationalWordCast_word]

theorem natFour_lower_action_of_rational_check {m : ℕ} (s : List ℕ)
    (dst : Fin m → List ℕ) (c : Fin m → ℚ)
    (h : natFourRationalLowerWord s = ∑ b, c b • (wordPolynomial (dst b) : Core ℕ ℚ)) :
    canonicalCOMLowerNat (scaledWord factorialRootNat s) =
      ∑ b, (c b : ℂ) • scaledWord factorialRootNat (dst b) := by
  have hp := congrArg natFourRationalWordCast h
  simp only [natFourRationalWordCast_lower,map_sum,natFourRationalWordCast_smul,
    natFourRationalWordCast_word] at hp
  rw [← rescaleHom_word,canonicalNatFourCOMLower_rescale,hp,map_sum]
  simp only [map_smul,rescaleHom_word]

theorem natFour_raise_action_of_rational_check {m : ℕ} (s : List ℕ)
    (dst : Fin m → List ℕ) (c : Fin m → ℚ)
    (h : natFourRationalRaiseWord s = ∑ b, c b • (wordPolynomial (dst b) : Core ℕ ℚ)) :
    canonicalCOMRaiseNat (scaledWord factorialRootNat s) =
      ∑ b, (c b : ℂ) • scaledWord factorialRootNat (dst b) := by
  have hp := congrArg natFourRationalWordCast h
  simp only [natFourRationalWordCast_raise,map_sum,natFourRationalWordCast_smul,
    natFourRationalWordCast_word] at hp
  rw [← rescaleHom_word,canonicalCOMRaiseNat_rescale,hp,map_sum]
  simp only [map_smul,rescaleHom_word]

#print axioms natFourRationalWordCast_word
#print axioms natFourRationalWordCast_smul
#print axioms natFourRationalWordCast_lower
#print axioms natFourRationalWordCast_raise
#print axioms natFour_lower_action_of_rational_check
#print axioms natFour_raise_action_of_rational_check
end TorusLean.BosonFiniteCertificate
