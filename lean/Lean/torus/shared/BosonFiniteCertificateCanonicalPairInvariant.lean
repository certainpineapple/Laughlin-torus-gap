import torus.shared.BosonFiniteCertificateCanonicalPairAdjoint

/-! True weighted-degree preserving action of the original canonical pair
Hamiltonian, before any finite block compression or inverse Gram operation. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.BosonFiniteCertificateCanonicalPairInvariant
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open TorusLean.Shared.BosonFiniteCertificateAction
open TorusLean.BosonFiniteCertificate
open scoped ComplexConjugate BigOperators

/-- All three surviving/recreated labels, with their exact order. -/
def pairOutputWord9 (d p a : ℕ) : List (Fin 9) :=
  [fin9 a, fin9 (p-a), fin9 (d-p)]

theorem pairCoefficient9_sq (p a : ℕ) (hp : p < 9) (ha : a ≤ p) :
    (pairCoefficient9 p a)^2 = (1 : ℂ) / ((a.factorial : ℂ) * ((p-a).factorial : ℂ)) := by
  have hs (j : ℕ) (hj : j < 9) :
      (pairFactorialRoot9 (fin9 j))^2 = (j.factorial : ℂ) := by
    unfold pairFactorialRoot9
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp [fin9, Nat.mod_eq_of_lt hj]
  simp only [pairCoefficient9, inv_pow, mul_pow]
  rw [hs a (by omega), hs (p-a) (by omega), one_div]

/-- The creator's true action contains no extra surviving-orbital factorial. -/
theorem canonicalPairCreator9_singleton (p t : ℕ) :
    canonicalPairCreator9 p (scaledWord pairFactorialRoot9 [fin9 t]) =
      ((List.range (p+1)).map fun a => (pairCoefficient9 p a)^2 •
        scaledWord pairFactorialRoot9 [fin9 a, fin9 (p-a), fin9 t]).sum := by
  rw [canonicalPairCreator9, linear_list_sum_apply]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  have hscalar : pairCoefficient9 p a * pairFactorialRoot9 (fin9 t) =
      (pairCoefficient9 p a)^2 * (pairFactorialRoot9 (fin9 a) *
        (pairFactorialRoot9 (fin9 (p-a)) * pairFactorialRoot9 (fin9 t))) := by
    dsimp [pairCoefficient9]
    field_simp [pairFactorialRoot9_ne_zero]
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, create, LinearMap.mulLeft_apply,
    scaledWord, wordScale, wordPolynomial, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, mul_smul_comm, smul_smul]
  rw [hscalar]

private theorem smul_list_map_sum {J : Type*} (c : ℂ) (l : List J)
    (f : J → Core (Fin 9) ℂ) : c • (l.map f).sum = (l.map fun a => c • f a).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [smul_add, ih]

/-- Explicit whole-core action on any true three-particle degree-d word.
The formula is derived from the differential operator and its actual adjoint. -/
theorem canonicalPairHamiltonian9_word_action (d : ℕ) (s : List ℕ)
    (hd : d < 9) (hs : sourceLabelsBounded9 s = true)
    (hlen : s.length = 3) (hsum : s.sum = d) :
    canonicalPairHamiltonian9 d (scaledWord pairFactorialRoot9 (s.map fin9)) =
      ((List.range (d+1)).map fun p =>
        ((List.range (p+1)).map fun a =>
          (((p.factorial : ℂ) / (2 : ℂ)^(p+1)) * (pairRemoval s p : ℂ) /
            ((a.factorial : ℂ) * ((p-a).factorial : ℂ))) •
              scaledWord pairFactorialRoot9 (pairOutputWord9 d p a)).sum).sum := by
  rw [canonicalPairHamiltonian9, linear_list_sum_apply]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  have hpd : p ≤ d := Nat.le_of_lt_succ (List.mem_range.mp hp)
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [canonicalPair9_word_action p d s hs (by omega) hd hlen hsum, map_smul,
    canonicalPairCreator9_singleton, smul_smul, smul_list_map_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  have hap : a ≤ p := Nat.le_of_lt_succ (List.mem_range.mp ha)
  rw [smul_smul, pairCoefficient9_sq p a (by omega) hap]
  congr 1
  simp only [div_eq_mul_inv, one_mul]

/-- Each actual output has exactly three particles, including repeated modes. -/
theorem pairOutputWord9_length (d p a : ℕ) : (pairOutputWord9 d p a).length = 3 := rfl

/-- The true output preserves total weighted orbital degree. The explicit
bounds are what rule out the modulo aliases in fin9. -/
theorem pairOutputWord9_degree (d p a : ℕ) (hd : d < 9) (hp : p ≤ d) (ha : a ≤ p) :
    ((pairOutputWord9 d p a).map Fin.val).sum = d := by
  simp only [pairOutputWord9, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    fin9, Nat.mod_eq_of_lt (show a < 9 by omega),
    Nat.mod_eq_of_lt (show p-a < 9 by omega), Nat.mod_eq_of_lt (show d-p < 9 by omega)]
  omega

/-- A successful derivative word cannot remove more weighted degree than
actually occurs in the source. This is independent of any cutoff table. -/
theorem pairRemoval_zero_of_degree_lt (s : List ℕ) (p : ℕ) (h : s.sum < p) :
    pairRemoval s p = 0 := by
  unfold pairRemoval
  have hz : ((List.range (p+1)).map fun a => removalWeight s [a,p-a]) =
      (List.range (p+1)).map (fun _ => (0:ℕ)) := by
    apply List.map_congr_left
    intro a ha
    have hap : a ≤ p := Nat.le_of_lt_succ (List.mem_range.mp ha)
    by_contra hn
    have hw : wordRemovalWeight s [a,p-a] ≠ 0 := by
      simpa only [removalWeight_eq_wordRemovalWeight] using hn
    have hs := eraseWord_sum_add s [a,p-a] hw
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at hs
    omega
  rw [hz]
  simp

theorem canonicalPair9_high_degree_zero (p d : ℕ) (s : List ℕ)
    (hp : p < 9) (hd : d < 9) (hdp : d < p)
    (hs : sourceLabelsBounded9 s = true) (hlen : s.length = 3) (hsum : s.sum = d) :
    canonicalPair9 p (scaledWord pairFactorialRoot9 (s.map fin9)) = 0 := by
  rw [canonicalPair9_word_action p d s hs hp hd hlen hsum,
    pairRemoval_zero_of_degree_lt s p (by rw [hsum]; exact hdp)]
  simp

theorem canonicalPairHamiltonian9_succ (d : ℕ) :
    canonicalPairHamiltonian9 (d+1) = canonicalPairHamiltonian9 d +
      (((d+1).factorial : ℂ) / (2 : ℂ)^((d+1)+1)) •
        (canonicalPairCreator9 (d+1)).comp (canonicalPair9 (d+1)) := by
  exact List.sum_range_succ _ (d+1)

/-- All nine degree blocks belong to the same finite canonical H_8:
higher pair degrees vanish by the actual derivative action. -/
theorem canonicalPairHamiltonian9_cutoff_word (d e : ℕ) (hde : d ≤ e) (he : e < 9)
    (s : List ℕ) (hs : sourceLabelsBounded9 s = true)
    (hlen : s.length = 3) (hsum : s.sum = d) :
    canonicalPairHamiltonian9 e (scaledWord pairFactorialRoot9 (s.map fin9)) =
      canonicalPairHamiltonian9 d (scaledWord pairFactorialRoot9 (s.map fin9)) := by
  induction e, hde using Nat.le_induction with
  | base => rfl
  | succ e hde ih =>
    rw [canonicalPairHamiltonian9_succ, LinearMap.add_apply, ih (by omega)]
    rw [LinearMap.smul_apply, LinearMap.comp_apply,
      canonicalPair9_high_degree_zero (e+1) d s (by omega) (by omega) (by omega) hs hlen hsum,
      map_zero, smul_zero, add_zero]

end TorusLean.Shared.BosonFiniteCertificateCanonicalPairInvariant
